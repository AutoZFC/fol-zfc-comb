#!/usr/bin/env python3
"""Run comb_checker on every fol_proof target under zfc/.

Parses zfc/*/BUILD.bazel for fol_proof and fol_library targets, builds the
transitive dep graph, runs each fol_proof through comb_checker with the
right deps, and tallies results.
"""

from __future__ import annotations

import re
import subprocess
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
BIN = REPO / "bazel-bin" / "src" / "tools" / "comb_checker"

@dataclass
class Target:
    name: str
    package: str           # e.g. "zfc/basics"
    kind: str              # "library" or "proof"
    header: str            # relative path within package
    proof: str | None = None  # relative path within package, for fol_proof
    deps: list[str] = field(default_factory=list)  # ":lib_name" or "//path:name"

def parse_build_files() -> dict[tuple[str, str], Target]:
    """Returns map from (package, name) → Target."""
    targets: dict[tuple[str, str], Target] = {}
    for build in REPO.glob("zfc/**/BUILD.bazel"):
        package = str(build.parent.relative_to(REPO))
        text = build.read_text()
        # Strip comments (line-based) — simpler than full parsing.
        lines = []
        for line in text.splitlines():
            stripped = line.lstrip()
            if stripped.startswith("#"): continue
            lines.append(line)
        text = "\n".join(lines)

        # Match fol_library(...) and fol_proof(...) blocks.
        for m in re.finditer(
            r'fol_(library|proof)\s*\(\s*([^)]*?)\)',
            text, re.DOTALL):
            kind = "library" if m.group(1) == "library" else "proof"
            body = m.group(2)
            name = re.search(r'name\s*=\s*"([^"]+)"', body)
            header = re.search(r'header\s*=\s*"([^"]+)"', body)
            proof = re.search(r'proof\s*=\s*"([^"]+)"', body)
            deps_m = re.search(r'deps\s*=\s*\[(.*?)\]', body, re.DOTALL)
            deps = []
            if deps_m:
                deps = re.findall(r'"([^"]+)"', deps_m.group(1))
            if not name or not header: continue
            t = Target(
                name=name.group(1),
                package=package,
                kind=kind,
                header=header.group(1),
                proof=proof.group(1) if proof else None,
                deps=deps,
            )
            targets[(package, name.group(1))] = t
    return targets

def resolve_dep(dep: str, pkg: str) -> tuple[str, str]:
    """Resolve a Bazel dep label to (package, name)."""
    if dep.startswith("//"):
        # "//zfc/basics:name"
        p, _, n = dep[2:].partition(":")
        return (p, n)
    if dep.startswith(":"):
        return (pkg, dep[1:])
    raise ValueError(f"unrecognized dep: {dep!r}")

def transitive_libraries(start: tuple[str, str],
                          targets: dict[tuple[str, str], Target]) -> list[Target]:
    """All transitive fol_library targets reachable from start (BFS, dedup,
       order = closer-deps-last so the caller can pass deepest first)."""
    out: list[Target] = []
    seen: set[tuple[str, str]] = set()
    stack = [start]
    while stack:
        key = stack.pop()
        if key in seen: continue
        seen.add(key)
        t = targets.get(key)
        if t is None: continue
        # Pre-order: dependents before deps. Reverse later if needed.
        if key != start: out.append(t)
        for d in t.deps:
            stack.append(resolve_dep(d, t.package))
    return out

def transitive_proofs_topo(start: tuple[str, str],
                            targets: dict[tuple[str, str], Target]) -> list[Target]:
    """All transitive fol_proof targets in topological order (deps first).
       The start target is NOT included."""
    visited: set[tuple[str, str]] = set()
    order: list[Target] = []
    def visit(key: tuple[str, str]):
        if key in visited: return
        visited.add(key)
        t = targets.get(key)
        if t is None: return
        for d in t.deps:
            visit(resolve_dep(d, t.package))
        if t.kind == "proof" and key != start:
            order.append(t)
    visit(start)
    return order

def gather_def_paths(targets_list: list[Target]) -> list[str]:
    """Gather unique .fol.def paths in dep order."""
    seen = set()
    paths = []
    for t in targets_list:
        p = f"{t.package}/{t.header}"
        if p in seen: continue
        seen.add(p); paths.append(p)
    return paths

def run_one(t: Target, targets: dict[tuple[str, str], Target]) -> tuple[str, int, int, str]:
    """Returns (name, ok_count, total, stage_summary)."""
    if t.proof is None: return (t.name, 0, 0, "no proof")
    proof_path = f"{t.package}/{t.proof}"
    # Transitive .fol.def files (from all lib + proof deps).
    libs = transitive_libraries((t.package, t.name), targets)
    # Also include defs of any dep that is a proof (their headers).
    proofs = transitive_proofs_topo((t.package, t.name), targets)
    all_defs = []
    for ti in libs + proofs:
        p = f"{ti.package}/{ti.header}"
        if p not in all_defs: all_defs.append(p)
    # Dep proof paths in topo order.
    dep_proof_paths = [f"{ti.package}/{ti.proof}" for ti in proofs if ti.proof]

    args = [str(BIN), f"{t.package}/{t.header}", proof_path] + all_defs
    if dep_proof_paths:
        args.append("--")
        args.extend(dep_proof_paths)

    try:
        result = subprocess.run(
            args, cwd=REPO, capture_output=True, text=True, timeout=300)
        out = result.stdout + result.stderr
    except subprocess.TimeoutExpired:
        return (t.name, 0, 0, "timeout")

    m = re.search(r'Theorems in [^:]+: (\d+)', out)
    total = int(m.group(1)) if m else 0
    m = re.search(r'^\s*OK: (\d+)', out, re.MULTILINE)
    ok = int(m.group(1)) if m else 0
    # First-stage summary line.
    stages = re.findall(r'FAIL @ (\S+): (\d+)', out)
    stage_summary = ", ".join(f"{s}={n}" for s, n in stages) or "all ok"
    return (t.name, ok, total, stage_summary)

def collect_global_topo(targets: dict[tuple[str, str], Target]) -> list[Target]:
    """Topological order of ALL fol_proof targets: a target's deps come
       before itself."""
    visited: set[tuple[str, str]] = set()
    order: list[Target] = []
    def visit(key: tuple[str, str]):
        if key in visited: return
        visited.add(key)
        t = targets.get(key)
        if t is None: return
        for d in t.deps:
            visit(resolve_dep(d, t.package))
        if t.kind == "proof":
            order.append(t)
    # Visit all proofs in a stable seed order.
    proofs = sorted([t for t in targets.values() if t.kind == "proof"],
                     key=lambda t: (t.package, t.name))
    for p in proofs:
        visit((p.package, p.name))
    return order

def main():
    if not BIN.exists():
        print(f"ERROR: comb_checker not built at {BIN}", file=sys.stderr)
        sys.exit(2)
    targets = parse_build_files()
    topo = collect_global_topo(targets)
    if not topo:
        print("No fol_proof targets found.", file=sys.stderr)
        sys.exit(1)

    # All transitive .fol.def headers needed.
    all_def_paths: list[str] = []
    seen_defs: set[str] = set()
    for t in topo:
        for libt in transitive_libraries((t.package, t.name), targets):
            p = f"{libt.package}/{libt.header}"
            if p not in seen_defs:
                seen_defs.add(p); all_def_paths.append(p)
        p = f"{t.package}/{t.header}"
        if p not in seen_defs:
            seen_defs.add(p); all_def_paths.append(p)

    # Main file: the last one in topo. Dep proofs: all earlier ones.
    main_t = topo[-1]
    dep_proofs = [f"{t.package}/{t.proof}" for t in topo[:-1] if t.proof]
    main_proof = f"{main_t.package}/{main_t.proof}"
    main_header = f"{main_t.package}/{main_t.header}"

    args = [str(BIN), main_header, main_proof] + all_def_paths
    if dep_proofs:
        args.append("--")
        args.extend(dep_proofs)

    print(f"Running comb_checker on {len(topo)} proof files "
          f"({len(all_def_paths)} headers).")
    print(f"Last file: {main_proof}\n")
    result = subprocess.run(args, cwd=REPO, capture_output=True,
                             text=True, timeout=1800)
    out = result.stdout + result.stderr

    # Parse summary.
    m = re.search(r'Total theorems processed: (\d+)', out)
    total = int(m.group(1)) if m else 0
    m = re.search(r'^\s*OK: (\d+)', out, re.MULTILINE)
    ok = int(m.group(1)) if m else 0
    m = re.search(r'^\s*unproved-marker: (\d+)', out, re.MULTILINE)
    unproved = int(m.group(1)) if m else 0
    stages = re.findall(r'FAIL @ (\S+): (\d+)', out)

    print(out)
    print(f"\n=== Coverage summary ===")
    print(f"  Total theorems: {total}")
    print(f"  OK end-to-end:  {ok} ({100.0*ok/total:.1f}%)" if total else "  no theorems")
    print(f"  unproved markers: {unproved}")
    for stage, count in stages:
        print(f"  FAIL @ {stage}: {count}")

if __name__ == "__main__":
    main()
