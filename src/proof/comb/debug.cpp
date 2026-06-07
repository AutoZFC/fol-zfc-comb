#include "src/proof/comb/debug.h"

#include <sstream>

namespace logic::proof::comb::debug {

std::string format_term(const Term& t) {
    if (t.is_fixed())       return "f" + std::to_string(t.as_variable());
    if (t.is_generalized()) return "g" + std::to_string(t.as_variable());
    if (t.is_description()) return "<desc>";
    return "?";
}

std::string format_args(const std::vector<Term>& args) {
    std::string s = "[";
    for (size_t i = 0; i < args.size(); ++i) {
        if (i) s += ",";
        s += format_term(args[i]);
    }
    return s + "]";
}

std::string format_predicate(const VertexLabel& lbl) {
    std::string s = lbl.negated ? "~" : "";
    s += lbl.pred.valid() ? lbl.pred.get().get_name() : "<invalid>";
    s += "/" + std::to_string(lbl.pred.valid() ? lbl.pred.get().get_num_args() : 0);
    return s;
}

std::string format_vertex_label(const VertexLabel& lbl) {
    switch (lbl.kind) {
        case VertexKind::Atom:
            return format_predicate(lbl) + format_args(lbl.args);
        case VertexKind::Binder:
            return std::string(lbl.is_existential ? "∃" : "∀") +
                   "f" + std::to_string(lbl.var);
        case VertexKind::One:
            return "1";
    }
    return "<unknown>";
}

namespace {

std::string format_edges(const Edges& edges) {
    std::string s;
    bool first = true;
    for (const auto& e : edges) {
        if (!first) s += " ";
        s += "(" + std::to_string(e.first) + "," + std::to_string(e.second) + ")";
        first = false;
    }
    return s;
}

}  // namespace

std::string dump_target(const Fograph& target) {
    std::ostringstream os;
    os << "=== TARGET (" << target.num_vertex() << " vertices) ===\n";
    for (size_t i = 0; i < target.labels.size(); ++i) {
        os << "  v" << i << " " << format_vertex_label(target.labels[i]) << "\n";
    }
    if (!target.cograph_edges.empty()) {
        os << "  cograph edges: " << format_edges(target.cograph_edges) << "\n";
    }
    if (!target.binding_edges.empty()) {
        os << "  binding edges: " << format_edges(target.binding_edges) << "\n";
    }
    return os.str();
}

std::string dump_source_vertices(const Fonet& source,
                                 const Fograph& target,
                                 const std::vector<size_t>& fibration)
{
    std::ostringstream os;
    os << "=== SOURCE VERTICES (" << source.num_vertex
       << ", fibration → target) ===\n";
    for (size_t v = 0; v < source.num_vertex; ++v) {
        size_t tgt = (v < fibration.size()) ? fibration[v] : static_cast<size_t>(-1);
        os << "  v" << v << " → t" << tgt << " ";
        if (tgt < target.labels.size()) {
            os << format_vertex_label(target.labels[tgt]);
        } else {
            os << "<fibration OOB>";
        }
        os << "\n";
    }
    return os.str();
}

std::string dump_source_structure(const Fonet& source) {
    std::ostringstream os;
    os << "=== SOURCE STRUCTURE ===\n";
    if (!source.cograph_edges.empty()) {
        os << "  cograph edges: " << format_edges(source.cograph_edges) << "\n";
    }
    if (!source.binding_edges.empty()) {
        os << "  binding edges: " << format_edges(source.binding_edges) << "\n";
    }
    return os.str();
}

std::string dump_links(const Fonet& source,
                       const Fograph& target,
                       const std::vector<size_t>& fibration)
{
    if (source.links.empty()) return "";
    std::ostringstream os;
    os << "=== LINKS (" << source.links.size() << ") ===\n";
    auto label_of = [&](size_t v) -> std::string {
        if (v >= fibration.size()) return "<OOB>";
        size_t t = fibration[v];
        if (t >= target.labels.size()) return "<fib-OOB>";
        return format_vertex_label(target.labels[t]);
    };
    for (const auto& lk : source.links) {
        os << "  {v" << lk.first << ",v" << lk.second << "}  "
           << "L=" << label_of(lk.first)
           << "  R=" << label_of(lk.second) << "\n";
    }
    return os.str();
}

std::string dump_dualizer(const Fonet& source) {
    if (source.dualizer.empty()) return "=== DUALIZER (empty) ===\n";
    std::ostringstream os;
    os << "=== DUALIZER (" << source.dualizer.size() << " entries) ===\n";
    for (const auto& [k, t] : source.dualizer) {
        os << "  f" << k << " → " << format_term(t) << "\n";
    }
    return os.str();
}

std::string dump_proof(const CombProof& cp) {
    std::ostringstream os;
    os << "==================== CombProof";
    if (!cp.claim_name.empty()) os << " '" << cp.claim_name << "'";
    os << " ====================\n";
    os << dump_target(cp.target);
    os << dump_source_vertices(cp.source, cp.target, cp.fibration);
    os << dump_source_structure(cp.source);
    os << dump_links(cp.source, cp.target, cp.fibration);
    os << dump_dualizer(cp.source);
    os << "==================== end ====================\n";
    return os.str();
}

}  // namespace logic::proof::comb::debug
