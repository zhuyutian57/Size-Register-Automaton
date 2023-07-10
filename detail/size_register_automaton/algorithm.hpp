
#ifndef atl_detail_size_register_automaton_algorithm_hpp
#define atl_detail_size_register_automaton_algorithm_hpp

#include "size_register_automaton.hpp"

namespace atl::detail {

  #define SRA size_register_automaton_gen
  
  typedef SRA::State State;
  typedef SRA::Transition Transition;
  typedef SRA::TransitionProperty TransitionProperty;
  
  typedef Guard::Bound Bound;
  typedef std::vector<Bound> Bounds;

  bool
  is_self_triggered(
    const Guard& g1, const ModesTr& mt1,
    const Guard& g2, const ModesTr& mt2) {
    if(g1 != g2) return true;
    const int n = mt1.first.size();
    assert(n == mt2.first.size());
    for(int i = 0; i < n; i++)
      if(mt1.first[i] != mt2.first[i]) return true;
    assert(n == mt1.second.size());
    assert(n == mt2.second.size());
    for(int i = 0; i < n; i++)
      if(mt1.first[i] == RegisterMode::COUNT
          && mt1.second[i] != mt2.second[i])
        return true;
    return false;
  }

  Bounds
  intersect_bounds(const Bounds& bounds, Bound b) {
    Bounds n_bounds;
    for(auto bp : bounds) {
      Bound nb = std::make_pair(
        std::max(b.first, bp.first), -1);
      if(bp.second != -1 || b.second != -1) {
        if(b.second == -1) {
          nb.second = bp.second;
        } else if(bp.second == -1) {
          nb.second = b.second;
        } else {
          nb.second = std::min(b.second, bp.second);
        }
      }
      if(nb.first > nb.second) continue;
      n_bounds.push_back(nb);
    }
    return n_bounds;
  }

  // Check deterministc
  bool
  is_deterministic(const SRA& sra) {
    auto state_iter = sra.states();
    for(auto it = state_iter.first; it != state_iter.second; it++) {
      auto out_edge_iter = sra.out_transitions(*it);
      for(auto oet1 = out_edge_iter.first; oet1 != out_edge_iter.second; oet1++)
        for(auto oet2 = out_edge_iter.first; oet2 != out_edge_iter.second; oet2++)
          if(oet1 != oet2) {
            const Guard& g1 = sra.get_property(*oet1);
            const Guard& g2 = sra.get_property(*oet2);
            Modes m1 = sra.get_property(oet1->m_source);
            Modes m1p = sra.get_property(oet1->m_target);
            Modes m2 = sra.get_property(oet2->m_source);
            Modes m2p = sra.get_property(oet2->m_target);
            if(!is_self_triggered(
              g1, std::make_pair(m1, m1p),
              g2, std::make_pair(m2, m2p)))
              return false;
          }
    }
    return true;
  }

  bool
  check_count_to_idle(const Modes& m1, const Modes& m2) {
    assert(m1.size() == m2.size());
    for(int i = 0; i < m1.size(); i++)
      if(m1[i] == RegisterMode::IDLE &&
          m2[i] == RegisterMode::COUNT)
        return false;
    return true;
  }

  SRA
  get_full_sra(const SRA& sra) {
    SRA fsra = sra;
    
    std::unordered_map<int, State> qm_map;
    int n_reg = sra.num_registers();
    int n_qm = (1 << n_reg);
    for(int i = 0; i < n_qm; i++) {
      Modes m = binary_to_modes(i, n_reg);
      qm_map[i] = fsra.add_state(m);
    }
    
    int_variable cur("cur");
    propositional_fomula top = cur >= 0;
    for(int i = 0; i < n_qm; i++) {
      Modes m1 = binary_to_modes(i, n_reg);
      for(int j = 0; j < n_qm; j++) {
        Modes m2 = binary_to_modes(j, n_reg);
        bool ok_mode_tr = true;
        for(int k = 0; k < n_reg; k++)
          if(m1[k] == RegisterMode::IDLE &&
            m2[k] == RegisterMode::COUNT)
            ok_mode_tr = false;
        if(!ok_mode_tr) continue;
        fsra.add_transition(qm_map[i], qm_map[j], top);
      }
    }

    // compute the negation of each transition
    auto state_iter_pair = sra.states();
    for(auto s_it = state_iter_pair.first;
      s_it != state_iter_pair.second; s_it++) {
      Modes ms = sra.get_property(*s_it);
      for(int i = 0; i < n_qm; i++) {
        Modes m1p = binary_to_modes(i, n_reg);
        if(!check_count_to_idle(ms, m1p)) continue;
        const Guard& g1 = top;
        const ModesTr& mt1 = std::make_pair(ms, m1p);
        auto out_edge_iter = sra.out_transitions(*s_it);
        std::vector<Bound> bounds;
        bounds.push_back(std::make_pair(0, -1));
        for(auto o_it = out_edge_iter.first;
          o_it != out_edge_iter.second && !bounds.empty(); o_it++) {
          const Guard& g2 = sra.get_property(*o_it);
          Modes m2p = sra.get_property(o_it->m_target);
          if(is_self_triggered(
            g1, mt1, g2, std::make_pair(ms, m2p)
          )) continue;
          Bound b = g2.get_bounds();
          Bounds nb1, nb2;
          if(b.first > 0)
            nb1 = intersect_bounds(bounds, std::make_pair(0, b.first - 1));
          if(b.second != -1)
            nb2 = intersect_bounds(bounds, std::make_pair(b.second + 1, -1));
          bounds.clear();
          for(auto nb : nb1) bounds.push_back(nb);
          for(auto nb : nb2) bounds.push_back(nb);
        }
        for(auto b : bounds) {
          Guard guard(cur >= b.first);
          if(b.second != -1)
            guard = guard & (cur <= b.second);
          fsra.add_transition(*s_it, qm_map[i], guard);
        }
      }
    }
    return fsra;
  }

  // Complement
  typedef size_register_automaton_gen::StateSet StateSet;
  SRA
  complement(const SRA& sra) {
    assert(is_deterministic(sra));
    SRA fsra = get_full_sra(sra);
    StateSet n_final_state_set;
    for(auto s : fsra.state_set())
      if(!fsra.is_final_state(s))
        n_final_state_set.insert(s);
    fsra.set_final_state_set(n_final_state_set);
    return fsra;
  }

  // Product
  SRA
  product(const SRA& lhs, const SRA& rhs) {
    SRA out;
    auto state2map = detail::product(lhs, rhs, out);

    out.set_register(lhs.num_registers() + rhs.num_registers());
    for(auto sp : state2map) {
      if(lhs.is_initial_state(sp.first.first) &&
          rhs.is_initial_state(sp.first.second))
        out.set_initial_state(sp.second);
      if(lhs.is_final_state(sp.first.first) &&
          rhs.is_final_state(sp.first.second))
        out.set_final_state(sp.second);
    }
    return out;
  }

  // Concatenate
  typedef size_register_automaton_gen::StateSet StateSet;

  SRA
  concatenate(const SRA& lhs, const SRA& rhs) {
    SRA out(lhs.num_registers() + rhs.num_registers());

    Modes lhs_idles, rhs_idles;
    for(int i = 0; i < lhs.num_registers(); i++)
      lhs_idles.push_back(RegisterMode::IDLE);
    for(int i = 0; i < rhs.num_registers(); i++)
      rhs_idles.push_back(RegisterMode::IDLE);

    std::unordered_map<State, State> lhs_state2state;
    std::unordered_map<State, State> rhs_state2state;
    for(auto state : lhs.state_set()) {
      Modes m = lhs.get_property(state);
      lhs_state2state[state] = out.add_state(m + rhs_idles);
    }
    for(auto state : rhs.state_set()) {
      if(rhs.is_initial_state(state)) continue;
      Modes m = rhs.get_property(state);
      rhs_state2state[state] = out.add_state(lhs_idles + m);
    }

    out.set_initial_state(lhs_state2state[lhs.initial_state()]);

    for(auto final_state : rhs.final_state_set()) {
      if(!rhs.is_initial_state(final_state)) {
        State n_final_state = rhs_state2state[final_state];
        out.set_final_state(n_final_state);
      } else for(auto lhs_final_state : lhs.final_state_set()) {
        State n_final_state = lhs_state2state[lhs_final_state];
        out.set_final_state(n_final_state);
      }
    }
    
    auto lhs_transition_iter = lhs.transitions();
    for(auto t_it = lhs_transition_iter.first;
      t_it != lhs_transition_iter.second; t_it++) {
        State ns = lhs_state2state[lhs.source(*t_it)];
        State nt = lhs_state2state[lhs.target(*t_it)];
        out.add_transition(ns, nt, lhs.get_property(*t_it)); 
    }

    auto rhs_transition_iter = rhs.transitions();
    for(auto t_it = rhs_transition_iter.first;
      t_it != rhs_transition_iter.second; t_it++) {
        State s = rhs.source(*t_it);
        State t = rhs.target(*t_it);
        StateSet ns_set, nt_set;
        if(!rhs.is_initial_state(s)) ns_set.insert(rhs_state2state[s]);
        else for(auto lhs_final_state : lhs.final_state_set())
          ns_set.insert(lhs_state2state[lhs_final_state]);
        if(!rhs.is_initial_state(t)) nt_set.insert(rhs_state2state[t]);
        else for(auto lhs_final_state : lhs.final_state_set())
          nt_set.insert(lhs_state2state[lhs_final_state]);
        for(auto ns : ns_set) for(auto nt : nt_set)
          out.add_transition(ns, nt, rhs.get_property(*t_it));
    }

    return out;
  }

}

#endif /* atl_detail_size_register_automaton_algorithm_hpp */