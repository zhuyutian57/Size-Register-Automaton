
#ifndef atl_detail_size_register_automaton_algorithm_hpp
#define atl_detail_size_register_automaton_algorithm_hpp

#include "size_register_automaton.hpp"

namespace atl::detail {

  #define SRA size_register_automaton_gen

  // Complement
  typedef SRA::State State;
  typedef SRA::TransitionProperty TransitionProperty;
  
  typedef Guard::Bound Bound;
  typedef std::vector<Bound> Bounds;

  bool
  is_self_triggered(
    const TransitionProperty& t1,
    const TransitionProperty& t2) {
    if(t1.default_property != t2.default_property)
      return true;
    const Modes& m1 = t1.extended_property.first;
    const Modes& m2 = t2.extended_property.first;
    const int n = m1.size();
    assert(n == m2.size());
    for(int i = 0; i < n; i++)
      if(m1[i] != m2[i]) return true;
    const Modes& m1p = t1.extended_property.second;
    const Modes& m2p = t2.extended_property.second;
    assert(n == m1p.size());
    assert(n == m2p.size());
    for(int i = 0; i < n; i++)
      if(m1[i] == RegisterMode::COUNT && m1p[i] != m2p[i])
        return true;
    return false;
  }

  Bounds
  intersect_bounds(const Bounds& bounds, Bound b) {
    Bounds n_bounds;
    for(auto bp : bounds) {
      Bound nb = std::make_pair(-1, -1);
      if(b.second == -1 && bp.second == -1)
        nb.first = std::max(b.first, bp.first);
      else if(b.second == -1) {
        nb.first = std::max(b.first, bp.first);
        nb.second = bp.second;
      } else {
        nb.first = std::max(b.first, bp.first);
        nb.second = std::min(b.second, bp.second);
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
          if(oet1 != oet2)
            if(!is_self_triggered(
              sra.get_property(*oet1),
              sra.get_property(*oet2)))
              return false;
    }
    return true;
  }

  SRA
  get_full_sra(const SRA& sra) {
    SRA fsra = sra;
    
    std::unordered_map<int, State> qm_map;
    int n_reg = sra.num_registers();
    int n_qm = (1 << n_reg);
    for(int i = 0; i < n_qm; i++)
      qm_map[i] = fsra.add_state();
    
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
        fsra.add_transition(
          qm_map[i], qm_map[j],
          SRA_TP(top, std::make_pair(m1, m2)));
      }
    }

    // compute the negation of each transition
    auto state_iter_pair = sra.states();
    for(auto s_it = state_iter_pair.first;
      s_it != state_iter_pair.second; s_it++) {
      for(int i = 0; i < n_qm; i++) {
        Modes m1 = binary_to_modes(i, n_reg);
        for(int j = 0; j < n_qm; j++) {
          Modes m2 = binary_to_modes(j, n_reg);
          SRA_TP prop(top, std::make_pair(m1, m2));
          auto out_edge_iter = fsra.out_transitions(*s_it);
          std::vector<Bound> bounds;
          bounds.push_back(std::make_pair(0, -1));
          for(auto o_it = out_edge_iter.first;
            o_it != out_edge_iter.second && !bounds.empty(); o_it++) {
            auto oprop = sra.get_property(*o_it);
            if(is_self_triggered(prop, oprop)) continue;
            Bound b = oprop.default_property.get_bounds();
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
            SRA_TP n_prop(guard, std::make_pair(m1, m2));
            fsra.add_transition(*s_it, qm_map[j], n_prop);
          }
        }
      }
    }
    return fsra;
  }

  SRA
  complement(const SRA& sra) {
    assert(is_deterministic(sra));
    SRA fsra = get_full_sra(sra);
    // TODO
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
          rhs.is_final_state(sp.first.second)) {
        Modes m1 = lhs.get_final_state_modes(sp.first.first);
        Modes m2 = rhs.get_final_state_modes(sp.first.second);
        out.set_final_state(sp.second, m1 & m2);
      }
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
      lhs_state2state[state] = out.add_state();
    }
    for(auto state : rhs.state_set()) {
      if(rhs.is_initial_state(state)) continue;
      rhs_state2state[state] = out.add_state();
    }

    out.set_initial_state(lhs_state2state[lhs.initial_state()]);

    for(auto state_modes : rhs.final_state_set()) {
      Modes n_modes = lhs_idles + state_modes.second;
      if(!rhs.is_initial_state(state_modes.first)) {
        State n_state = rhs_state2state[state_modes.first];
        out.set_final_state(n_state, n_modes);
      } else for(auto lhs_final_state : lhs.final_state_set()) {
        State n_state = lhs_state2state[lhs_final_state.first];
        out.set_final_state(n_state, n_modes);
      }
    }
    
    auto lhs_transition_iter = lhs.transitions();
    for(auto t_it = lhs_transition_iter.first;
      t_it != lhs_transition_iter.second; t_it++) {
        State ns = lhs_state2state[lhs.source(*t_it)];
        State nt = lhs_state2state[lhs.target(*t_it)];
        TransitionProperty ntp = lhs.get_property(*t_it);
        ntp.extended_property =
          ntp.extended_property + std::make_pair(rhs_idles, rhs_idles);
        out.add_transition(ns, nt, ntp); 
    }

    auto rhs_transition_iter = rhs.transitions();
    for(auto t_it = rhs_transition_iter.first;
      t_it != rhs_transition_iter.second; t_it++) {
        TransitionProperty ntp = rhs.get_property(*t_it);
        ntp.extended_property =
          std::make_pair(lhs_idles, lhs_idles) + ntp.extended_property;

        State s = rhs.source(*t_it);
        State t = rhs.target(*t_it);
        StateSet ns_set, nt_set;
        if(!rhs.is_initial_state(s)) ns_set.insert(rhs_state2state[s]);
        else for(auto lhs_final_state : lhs.final_state_set())
          ns_set.insert(lhs_state2state[lhs_final_state.first]);
        if(!rhs.is_initial_state(t)) nt_set.insert(rhs_state2state[t]);
        else for(auto lhs_final_state : lhs.final_state_set())
          nt_set.insert(lhs_state2state[lhs_final_state.first]);

        for(auto ns : ns_set) for(auto nt : nt_set)
          out.add_transition(ns, nt, ntp);
    }

    return out;
  }

}

#endif /* atl_detail_size_register_automaton_algorithm_hpp */