
#ifndef atl_detail_size_register_automaton_hpp
#define atl_detail_size_register_automaton_hpp

#include "property.hpp"

namespace atl::detail {

  class size_register_automaton_gen
    : public automaton_gen<SRA_TP, boost::no_property, boost::no_property> {
  public: 
    typedef automaton_gen<SRA_TP, boost::no_property, boost::no_property> Base;

    typedef Base::State State;
    typedef Base::Transition Transition;
    typedef Base::StateIter StateIter;
    typedef Base::TransitionIter TransitionIter;
    typedef Base::state_property_type StateProperty;
    typedef Base::transition_property_type TransitionProperty;
    typedef Base::automaton_property_type AutomatonProperty;

    typedef std::unordered_set<State> StateSet;
    typedef std::unordered_map<State, Modes> State2Modes;

  public:
    size_register_automaton_gen() {
      register_n_ = 0;
      initial_state_ = -1;
      state_set_.clear();
      final_state_set_.clear();
    }

    size_register_automaton_gen(int n) {
      register_n_ = n;
      initial_state_ = -1;
      state_set_.clear();
      final_state_set_.clear();
    }

    size_register_automaton_gen(const size_register_automaton_gen& x)
      : Base(x),
        register_n_(x.register_n_),
        initial_state_(x.initial_state_),
        state_set_(x.state_set_),
        final_state_set_(x.final_state_set_) {}

    virtual ~size_register_automaton_gen() {}

    void
    set_register(int n) {
      register_n_ = n;
    }

    int
    num_registers() const {
      return register_n_;
    }

    void
    set_initial_state(State state) {
      initial_state_ = state;
    }

    State
    initial_state() const {
      return initial_state_;
    }

    bool
    is_initial_state(State s) const {
      return s == initial_state_;
    }

    State
    add_state() {
      State state = Base::add_state();
      state_set_.insert(state);
      return state;
    }

    State
    add_state(const Base::state_property_type& sp) {
      State state = Base::add_state(sp);
      state_set_.insert(state);
      return state;
    }

    const StateSet&
    state_set() const {
      return state_set_;
    }

    void
    set_state_set(const StateSet& s) {
      state_set_ = s;
    }

    void
    set_final_state(State state, Modes modes) {
      assert(register_n_ == modes.size());
      final_state_set_[state] = modes;
    }

    const State2Modes&
    final_state_set() const {
      return final_state_set_;
    }

    Modes
    get_final_state_modes(State s) const {
      assert(is_final_state(s));
      return final_state_set_.at(s);
    }

    bool
    is_final_state(const State s) const {
      return final_state_set_.find(s) != final_state_set_.end();
    }

    void clear_final_state_set() {
      final_state_set_.clear();
    }
    
    std::pair<Transition, bool>
    add_transition(State s, State t,
      const Base::transition_property_type& prop) {
      return Base::add_transition(s, t, prop);
    }
  
  private:
    int register_n_;
    State initial_state_;
    StateSet state_set_;
    State2Modes final_state_set_;

  }; /* class size_register_automaton_gen*/

}

#endif /* atl_detail_size_register_automaton_hpp */