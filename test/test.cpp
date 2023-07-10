#include <iostream>
#include <string>

#include <boost/graph/adjacency_list.hpp>

#include <fml/atl/automaton_utility.hpp>
#include <fml/atl/detail/algorithm.hpp>
#include <fml/ll/atomic_proposition.hpp>
#include <fml/ll/propositional_logic.hpp>
using namespace atl;
using namespace ll;

#include "../size_register_automaton/size_register_automaton.hpp"

typedef size_register_automaton::State State;
typedef size_register_automaton::Transition Transition;
typedef size_register_automaton::TransitionProperty TransitionProperty;

int main() {

  int_variable cur("cur");
  Guard g1(cur >= 0);
  Guard g2(cur >= 1);
  
  Modes mi; mi.push_back(RegisterMode::IDLE);
  Modes mc; mc.push_back(RegisterMode::COUNT);

  size_register_automaton sra(1);
  
  State s = sra.add_state(mi);
  sra.set_initial_state(s);
  sra.add_state(mi);
  sra.add_state(mc);
  sra.set_final_state(s);

  sra.add_transition(0, 1, g2);
  sra.add_transition(1, 2, g2);
  sra.add_transition(2, 2, g1);
  sra.add_transition(2, 0, g1);

  std::cout << sra << std::endl;

  std::cout << "complement :\n" << !sra << std::endl;

  std::cout << "product :\n" << (sra & sra) << std::endl;

  std::cout << "comcatenation :\n" << (sra + sra) << std::endl;

  return 0;
}