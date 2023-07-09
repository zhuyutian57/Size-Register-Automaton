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

  size_register_automaton sra(1);
  
  State s = sra.add_state();
  sra.set_initial_state(s);
  sra.add_state();
  sra.add_state();

  Modes m_f; m_f.push_back(RegisterMode::IDLE);
  sra.set_final_state(0, m_f);

  int_variable cur("cur");
  Guard g1(cur >= 0);
  Guard g2(cur >= 1);
  
  Modes mi; mi.push_back(RegisterMode::IDLE);
  Modes mc; mc.push_back(RegisterMode::COUNT);
  
  TransitionProperty tp1(g1, std::make_pair(mi, mi));
  TransitionProperty tp2(g2,  std::make_pair(mi, mc));
  TransitionProperty tp3(g1,  std::make_pair(mc, mc));
  TransitionProperty tp4(g1,  std::make_pair(mc, mi));
  sra.add_transition(0, 1, tp1);
  sra.add_transition(1, 2, tp2);
  sra.add_transition(2, 2, tp3);
  sra.add_transition(2, 0, tp4);

  std::cout << sra << std::endl;

  std::cout << !sra << std::endl;

  std::cout << (sra & sra) << std::endl;

  std::cout << (sra + sra) << std::endl;

  return 0;
}