Layout-only use and use of the default initializer export identical members.
The unused invalid default must remain legal.
  $ cpp2v --no-elaborate --no-templates -o inc_cpp.v inc.hpp -- -xc++ -std=c++20
  $ cpp2v --no-elaborate --no-templates -o src_cpp.v src.cpp -- -std=c++20
  $ rocq c $CHECK_CPP2V_ROCQC_ARGS -Q . test inc_cpp.v
  $ rocq c $CHECK_CPP2V_ROCQC_ARGS -Q . test src_cpp.v
  $ rocq c $CHECK_CPP2V_ROCQC_ARGS -Q . test test.v

Template export must retain the generic initializer as well.
  $ cpp2v --no-elaborate -o instances.v --templates templates.v inc.hpp -- -xc++ -std=c++20
  $ rocq c $CHECK_CPP2V_ROCQC_ARGS -Q . test instances.v
  $ rocq c $CHECK_CPP2V_ROCQC_ARGS -Q . test templates.v
