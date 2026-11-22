  $ setup_project

Compiling the C++ code, use "make Q=" for debugging.
  $ ulimit -S -s 40960
  $ make 2> /dev/null
  $ ls *.v | wc -l | sed -e 's/ //g'
  2

Compiling the generated Coq files.
  $ dune build
       = ["Name std::__are_same<?Builtin long double, float> may denote several types"%pstring;
          "Name std::__are_same<?Builtin long double, double> may denote several types"%pstring;
          "Name std::__is_floating<?Builtin long double> may denote several types"%pstring;
          "Name std::__is_floating_point_helper<?Builtin long double> may denote several types"%pstring;
          "Name std::__is_integer<?Builtin long double> may denote several types"%pstring;
          "Name __gnu_cxx::__numeric_traits<?Builtin long double> may denote several types"%pstring;
          "Name __gnu_cxx::__numeric_traits_floating<?Builtin long double> may denote several types"%pstring;
          "Name __gnu_cxx::__promote<?Builtin long double, !nyi> may denote several types"%pstring;
          "Name std::__are_same<?Builtin long double, float>::__type may denote several types"%pstring;
          "Name std::__are_same<?Builtin long double, double>::__type may denote several types"%pstring;
          "Name std::__is_floating<?Builtin long double>::__type may denote several types"%pstring;
          "Name std::__is_integer<?Builtin long double>::__type may denote several types"%pstring;
          "Name __gnu_cxx::__promote<?Builtin long double, !nyi>::__type may denote several types"%pstring;
          "Name std::__are_same<?Builtin long double, float>::.__value::__value may denote several types"%pstring;
          "Name std::__are_same<?Builtin long double, double>::.__value::__value may denote several types"%pstring;
          "Name std::__is_floating<?Builtin long double>::.__value::__value may denote several types"%pstring;
          "Name std::__is_integer<?Builtin long double>::.__value::__value may denote several types"%pstring;
          "Name std::__are_same<?Builtin long double, float>::.__value may denote several types"%pstring;
          "Name std::__are_same<?Builtin long double, double>::.__value may denote several types"%pstring;
          "Name std::__is_floating<?Builtin long double>::.__value may denote several types"%pstring;
          "Name std::__is_integer<?Builtin long double>::.__value may denote several types"%pstring;
          "if consteval"%pstring; "if consteval"%pstring]
       : supported.check.M
