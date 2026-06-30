# AGENTS.md

- In Rocq tests that mention C++ names or types, prefer the string notations
  such as `%cpp_name` and `%cpp_type` when they can express the expected term.
  Use explicit constructors only for cases the notation cannot represent, such
  as template-template parameter variables (`Atemplate_param`).
