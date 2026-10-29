The hidden-field regression is separate; check the template expressions here.
  $ cpp2v -check-types -o test.v --templates test_templates.v test.cpp -- -std=gnu++17 2>cpp2v.log
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix test_templates.v
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix test.v
