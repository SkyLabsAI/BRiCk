  $ . ../../setup-cpp2v.sh
  $ check_cpp2v_templates test.cpp
  cpp2v -v -check-types -o test_17_cpp.v --templates test_17_cpp_templates.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  $TESTCASE_ROOT/test.cpp:1:10 (TemplateTypeParm <Ts>TypePack::Ts): warning: unsupported template parameter pack
  $TESTCASE_ROOT/test.cpp:1:10 (TemplateTypeParm <Ts>TypePack::Ts): warning: unsupported template parameter pack
  $TESTCASE_ROOT/test.cpp:1:10 (TemplateTypeParm <Ts>TypePack::Ts): warning: unsupported template parameter pack
  $TESTCASE_ROOT/test.cpp:1:10 (TemplateTypeParm <Ts>TypePack::Ts): warning: unsupported template parameter pack
  $TESTCASE_ROOT/test.cpp:1:10 (TemplateTypeParm <Ts>TypePack::Ts): warning: unsupported template parameter pack
  $TESTCASE_ROOT/test.cpp:1:10 (TemplateTypeParm <Ts>TypePack::Ts): warning: unsupported template parameter pack
  $TESTCASE_ROOT/test.cpp:8:10 (NonTypeTemplateParm <Ns>ValuePack::Ns): warning: unsupported template parameter pack
  $TESTCASE_ROOT/test.cpp:8:10 (NonTypeTemplateParm <Ns>ValuePack::Ns): warning: unsupported template parameter pack
  $TESTCASE_ROOT/test.cpp:8:10 (NonTypeTemplateParm <Ns>ValuePack::Ns): warning: unsupported template parameter pack
  $TESTCASE_ROOT/test.cpp:12:10 (TemplateTemplateParm <Templates, >TemplateTemplatePack::Templates): warning: unsupported template parameter pack
  $TESTCASE_ROOT/test.cpp:12:10 (TemplateTemplateParm <Templates, >TemplateTemplatePack::Templates): warning: unsupported template parameter pack
  $TESTCASE_ROOT/test.cpp:12:10 (TemplateTemplateParm <Templates, >TemplateTemplatePack::Templates): warning: unsupported template parameter pack
  $TESTCASE_ROOT/test.cpp:16:10 (TemplateTypeParm <Ts>Ts): warning: unsupported template parameter pack
  $TESTCASE_ROOT/test.cpp:16:10 (TemplateTypeParm <Ts>Ts): warning: unsupported template parameter pack
  $TESTCASE_ROOT/test.cpp:22:10 (TemplateTypeParm <Ts>Ts): warning: unsupported template parameter pack
  $TESTCASE_ROOT/test.cpp:22:10 (TemplateTypeParm <Ts>Ts): warning: unsupported template parameter pack
  $TESTCASE_ROOT/test.cpp:31:21 (PackExpansionExpr): warning: unsupported expression
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp_templates.v
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v
  $ coqc -w -notation-overridden test.v
