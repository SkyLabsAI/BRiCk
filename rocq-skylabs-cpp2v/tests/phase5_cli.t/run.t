  $ . ../setup-project.sh
  $ . ../setup-cpp2v.sh

Owned output preserves diagnostic name comments in both ordinary and template
partitions, while both files remain valid Rocq terms.

  $ cpp2v -o comments.v --templates comments_templates.v --comment --no-sharing --check-types fixture.cpp -- -std=c++17
  $ rocq c $ROCQC_ARGS comments_templates.v
  $ rocq c $ROCQC_ARGS comments.v
  $ grep -q '(\* phase5_function(int) \*)' comments.v
  $ grep -q '(\* <T>identity(T) \*)' comments_templates.v
  $ grep -q '(\* <T>Alias \*)' comments_templates.v

The compatibility --no-aliases option suppresses ordinary typedefs and
template aliases without affecting the rest of the translation unit.

  $ cpp2v -o no_aliases.v --no-aliases --no-sharing --check-types fixture.cpp -- -std=c++17
  $ rocq c $ROCQC_ARGS no_aliases.v
  $ ! grep -q '"Plain"' no_aliases.v
  $ ! grep -q '"Alias"' no_aliases.v
  $ grep -q 'phase5_function' no_aliases.v

Attributes and interactive framing are retained outside semantic IR emission.
The interactive fragment is compiled after supplying the plugin import that an
interactive host already has loaded.

  $ cpp2v -o attributes.v --attributes check_types --no-templates --check-types fixture.cpp -- -std=c++17
  $ rocq c $ROCQC_ARGS attributes.v
  $ grep -q '^#\[check_types\]$' attributes.v
  $ cpp2v -o interactive.v --for-interactive phase5_interactive --no-templates fixture.cpp -- -std=c++17
  $ { echo 'Require Import skylabs.lang.cpp.parser.plugin.cpp2v.'; cat interactive.v; } > interactive_standalone.v
  $ rocq c $ROCQC_ARGS interactive_standalone.v
  $ grep -q '^Section cpp_prog__phase5_interactive__\.$' interactive.v
  $ grep -q '^End cpp_prog__phase5_interactive__\.$' interactive.v
