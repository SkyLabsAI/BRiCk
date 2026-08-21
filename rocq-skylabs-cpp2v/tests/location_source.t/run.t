  $ . ../setup-project.sh
  $ . ../setup-cpp2v.sh
  $ CRAM_CXXFLAGS="-I. -isystem system"

The default companion uses physical main-file membership. It omits header-only
roots (even when a header's `#line` names the main file), keeps main-file
presumed coordinates, and strips header spelling plus complete macro stacks
from main-file macro expansions.

  $ check_cpp2v_locations fixture.cpp
  cpp2v -v -check-types -o fixture_17_cpp.v --locations fixture_17_cpp_locations.v fixture.cpp -- -std=c++17 -I. -isystem system 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix fixture_17_cpp.v
  rocq c -w -notation-overridden -w -notation-incompatible-prefix fixture_17_cpp_locations.v
  $ rocq c $ROCQC_ARGS check.v

The explicit opt-out retains the complete legacy all-file data: nested macro
frames, spelling and expansion ranges, first-seen files, include ancestry, and
user/system classification.

  $ cpp2v -o all_files_ast.v --locations all_files_locations.v --locations-all-files fixture.cpp -- -std=c++17 -I. -isystem system
  $ rocq c $ROCQC_ARGS all_files_ast.v
  $ rocq c $ROCQC_ARGS all_files_locations.v
  $ rocq c $ROCQC_ARGS check_all_files.v

A configured stable external root replaces the complete sandbox path in
physical, requested, and presumed header names while the main file remains
AST-relative.

  $ mkdir -p external_root external_source
  $ cp user_header.hpp system/system_header.hpp external_root/
  $ cp fixture.cpp external_source/
  $ cpp2v -o rooted_ast.v --locations rooted_locations.v --locations-all-files --locations-source-root headers=$PWD/external_root external_source/fixture.cpp -- -std=c++17 -Iexternal_root -isystem external_root
  $ test "$(grep -Fo 'NamedRootSourceName "headers" ("user_header.hpp" :: nil)' rooted_locations.v | wc -l)" -eq 3
  $ test "$(grep -Fo 'NamedRootSourceName "headers" ("system_header.hpp" :: nil)' rooted_locations.v | wc -l)" -eq 3
  $ grep -q 'AstRelativeSourceName' rooted_locations.v
  $ grep -q 'LiteralSourceName "/logical/absolute.cpp"' rooted_locations.v
  $ ! grep -F "$PWD" rooted_locations.v
  $ rocq c $ROCQC_ARGS rooted_locations.v
  $ ln -s external_root external_link
  $ cpp2v -o symlink_root_ast.v --locations symlink_root_locations.v --locations-all-files --locations-source-root headers=$PWD/external_link external_source/fixture.cpp -- -std=c++17 -Iexternal_link -isystem external_link
  $ grep -q 'NamedRootSourceName "headers" ("user_header.hpp" :: nil)' symlink_root_locations.v
  $ ! grep -F "$PWD/external_root" symlink_root_locations.v
  $ rocq c $ROCQC_ARGS symlink_root_locations.v

Distinct stable roots can be configured simultaneously and retain independent
names.

  $ mkdir user_root system_root
  $ cp user_header.hpp user_root/
  $ cp system/system_header.hpp system_root/
  $ cpp2v -o distinct_roots_ast.v --locations distinct_roots_locations.v --locations-all-files --locations-source-root user=$PWD/user_root --locations-source-root system=$PWD/system_root external_source/fixture.cpp -- -std=c++17 -Iuser_root -isystem system_root
  $ test "$(grep -Fo 'NamedRootSourceName "user" ("user_header.hpp" :: nil)' distinct_roots_locations.v | wc -l)" -eq 3
  $ test "$(grep -Fo 'NamedRootSourceName "system" ("system_header.hpp" :: nil)' distinct_roots_locations.v | wc -l)" -eq 3
  $ rocq c $ROCQC_ARGS distinct_roots_locations.v
