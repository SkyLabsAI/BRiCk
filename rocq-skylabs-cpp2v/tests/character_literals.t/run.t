  $ setup_project
  $ make
  $ dune build

The code-unit representation is unchanged when ordinary char is unsigned.
  $ make -B CPPFLAGS='-std=c++20 --target=x86_64-linux-gnu -funsigned-char -Wno-multichar'
  $ dune build
