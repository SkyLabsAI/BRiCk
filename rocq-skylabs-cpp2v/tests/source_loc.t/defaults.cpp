// These constants are evaluated at distinct use sites, not at their definitions.
unsigned argument(unsigned line = __builtin_LINE()) { return line; }
struct Aggregate { unsigned line = __builtin_LINE(); };
unsigned nested(Aggregate value = {}) { return value.line; }
#line 50 "defaults.cpp"
struct Constructed {
  unsigned line = __builtin_LINE();
  Constructed() {}
};

int main() {
#line 100 "defaults.cpp"
  if (argument() != 100) return 1;
#line 200 "defaults.cpp"
  if (argument() != 200) return 2;
#line 300 "defaults.cpp"
  Aggregate first{};
  if (first.line != 300) return 3;
#line 400 "defaults.cpp"
  Aggregate second{};
  if (second.line != 400) return 4;
#line 500 "defaults.cpp"
  if (nested() != 500) return 5;
  Constructed constructed;
  if (constructed.line != 52) return 6;
#line 600 "defaults.cpp"
  if (__builtin_LINE() != 600) return 7;
}
