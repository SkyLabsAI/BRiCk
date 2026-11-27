// The builtin allocates stack storage; this unrelated function returns null.
// Clang marks __builtin_alloca_with_align with F despite there being no
// corresponding library function to which it can safely be rewritten.
extern "C" void *alloca_with_align(__SIZE_TYPE__, __SIZE_TYPE__) {
  return nullptr;
}
bool builtin_call() { return __builtin_alloca_with_align(1, 8) == nullptr; }
bool ordinary_call() { return alloca_with_align(1, 8) == nullptr; }
