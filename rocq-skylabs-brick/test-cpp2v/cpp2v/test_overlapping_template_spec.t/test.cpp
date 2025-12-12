// I've also posted this code, with more discussion and a disassembly, at
// https://stackoverflow.com/a/68482995/53974

template<typename T> T var = {};
template long var<long>;
// long var; // Error

// Function specializations and functions can coexist, so they have different
// mangled names.

// As long as two templates are different, their specializations can coexist
// even when overload resolution cannot pick between them; so the mangled name
// includes the template signature.
void fun(long) {}

template<typename T> void fun(T) {}
template void fun<long>(long); // void fun<long>(long)

void notfun1() {
  fun(1L);
  fun<long>(2); // Calls void fun<long>(long)
}

template<typename T> struct identity { using type = T; };
template<typename T> void fun(typename identity<T>::type);
template void fun<long>(long); // Generates void fun<long>(identity<long>::type)
//template void fun<long>(typename identity<long>::type); //Ditto, can't write both

void notfun() {
  fun(1L);
  fun<long>(2); // Calls void fun<long>(identity<long>::type)

}

template<typename T> void fun(typename identity<T>::type) {}

int main() {}
