template<int N> int constant() { return N; }
template<long long N> long long wide_constant() { return N; }
template<unsigned long long N> unsigned long long unsigned_constant() {
    return N;
}

int negative_constant() { return constant<-1>(); }
int minimum_constant() { return constant<(-2147483647 - 1)>(); }
long long minimum_wide_constant() {
    return wide_constant<(-9223372036854775807LL - 1)>();
}
int zero_constant() { return constant<0>(); }
int positive_constant() { return constant<1>(); }
unsigned long long maximum_unsigned_constant() {
    return unsigned_constant<18446744073709551615ULL>();
}
int ordinary_negative_literal() { return -42; }
