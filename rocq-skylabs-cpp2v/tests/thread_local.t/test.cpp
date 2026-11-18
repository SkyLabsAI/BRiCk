// Uses of thread-local variables become [Eunsupported].
thread_local int tls;
static __thread int gnu_tls;
int plain;
int get() { return tls + gnu_tls + plain; }
int *addr() { return &tls; }
