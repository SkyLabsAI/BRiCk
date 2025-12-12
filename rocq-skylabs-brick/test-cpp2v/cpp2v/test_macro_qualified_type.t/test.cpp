
#define X __attribute__((ms_abi))

struct foo { void (X *f)(); };
