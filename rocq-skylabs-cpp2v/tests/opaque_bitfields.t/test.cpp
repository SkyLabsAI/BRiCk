struct Bits {
  unsigned low : 3;
  unsigned high : 5;
};

struct SplitBits {
  unsigned low : 1;
  unsigned : 0;
  unsigned high : 1;
};

class alignas(16) Nontrivial {
  unsigned bits : 5;

public:
  ~Nontrivial();
  unsigned query() const;
  void update();
};

struct WithMember {
  unsigned bits : 1;
  Nontrivial member;
};

struct Forward;
void forward(Forward *);

template <unsigned Width> struct SizedBits {
  unsigned bits : Width;
};
template struct SizedBits<7>;

static_assert(sizeof(Bits) == 4 && alignof(Bits) == 4);
static_assert(sizeof(SplitBits) == 8 && alignof(SplitBits) == 4);
static_assert(sizeof(Nontrivial) == 16 && alignof(Nontrivial) == 16);
static_assert(sizeof(WithMember) == 32 && alignof(WithMember) == 16);
static_assert(sizeof(SizedBits<7>) == 4 && alignof(SizedBits<7>) == 4);
static_assert(__is_trivially_destructible(Bits));
static_assert(!__is_trivially_destructible(Nontrivial));
static_assert(!__is_trivially_destructible(WithMember));

Bits make_bits();
void take_bits(Bits);
Nontrivial make_nontrivial();
void take_nontrivial(Nontrivial);

unsigned calls(Nontrivial &value) {
  take_bits(make_bits());
  take_nontrivial(make_nontrivial());
  value.update();
  return value.query();
}
