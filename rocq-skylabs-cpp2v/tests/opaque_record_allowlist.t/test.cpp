// A bit-field must not override restrictions on opaque-record metadata.
struct [[clang::trivial_abi]] TrivialABI {
    unsigned b : 1;
    ~TrivialABI();
};
void consume(TrivialABI);

struct Plain {
    unsigned b : 1;
    ~Plain();
};

struct Base { int x; };
struct VirtualBase : virtual Base { unsigned b : 1; };

// Under-aligned fields and bases are intentionally allowed when the record
// is opaque: their layout is hidden. Check that the test really packs them.
#pragma pack(push, 1)
struct PackedClass { unsigned b : 1; Base member; };
struct PackedReference { unsigned b : 1; int &member; };
struct PackedBase : Base { unsigned b : 1; };
#pragma pack(pop)
static_assert(alignof(PackedClass) < alignof(Base));
static_assert(alignof(PackedReference) < alignof(int *));
static_assert(alignof(PackedBase) < alignof(Base));
