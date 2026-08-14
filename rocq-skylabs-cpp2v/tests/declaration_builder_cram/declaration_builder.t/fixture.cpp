namespace canonical_namespace {
int namespace_value;
}
namespace alias_namespace = canonical_namespace;
namespace zeta_namespace {
int zeta_value;
}
namespace alpha_namespace {
int alpha_value;
}
namespace middle_namespace {
int middle_value;
}
namespace zeta_alias = zeta_namespace;
namespace alpha_alias = alpha_namespace;
namespace middle_alias = middle_namespace;
inline namespace inline_namespace {
int inline_value;
}

static_assert(sizeof(int) >= 2, "wide enough");

extern int external_value;
int plain_value;
int initialized_value = 3;

int free_function(int named, int) { return named + 1; }
int redeclared_function(int value);
int redeclared_function(int value) { return value; }

struct Forward;
struct RedeclaredRecord;
struct RedeclaredRecord {
    int value;
};

struct FallbackOnly {
    int value;
};

struct ImplicitOnly {
    int value;
};

struct NoThrowMember {
    ~NoThrowMember() noexcept;
};
struct ExceptionHolder {
    NoThrowMember member;
};
ExceptionHolder exception_holder;

ImplicitOnly exercise_implicit(ImplicitOnly value) {
    ImplicitOnly defaulted;
    ImplicitOnly copy(value);
    ImplicitOnly moved(static_cast<ImplicitOnly &&>(copy));
    copy = value;
    moved = static_cast<ImplicitOnly &&>(copy);
    copy.~ImplicitOnly();
    return moved;
}

struct Base {
    int base_field;
    virtual int virtual_method() { return base_field; }
    virtual ~Base() = default;
};

struct PureBase {
    virtual int pure_method() = 0;
};
struct PureOverride : PureBase {
    int pure_method() override = 0;
};

struct Record : Base {
    mutable int field = 4;

    Record() : Base(), field(5) {}
    ~Record() override {}

    int method(int value) const noexcept { return value + field; }
    static int static_method(int value) { return value; }
    int virtual_method() override { return field; }
};

union Choice {
    int integer;
    long longer;
};

enum class AuditEnum : unsigned { First = 1, Second };
using Alias = int *;

template <class T> struct EnumScope {
    enum Concrete : unsigned { Suppressed = 1 };
};

template <class T> struct RedeclaredTemplate;
template <class T> struct RedeclaredTemplate {
    T value;
};

template <class T = int, int N = 2> struct Box {
    T values[N];
};

template <class T> T templated_function(T value) { return value; }

template <class T> using AliasTemplate = T *;

template <> struct Box<long, 3> {
    long values[3];
};

Box<long, 4> box_instance;
