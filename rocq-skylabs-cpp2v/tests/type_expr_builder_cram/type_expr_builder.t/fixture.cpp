#pragma clang diagnostic ignored "-Wvla-cxx-extension"
#pragma clang diagnostic ignored "-Wunused-value"
#pragma clang diagnostic ignored "-Wgnu-alignof-expression"

typedef int Alias;

struct C {
    C(const int values[3]);
    ~C();
    operator const int *() const;
    int operator+(const int values[2]) const;
    int member;
};

int ordinary;

enum KernelEnum { KFirst = 1, KSecond = KFirst };
KernelEnum enum_value = KFirst;
struct BindingPair {
    int member;
};

int normalized(const int values[3], int callback(int), int *const pointer);
int C::*member_pointer;
int (*function_pointer)(int);
const int *pointer_cv;
int fixed_array[4];
Alias alias_value;
int *__restrict restrict_unported;

int literal_value = (42);
bool bool_value = true;
const char *string_value = "hi";
decltype(nullptr) null_value = nullptr;

int use_ordinary() { return ordinary; }
unsigned long use_builtin(const char *text) { return __builtin_strlen(text); }
int local_unported() {
    int local_value = 1;
    return local_value;
}
int reference_kernel() {
    int storage = 0;
    int &reference_local = storage;
    auto [binding_value] = BindingPair{0};
    return reference_local + binding_value;
}
int variable_array_kernel(int bound) {
    int values[bound + 1];
    return sizeof(values);
}
int local_reference_kernel() {
    int named_local = 1;
    static int static_local = 2;
    return named_local + static_local;
}

long double long_double_value;
auto undeduced_function();
int resolved_constant = -2 + 1;

int arithmetic_kernel(int kernel_value) { return -kernel_value + 1; }

template <class> struct DefaultBox {};
template <class T> struct DeductionGuideAudit {
    DeductionGuideAudit(T);
};
DeductionGuideAudit(int) -> DeductionGuideAudit<int>;
template <class T = int, int N = 5, template <class> class TT = DefaultBox>
struct InheritedDefaults;
template <class T, int N, template <class> class TT>
struct InheritedDefaults {};

template <class T = int, int N = 3, template <class> class TT = DefaultBox>
struct Primary {
    using type = T;
    template <class U> using rebind = TT<U>;
    int values[N + 1];
    static int dependent_value() { return -N + (N + 1); }
};
template <class T, int N, template <class> class TT>
struct Primary<T *, N, TT> {};
template <> struct Primary<long, 2, DefaultBox> {};
Primary<> default_primary;

template <class T> int function_template(const T values[2]) {
    return sizeof(values);
}
template <> int function_template<int>(const int values[2]) {
    return values[0];
}
template <class T> int variable_template = 0;
template <> int variable_template<int> = 1;
template <class T> using AliasTemplate = Primary<T>;
template <template <class> class TT, class T> using ApplyTemplate = TT<T>;
template <class T> using DependentType = typename T::type;
template <class T> using ReboundType = typename T::template rebind<int>;
template <class T> int dependent_lookup() { return T::value + 1; }

template <class T, int N> struct Tagged {};
using TaggedUse = Tagged<const int *, 7>;

int declaration_target;
template <int *> struct DeclarationArg {};
using DeclarationUse = DeclarationArg<&declaration_target>;
template <class...> struct PackTarget {};

enum AuditEnum { AuditZero };
using UnaryUnderlying = __underlying_type(AuditEnum);
auto deduced_auto_value = 9;
using DecltypeIdStatic = decltype(ordinary);
using DecltypeParenStatic = decltype((ordinary));
using ElaboratedAudit = struct C;
using VectorAudit = int __attribute__((vector_size(16)));
VectorAudit vector_value;
int (^block_pointer)(int);
template <class T> using DecayAudit = __decay(T);
using DecayUse = DecayAudit<int[3]>;
template <class... Ts> using PackExpansionAudit = PackTarget<Ts...>;
template <class T> using DependentDecltypeId = decltype(T::value);
template <class T> using DependentDecltypeParen = decltype((T::value));
template <class T> struct InjectedAudit {
    using Self = InjectedAudit;
};

void *operator new(unsigned long);
void *operator new[](unsigned long);
void *operator new(unsigned long, void *) noexcept;
void operator delete(void *) noexcept;
void operator delete[](void *) noexcept;
namespace std {
enum class align_val_t : unsigned long;
}
void *operator new(unsigned long, std::align_val_t);
void operator delete(void *, std::align_val_t) noexcept;

struct CastBase {
    virtual ~CastBase() = default;
    int member;
};
struct CastMiddle : CastBase {};
struct CastDerived : CastMiddle {};
int cast_function(int value) { return value; }
int cast_source = 1;
int *cast_pointer;
const int *cast_const_pointer;
int cast_array[2];
CastBase *cast_base;
CastDerived *cast_derived;

long cast_implicit_integral = cast_source;
bool cast_pointer_bool = cast_pointer;
bool cast_integral_bool = cast_source;
bool cast_floating_bool = 1.0;
double cast_integral_float = cast_source;
double cast_double_source = 1.5;
int cast_floating_integral = cast_double_source;
float cast_floating = 1.5;
void *cast_null_pointer = 0;
int CastBase::*cast_null_member = nullptr;
int (*cast_function_pointer)(int) = cast_function;
int *cast_array_pointer = cast_array;
long cast_cstyle = (long)cast_source;
long cast_functional = long(cast_source);
long cast_static = static_cast<long>(cast_source);
unsigned long cast_reinterpret = reinterpret_cast<unsigned long>(cast_pointer);
int *cast_const = const_cast<int *>(cast_const_pointer);
float cast_bit_source = 1.0f;
char *cast_bit_pointer = reinterpret_cast<char *>(cast_pointer);
int &cast_lvalue_bit = reinterpret_cast<int &>(cast_bit_source);
int *cast_integral_pointer = reinterpret_cast<int *>(1UL);
CastBase *cast_unchecked_base = (CastBase *)cast_derived;
CastDerived *cast_dynamic = dynamic_cast<CastDerived *>(cast_base);
CastBase *cast_derived_to_base = static_cast<CastBase *>(cast_derived);
CastDerived *cast_base_to_derived = static_cast<CastDerived *>(cast_base);
unsigned cast_builtin_bit = __builtin_bit_cast(unsigned, cast_bit_source);
void cast_to_void() { static_cast<void>(cast_source); }
template <class T> int cast_dependent(T value) {
    return static_cast<int>(value);
}

char literal_char = 'A';
wchar_t literal_wchar = L'B';
char16_t literal_char16 = u'C';
char32_t literal_char32 = U'D';
float literal_float = 1.5f;
double literal_double = 2.5;
long double literal_long_double = 3.5L;
const wchar_t *literal_wide_string = L"AZ";
const char16_t *literal_u16_string = u"AZ";
const char32_t *literal_u32_string = U"AZ";
#if __cplusplus >= 202002L
char8_t literal_char8 = u8'E';
const char8_t *literal_u8_string = u8"AZ";
#endif
long literal_gnu_null = __null;
unsigned literal_source_line = __builtin_LINE();
const char *literal_source_file = __builtin_FILE();
bool literal_noexcept = noexcept(cast_function(1));
bool literal_trait = __is_same(int, int);
const char *literal_predefined() { return __func__; }
struct DefaultInitAudit {
    int value = 9;
    DefaultInitAudit() = default;
};
DefaultInitAudit default_init_audit;

// Phase 4B built-in operator and unary-trait matrix. Keep every selected
// expression as the semantic initializer (below only parentheses/implicit
// casts) so the two probes can choose the same Clang node independently.
int op_left = 8;
int op_right = 2;
int op_array[4] = {0, 1, 2, 3};
int *op_pointer = op_array;

struct OperatorMemberAudit {
    int field;
};
OperatorMemberAudit op_object;
OperatorMemberAudit *op_object_pointer = &op_object;
int OperatorMemberAudit::*op_member_pointer = &OperatorMemberAudit::field;
auto op_member_address_deferred = &OperatorMemberAudit::field;

auto op_unary_plus = +op_left;
auto op_unary_minus = -op_left;
auto op_unary_bitnot = ~op_left;
auto op_unary_lnot = !op_left;
auto op_preinc = ++op_left;
auto op_postinc = op_left++;
auto op_predec = --op_left;
auto op_postdec = op_left--;
auto op_deref = *op_pointer;
auto op_addrof = &op_left;
auto op_extension = __extension__ op_left;
auto op_real = __real op_left;
auto op_imag = __imag op_left;

auto op_mul = op_left * op_right;
auto op_div = op_left / op_right;
auto op_rem = op_left % op_right;
auto op_add = op_left + op_right;
auto op_sub = op_left - op_right;
auto op_shl = op_left << op_right;
auto op_shr = op_left >> op_right;
auto op_lt = op_left < op_right;
auto op_gt = op_left > op_right;
auto op_le = op_left <= op_right;
auto op_ge = op_left >= op_right;
auto op_eq = op_left == op_right;
auto op_ne = op_left != op_right;
auto op_bitand = op_left & op_right;
auto op_bitxor = op_left ^ op_right;
auto op_bitor = op_left | op_right;
auto op_dotp = op_object.*op_member_pointer;
auto op_dotip = op_object_pointer->*op_member_pointer;

auto op_assign = (op_left = op_right);
auto op_mul_assign = (op_left *= op_right);
auto op_div_assign = (op_left /= op_right);
auto op_rem_assign = (op_left %= op_right);
auto op_add_assign = (op_left += op_right);
auto op_sub_assign = (op_left -= op_right);
auto op_shl_assign = (op_left <<= op_right);
auto op_shr_assign = (op_left >>= op_right);
auto op_and_assign = (op_left &= op_right);
auto op_xor_assign = (op_left ^= op_right);
auto op_or_assign = (op_left |= op_right);
auto op_comma = (op_left, op_right);
auto op_logical_and = op_left && op_right;
auto op_logical_or = op_left || op_right;
auto op_subscript_array = op_array[op_right];
auto op_subscript_reversed = op_right[op_array];
auto op_subscript_pointer = op_pointer[op_right];

auto op_sizeof_type = sizeof(int);
auto op_sizeof_expr = sizeof(op_left);
auto op_alignof_type = alignof(int);
auto op_alignof_expr = alignof(op_left);
auto op_preferred_type = __alignof__(int);
auto op_preferred_expr = __alignof__(op_left);
typedef int OperatorVectorAudit __attribute__((vector_size(16)));
OperatorVectorAudit op_vector = {0, 1, 2, 3};
auto op_vec_step = __builtin_vectorelements(op_vector);

#if __cplusplus >= 202002L
namespace std {
enum class _cpp2v_ord : signed char { less = -1, equal = 0, greater = 1 };
class strong_ordering {
    signed char value;
    constexpr explicit strong_ordering(_cpp2v_ord v)
        : value(static_cast<signed char>(v)) {}

public:
    static const strong_ordering less;
    static const strong_ordering equal;
    static const strong_ordering equivalent;
    static const strong_ordering greater;
};
inline constexpr strong_ordering strong_ordering::less(_cpp2v_ord::less);
inline constexpr strong_ordering strong_ordering::equal(_cpp2v_ord::equal);
inline constexpr strong_ordering strong_ordering::equivalent(_cpp2v_ord::equal);
inline constexpr strong_ordering strong_ordering::greater(_cpp2v_ord::greater);
} // namespace std

auto op_cmp = op_left <=> op_right;
#endif

template <class T>
void dependent_operator_kernel(T value, T other, T *pointer) {
    auto dep_op_unary_plus = +value;
    auto dep_op_unary_minus = -value;
    auto dep_op_unary_bitnot = ~value;
    auto dep_op_unary_lnot = !value;
    auto dep_op_preinc = ++value;
    auto dep_op_postinc = value++;
    auto dep_op_predec = --value;
    auto dep_op_postdec = value--;
    auto dep_op_deref = *pointer;
    auto dep_op_addrof = &value;
    auto dep_op_extension = __extension__ value;
    auto dep_op_real = __real value;
    auto dep_op_imag = __imag value;

    auto dep_op_mul = value * other;
    auto dep_op_div = value / other;
    auto dep_op_rem = value % other;
    auto dep_op_add = value + other;
    auto dep_op_sub = value - other;
    auto dep_op_shl = value << other;
    auto dep_op_shr = value >> other;
    auto dep_op_lt = value < other;
    auto dep_op_gt = value > other;
    auto dep_op_le = value <= other;
    auto dep_op_ge = value >= other;
    auto dep_op_eq = value == other;
    auto dep_op_ne = value != other;
    auto dep_op_bitand = value & other;
    auto dep_op_bitxor = value ^ other;
    auto dep_op_bitor = value | other;
#if __cplusplus >= 202002L
    auto dep_op_cmp = value <=> other;
#endif

    auto dep_op_assign = (value = other);
    auto dep_op_mul_assign = (value *= other);
    auto dep_op_div_assign = (value /= other);
    auto dep_op_rem_assign = (value %= other);
    auto dep_op_add_assign = (value += other);
    auto dep_op_sub_assign = (value -= other);
    auto dep_op_shl_assign = (value <<= other);
    auto dep_op_shr_assign = (value >>= other);
    auto dep_op_and_assign = (value &= other);
    auto dep_op_xor_assign = (value ^= other);
    auto dep_op_or_assign = (value |= other);
    auto dep_op_comma = (value, other);
    auto dep_op_logical_and = value && other;
    auto dep_op_logical_or = value || other;
    auto dep_op_subscript = pointer[0];

    auto dep_op_sizeof_type = sizeof(T);
    auto dep_op_sizeof_expr = sizeof(value);
    auto dep_op_alignof_type = alignof(T);
    auto dep_op_alignof_expr = alignof(value);
    auto dep_op_preferred_type = __alignof__(T);
    auto dep_op_preferred_expr = __alignof__(value);
}

template <class T, class U>
void dependent_pointer_operator_kernel(T *pointer, T *other, U *different,
                                       int index, char character_index) {
    auto dep_ptr_unary_plus = +pointer;
    auto dep_ptr_logical_not = !pointer;
    auto dep_ptr_preinc = ++pointer;
    auto dep_ptr_postinc = pointer++;
    auto dep_ptr_predec = --pointer;
    auto dep_ptr_postdec = pointer--;
    auto dep_ptr_add = pointer + index;
    auto dep_ptr_add_reversed = index + pointer;
    auto dep_ptr_character_add_reversed = character_index + pointer;
    auto dep_ptr_sub = pointer - index;
    auto dep_ptr_diff = pointer - other;
    auto dep_ptr_incompatible_diff = pointer - different;
    auto dep_ptr_lt = pointer < other;
    auto dep_ptr_eq = pointer == other;
    auto dep_ptr_assign = (pointer = other);
    auto dep_ptr_add_assign = (pointer += index);
    auto dep_ptr_sub_assign = (pointer -= index);
    auto dep_ptr_comma = (pointer, other);
    auto dep_ptr_logical_and = pointer && other;
    auto dep_ptr_logical_or = pointer || other;
    auto dep_ptr_subscript = pointer[index];
    auto dep_ptr_subscript_reversed = index[pointer];
}

int operator_nttp_target;
template <int N, int *P> void dependent_nontype_operator_kernel() {
    int *pointer = P;
    auto dep_nttp_pointer_plus = +P;
    auto dep_nttp_comma = (N, N);
    auto dep_nttp_subscript = pointer[N];
}

template <class T> void dependent_global_operator_kernel() {
    auto dep_global_add = T::left + T::right;
    auto dep_global_comma = (T::left, T::right);
}

template <class... Ts> constexpr auto operator_pack_kernel() {
    return sizeof...(Ts);
}
template auto operator_pack_kernel<int, long>();

// Phase 4B calls and members. The probes select the named initializers (or the
// pseudo-destructor call itself) before later construction/statement lowering.
int call_zero() { return 0; }
int call_two(int left, int right) { return left + right; }
int call_defaulted(int value = 7) { return value; }
int call_fixed(int value) { return value; }

auto call_free_zero = call_zero();
auto call_free_two = call_two(1, 2);
auto call_with_default = call_defaulted();
auto call_nested = call_two(call_zero(), call_defaulted(8));

struct CallMemberAudit {
    enum Kind { kind_value = 3 };

    int field = 0;
    mutable int mutable_field = 0;
    static int static_field;
    static int static_method(int);
    int direct(int);
    virtual int virtual_method(int);
    int operator-(int) const;
    virtual int operator*(int) const;
    int operator()(int) const;

    CallMemberAudit *this_kernel() {
        auto call_this = this;
        auto member_this_field = this->field;
        auto member_this_call = direct(member_this_field);
        (void)member_this_call;
        return call_this;
    }
};

CallMemberAudit call_member_object;
CallMemberAudit *call_member_pointer = &call_member_object;
using CallMemberFunctionPointer = int (CallMemberAudit::*)(int);
CallMemberFunctionPointer call_member_function_pointer =
    &CallMemberAudit::direct;

auto member_field_dot = call_member_object.field;
auto member_field_arrow = call_member_pointer->field;
auto member_mutable = call_member_object.mutable_field;
auto member_enum = call_member_object.kind_value;
auto member_enum_arrow = call_member_pointer->kind_value;
auto member_static = call_member_object.static_field;
auto member_static_arrow = call_member_pointer->static_field;
auto member_static_method = call_member_object.static_method;
auto member_call_direct = call_member_object.direct(1);
auto member_call_arrow = call_member_pointer->direct(2);
auto member_call_virtual = call_member_object.virtual_method(3);
auto member_call_qualified_virtual =
    call_member_object.CallMemberAudit::virtual_method(6);
auto member_call_static = call_member_object.static_method(7);
auto member_pointer_dot_call =
    (call_member_object.*call_member_function_pointer)(4);
auto member_pointer_arrow_call =
    (call_member_pointer->*call_member_function_pointer)(5);
auto member_address_field = &CallMemberAudit::field;
auto member_address_method = &CallMemberAudit::direct;
auto operator_call_member = call_member_object - 1;
auto operator_call_virtual = call_member_object * 2;
auto operator_call_function = call_member_object(3);

struct FreeOperatorAudit {};
FreeOperatorAudit call_free_operator_object;
FreeOperatorAudit operator+(const FreeOperatorAudit &, int);
auto operator_call_free = call_free_operator_object + 4;

struct UnresolvedOverloadAudit {
    int overload(int);
    int overload(double);
    template <class U> int overload_template(U);
    template <class U> int overload_template(U *);
};

template <class T> T dependent_call_target(T value);
template <class T>
void dependent_call_member_kernel(T value, T *pointer,
                                  UnresolvedOverloadAudit &overloaded,
                                  int (*fixed_pointer)(int)) {
    auto call_dependent_free = dependent_call_target(value);
    auto member_dependent_dot = value.field;
    auto member_dependent_arrow = pointer->field;
    auto call_dependent_member = value.method(1);
    auto call_dependent_member_arrow = pointer->method(2);
    auto call_dependent_member_template = value.template method<int>(3);
    auto call_dependent_local = value(4);
    auto call_dependent_fixed = call_fixed(value);
    auto call_dependent_parenthesized = ((value))(5);
    auto call_unresolved_overload = overloaded.overload(value);
    auto call_unresolved_overload_template =
        overloaded.template overload_template<T>(value);
    auto call_dependent_cast = static_cast<int (*)(int)>(value)(1);
    auto call_noop_pointer_cast =
        static_cast<int (*)(int)>(fixed_pointer)(value);
    auto call_noop_function_cast = static_cast<int (&)(int)>(call_fixed)(value);
}

struct ConstructionAudit {
    int first;
    int second;
    ConstructionAudit();
    ConstructionAudit(int);
    ConstructionAudit(int, int);
    ConstructionAudit(long, int = 7);
    ~ConstructionAudit();
};

ConstructionAudit construct_zero;
ConstructionAudit construct_one(1);
ConstructionAudit construct_two(1, 2);
ConstructionAudit construct_default(1L);
ConstructionAudit make_construction();
auto construction_cleanup = make_construction();
const ConstructionAudit &construction_extended = ConstructionAudit(6);
void consume_construction(const ConstructionAudit &);
void construction_temporary_kernel() {
    consume_construction(ConstructionAudit(5));
}

struct AggregateInitAudit {
    int first;
    int second;
};
union UnionInitAudit {
    int first;
    long second;
};
AggregateInitAudit init_list_aggregate = {1, 2};
UnionInitAudit init_list_union = {3};
int init_list_array[4] = {4, 5};
int scalar_value_init = int();
int transparent_init_list = {scalar_value_init};

struct InheritedBaseAudit {
    InheritedBaseAudit(int, long);
};
struct InheritedDerivedAudit : InheritedBaseAudit {
    using InheritedBaseAudit::InheritedBaseAudit;
};
InheritedDerivedAudit inherited_constructor_use(1, 2L);

struct ArrayElementAudit {
    ArrayElementAudit();
    ArrayElementAudit(const ArrayElementAudit &);
};
struct ArrayLoopAudit {
    ArrayElementAudit elements[3];
    ArrayLoopAudit();
    ArrayLoopAudit(const ArrayLoopAudit &) = default;
};
ArrayLoopAudit array_loop_source;
ArrayLoopAudit array_loop_copy(array_loop_source);

template <class T> void dependent_initialization_kernel(T first, T second) {
    T unresolved_paren_list(first, second);
    T unresolved_init_list{first, second};
    auto unresolved_construct = T(first);
}

struct AllocationObjectAudit {
    int value;
    AllocationObjectAudit(int);
    ~AllocationObjectAudit();
};
struct alignas(64) AlignedAllocationAudit {
    int value;
};
void *allocation_storage;
int *allocation_pointer;
auto allocation_new_scalar = new int;
auto allocation_new_initialized = new int(9);
auto allocation_new_array = new int[3];
auto allocation_new_array_initialized = new int[3]{1, 2};
auto allocation_new_object = new AllocationObjectAudit(10);
auto allocation_new_placement = new (allocation_storage) int(11);
auto allocation_new_aligned = new AlignedAllocationAudit;
void allocation_delete_kernel() {
    delete allocation_pointer;
    delete[] allocation_pointer;
}
template <class T> void dependent_allocation_kernel(T *pointer) {
    auto allocation_new_dependent = new T;
    delete pointer;
    delete[] pointer;
}

int conditional_source = 1;
int conditional_true = 2;
int conditional_false = 3;
int conditional_ordinary =
    conditional_source ? conditional_true : conditional_false;
int conditional_binary = conditional_source ?: conditional_false;
int conditional_binary_nested =
    (conditional_source ?: conditional_true) ?: conditional_false;
template <class T>
void conditional_template_kernel(bool condition, T value, T other) {
    auto conditional_dependent = condition ? value : other;
    auto conditional_binary_dependent = value ?: other;
    (void)conditional_dependent;
    (void)conditional_binary_dependent;
}

struct OffsetAudit {
    int first;
    int second;
};
struct OffsetNestedAudit {
    OffsetAudit nested;
};
auto offset_field = __builtin_offsetof(OffsetAudit, second);
auto offset_nested = __builtin_offsetof(OffsetNestedAudit, nested.second);
auto unsupported_choose = __builtin_choose_expr(true, 14, 15);
int unsupported_kernel(bool condition) { return condition ? throw 16 : 17; }
int statement_expression_kernel() {
    int statement_expression = ({
        int value = 18;
        value;
    });
    return statement_expression;
}

#if __cplusplus >= 202002L
template <class T>
concept SmallConcept = sizeof(T) <= sizeof(int);
bool concept_nondependent = SmallConcept<int>;
template <class T> void concept_template_kernel() {
    bool concept_dependent = SmallConcept<T>;
    (void)concept_dependent;
}
#endif

_Atomic(int) atomic_storage;
int atomic_va_kernel(__builtin_va_list arguments) {
    auto atomic_load_value =
        __c11_atomic_load(&atomic_storage, __ATOMIC_SEQ_CST);
    auto atomic_exchange_value =
        __c11_atomic_exchange(&atomic_storage, 12, __ATOMIC_SEQ_CST);
    auto va_arg_value = __builtin_va_arg(arguments, int);
    return atomic_load_value + atomic_exchange_value + va_arg_value;
}

using PseudoInt = int;
void pseudo_destructor_kernel(PseudoInt *pointer, PseudoInt value) {
    pointer->PseudoInt::~PseudoInt();
    value.PseudoInt::~PseudoInt();
}

auto lambda_empty = [] { return 0; };
struct LambdaThisBoundary {
    int field;
    void kernel(int parameter) {
        int local = parameter;
        auto lambda = [this, local] { return this->field + local; };
        auto lambda_reference = [&local] { return local; };
        auto lambda_unevaluated = [=] { return sizeof(local); };
        (void)lambda;
        (void)lambda_reference;
        (void)lambda_unevaluated;
    }
};
template <class T> void lambda_template_kernel(T value) {
    auto lambda_template_capture = [value] { return value; };
    auto lambda_template_init = [captured{value}] { return captured; };
    (void)lambda_template_capture;
    (void)lambda_template_init;
}

struct NestedLambdaBoundary {
    int field;
    void kernel(int parameter) {
        int nested_local = parameter;
        auto nested_outer_static = [this, nested_local]() mutable {
            auto nested_inner_static = [static_copy = nested_local,
                                        &static_reference = nested_local,
                                        static_copy_this = this] {
                return static_copy + static_reference + static_copy_this->field;
            };
            return nested_inner_static();
        };
        (void)nested_outer_static;
    }
};

struct NestedTemplateLambdaBoundary {
    int field;
    template <class T> void kernel(T nested_value) {
        auto nested_outer_template = [this, nested_value]() mutable {
            auto nested_inner_template = [template_copy = nested_value,
                                          &template_reference = nested_value,
                                          template_copy_this = this] {
                return template_copy + template_reference +
                       template_copy_this->field;
            };
            return nested_inner_template();
        };
        (void)nested_outer_template;
    }
};

void lambda_vla_static_kernel(int bound) {
    int values[bound];
    auto lambda_vla_static = [&values] { return sizeof(values); };
    (void)lambda_vla_static;
}
template <class T> void lambda_vla_template_kernel(int bound, T vla_value) {
    int values[bound];
    auto lambda_vla_template = [&values, vla_value] {
        return sizeof(values) + sizeof(vla_value);
    };
    (void)lambda_vla_template;
}

struct TupleLikeAudit {
    int value;
};
namespace std {
template <class T> struct tuple_size;
template <decltype(sizeof(0)), class T> struct tuple_element;
template <> struct tuple_size<TupleLikeAudit> {
    static constexpr decltype(sizeof(0)) value = 1;
};
template <> struct tuple_element<0, TupleLikeAudit> {
    using type = int;
};
} // namespace std
template <decltype(sizeof(0)) Index> int &&get(TupleLikeAudit &&value) {
    return static_cast<int &&>(value.value);
}

int local_external_target;
int statement_static_kernel(int input) {
    int local_uninitialized;
    int local_initialized = 1;
    static int local_static = 2;
    extern int local_external_target;
    using LocalFilteredAlias = int;
    static_assert(true);
    int mixed_first = 3, mixed_function(void), mixed_last = 4;
    auto [direct_binding] = BindingPair{5};
    auto [holding_binding] = TupleLikeAudit{6};

    {
        ;
        local_initialized += input;
    }
    int while_count = input;
    while (int while_value = while_count) {
        --while_count;
        if (while_value > 10)
            break;
    }
    for (int for_index = 0; for_index < 2; ++for_index) {
        if (for_index == 0)
            continue;
        input += for_index;
    }
    do {
        --input;
    } while (input > 20);

    if (input)
        ++input;
    if (int if_init = input; int if_condition = if_init) {
        input += if_condition;
    } else {
        input -= if_init;
    }

    switch (input) {
    case 0:
        input += 1;
        break;
    case 2 ... 3:
        input += 2;
        break;
    default:
        input += 3;
    }
    switch (input)
    case 4:
        input += 4;

    int range_values[2] = {1, 2};
    for (int range_value : range_values)
        input += range_value;
#if __cplusplus >= 202002L
    for (int range_init = 0; int range_value : range_values)
        input += range_init + range_value;
#endif

    int asm_output;
    asm volatile("mov %1, %0" : "=r"(asm_output) : "r"(input) : "memory");
    [[likely]] if (asm_output)
        input += asm_output;
    goto statement_label;
statement_label:
    input += 1;
    try {
        input += 2;
    } catch (...) {
        input -= 2;
    }
    if (input < 0)
        return input;
    return local_uninitialized + local_initialized + local_static +
           mixed_first + mixed_last + direct_binding + holding_binding + input;
}

#if __cplusplus >= 202302L

template <class T> constexpr int statement_consteval_kernel(T value) {
    if consteval {
        return 1;
    }
}
#endif

template <class T, int N> int statement_template_kernel(T range, T value) {
    T template_local(value);
    T template_uninitialized;
    if (value)
        template_local = value;
    switch (N) {
    case N:
        break;
    default:
        break;
    }
    for (auto element : range)
        template_local = element;
    return N;
}
