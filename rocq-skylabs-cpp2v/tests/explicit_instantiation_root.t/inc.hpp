template <typename T> struct ExplicitClass {
    struct Entry {
        T value;
    };

    T read() const { return Entry{T{1}}.value; }
};

template struct ExplicitClass<int>;

template <typename T> T explicit_function(T value) { return value; }
template int explicit_function<int>(int);

template <typename T> T explicit_variable = T{2};
template int explicit_variable<int>;

template <typename T> T declared_function(T value) { return value; }
extern template int declared_function<int>(int);

template <typename T> struct MemberOwner {
    T member_function();
    static T member_variable;
};

template <typename T> T MemberOwner<T>::member_function() { return T{3}; }
template <typename T> T MemberOwner<T>::member_variable = T{4};

template int MemberOwner<int>::member_function();
template int MemberOwner<int>::member_variable;

struct UnusedRecord {};
