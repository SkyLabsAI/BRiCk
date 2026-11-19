// What `std::source_location::current()` expands to. The result points to a
// global object clang makes up (an UnnamedGlobalConstantDecl), not to an
// expression.
namespace std {
struct source_location {
    struct __impl {
        const char *_M_file_name;
        const char *_M_function_name;
        unsigned _M_line, _M_column;
    };
};
} // namespace std

const void *f() { return __builtin_source_location(); }
