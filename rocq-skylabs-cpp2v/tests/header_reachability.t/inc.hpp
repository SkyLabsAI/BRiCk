struct DeadRecord {
    int value;
};

inline int dead_helper() { return 40; }
inline int dead_function() { return dead_helper(); }

template <typename T> T dead_template(T value) { return value; }

namespace unused_namespace {
struct DeadNamespaceRecord {};
} // namespace unused_namespace
namespace dead_alias = unused_namespace;

static_assert(true, "unrelated assertion");

struct UsedRecord {
    int value;
};

inline int used_helper(UsedRecord record) { return record.value; }
inline int used_function(UsedRecord record) { return used_helper(record); }

namespace api {
inline namespace v1 {
struct UsedInlineRecord {
    int value;
};
} // namespace v1
} // namespace api
