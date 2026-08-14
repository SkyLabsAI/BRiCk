int global_value;
namespace scope {
int scoped_value;
}
struct Record {
  static int member_value;
};
namespace {
int hidden;
}
struct {
  int payload;
} by_decl;
typedef struct {
  int typed_payload;
} Alias;
static union {
  int leaked_field;
};
struct Holder {
  struct {};
  struct {
    int child;
  };
};
void unported_function();
