extern void assert(bool);
#define CHECK_NULL(expr) assert((expr) == nullptr)

struct NullptrHolder {
  decltype(nullptr) value;
};

void coverage_nullptr_local_direct_reads() {
  decltype(nullptr) local = nullptr;
  CHECK_NULL(local);
}

void coverage_nullptr_local_reference_reads() {
  decltype(nullptr) local = nullptr;
  decltype(nullptr)& npr = local;
  CHECK_NULL(npr);

  const decltype(nullptr)& cnpr = local;
  CHECK_NULL(cnpr);
}

void coverage_nullptr_field_direct_reads() {
  NullptrHolder holder{nullptr};
  CHECK_NULL(holder.value);
}

void coverage_nullptr_field_reference_reads() {
  NullptrHolder holder{nullptr};
  decltype(nullptr)& npr = holder.value;
  CHECK_NULL(npr);

  const decltype(nullptr)& cnpr = holder.value;
  CHECK_NULL(cnpr);
}
