// OpenMP: directives print as unsupported statements, and local
// declarations (threadprivate, declare reduction, allocate) are not dropped.
int omp_parallel() { int s = 0;
#pragma omp parallel
  { s = 1; }
  return s; }
int omp_for(int *a, int n) {
#pragma omp parallel for
  for (int i = 0; i < n; ++i) a[i] = i;
  return 0; }
int omp_simd(int *a, int n) {
#pragma omp simd
  for (int i = 0; i < n; ++i) a[i] = i;
  return 0; }
int omp_critical(int *a) {
#pragma omp critical
  { a[0] = 1; }
  return 0; }
int omp_atomic(int *a) {
#pragma omp atomic
  a[0] += 1;
  return 0; }
int omp_task(int *a) {
#pragma omp task depend(in: a[0:2])
  { a[0] = 1; }
  return 0; }
int omp_sections(int *a) {
#pragma omp parallel sections
  {
#pragma omp section
    a[0] = 1;
#pragma omp section
    a[1] = 1;
  }
  return 0; }
int omp_attr(int *a, int n) {
  [[omp::directive(parallel for)]] for (int i = 0; i < n; ++i) a[i] = 0;
  return 0; }
int omp_threadprivate() {
  static int t = 3;
#pragma omp threadprivate(t)
  return t; }
struct Acc { int v; };
int omp_declare_reduction(int *a, int n) {
#pragma omp declare reduction(accplus : Acc : omp_out.v += omp_in.v)
  Acc acc{0};
  for (int i = 0; i < n; ++i) acc.v += a[i];
  return acc.v; }
int omp_allocate() {
  int x = 1;
#pragma omp allocate(x)
  return x; }
