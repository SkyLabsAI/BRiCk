// Coroutines, in functions and in a lambda: every body is a
// [CoroutineBodyStmt], so nothing of it is printed as ordinary statements.
// Coroutines, with a minimal <coroutine>.
namespace std {
template <class R, class... Args> struct coroutine_traits {
  using promise_type = typename R::promise_type;
};
template <class P = void> struct coroutine_handle {
  static coroutine_handle from_address(void *) noexcept { return {}; }
  void *address() const noexcept { return nullptr; }
  operator coroutine_handle<void>() const noexcept;
};
template <> struct coroutine_handle<void> {
  static coroutine_handle from_address(void *) noexcept { return {}; }
  void *address() const noexcept { return nullptr; }
};
} // namespace std

struct suspend_never {
  bool await_ready() const noexcept { return true; }
  void await_suspend(std::coroutine_handle<>) const noexcept {}
  void await_resume() const noexcept {}
};
struct task {
  struct promise_type {
    task get_return_object() { return {}; }
    suspend_never initial_suspend() { return {}; }
    suspend_never final_suspend() noexcept { return {}; }
    void return_void() {}
    void unhandled_exception() {}
  };
};
task coro() { co_return; }
struct gen {
  struct promise_type {
    gen get_return_object() { return {}; }
    suspend_never initial_suspend() { return {}; }
    suspend_never final_suspend() noexcept { return {}; }
    suspend_never yield_value(int) { return {}; }
    void return_void() {}
    void unhandled_exception() {}
  };
};
task co_awaiting() { co_await suspend_never{}; co_return; }
gen co_yielding() { co_yield 1; co_yield 2; }
int lambda_coro() { auto l = []() -> task { co_await suspend_never{}; co_return; }; l(); return 0; }
