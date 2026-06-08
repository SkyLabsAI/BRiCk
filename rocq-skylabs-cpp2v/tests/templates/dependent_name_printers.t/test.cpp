struct Known {
  int member();
  operator int();
};

void accepts(...);

template<class T>
int paren_member_call(Known *p)
{
  return (p->member)();
}

template<class T>
int cast_member_call(Known *p)
{
  return p->operator int();
}

template<class T>
void pseudo_destructor(T *p)
{
  p->~T();
}

template<class T>
int unresolved_member(T p)
{
  return p.member();
}

template<class T>
int unresolved_conversion(T p)
{
  return p.operator int();
}

template<class F>
auto paren_call(F f)
{
  return (f)();
}

template<class T>
int scope_value()
{
  return T::value;
}

template<class T>
int scope_call()
{
  return T::func();
}

template<class T>
int scope_template_call()
{
  return T::template func<int>();
}

template<class T>
auto member_value(T p)
{
  return p.value;
}

template<class T>
auto arrow_member_value(T *p)
{
  return p->value;
}

template<class T>
auto member_template_call(T p)
{
  return p.template func<int>();
}

template<class T>
auto adl_call(T p)
{
  return adl_target(p);
}

template<class T>
auto unary_plus(T p)
{
  return +p;
}

template<class T>
auto binary_plus(T a, T b)
{
  return a + b;
}

template<class T>
auto subscript(T p)
{
  return p[0];
}

template<class T>
auto pointer_to_member(T obj, int T::* member)
{
  return obj.*member;
}

template<class T>
void known_function_dependent_arg(T p)
{
  accepts(p);
}

template<class T>
void qualified_known_function_dependent_arg(T p)
{
  ::accepts(p);
}

template<class T>
long builtin_expect_dependent(T p)
{
  return __builtin_expect(p, 0);
}

template<class T>
int function_pointer_dependent_arg(int (*fp)(T), T p)
{
  return fp(p);
}
