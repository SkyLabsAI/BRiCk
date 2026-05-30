template<typename T>
void unresolved_initializer_lists(T target)
{
  target.consume({1, 2, 3});
  target.consume({T::value, 4});
  target.consume({{1}, {2, 3}});
}

template<typename T>
void unresolved_constructor_initializer()
{
  T value({1, 2, 3});
  (void)value;
}
