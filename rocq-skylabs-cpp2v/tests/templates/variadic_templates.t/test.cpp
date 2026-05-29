template<typename... Ts>
struct TypePack {
  static int size() {
    return sizeof...(Ts);
  }
};

template<int... Ns>
struct ValuePack {
};

template<template<typename> class... Templates>
struct TemplateTemplatePack {
};

template<typename... Ts>
int variadic_function(Ts... args)
{
  return sizeof...(Ts) + sizeof...(args);
}

template<typename... Ts>
void use_variadic_templates(Ts... args)
{
  TypePack<Ts...> type_pack;
  TypePack<int, Ts...> mixed_type_pack;
  ValuePack<1, sizeof...(Ts)> value_pack;
  (void)type_pack;
  (void)mixed_type_pack;
  (void)value_pack;
  variadic_function(args...);
}
