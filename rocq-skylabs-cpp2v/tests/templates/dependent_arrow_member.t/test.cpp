template<class T>
auto dependent_arrow_member(T* p) -> decltype(p->field);
