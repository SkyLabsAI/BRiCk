enum Shared {};
Shared *first_occurrence;
Shared *second_occurrence;
const Shared *qualified_occurrence;
template <class T> long *template_only_type;
int shared_function(Shared *value);
template <class T> struct MetaOnly { T *field; };
