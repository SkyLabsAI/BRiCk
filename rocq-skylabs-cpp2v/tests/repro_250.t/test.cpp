template<class D> struct view_interface {};
template<class T> struct chunk_view { struct OuterIter { struct value_type; }; };
template<class T> struct chunk_view<T>::OuterIter::value_type : view_interface<value_type> {};
