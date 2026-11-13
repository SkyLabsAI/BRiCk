struct B { virtual ~B() { } };
void plain(B* p) { delete p; }
void global(B* p) { ::delete p; }
void plain_array(int* p) { delete[] p; }
void global_array(int* p) { ::delete[] p; }
template<typename T> void dependent(T* p) { ::delete p; }
