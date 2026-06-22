enum Small : int { A = 65, B = 66 };

void floating_casts_extra() {
  bool b = static_cast<bool>(0.0f);
  float from_bool = static_cast<float>(true);
  float from_char = static_cast<float>('A');
  float from_enum = static_cast<float>(A);
  int to_int = static_cast<int>(1.0f);
  char to_char = static_cast<char>(1.0f);
  Small to_enum = static_cast<Small>(1.0f);
  (void)b;
  (void)from_bool;
  (void)from_char;
  (void)from_enum;
  (void)to_int;
  (void)to_char;
  (void)to_enum;
}
