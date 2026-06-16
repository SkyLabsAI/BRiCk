_Float16 decimal_float16() {
  return 1.0f16;
}

float decimal_float() {
  return 1.0f;
}

float negative_zero_float() {
  return -0.0f;
}

double decimal_double() {
  return 2.5;
}

double hex_double() {
  return 0x1.8p+2;
}

double scientific_double() {
  return 1.25e-3;
}

__float128 decimal_float128() {
  return 1.0Q;
}
