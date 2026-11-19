// The string literal takes the declared type, here the typedef `Buf`, so its
// type is sugar over an array type.
typedef char Buf[4];
Buf b = "abc";
