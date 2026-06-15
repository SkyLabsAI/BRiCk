/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

enum Small : int { A = 1, B = 2 };
enum Byte : unsigned char { C = 255 };

float char_to_float(char c) { return static_cast<float>(c); }
double char16_to_double(char16_t c) { return static_cast<double>(c); }
char float_to_char(float f) { return static_cast<char>(f); }
char8_t double_to_char8(double d) { return static_cast<char8_t>(d); }
float enum_to_float(Small e) { return static_cast<float>(e); }
Small float_to_enum(float f) { return static_cast<Small>(f); }
__float128 char_to_quad(char c) { return static_cast<__float128>(c); }
float byte_enum_to_float(Byte e) { return static_cast<float>(e); }
