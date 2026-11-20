/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 *
 * SPDX-License-Identifier: MIT-0
 */

typedef long long v4di __attribute__((__vector_size__(32)));
typedef long long v4di_u __attribute__((__vector_size__(32), __aligned__(1)));
using v16qi_u = char __attribute__((__vector_size__(16), __aligned__(1)));

v4di id_vec(v4di const x) {
    return x;
}

v4di_u const *as_unaligned_vec(unsigned char const *p) {
    return reinterpret_cast<v4di_u const *>(p);
}

v16qi_u const *as_unaligned_vec16(char const *p) {
    return reinterpret_cast<v16qi_u const *>(p);
}
