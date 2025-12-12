/*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

[[noreturn]] void assertion_failed(const char *e, const char *func,
                                   const char *file, int line);

/// Unconditional variant of `assert`
#define always_assert(e)                                                       \
    ((e) ? (void)0 : assertion_failed(#e, __func__, __FILE__, __LINE__))
