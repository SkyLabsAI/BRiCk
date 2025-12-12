/*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

namespace Trace {

using underlying = unsigned;

/**
For use by the command line parser.

Clang's cl::bits makes `--trace=ALL` awkward. As a work-around, we
enumerate the values twice and (in Trace::fromBits), promote bit::ALL to
a mask with all bits set.
*/
enum class Bit : underlying {
    Elaborate = 1,
    ModuleBuilder,
    Decl,
    Name,
    Type,
    Stmt,
    Local,
    Expr,
    ALL,
};

inline constexpr underlying mask(Bit b) {
    return underlying{1} << static_cast<underlying>(b);
}

enum Mask : underlying {
    NONE = underlying{0},
#define TRACE(b) b = mask(Bit::b)
    TRACE(Elaborate),
    TRACE(ModuleBuilder),
    TRACE(Decl),
    TRACE(Name),
    TRACE(Type),
    TRACE(Stmt),
    TRACE(Local),
    TRACE(Expr),
#undef TRACE
    ALL = ~underlying{0},
};

/// For use by the command line parser.
inline constexpr Mask fromBits(underlying bits) {
    return bits & mask(Bit::ALL) ? Mask::ALL : Mask{bits};
}
} // namespace Trace
