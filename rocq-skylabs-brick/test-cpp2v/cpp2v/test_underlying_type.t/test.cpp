/*
 * Copyright (C) 2021 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

template <typename T>
constexpr auto	// __underlying_type (T)
my_underlying (T x)
{
    return static_cast <__underlying_type (T)> (x);
}

enum my_type : unsigned { Cats, Dogs, Bunnies };

unsigned
test (my_type x)
{
    return my_underlying (Bunnies) - my_underlying (x);
}
