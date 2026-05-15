/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

template<typename T>
class P {
};

template<typename T, typename U, int n>
class Q {
};

template class P<unsigned int>;
template class Q<unsigned char, unsigned long long, 32>;
