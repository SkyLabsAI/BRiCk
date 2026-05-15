/*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

// Cover synthesized anonymous scopes for disambiguation

// NOTE: We're using variables simply to reduce clutter in the output.

void f() {
    { }	// f::0
    { static int v; }	// f::1::v
#if 0
    { { } }	// f::2
    { { static int v; } }	// f::3::0::v
    { }	// f::4
#endif
    static int v;	// f::v
}
