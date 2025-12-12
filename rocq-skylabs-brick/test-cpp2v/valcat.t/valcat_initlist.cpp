/*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

void lvalues(int& r){
    int init_list_1[] {1, 2, 3};	// prvalue
    int& init_list_2 { r };	// lvalue (but "transparent" and suppressed in our AST)
}
