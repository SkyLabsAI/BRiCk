/*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

// Cover names that become `Nanon`
namespace{
    struct inhabit_ns;
}
struct container{
    container();
    ~container();
    container(const container&) = delete;
    container(container&&) = delete;
    container& operator=(const container&) = delete;
    container& operator=(container&&) = delete;

    struct{
        int inhabit_s;
    };

    union{
        const int inhabit_u;
    };
};
enum { inhabit_e };
