/*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

// Cover `function_name` constructors

void fid();
struct fname{
    fname();
    ~fname();
    fname(const fname&) = delete;
    fname(fname&&) = delete;
    fname& operator=(const fname&) = delete;
    fname& operator=(fname&&) = delete;
    fname& operator++();
    operator int();
};
int operator ""_lit(unsigned long long);

// Cover other bits in `Nfunction`

struct extra{
    extra() = delete;
    ~extra();
    extra(const extra&) = delete;
    extra(extra&&) = delete;
    extra& operator=(const extra&) = delete;
    extra& operator=(extra&&) = delete;

    void args();
    void args(int, bool=false);
    void l() &;
    void r() &&;
    void c() const;
    void v() volatile;
    void cvl() const volatile &;
};
