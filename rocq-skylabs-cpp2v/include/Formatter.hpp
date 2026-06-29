/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include "llvm/ADT/APSInt.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/raw_ostream.h"

namespace fmt {

class Formatter {
private:
    llvm::raw_ostream &out;
    unsigned int depth;
    unsigned int spaces;
    bool blank;

public:
    explicit Formatter();
    explicit Formatter(llvm::raw_ostream &);

    Formatter &line();

    Formatter &nobreak();

    Formatter &flush();

    llvm::raw_ostream &raw();

    void nbsp();

    void indent();
    void outdent();

    void clear_spaces() { spaces = 0; }

    void ascii(int c);

    template <typename T> Formatter &operator<<(T val) {
        raw() << val;
        blank = false;
        return *this;
    }

public:
    // debugging
    unsigned int get_depth() const { return depth; }

};

struct NBSP {};
inline constexpr NBSP nbsp{};
Formatter &operator<<(Formatter &out, NBSP);

struct NUM {
    NUM() = delete;
    const llvm::APInt &val;
    const bool is_signed;
    const bool is_negative;
    const char *scope;
};
Formatter &operator<<(Formatter &, const NUM &);

template <typename T> struct ByDump {
    ByDump(T &val) : value{val} {}
    T &value;
};
template <typename T>
inline Formatter &operator<<(Formatter &fmt, ByDump<T> obj) {
    obj.value.dump(fmt.raw());
    return fmt;
}
template <typename T>
inline llvm::raw_ostream &operator<<(llvm::raw_ostream &out, ByDump<T> obj) {
    obj.value.dump(out);
    return out;
}

template <typename T> ByDump<T> dump(T &val) { return ByDump<T>{val}; }

/// A Coq integer of type `Z` with optional `%Z`
inline NUM Z(const llvm::APSInt &val, bool scope = true) {
    return NUM{val, val.isSigned(), val.isNegative(), scope ? "Z" : nullptr};
}

/// A Coq natural of type `N` with optional `%N`
inline NUM N(const llvm::APInt &val, bool scope = true) {
    return NUM{val, false, false, scope ? "N" : nullptr};
}

/// Equivalent to `fmt::Z`
Formatter &operator<<(Formatter &, const llvm::APSInt &);

struct INDENT {};
inline constexpr INDENT indent{};
Formatter &operator<<(Formatter &out, INDENT);

struct OUTDENT {};
inline constexpr OUTDENT outdent{};
Formatter &operator<<(Formatter &out, OUTDENT);

struct LPAREN {};
inline constexpr LPAREN lparen{};
Formatter &operator<<(Formatter &out, LPAREN);

struct RPAREN {};
inline constexpr RPAREN rparen{};
Formatter &operator<<(Formatter &out, RPAREN);

struct LINE {};
inline constexpr LINE line{};
Formatter &operator<<(Formatter &out, LINE);

struct TUPLESEP {};
inline constexpr TUPLESEP tuple_sep{};
Formatter &operator<<(Formatter &, TUPLESEP);

struct CONS {};
inline constexpr CONS cons{};
Formatter &operator<<(Formatter &, CONS);

struct BOOL {
    bool value;
    explicit BOOL(bool b) : value(b) {}
};
Formatter &operator<<(Formatter &out, BOOL b);

} // namespace fmt
