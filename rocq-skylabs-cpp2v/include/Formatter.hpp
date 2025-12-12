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

    llvm::raw_ostream &line();

    llvm::raw_ostream &nobreak();

    llvm::raw_ostream &flush();

    void nbsp();

    void indent();
    void outdent();

    void clear_spaces() { spaces = 0; }

    void ascii(int c);

    template <typename T> Formatter &operator<<(T val) {
        nobreak() << val;
        blank = false;
        return *this;
    }

public:
    // debugging
    unsigned int get_depth() const { return depth; }

public:
    static Formatter default_output;
};

struct NBSP;
extern const NBSP *nbsp;
Formatter &operator<<(Formatter &out, const NBSP *_);

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
    obj.value.dump(fmt.nobreak());
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

struct INDENT;
extern const INDENT *indent;
Formatter &operator<<(Formatter &out, const INDENT *_);

struct OUTDENT;
extern const OUTDENT *outdent;
Formatter &operator<<(Formatter &out, const OUTDENT *_);

struct LPAREN;
extern const LPAREN *lparen;
Formatter &operator<<(Formatter &out, const LPAREN *_);

struct RPAREN;
extern const RPAREN *rparen;
Formatter &operator<<(Formatter &out, const RPAREN *_);

struct LINE;
extern const LINE *line;
Formatter &operator<<(Formatter &out, const LINE *_);

struct TUPLESEP;
extern const TUPLESEP *tuple_sep;
Formatter &operator<<(Formatter &, const TUPLESEP *);

struct CONS;
extern const CONS *cons;
Formatter &operator<<(Formatter &, const CONS *);

struct BOOL {
    bool value;
    explicit BOOL(bool b) : value(b) {}
};
Formatter &operator<<(Formatter &out, BOOL b);

} // namespace fmt
