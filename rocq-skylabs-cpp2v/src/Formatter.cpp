/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "Formatter.hpp"
#include "Assert.hpp"
#include "clang/Basic/LLVM.h"
#include "llvm/ADT/APSInt.h"
#include "llvm/Support/raw_ostream.h"

namespace fmt {

Formatter::Formatter() : Formatter(llvm::outs()) {}

Formatter::Formatter(llvm::raw_ostream &_out)
    : out(_out), depth(0), spaces(0), blank(true) {}

Formatter &Formatter::line() {
    out << "\n";
    blank = true;
    spaces = 0;
    return *this;
}

Formatter &Formatter::nobreak() {
    if (blank) {
        for (unsigned int d = this->depth; d > 0; --d) {
            out << " ";
        }
        blank = false;
    }
    for (; spaces > 0; --spaces) {
        out << " ";
    }
    return *this;
}

Formatter &Formatter::flush() {
    raw().flush();
    return *this;
}

llvm::raw_ostream &Formatter::raw() {
    nobreak();
    return out;
}

void Formatter::nbsp() { spaces = 1; }

void Formatter::indent() { this->depth += 2; }
void Formatter::outdent() {
    always_assert(this->depth >= 2);
    this->depth -= 2;
}

void Formatter::ascii(int val) {
    raw() << "\"";
    out << (char)((val >> 6) + '0');
    out << (char)(((val >> 3) & 0x7) + '0');
    out << (char)((val & 0x7) + '0');
    out << "\"";
}

Formatter Formatter::default_output = Formatter();

Formatter &operator<<(Formatter &out, NBSP) {
    out.nbsp();
    return out;
}

Formatter &operator<<(Formatter &out, INDENT) {
    out.indent();
    return out;
}

Formatter &operator<<(Formatter &out, OUTDENT) {
    out.outdent();
    return out;
}

Formatter &operator<<(Formatter &out, LPAREN) {
    out.raw() << "(";
    out.indent();
    return out;
}

Formatter &operator<<(Formatter &out, RPAREN) {
    out.outdent();
    out.clear_spaces();
    out.raw() << ")";
    return out;
}

Formatter &operator<<(Formatter &out, LINE) {
    out.line();
    return out;
}

Formatter &operator<<(Formatter &out, TUPLESEP) {
    return out << "," << fmt::nbsp;
}

Formatter &operator<<(Formatter &out, CONS) {
    return out << fmt::nbsp << "::" << fmt::nbsp;
}

Formatter &operator<<(Formatter &out, BOOL b) {
    out.raw() << (b.value ? "true" : "false");
    return out;
}

Formatter &operator<<(Formatter &out, const NUM &n) {
    auto &[val, is_signed, is_negative, scope] = n;
    auto &os = out.raw();
    if (is_negative)
        os << '(';
    val.print(os, is_signed);
    if (is_negative)
        os << ')';
    if (scope)
        os << '%' << scope;
    return out;
}

Formatter &operator<<(Formatter &out, const llvm::APSInt &n) {
    return out << Z(n);
}

} // namespace fmt
