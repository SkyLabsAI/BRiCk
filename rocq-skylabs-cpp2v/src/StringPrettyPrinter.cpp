/*
 * Copyright (c) 2022-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "CoqPrinter.hpp"
#include <clang/AST/Expr.h>

using namespace clang;
using namespace fmt;

fmt::Formatter &CoqPrinter::str(llvm::StringRef str) {
    auto &os = output_;
    /*
    Coq string literals may include embeded newlines
    and utf8 sequences. We only need to double any
    occurrences of `"`.
    */
    os << '\"';
    for (char c : str) {
        os << c;
        if (c == '"')
            os << c;
    }
    return os << '\"';
}

fmt::Formatter &CoqPrinter::cmt(llvm::StringRef str) {
    auto &os = output_;
    os << "(* ";
    auto b = str.begin();
    auto n = str.size();
    for (size_t i = 0; i < n; i++) {
        char c = *(b + i);
        os << c;
        if ((c == '(' || c == '*') && i + 1 < n) {
            char d = *(b + i + 1);
            if ((c == '(' && d == '*') || (c == '*' && d == ')'))
                os << ' ';
        }
    }
    return os << " *)";
}
