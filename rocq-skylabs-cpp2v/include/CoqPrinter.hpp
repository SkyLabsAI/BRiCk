/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include "Formatter.hpp"
#include "PrePrint.hpp"
#include <clang/AST/Expr.h>
#include <llvm/ADT/StringRef.h>

namespace clang {
class NamedDecl;
class Type;
}; // namespace clang

namespace logging {
[[noreturn]] void die();
}

class CoqPrinter {
private:
    fmt::Formatter &output_;
    const bool templates_;
    Cache &name_cache_;

public:
    CoqPrinter(fmt::Formatter &output, bool templates, Cache &c)
        : output_(output), templates_(templates), name_cache_{c} {}

    bool reference(const clang::Type *p) {
        return name_cache_.reference(p, output_);
    }
    bool reference(const clang::NamedDecl *p) {
        return name_cache_.reference(p, output_);
    }

    fmt::Formatter &output() const { return output_; }
    bool templates() const { return templates_; }

    [[noreturn]] void die() {
        output().flush();
        logging::die();
    }

    fmt::Formatter &type() {
        return this->output_ << (templates() ? "Mtype" : "type");
    }

    fmt::Formatter &begin_tuple() { return this->output_ << "("; }
    fmt::Formatter &end_tuple() { return this->output_ << ")"; }
    fmt::Formatter &next_tuple() { return this->output_ << fmt::tuple_sep; }

    template <typename T> fmt::Formatter &ctor(T ctor, bool line = true) {
        if (line) {
            this->output_ << fmt::line;
        }
        return this->output_ << fmt::lparen << ctor << fmt::nbsp;
    }

    fmt::Formatter &end_ctor() { return this->output_ << fmt::rparen; }

    fmt::Formatter &begin_record(bool line = true) {
        if (line) {
            this->output_ << fmt::line;
        }
        return this->output_ << "{|" << fmt::nbsp;
    }
    fmt::Formatter &end_record(bool line = true) {
        if (line) {
            this->output_ << fmt::line;
        }
        return this->output_ << fmt::nbsp << "|}";
    }
    fmt::Formatter &record_field(llvm::StringRef field, bool line = true) {
        return this->output_ << field << fmt::nbsp << ":=" << fmt::nbsp;
    }

    fmt::Formatter &some() { return this->ctor("Some"); }
    fmt::Formatter &none() { return this->output_ << "None"; }

    fmt::Formatter &ascii(int c) {
        assert(0 <= c && c < 256);
        this->output_.ascii(c);
        return this->output_;
    }

    /// Print str as a Coq string literal
    fmt::Formatter &str(llvm::StringRef str);

    /// `(* str *)` with `(*`, `*)` in str printed as `( *`, `* )`
    fmt::Formatter &cmt(llvm::StringRef str);

    fmt::Formatter &boolean(bool b) {
        return this->output_ << (b ? "true" : "false");
    }

    // List-printing functions
    template <typename I, typename CLOSURE>
    fmt::Formatter &list_range(I begin, I end, CLOSURE fn) {
        if (begin == end) {
            return this->output_ << "nil";
        }
        begin_list();
        while (begin != end) {
            fn(*begin);
            cons();
            ++begin;
        }
        return end_list();
    }

    template <typename L, typename CLOSURE>
    fmt::Formatter &list(L list, CLOSURE fn) {
        return list_range(list.begin(), list.end(), fn);
    }

    // List-printing functions
    template <typename I, typename CLOSURE>
    fmt::Formatter &list_range_filter(I begin, I end, CLOSURE fn) {
        if (begin == end) {
            return this->output_ << "nil";
        }
        begin_list();
        while (begin != end) {
            if (fn(*begin))
                cons();
            ++begin;
        }
        return end_list();
    }

    template <typename C, typename CLOSURE>
    fmt::Formatter &list_filter(const C &&list, CLOSURE fn) {
        return list_range_filter(list.begin(), list.end(), fn);
    }

    // low-level list-printing API
    fmt::Formatter &begin_list() { return this->output_ << fmt::lparen; }
    fmt::Formatter &end_list() { return this->output_ << "nil" << fmt::rparen; }
    fmt::Formatter &cons() { return this->output_ << fmt::cons; }
};

namespace guard {

class guard {
protected:
    CoqPrinter &print;
    guard(CoqPrinter &p) : print{p} {}

public:
    guard(const guard &) = delete;
    guard &operator=(const guard &) = delete;

    fmt::Formatter &output() const { return print.output(); }
};

struct ctor : public guard {
    ctor(CoqPrinter &p, llvm::StringRef name, bool line = true) : guard{p} {
        print.ctor(name, line);
    }
    ~ctor() { print.end_ctor(); }
};

struct some : public ctor {
    some(CoqPrinter &p, bool line = true) : ctor{p, "Some", line} {}
};

struct tuple : public guard {
    tuple(CoqPrinter &p) : guard{p} { print.begin_tuple(); }
    ~tuple() { print.end_tuple(); }
};

class record : public guard {
public:
    enum class Line : unsigned {
        None = 0,
        Begin = 1,
        End = 2,
        Both = Begin | End,
    };

private:
    Line wantlines;

    bool want(Line bit) const {
        auto w = static_cast<std::underlying_type_t<Line>>(wantlines);
        auto b = static_cast<std::underlying_type_t<Line>>(bit);
        return w & b;
    }

public:
    record(CoqPrinter &p, Line l = Line::Both) : guard{p}, wantlines{l} {
        print.begin_record(want(Line::Begin));
    }
    ~record() { print.end_record(want(Line::End)); }
};

struct list : public guard {
    list(CoqPrinter &p) : guard(p) { print.begin_list(); }
    ~list() { print.end_list(); }
};

} // namespace guard