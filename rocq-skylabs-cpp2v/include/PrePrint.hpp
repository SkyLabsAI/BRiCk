#pragma once
#include "Formatter.hpp"
#include <Assert.hpp>
#include <map>

namespace clang {
class Decl;
class Type;
class NamedDecl;
} // namespace clang

class Cache {
public:
    using name_t = unsigned int;
    static constexpr char TYPE_PREFIX = 't';
    static constexpr char NAME_PREFIX = 'n';

private:
    template <typename T, char PREFIX> class NameCache {
        std::map<T *, name_t> entries_{};
        name_t next_{1}; // we reserve 0

    public:
        name_t fresh(T *) { return next_++; }
        void store(T *p, name_t n) {
            always_assert(entries_.find(p) == entries_.end());
            entries_.insert({p, n});
        }
        name_t lookup(T *p) {
            auto nm = entries_.find(p);
            return nm == entries_.end() ? 0 : nm->second;
        }
        bool reference(T *p, fmt::Formatter &output) {
            auto x = lookup(p);
            if (x) {
                output << PREFIX << x;
            }
            return (bool)x;
        }
    };

    NameCache<const clang::Type, TYPE_PREFIX> types_{};
    NameCache<const clang::NamedDecl, NAME_PREFIX> names_{};

public:
#define PASSTHRU(TY, MP)                                                       \
    name_t fresh(TY *t) { return MP.fresh(t); }                                \
    void store(TY *p, unsigned int n) { return MP.store(p, n); }               \
    name_t lookup(TY *t) { return MP.lookup(t); }                              \
    bool reference(TY *p, fmt::Formatter &output) {                            \
        return MP.reference(p, output);                                        \
    }
    PASSTHRU(const clang::Type, types_)
    PASSTHRU(const clang::NamedDecl, names_)
};

class ClangPrinter;
class CoqPrinter;

template <typename T>
using PRINTER = std::function<void(char, Cache::name_t, const T *)>;

void prePrintDecl(const clang::Decl *, Cache &, const PRINTER<clang::Type> &,
                  const PRINTER<clang::NamedDecl> &);