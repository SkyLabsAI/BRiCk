/*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once
#include <clang/Basic/Diagnostic.h>
#include <llvm/ADT/SmallVector.h>

namespace clang {
class ValueDecl;
class OpaqueValueExpr;
} // namespace clang

struct OpaqueNames {
    OpaqueNames() {}
    llvm::SmallVector<const clang::OpaqueValueExpr *, 3> indexes;
    llvm::SmallVector<const clang::ValueDecl *, 3> anonymous;
    int _index_count{-1};
    int fresh(const clang::OpaqueValueExpr *e) {
        int index = indexes.size();
        indexes.push_back(e);
        return index;
    }
    // We don't need to reuse names (it would be an optimization), so we don't
    // bother removing them from the `SmallVector`
    void free(const clang::OpaqueValueExpr *e) {}
    int find(const clang::OpaqueValueExpr *e) {
        int result = 0;
        for (auto i : indexes) {
            if (i == e)
                return result;
            ++result;
        }
        return -1;
    }

    int push_anon(const clang::ValueDecl *e) {
        int index = anonymous.size();
        anonymous.push_back(e);
        return index;
    }
    int find_anon(const clang::ValueDecl *e) const {
        int result = 0;
        for (auto i : anonymous) {
            if (i == e)
                return result;
            ++result;
        }
        return -1;
    }
    void pop_anon(const clang::ValueDecl *e) {
        assert(0 < anonymous.size() && "popping from empty vector");
        assert(e == anonymous.back() && "popping wrong entry");
        anonymous.pop_back();
    }

    int index_count() const { return _index_count; }
    void inc_index_count() { _index_count++; }
    void dec_index_count() { _index_count--; }
};
