/*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once
#include "clang/AST/ASTContext.h"
#include "clang/AST/Type.h"
#include "clang/Basic/SourceManager.h"
#include <list>

using namespace clang;

class Filter {
public:
    enum class What : unsigned int {
        NOTHING = 0,
        DECLARATION = 1,
        DEFINITION = 2
    };

    static What min(What a, What b) {
        if (a < b) {
            return a;
        } else {
            return b;
        }
    }

    static What max(What a, What b) {
        if (a < b) {
            return b;
        } else {
            return a;
        }
    }

    virtual What shouldInclude(const Decl *) = 0;
};

class Default : public Filter {
private:
    const Filter::What what;

public:
    Default(Filter::What w) : what(w) {}
    virtual What shouldInclude(const Decl *) { return what; }
};

class NoInclude : public Filter {
private:
    const SourceManager &SM;

public:
    NoInclude(SourceManager &_SM) : SM(_SM) {}

    /* is this location in an include'd file? */
    bool isIncluded(SourceLocation loc) {
        if (!loc.isValid()) {
            return false;
        }
        PresumedLoc PLoc = SM.getPresumedLoc(loc);
        if (PLoc.isInvalid()) {
            return false;
        } else {
            if (PLoc.getIncludeLoc().isValid()) {
                return true;
            } else {
                return false;
            }
        }
    }

    virtual What shouldInclude(const Decl *d) {
        SourceLocation loc = d->getSourceRange().getBegin();
        return isIncluded(loc) ? What::DECLARATION : What::DEFINITION;
    }
};

class NoPrivate : public Filter {
public:
    virtual What shouldInclude(const Decl *d) { return What::DEFINITION; }
};

template <Filter::What unit,
          Filter::What (*combine)(Filter::What, Filter::What)>
class Combine : public Filter {
private:
    const std::list<Filter *> &filters;

public:
    Combine(std::list<Filter *> &f) : filters(f) {}

    virtual What shouldInclude(const Decl *d) {
        What result = unit;

        for (auto x : filters) {
            result = combine(result, x->shouldInclude(d));
        }

        return result;
    }
};

class FromComment : public Filter {
private:
    const ASTContext *const ctxt;

public:
    FromComment(const ASTContext *_ctxt) : ctxt(_ctxt) {}

    virtual What shouldInclude(const Decl *d) {
        if (auto comment = ctxt->getRawCommentForDeclNoCache(d)) {
            auto text = comment->getRawText(ctxt->getSourceManager());
            if (StringRef::npos != text.find("definition")) {
                return What::DEFINITION;
            } else if (StringRef::npos != text.find("declaration")) {
                return What::DECLARATION;
            } else {
                return What::NOTHING;
            }
        } else {
            // private by default
            return What::NOTHING;
        }
    }
};
