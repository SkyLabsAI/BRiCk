//===- DeclVisitor.h - Visitor for Decl subclasses --------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file defines the DeclVisitor interface.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_AST_DECLVISITOR_ARGS_H
#define LLVM_CLANG_AST_DECLVISITOR_ARGS_H

#include "clang/AST/Decl.h"
#include "clang/AST/DeclBase.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclFriend.h"
#include "clang/AST/DeclObjC.h"
#include "clang/AST/DeclOpenMP.h"
#include "clang/AST/DeclTemplate.h"
#include "llvm/Support/ErrorHandling.h"

namespace clang {

namespace declvisitor2 {

template <typename T> struct make_ptr { using type = T *; };
template <typename T> struct make_const_ptr { using type = const T *; };

/// \brief A simple visitor class that helps create declaration visitors.
template <template <typename> class Ptr, typename ImplClass,
          typename RetTy = void, class... ParamTys>
class Base {
public:
#define PTR(CLASS) typename Ptr<CLASS>::type
#define DISPATCH(NAME, CLASS)                                                  \
  return static_cast<ImplClass *>(this)->Visit##NAME(                          \
      static_cast<PTR(CLASS)>(D), std::forward<ParamTys>(P)...)

  RetTy Visit(PTR(Decl) D, ParamTys... P) {
    switch (D->getKind()) {
#define DECL(DERIVED, BASE)                                                    \
  case Decl::DERIVED:                                                          \
    DISPATCH(DERIVED##Decl, DERIVED##Decl);
#define ABSTRACT_DECL(DECL)
#include "clang/AST/DeclNodes.inc"
    }
    llvm_unreachable("Decl that isn't part of DeclNodes.inc!");
  }

  // If the implementation chooses not to implement a certain visit
  // method, fall back to the parent.
#define DECL(DERIVED, BASE)                                                    \
  RetTy Visit##DERIVED##Decl(PTR(DERIVED##Decl) D, ParamTys... P) {            \
    DISPATCH(BASE, BASE);                                                      \
  }
#include "clang/AST/DeclNodes.inc"

  RetTy VisitDecl(PTR(Decl) D, ParamTys... P) { return RetTy(); }

#undef PTR
#undef DISPATCH
};

} // namespace declvisitor2

/// \brief A simple visitor class that helps create declaration visitors.
///
/// This class does not preserve constness of Decl pointers (see also
/// ConstDeclVisitor).
template <typename ImplClass, typename RetTy = void, typename... ParamTys>
class DeclVisitorArgs
    : public declvisitor2::Base<declvisitor2::make_ptr, ImplClass, RetTy,
                                ParamTys...> {};

/// \brief A simple visitor class that helps create declaration visitors.
///
/// This class preserves constness of Decl pointers (see also DeclVisitor).
template <typename ImplClass, typename RetTy = void, typename... ParamTys>
class ConstDeclVisitorArgs
    : public declvisitor2::Base<declvisitor2::make_const_ptr, ImplClass, RetTy,
                                ParamTys...> {};

} // namespace clang

#endif // LLVM_CLANG_AST_DECLVISITOR_H
