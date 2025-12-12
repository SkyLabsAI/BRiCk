//===- DeclVisitor.h - Visitor for Decl subclasses --------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file backports AtomicExpr::getOpAsString() to clang <= 17.
//
//===----------------------------------------------------------------------===//

#pragma once
#include "clang/AST/Expr.h"
#include "clang/AST/OperationKinds.h"
#include "llvm/ADT/StringRef.h"
#include <clang/Basic/Version.inc>

namespace AtomicOpBackport {
using namespace clang;
#if 18 <= CLANG_VERSION_MAJOR
static llvm::StringRef
getOpAsString(const clang::AtomicExpr* expr) {
	return expr->getOpAsString();
}
#else
static llvm::StringRef
getOpAsString(const clang::AtomicExpr* expr) {
	switch (expr->getOp()) {
#define BUILTIN(ID, TYPE, ATTRS)
#define ATOMIC_BUILTIN(ID, TYPE, ATTRS)                                        \
	case AtomicExpr::AtomicOp::AO##ID:                                         \
		return #ID;
#include "clang/Basic/Builtins.def"
	}
	llvm_unreachable("not an atomic operator?");
}
#endif
}