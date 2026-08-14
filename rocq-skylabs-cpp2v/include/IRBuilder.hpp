/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include "IR.hpp"
#include "IRFactories.hpp"

#include <memory>
#include <optional>
#include <vector>

#include <clang/AST/TemplateBase.h>
#include <clang/AST/Type.h>
#include <llvm/ADT/ArrayRef.h>
#include <llvm/Support/Error.h>

class Module;

namespace clang {
class ASTContext;
class Decl;
class Expr;
class NamedDecl;
class Sema;
class Stmt;
class TypeSourceInfo;
} // namespace clang

namespace ir {

enum class SemanticMode { Static, Template };

template <typename T> struct PointerUse {
    const T *value = nullptr;
    SemanticMode mode = SemanticMode::Static;
};

struct QualTypeUse {
    clang::QualType value;
    SemanticMode mode = SemanticMode::Static;
};

enum class DeclarationFamily { Object, Global };
struct RootDeclarationUse {
    const clang::NamedDecl *value = nullptr;
    SemanticMode mode = SemanticMode::Static;
    DeclarationFamily family = DeclarationFamily::Object;
    bool templateRoot = false;
    bool seedName = true;
    bool includeImplicitMembers = false;
};
struct NamespaceAliasUse {
    const clang::Decl *owner = nullptr;
    const clang::NamedDecl *from = nullptr;
    const clang::NamedDecl *to = nullptr;
    SemanticMode mode = SemanticMode::Static;
};

enum class BuildCardinality { Zero, One, Forwarded, Several };

struct BuildNodeGroup {
    BuildCardinality cardinality = BuildCardinality::Zero;
    std::vector<NodeId> nodes;
};

/// An owned experimental result. `names` index into the finished unit; neither
/// this artifact nor its unit retains a Clang pointer.
struct BuildArtifact {
    std::unique_ptr<TranslationUnitIR> unit;
    std::vector<NodeId> names;
    std::vector<NodeId> types;
    std::vector<NodeId> expressions;
    std::vector<NodeId> templateParameters;
    std::vector<TemplateParameterEntry> templateParameterEntries;
    std::vector<NodeId> templateArguments;
    std::vector<NodeId> objectValues;
    std::vector<NodeId> globalDeclarations;
    std::vector<factory::TemplateParameters> declarationTemplateParameters;
    std::vector<BuildNodeGroup> localDeclarationGroups;
    std::vector<BuildNodeGroup> statementGroups;
};

/// Experimental selection boundary used only by focused migration probes.
/// All pointers are consumed while the AST is live and none enters
/// BuildArtifact.
struct BuildSelection {
    llvm::ArrayRef<PointerUse<clang::NamedDecl>> names;
    llvm::ArrayRef<PointerUse<clang::TypeSourceInfo>> writtenTypes;
    llvm::ArrayRef<QualTypeUse> semanticTypes;
    llvm::ArrayRef<PointerUse<clang::Expr>> expressions;
    llvm::ArrayRef<PointerUse<clang::NamedDecl>> templateParameters;
    llvm::ArrayRef<PointerUse<clang::TemplateArgumentLoc>>
        writtenTemplateArguments;
    llvm::ArrayRef<PointerUse<clang::TemplateArgument>>
        semanticTemplateArguments;
    llvm::ArrayRef<PointerUse<clang::Decl>> localDeclarations;
    llvm::ArrayRef<PointerUse<clang::Stmt>> statements;
    llvm::ArrayRef<PointerUse<clang::NamedDecl>> objectDeclarations;
    llvm::ArrayRef<PointerUse<clang::NamedDecl>> globalDeclarations;
    llvm::ArrayRef<PointerUse<clang::Decl>> declarationTemplateParameters;
    llvm::ArrayRef<RootDeclarationUse> rootDeclarations;
    llvm::ArrayRef<NamespaceAliasUse> namespaceAliases;
    llvm::ArrayRef<PointerUse<clang::Decl>> staticAssertions;
    llvm::ArrayRef<PointerUse<clang::NamedDecl>> templateAliases;
    llvm::ArrayRef<PointerUse<clang::NamedDecl>> templateInstances;
};

/// Phase 4 focused builder shell. ModuleBuilder remains the outer production
/// seam; this deliberately narrow entry point builds caller-selected owned
/// names, types, expressions, declaration records, local declarations, and
/// statements. Ordered production module/root events remain at ModuleBuilder.
class IRBuilder {
public:
    static llvm::Expected<BuildArtifact> build(clang::ASTContext &context,
                                               const BuildSelection &selection,
                                               clang::Sema *sema = nullptr);
    static llvm::Expected<BuildArtifact>
    buildNames(clang::ASTContext &context,
               llvm::ArrayRef<const clang::NamedDecl *> declarations);
    /// Consume the exact declaration partitions selected by legacy
    /// ModuleBuilder while Clang is alive, returning only owned IR.
    static llvm::Expected<BuildArtifact>
    buildModule(clang::ASTContext &, const ::Module &, clang::Sema * = nullptr,
                bool includeTypedefs = true, bool includeComments = false);
};

} // namespace ir
