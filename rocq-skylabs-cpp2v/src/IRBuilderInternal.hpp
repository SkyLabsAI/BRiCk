/* Internal, transient Clang-backed builder state. */
#pragma once

#include "ClangSourceInfo.hpp"
#include "IRBuilder.hpp"
#include "IRFactories.hpp"

#include <clang/AST/ASTContext.h>
#include <clang/AST/Decl.h>
#include <clang/AST/Expr.h>
#include <clang/AST/NestedNameSpecifier.h>
#include <clang/AST/TemplateBase.h>
#include <clang/AST/Type.h>
#include <clang/AST/TypeLoc.h>
#include <cstdint>
#include <utility>
#include <vector>

#include <llvm/ADT/DenseMap.h>

namespace clang {
class Sema;
}

namespace ir {
namespace builder {

class State {
public:
    explicit State(clang::ASTContext &context, clang::Sema *sema = nullptr);

    llvm::Expected<NodeId> buildName(const clang::NamedDecl &declaration,
                                     SemanticMode mode);
    llvm::Expected<NodeId>
    buildUndecoratedName(const clang::NamedDecl &declaration,
                         SemanticMode mode);
    llvm::Expected<NodeId> buildPatternName(const clang::NamedDecl &declaration,
                                            SemanticMode mode);
    llvm::Expected<NodeId> buildFieldName(const clang::FieldDecl &field,
                                          SemanticMode mode,
                                          factory::OriginList origins);
    llvm::Expected<NodeId>
    buildUnresolvedName(clang::NestedNameSpecifier qualifier,
                        clang::NestedNameSpecifierLoc qualifierLocation,
                        llvm::StringRef identifier,
                        llvm::ArrayRef<clang::TemplateArgumentLoc> arguments,
                        SemanticMode mode, factory::OriginList origins);
    llvm::Expected<NodeId>
    buildUnresolvedName(clang::NestedNameSpecifier qualifier,
                        clang::NestedNameSpecifierLoc qualifierLocation,
                        clang::DeclarationName name,
                        llvm::ArrayRef<clang::TemplateArgumentLoc> arguments,
                        SemanticMode mode, factory::OriginList origins);
    llvm::Expected<NodeId> buildType(clang::QualType type, SemanticMode mode,
                                     factory::OriginList origins = {});
    llvm::Expected<NodeId>
    buildWrittenType(const clang::TypeSourceInfo &typeSourceInfo,
                     SemanticMode mode);
    llvm::Expected<NodeId> buildTypeLoc(clang::TypeLoc typeLoc,
                                        SemanticMode mode,
                                        factory::OriginList inherited = {});
    llvm::Expected<NodeId> buildNormalizedArgumentType(
        clang::QualType adjusted, const clang::TypeSourceInfo *written,
        SemanticMode mode, factory::OriginList inherited = {});
    llvm::Expected<NodeId> buildExpression(const clang::Expr &expression,
                                           SemanticMode mode);
    llvm::Expected<BuildNodeGroup>
    buildLocalDeclaration(const clang::Decl &declaration, SemanticMode mode);
    llvm::Expected<BuildNodeGroup> buildStatement(const clang::Stmt *statement,
                                                  SemanticMode mode);
    llvm::Expected<NodeId> buildSingleStatement(const clang::Stmt *statement,
                                                SemanticMode mode);
    llvm::Expected<NodeId> buildObjectValue(const clang::NamedDecl &,
                                            SemanticMode);
    llvm::Expected<NodeId> buildGlobalDeclaration(const clang::NamedDecl &,
                                                  SemanticMode);
    llvm::Expected<factory::TemplateParameters>
    buildDeclarationTemplateParameters(const clang::Decl &, SemanticMode);
    llvm::Error addImplicitMemberRoots(const clang::NamedDecl &, SemanticMode);
    llvm::Error addNamespaceAlias(const clang::Decl &, const clang::NamedDecl *,
                                  const clang::NamedDecl &, SemanticMode);
    llvm::Error addStaticAssertion(const clang::Decl &, SemanticMode);
    llvm::Error addTemplateAlias(const clang::NamedDecl &, SemanticMode,
                                 bool includeComment = false);
    llvm::Error addTemplateInstance(const clang::NamedDecl &, SemanticMode,
                                    bool includeComments = false);
    llvm::Expected<NodeId> applyInitializingType(NodeId initializer,
                                                 clang::QualType targetType,
                                                 SemanticMode mode,
                                                 source::OriginId generated);
    llvm::Expected<NodeId>
    buildTemplateParameter(const clang::NamedDecl &parameter,
                           SemanticMode mode);
    llvm::Expected<std::optional<NodeId>>
    buildTemplateParameterDefault(const clang::NamedDecl &parameter,
                                  NodeId builtParameter, SemanticMode mode);
    llvm::Expected<NodeId>
    buildTemplateArgument(const clang::TemplateArgument &argument,
                          SemanticMode mode, factory::OriginList origins = {});
    llvm::Expected<NodeId>
    buildTemplateArgumentLoc(const clang::TemplateArgumentLoc &argument,
                             SemanticMode mode);
    llvm::Error attachNameShare(NodeId node,
                                const clang::NamedDecl &declaration,
                                SemanticMode mode);
    llvm::Error attachTypeShare(NodeId node, clang::QualType type,
                                SemanticMode mode);
    std::string diagnosticName(const clang::NamedDecl &declaration);
    llvm::Expected<factory::OriginList>
    declarationOrigins(const clang::Decl &declaration);
    llvm::Expected<source::OriginId>
    transformedDeclarationOrigin(const clang::Decl &declaration,
                                 source::OriginId derivedFrom);
    llvm::Expected<factory::OriginList>
    inheritedTypeOrigins(clang::QualType type,
                         const factory::OriginList &parentOrigins);
    llvm::Expected<BuildArtifact> finish(BuildArtifact artifact);

    clang::ASTContext &context;
    clang::Sema *sema;
    std::unique_ptr<TranslationUnitIR> unit;
    source::ClangTableBuilder sources;
    llvm::DenseMap<const clang::NamedDecl *, ShareClassId> nameClasses;
    llvm::DenseMap<const clang::NamedDecl *, NodeId> nameRepresentatives;
    llvm::DenseMap<std::pair<const clang::Type *, unsigned>, ShareClassId>
        typeClasses;
    llvm::DenseMap<std::pair<const clang::Type *, unsigned>, NodeId>
        typeRepresentatives;
    llvm::DenseMap<std::pair<unsigned, unsigned>, std::string>
        preferredTemplateTypeNames;
    llvm::DenseMap<std::pair<unsigned, unsigned>, std::string>
        preferredTemplateTypeErrors;
    std::optional<std::string> preferredTemplateTypeFallbackError;
    bool buildingPatternName = false;
    unsigned expressionBuildDepth = 0;
    std::uint64_t nextOpaqueName = 0;
    int arrayLoopIndexDepth = -1;
    std::vector<const clang::CXXRecordDecl *> activeCaptureInitializerClosures;
    llvm::DenseMap<const clang::OpaqueValueExpr *, std::uint64_t> opaqueNames;
    llvm::DenseMap<const clang::OpaqueValueExpr *, source::OriginId>
        opaqueOrigins;
    llvm::DenseMap<const clang::OpaqueValueExpr *, source::OriginId>
        opaqueAnchors;
    std::vector<source::OriginId> arrayLoopOrigins;
    std::vector<source::OriginId> generatedExpressionAnchors;
    llvm::DenseMap<const clang::Stmt *, source::OriginId>
        statementOriginOverrides;
    llvm::DenseMap<const clang::ValueDecl *, std::uint64_t> anonymousLocals;
    std::vector<const clang::ValueDecl *> activeAnonymousLocals;
};

llvm::Error migrationIncomplete(const clang::Decl &declaration,
                                llvm::StringRef branch);
llvm::Expected<const clang::DeclContext *>
nonIgnorableContext(const clang::Decl &declaration);
llvm::Expected<unsigned> anonymousIndex(const clang::DeclContext &context,
                                        const clang::Decl &declaration);
bool isSemanticallyNamed(const clang::Decl &declaration);

/// Internal exact-legacy dispatch seam used by the focused builder probe.
const char *
templateArgumentKindNameForTest(clang::TemplateArgument::ArgKind kind);

} // namespace builder
} // namespace ir
