/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "IRBuilderInternal.hpp"
#include "Sharing.hpp"

#include <system_error>

#include <clang/AST/DeclCXX.h>
#include <clang/AST/DeclTemplate.h>
#include <clang/Basic/SourceManager.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/Support/raw_ostream.h>

namespace ir {
namespace builder {
namespace {

enum class ContextKind { Global, Scope, Ignorable };

llvm::Error error(const std::string &message) {
    return llvm::createStringError(std::errc::not_supported, "%s",
                                   message.c_str());
}

llvm::Expected<ContextKind> classify(const clang::DeclContext &context) {
    using K = clang::Decl::Kind;
    switch (context.getDeclKind()) {
    case K::TranslationUnit:
        return ContextKind::Global;
    case K::Namespace:
    case K::Record:
    case K::CXXRecord:
    case K::ClassTemplateSpecialization:
    case K::ClassTemplatePartialSpecialization:
    case K::Function:
    case K::CXXMethod:
    case K::CXXConstructor:
    case K::CXXDestructor:
    case K::CXXConversion:
    case K::Block:
    case K::Enum:
        return ContextKind::Scope;
    case K::LinkageSpec:
    case K::ExternCContext:
    case K::Export:
    case K::RequiresExprBody:
    case K::CXXDeductionGuide:
        return ContextKind::Ignorable;
    default:
        return error("migration incomplete: unported declaration context " +
                     std::string(context.getDeclKindName()));
    }
}

const clang::TemplateDecl *diagnosticTemplate(const clang::Decl &declaration) {
    if (const auto *value = llvm::dyn_cast<clang::TemplateDecl>(&declaration))
        return value;
    if (const auto *value = llvm::dyn_cast<clang::CXXRecordDecl>(&declaration))
        return value->getDescribedClassTemplate();
    if (const auto *value = llvm::dyn_cast<clang::FunctionDecl>(&declaration))
        return value->getDescribedFunctionTemplate();
    if (const auto *value = llvm::dyn_cast<clang::TypeAliasDecl>(&declaration))
        return value->getDescribedAliasTemplate();
    if (const auto *value = llvm::dyn_cast<clang::VarDecl>(&declaration))
        return value->getDescribedVarTemplate();
    return nullptr;
}

using DiagnosticParameterLists =
    llvm::SmallVector<const clang::TemplateParameterList *, 4>;

unsigned collectDiagnosticParameterLists(const clang::Decl &declaration,
                                         DiagnosticParameterLists &lists) {
    unsigned count = 0;
    if (const clang::DeclContext *declarationContext =
            declaration.getDeclContext()) {
        const auto &contextDeclaration =
            llvm::cast<clang::Decl>(*declarationContext);
        count += collectDiagnosticParameterLists(contextDeclaration, lists);
        if (const clang::TemplateDecl *value = diagnosticTemplate(declaration))
            if (const clang::TemplateParameterList *parameters =
                    value->getTemplateParameters()) {
                count += parameters->size();
                lists.push_back(parameters);
            }
    }
    return count;
}

void printDiagnosticTemplateParameters(llvm::raw_ostream &output,
                                       const clang::Decl &declaration,
                                       const clang::ASTContext &context) {
    DiagnosticParameterLists lists;
    unsigned remaining = collectDiagnosticParameterLists(declaration, lists);
    if (lists.empty())
        return;
    output << '<';
    const clang::PrintingPolicy &policy = context.getPrintingPolicy();
    for (const clang::TemplateParameterList *parameters : lists)
        for (const clang::NamedDecl *parameter : parameters->asArray()) {
            parameter->printName(output, policy);
            if (--remaining)
                output << ", ";
        }
    output << '>';
}

llvm::Expected<bool> anonymousBefore(const clang::DeclContext &context,
                                     const clang::Decl &target,
                                     unsigned &count) {
    for (const clang::Decl *declaration : context.decls()) {
        if (!declaration)
            return error("migration incomplete: null declaration in context");
        if (declaration == &target)
            return true;
        if (const auto *nested =
                llvm::dyn_cast<clang::DeclContext>(declaration)) {
            auto kind = classify(*nested);
            if (!kind)
                return kind.takeError();
            if (*kind == ContextKind::Ignorable) {
                auto found = anonymousBefore(*nested, target, count);
                if (!found)
                    return found.takeError();
                if (*found)
                    return true;
            }
        }
        if (!isSemanticallyNamed(*declaration))
            ++count;
    }
    return false;
}

} // namespace

State::State(clang::ASTContext &astContext, clang::Sema *astSema)
    : context(astContext), sema(astSema),
      unit(std::make_unique<TranslationUnitIR>()),
      sources(astContext.getSourceManager(), astContext.getLangOpts()) {}

std::string State::diagnosticName(const clang::NamedDecl &declaration) {
    std::string result;
    llvm::raw_string_ostream output(result);
    printDiagnosticTemplateParameters(output, declaration, context);
    const clang::PrintingPolicy &policy = context.getPrintingPolicy();
    declaration.getNameForDiagnostic(output, policy, true);
    const clang::FunctionDecl *function =
        llvm::dyn_cast<clang::FunctionDecl>(&declaration);
    if (!function)
        if (const auto *functionTemplate =
                llvm::dyn_cast<clang::FunctionTemplateDecl>(&declaration))
            function = functionTemplate->getTemplatedDecl();
    if (function) {
        output << '(';
        auto parameters = function->parameters();
        for (std::size_t index = 0; index < parameters.size(); ++index) {
            if (const clang::ParmVarDecl *parameter = parameters[index])
                parameter->getType().print(output, policy);
            else
                output << "?null";
            if (index + 1 < parameters.size())
                output << ", ";
        }
        output << ')';
        if (const auto *method =
                llvm::dyn_cast<clang::CXXMethodDecl>(function)) {
            if (method->isConst())
                output << " const";
            if (method->isVolatile())
                output << " volatile";
            if (method->getRefQualifier() == clang::RQ_LValue)
                output << " &";
            else if (method->getRefQualifier() == clang::RQ_RValue)
                output << " &&";
        }
    }
    output.flush();
    return result;
}

llvm::Error State::attachNameShare(NodeId node,
                                   const clang::NamedDecl &declaration,
                                   SemanticMode mode) {
    (void)mode;
    const auto *key =
        llvm::cast<clang::NamedDecl>(declaration.getCanonicalDecl());
    auto found = nameClasses.find(key);
    ShareClassId share;
    if (found == nameClasses.end()) {
        auto created = unit->addShareClass(ShareClassKind::Name);
        if (!created)
            return created.takeError();
        share = *created;
        nameClasses.insert({key, share});
        nameRepresentatives.insert({key, node});
    } else {
        auto representative = nameRepresentatives.find(key);
        if (representative == nameRepresentatives.end())
            return llvm::createStringError(
                std::errc::invalid_argument,
                "name sharing class lost its representative");
        auto equal =
            IRSharing::semanticallyEqual(*unit, representative->second, node);
        if (!equal)
            return equal.takeError();
        if (*equal) {
            share = found->second;
        } else {
            auto created = unit->addShareClass(ShareClassKind::Name);
            if (!created)
                return created.takeError();
            share = *created;
        }
    }
    return unit->buildingArena().setShareClass(node, share);
}

llvm::Error State::attachTypeShare(NodeId node, clang::QualType type,
                                   SemanticMode mode) {
    if (type.isNull() || type.hasLocalQualifiers())
        return llvm::Error::success();
    auto built = unit->buildingArena().get(node);
    if (!built)
        return built.takeError();
    switch ((*built)->constructor) {
    case Constructor::TypeNamed:
    case Constructor::TypeEnum:
    case Constructor::TypePointer:
    case Constructor::TypeLvalueReference:
    case Constructor::TypeRvalueReference:
    case Constructor::TypeArray:
    case Constructor::TypeIncompleteArray:
    case Constructor::TypeFunction:
        break;
    default:
        return llvm::Error::success();
    }
    const auto key = std::make_pair(type.getCanonicalType().getTypePtr(),
                                    static_cast<unsigned>(mode));
    auto found = typeClasses.find(key);
    ShareClassId share;
    if (found == typeClasses.end()) {
        auto created = unit->addShareClass(ShareClassKind::Type);
        if (!created)
            return created.takeError();
        share = *created;
        typeClasses.insert({key, share});
        typeRepresentatives.insert({key, node});
    } else {
        auto representative = typeRepresentatives.find(key);
        if (representative == typeRepresentatives.end())
            return llvm::createStringError(
                std::errc::invalid_argument,
                "type sharing class lost its representative");
        auto equal =
            IRSharing::semanticallyEqual(*unit, representative->second, node);
        if (!equal)
            return equal.takeError();
        if (*equal) {
            share = found->second;
        } else {
            auto created = unit->addShareClass(ShareClassKind::Type);
            if (!created)
                return created.takeError();
            share = *created;
        }
    }
    return unit->buildingArena().setShareClass(node, share);
}

llvm::Expected<factory::OriginList>
State::declarationOrigins(const clang::Decl &declaration) {
    const source::OriginKind kind = declaration.isImplicit()
                                        ? source::OriginKind::Implicit
                                        : source::OriginKind::Explicit;
    auto origin = sources.declarationNode(declaration, std::nullopt, kind);
    if (!origin)
        return origin.takeError();
    return factory::OriginList{*origin};
}

llvm::Expected<source::OriginId>
State::transformedDeclarationOrigin(const clang::Decl &declaration,
                                    source::OriginId derivedFrom) {
    return sources.transformedNode(
        clang::CharSourceRange::getTokenRange(declaration.getSourceRange()),
        {derivedFrom});
}

llvm::Expected<factory::OriginList>
State::inheritedTypeOrigins(clang::QualType type,
                            const factory::OriginList &parentOrigins) {
    if (parentOrigins.empty())
        return sources.semanticQualTypeOrigins(
            type, source::SemanticTypeOriginPolicy::Empty, std::nullopt);
    return sources.semanticQualTypeOrigins(
        type, source::SemanticTypeOriginPolicy::Inherited,
        parentOrigins.front());
}

llvm::Expected<BuildArtifact> State::finish(BuildArtifact artifact) {
    const Arena &arena = unit->buildingArena();
    if (auto failure = IRValidator::validateSelected(arena, artifact.names,
                                                     Category::Name, "name"))
        return std::move(failure);
    if (auto failure = IRValidator::validateSelected(arena, artifact.types,
                                                     Category::Type, "type"))
        return std::move(failure);
    if (auto failure = IRValidator::validateSelected(
            arena, artifact.expressions, Category::Expression, "expression"))
        return std::move(failure);
    if (auto failure = IRValidator::validateSelected(
            arena, artifact.templateParameters, Category::TemplateParameter,
            "template parameter"))
        return std::move(failure);
    std::vector<NodeId> entryParameters;
    std::vector<NodeId> entryDefaults;
    for (const TemplateParameterEntry &entry :
         artifact.templateParameterEntries) {
        entryParameters.push_back(entry.parameter);
        if (entry.defaultArgument)
            entryDefaults.push_back(*entry.defaultArgument);
    }
    if (auto failure = IRValidator::validateSelected(
            arena, entryParameters, Category::TemplateParameter,
            "template parameter entry"))
        return std::move(failure);
    if (auto failure = IRValidator::validateSelected(
            arena, entryDefaults, Category::TemplateArgument,
            "template parameter default"))
        return std::move(failure);
    if (auto failure = IRValidator::validateSelected(
            arena, artifact.templateArguments, Category::TemplateArgument,
            "template argument"))
        return std::move(failure);
    if (auto failure = IRValidator::validateSelected(
            arena, artifact.objectValues, Category::ObjectValue,
            "object value"))
        return std::move(failure);
    if (auto failure = IRValidator::validateSelected(
            arena, artifact.globalDeclarations, Category::GlobalDeclaration,
            "global declaration"))
        return std::move(failure);

    auto tables = std::move(sources).finish();
    if (!tables)
        return tables.takeError();
    if (auto failure = unit->setSources(std::move(*tables)))
        return std::move(failure);
    if (auto failure = unit->finish())
        return std::move(failure);
    artifact.unit = std::move(unit);
    return artifact;
}

llvm::Error migrationIncomplete(const clang::Decl &declaration,
                                llvm::StringRef branch) {
    return error("migration incomplete: " + branch.str() + " name branch (" +
                 declaration.getDeclKindName() + ")");
}

llvm::Expected<const clang::DeclContext *>
nonIgnorableContext(const clang::Decl &declaration) {
    const clang::DeclContext *context = declaration.getDeclContext();
    while (context) {
        auto kind = classify(*context);
        if (!kind)
            return kind.takeError();
        if (*kind != ContextKind::Ignorable)
            return context;
        context = context->getParent();
    }
    return error(
        "migration incomplete: declaration outside a translation unit");
}

bool isSemanticallyNamed(const clang::Decl &declaration) {
    if (const auto *space = llvm::dyn_cast<clang::NamespaceDecl>(&declaration))
        return !space->isAnonymousNamespace();
    if (const auto *record = llvm::dyn_cast<clang::RecordDecl>(&declaration))
        if (record->isAnonymousStructOrUnion())
            return false;
    if (const auto *cxx = llvm::dyn_cast<clang::CXXRecordDecl>(&declaration))
        if (cxx->isLambda())
            return false;
    if (const auto *named = llvm::dyn_cast<clang::NamedDecl>(&declaration))
        return named->getIdentifier() != nullptr;
    return false;
}

llvm::Expected<unsigned> anonymousIndex(const clang::DeclContext &context,
                                        const clang::Decl &declaration) {
    unsigned count = 0;
    auto found = anonymousBefore(context, declaration, count);
    if (!found)
        return found.takeError();
    if (!*found)
        return error("migration incomplete: anonymous declaration absent from "
                     "its context");
    return count;
}

} // namespace builder
} // namespace ir
