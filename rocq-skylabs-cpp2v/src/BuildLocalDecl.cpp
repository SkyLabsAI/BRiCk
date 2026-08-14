/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "IRBuilderInternal.hpp"

#include <clang/AST/DeclCXX.h>
#include <clang/AST/DeclTemplate.h>

namespace ir {
namespace builder {
namespace {

BuildNodeGroup zeroNodes() { return {BuildCardinality::Zero, {}}; }

BuildNodeGroup oneNode(NodeId node) { return {BuildCardinality::One, {node}}; }

llvm::Expected<NodeId>
buildDeclarationType(State &state, const clang::VarDecl &declaration,
                     SemanticMode mode, const factory::OriginList &origins) {
    if (!declaration.isImplicit())
        if (const clang::TypeSourceInfo *written =
                declaration.getTypeSourceInfo()) {
            if (!written->getType()->getContainedAutoType() &&
                state.context.hasSameType(written->getType(),
                                          declaration.getType()))
                return state.buildWrittenType(*written, mode);
            auto origin = state.sources.typeSourceInfoNode(written);
            if (!origin)
                return origin.takeError();
            return state.buildType(declaration.getType(), mode, {*origin});
        }
    auto inherited = state.inheritedTypeOrigins(declaration.getType(), origins);
    if (!inherited)
        return inherited.takeError();
    return state.buildType(declaration.getType(), mode, std::move(*inherited));
}

llvm::Expected<NodeId> buildBindingType(State &state, clang::QualType type,
                                        SemanticMode mode,
                                        const factory::OriginList &origins) {
    auto inherited = state.inheritedTypeOrigins(type, origins);
    if (!inherited)
        return inherited.takeError();
    return state.buildType(type, mode, std::move(*inherited));
}

} // namespace

llvm::Expected<BuildNodeGroup>
State::buildLocalDeclaration(const clang::Decl &declaration,
                             SemanticMode mode) {
    if (declaration.isInvalidDecl())
        return migrationIncomplete(declaration,
                                   "invalid local declaration (Derror)");

    if (const auto *variable = llvm::dyn_cast<clang::VarDecl>(&declaration)) {
        // DecompositionDecl is a VarDecl subclass and has distinct final IR.
        if (!llvm::isa<clang::DecompositionDecl>(variable)) {
            if (variable->hasExternalStorage())
                return zeroNodes();
            auto origins = declarationOrigins(declaration);
            if (!origins)
                return origins.takeError();
            auto type = buildDeclarationType(*this, *variable, mode, *origins);
            if (!type)
                return type.takeError();
            std::optional<NodeId> initializer;
            if (const clang::Expr *value = variable->getInit()) {
                auto built = buildExpression(*value, mode);
                if (!built)
                    return built.takeError();
                initializer = *built;
                if (mode == SemanticMode::Template &&
                    !variable->isStaticLocal()) {
                    auto generated =
                        sources.synthesizedNode(origins->front(), *origins);
                    if (!generated)
                        return generated.takeError();
                    auto initialized = applyInitializingType(
                        *initializer, variable->getType(), mode, *generated);
                    if (!initialized)
                        return initialized.takeError();
                    initializer = *initialized;
                }
            }
            if (variable->isStaticLocal()) {
                auto name = buildName(*variable, mode);
                if (!name)
                    return name.takeError();
                auto result = factory::makeStaticVariableDeclaration(
                    unit->buildingArena(), std::move(*origins),
                    context.getLangOpts().ThreadsafeStatics, *name, *type,
                    initializer);
                if (!result)
                    return result.takeError();
                return oneNode(*result);
            }
            auto result = factory::makeVariableDeclaration(
                unit->buildingArena(), std::move(*origins),
                variable->getNameAsString(), *type, initializer);
            if (!result)
                return result.takeError();
            return oneNode(*result);
        }
    }

    if (const auto *decomposition =
            llvm::dyn_cast<clang::DecompositionDecl>(&declaration)) {
        auto origins = declarationOrigins(declaration);
        if (!origins)
            return origins.takeError();
        if (!decomposition->getInit())
            return migrationIncomplete(declaration,
                                       "decomposition without initializer");
        auto initializer = buildExpression(*decomposition->getInit(), mode);
        if (!initializer)
            return initializer.takeError();

        const std::uint64_t anonymousIndex = activeAnonymousLocals.size();
        activeAnonymousLocals.push_back(decomposition);
        anonymousLocals[decomposition] = anonymousIndex;
        auto popAnonymous = [&] {
            anonymousLocals.erase(decomposition);
            activeAnonymousLocals.pop_back();
        };

        std::vector<NodeId> bindings;
        bindings.reserve(decomposition->bindings().size());
        for (const clang::BindingDecl *binding : decomposition->bindings()) {
            if (!binding) {
                popAnonymous();
                return migrationIncomplete(declaration,
                                           "null decomposition binding");
            }
            auto bindingOrigins = declarationOrigins(*binding);
            if (!bindingOrigins) {
                popAnonymous();
                return bindingOrigins.takeError();
            }
            Constructor constructor;
            std::string name;
            clang::QualType bindingType;
            const clang::Expr *bindingInitializer = nullptr;
            if (const clang::VarDecl *holding = binding->getHoldingVar()) {
                constructor = Constructor::BindingVariable;
                name = holding->getNameAsString();
                bindingType = holding->getType();
                bindingInitializer = holding->getInit();
            } else {
                constructor = Constructor::BindingReference;
                name = binding->getNameAsString();
                bindingType = binding->getType();
                bindingInitializer = binding->getBinding();
            }
            if (bindingType.isNull()) {
                popAnonymous();
                return migrationIncomplete(declaration, "binding without type");
            }
            auto type =
                buildBindingType(*this, bindingType, mode, *bindingOrigins);
            if (!type) {
                popAnonymous();
                return type.takeError();
            }
            llvm::Expected<NodeId> value = [&]() -> llvm::Expected<NodeId> {
                if (bindingInitializer)
                    return buildExpression(*bindingInitializer, mode);

                // Clang deliberately leaves BindingDecl::getBinding() null
                // until a type-dependent decomposition is instantiated. BRiCk
                // requires an initializer, so retain the binding and make this
                // deferred semantic boundary explicit rather than inventing an
                // executable reference or dropping the declaration.
                if (constructor != Constructor::BindingReference ||
                    !decomposition->getInit()->isTypeDependent() ||
                    !bindingType->isDependentType())
                    return migrationIncomplete(declaration,
                                               "binding without initializer");
                auto generated = sources.synthesizedNode(
                    bindingOrigins->front(), *bindingOrigins);
                if (!generated)
                    return generated.takeError();
                auto unsupportedType =
                    buildBindingType(*this, bindingType, mode, {*generated});
                if (!unsupportedType)
                    return unsupportedType.takeError();
                return factory::makeUnsupportedExpression(
                    unit->buildingArena(), {*generated}, "BindingDecl",
                    *unsupportedType);
            }();
            if (!value) {
                popAnonymous();
                return value.takeError();
            }
            auto built = factory::makeBindingDeclaration(
                unit->buildingArena(), constructor, std::move(*bindingOrigins),
                std::move(name), *type, *value);
            if (!built) {
                popAnonymous();
                return built.takeError();
            }
            bindings.push_back(*built);
        }
        popAnonymous();
        auto result = factory::makeVariableDecomposition(
            unit->buildingArena(), std::move(*origins), *initializer,
            anonymousIndex, std::move(bindings));
        if (!result)
            return result.takeError();
        return oneNode(*result);
    }

    if (llvm::isa<clang::TypeDecl, clang::StaticAssertDecl>(&declaration))
        return zeroNodes();

    // Match legacy filtering of unexpected local declaration kinds. They do
    // not create semantic list elements or location children.
    return zeroNodes();
}

} // namespace builder
} // namespace ir
