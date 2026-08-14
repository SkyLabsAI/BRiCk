/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once
#include "Trace.hpp"
#include <clang/AST/Decl.h>
#include <clang/AST/DeclCXX.h>
#include <list>
#include <map>
#include <set>
#include <string>
#include <tuple>
#include <utility>

namespace clang {
class CompilerInstance;
};

class Module {
public:
    struct Flags {
        bool in_template;
        bool in_specialization; // explicit specialization or implicit
                                // instantiation

        Flags set_template() const { return Flags{true, in_specialization}; }
        Flags set_specialization() const { return Flags{in_template, true}; }

        bool none() const { return !in_template && !in_specialization; }
    };

    void add_definition(const clang::NamedDecl &, Flags);
    void add_declaration(const clang::NamedDecl &, Flags);
    void add_assert(const clang::StaticAssertDecl &);

    using AssertList = std::list<const clang::StaticAssertDecl *>;
    using DeclList = std::list<const clang::NamedDecl *>;
    using AliasEntry =
        std::pair<const clang::NamedDecl *, const clang::NamedDecl *>;
    using AliasSet = std::set<AliasEntry>;

    const AssertList &asserts() const { return asserts_; }

    const DeclList &declarations() const { return declarations_; }

    const DeclList &definitions() const { return definitions_; }

    const DeclList &template_declarations() const {
        return template_declarations_;
    }

    const DeclList &template_definitions() const {
        return template_definitions_;
    }

    const AliasSet &aliases() const { return ns_aliases_; }
    std::list<AliasEntry> ordered_aliases() const {
        std::set<std::tuple<std::string, std::string, AliasEntry>> sorted;
        auto qualifiedName = [](const clang::NamedDecl *declaration) {
            return declaration ? declaration->getQualifiedNameAsString()
                               : std::string{};
        };
        for (const AliasEntry &alias : ns_aliases_)
            sorted.emplace(qualifiedName(alias.first),
                           qualifiedName(alias.second), alias);
        std::list<AliasEntry> result;
        for (const auto &entry : sorted)
            result.push_front(std::get<2>(entry));
        return result;
    }
    const clang::Decl *alias_origin(const AliasEntry &alias) const {
        const auto found = alias_origins_.find(alias);
        return found == alias_origins_.end() ? nullptr : found->second;
    }

    Module() = delete;
    Module(Trace::Mask trace) : trace_(trace & Trace::ModuleBuilder) {}

    void add_inline_namespace(const clang::NamespaceDecl *ns) {
        add_alias(llvm::dyn_cast<clang::NamedDecl>(ns->getParent()), ns, ns);
    }
    void add_namespace_alias(const clang::NamespaceAliasDecl *ns) {
        add_alias(ns->getNamespace(), ns->getAliasedNamespace(), ns);
    }

private:
    const bool trace_;

    DeclList declarations_;
    DeclList definitions_;

    DeclList template_declarations_;
    DeclList template_definitions_;

    AliasSet ns_aliases_;
    std::map<AliasEntry, const clang::Decl *> alias_origins_;

    void add_alias(const clang::NamedDecl *from, const clang::NamedDecl *to,
                   const clang::Decl *owner) {
        const AliasEntry alias{from, to};
        ns_aliases_.insert(alias);
        alias_origins_.emplace(alias, owner);
    }

    AssertList asserts_;

    void add_decl(llvm::StringRef, DeclList &, DeclList &,
                  const clang::NamedDecl &, Flags);
};

class Filter;
class SpecCollector;

void build_module(clang::TranslationUnitDecl *tu, ::Module &mod, Filter &filter,
                  SpecCollector &specs, clang::CompilerInstance *,
                  bool elaborate, bool templates);
