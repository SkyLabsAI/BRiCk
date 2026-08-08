/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "ClangSourceInfo.hpp"
#include "IR.hpp"
#include "LocationEmitter.hpp"

#include <algorithm>
#include <fstream>
#include <iostream>
#include <optional>
#include <sstream>
#include <string>
#include <vector>

#include <clang/AST/ASTContext.h>
#include <clang/AST/Decl.h>
#include <clang/AST/DeclCXX.h>
#include <clang/AST/DeclTemplate.h>
#include <clang/AST/Expr.h>
#include <clang/AST/RecursiveASTVisitor.h>
#include <clang/Frontend/ASTUnit.h>
#include <clang/Lex/Lexer.h>
#include <clang/Tooling/Tooling.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/MemoryBuffer.h>

namespace {

class Finder : public clang::RecursiveASTVisitor<Finder> {
public:
    bool shouldVisitTemplateInstantiations() const { return true; }

    bool VisitVarDecl(clang::VarDecl *declaration) {
        if (declaration->getIdentifier())
            variables.emplace_back(declaration->getName().str(), declaration);
        return true;
    }

    bool VisitFunctionDecl(clang::FunctionDecl *declaration) {
        if (declaration->getName() == "id" &&
            declaration->getTemplateSpecializationInfo())
            instantiatedFunction = declaration;
        return true;
    }

    bool VisitIntegerLiteral(clang::IntegerLiteral *literal) {
        literals.push_back(literal);
        return true;
    }

    bool VisitCXXRecordDecl(clang::CXXRecordDecl *declaration) {
        if (declaration->getName() == "Nested" &&
            declaration->getMemberSpecializationInfo() &&
            declaration->getMemberSpecializationInfo()
                ->getPointOfInstantiation()
                .isValid())
            instantiatedMemberRecord = declaration;
        return true;
    }

    bool VisitEnumDecl(clang::EnumDecl *declaration) {
        if (declaration->getName() == "MemberEnum" &&
            declaration->getMemberSpecializationInfo() &&
            declaration->getMemberSpecializationInfo()
                ->getPointOfInstantiation()
                .isValid())
            instantiatedMemberEnum = declaration;
        return true;
    }

    clang::VarDecl *variable(const std::string &name) const {
        for (const auto &entry : variables)
            if (entry.first == name)
                return entry.second;
        return nullptr;
    }

    clang::IntegerLiteral *integer(std::uint64_t value) const {
        for (auto *literal : literals)
            if (literal->getValue().getLimitedValue() == value)
                return literal;
        return nullptr;
    }

    std::vector<std::pair<std::string, clang::VarDecl *>> variables;
    std::vector<clang::IntegerLiteral *> literals;
    clang::FunctionDecl *instantiatedFunction = nullptr;
    clang::CXXRecordDecl *instantiatedMemberRecord = nullptr;
    clang::EnumDecl *instantiatedMemberEnum = nullptr;
};

struct Check {
    bool ok = true;

    void require(bool condition, const std::string &message) {
        if (!condition) {
            ok = false;
            std::cerr << "source-info probe: " << message << '\n';
        }
    }

    template <typename T>
    std::optional<T> take(llvm::Expected<T> value, const std::string &where) {
        if (value)
            return std::move(*value);
        ok = false;
        std::cerr << "source-info probe: " << where << ": "
                  << llvm::toString(value.takeError()) << '\n';
        return std::nullopt;
    }
};

llvm::Expected<std::string> renderRocqValues(const source::Tables &tables) {
    ir::TranslationUnitIR unit;
    if (auto failure = unit.setSources(tables))
        return std::move(failure);
    if (auto failure = unit.finish())
        return std::move(failure);
    auto body = ir::LocationRocqEmitter().emit(unit);
    if (!body)
        return body.takeError();
    return std::move(*body);
}

bool writeRocqValues(const std::string &path, const std::string &contents) {
    std::ofstream output(path);
    output << contents;
    return output.good();
}

using FrameFact = std::pair<std::string, source::MacroOriginKind>;

std::vector<FrameFact> frameFacts(const source::Origin &origin) {
    std::vector<FrameFact> result;
    for (const auto &frame : origin.macroStack)
        result.emplace_back(frame.name.value_or(""), frame.kind);
    return result;
}

bool contains(const std::string &text, const std::string &needle) {
    return text.find(needle) != std::string::npos;
}

} // namespace

int main(int argc, char **argv) {
    if (argc < 2) {
        std::cerr << "usage: cpp2v-source-info-probe SOURCE "
                     "[--rocq-output FILE] [-- CLANG-ARGS...]\n";
        return 2;
    }
    std::string input = argv[1];
    std::string rocqOutput;
    std::vector<std::string> clangArgs{"-std=c++17"};
    bool afterDash = false;
    for (int i = 2; i < argc; ++i) {
        std::string argument = argv[i];
        if (afterDash) {
            clangArgs.push_back(argument);
        } else if (argument == "--") {
            afterDash = true;
        } else if (argument == "--rocq-output" && i + 1 < argc) {
            rocqOutput = argv[++i];
        } else {
            std::cerr << "unknown probe argument: " << argument << '\n';
            return 2;
        }
    }

    auto buffer = llvm::MemoryBuffer::getFile(input);
    if (!buffer) {
        std::cerr << "cannot read " << input << '\n';
        return 2;
    }
    auto ast = clang::tooling::buildASTFromCodeWithArgs(
        (*buffer)->getBuffer().str(), clangArgs, input);
    if (!ast) {
        std::cerr << "source-info probe: Clang failed to build the fixture\n";
        return 1;
    }

    Finder finder;
    finder.TraverseDecl(ast->getASTContext().getTranslationUnitDecl());
    Check check;
    auto *lineMapped = finder.variable("line_mapped");
    auto *nested = finder.variable("nested_macro");
    auto *header = finder.variable("header_value");
    auto *userHeader = finder.variable("user_header_value");
    auto *system = finder.variable("system_value");
    auto *typed = finder.variable("typed_value");
    auto *instantiated = finder.variable("instantiated");
    auto *nestedLiteral = finder.integer(3);
    auto *headerLiteral = finder.integer(4);
    auto *headerBodyLiteral = finder.integer(2);
    auto *bodyLiteral = finder.integer(31);
    auto *leftLiteral = finder.integer(10);
    auto *rightLiteral = finder.integer(20);
    check.require(lineMapped && nested && header && userHeader && system &&
                      typed && instantiated && nestedLiteral && headerLiteral &&
                      headerBodyLiteral && bodyLiteral && leftLiteral &&
                      rightLiteral,
                  "fixture declarations and specific literals were not all "
                  "found");
    if (!check.ok)
        return 1;

    auto &manager = ast->getSourceManager();
    source::ClangTableBuilder builder(manager, ast->getLangOpts());

    auto valid =
        check.take(builder.physicalPoint(lineMapped->getLocation(),
                                         source::LocationProjection::Spelling),
                   "valid physical point");
    auto invalid =
        check.take(builder.physicalPoint(clang::SourceLocation(),
                                         source::LocationProjection::Spelling),
                   "invalid physical point");
    check.require(valid && *valid && invalid && !*invalid,
                  "valid/invalid point projection");

    auto userPoint =
        check.take(builder.physicalPoint(userHeader->getLocation(),
                                         source::LocationProjection::Spelling),
                   "user-header point");
    auto systemPoint =
        check.take(builder.physicalPoint(system->getLocation(),
                                         source::LocationProjection::Spelling),
                   "system-header point");
    check.require(userPoint && *userPoint && systemPoint && *systemPoint,
                  "included physical points");
    auto includeOffset = [&](clang::SourceLocation location) {
        clang::FileID file =
            manager.getFileID(manager.getSpellingLoc(location));
        clang::SourceLocation include =
            manager.getSpellingLoc(manager.getIncludeLoc(file));
        return static_cast<std::uint64_t>(
            manager.getDecomposedLoc(include).second);
    };
    std::uint64_t userIncludeOffset = includeOffset(userHeader->getLocation());
    std::uint64_t systemIncludeOffset = includeOffset(system->getLocation());

    auto duplicateA = llvm::MemoryBuffer::getMemBufferCopy(
        "first distinct contents\n", "same-name-buffer.hpp");
    auto duplicateB = llvm::MemoryBuffer::getMemBufferCopy(
        "second distinct contents\n", "same-name-buffer.hpp");
    clang::FileID duplicateFileA = manager.createFileID(std::move(duplicateA));
    clang::FileID duplicateFileB = manager.createFileID(std::move(duplicateB));
    auto duplicatePointA = check.take(
        builder.physicalPoint(manager.getLocForStartOfFile(duplicateFileA),
                              source::LocationProjection::Spelling),
        "first same-named buffer");
    auto duplicatePointB = check.take(
        builder.physicalPoint(manager.getLocForStartOfFile(duplicateFileB),
                              source::LocationProjection::Spelling),
        "second same-named buffer");
    check.require(duplicatePointA && *duplicatePointA && duplicatePointB &&
                      *duplicatePointB &&
                      (*duplicatePointA)->file != (*duplicatePointB)->file,
                  "distinct same-named buffers have distinct FileIds");

    clang::SourceRange mappedSource = lineMapped->getSourceRange();
    auto token = check.take(
        builder.range(clang::CharSourceRange::getTokenRange(mappedSource),
                      source::LocationProjection::Spelling),
        "token range");
    auto character = check.take(
        builder.range(clang::CharSourceRange::getCharRange(mappedSource),
                      source::LocationProjection::Spelling),
        "character range");
    check.require(token && character &&
                      token->endSemantics == source::RangeKind::Token &&
                      character->endSemantics == source::RangeKind::Character &&
                      token->normalizedHalfOpen &&
                      character->normalizedHalfOpen && token->end &&
                      token->normalizedHalfOpen->second.byteOffset >
                          token->end->byteOffset &&
                      character->normalizedHalfOpen->second.byteOffset ==
                          character->end->byteOffset,
                  "token/character half-open semantics");

    clang::SourceRange partialBegin(clang::SourceLocation(),
                                    lineMapped->getEndLoc());
    clang::SourceRange partialEnd(lineMapped->getBeginLoc(),
                                  clang::SourceLocation());
    auto missingBegin = check.take(
        builder.range(clang::CharSourceRange::getTokenRange(partialBegin),
                      source::LocationProjection::Spelling),
        "missing begin range");
    auto missingEnd = check.take(
        builder.range(clang::CharSourceRange::getTokenRange(partialEnd),
                      source::LocationProjection::Spelling),
        "missing end range");
    check.require(missingBegin && !missingBegin->begin && missingBegin->end &&
                      !missingBegin->normalizedHalfOpen && missingEnd &&
                      missingEnd->begin && !missingEnd->end &&
                      !missingEnd->normalizedHalfOpen,
                  "independently invalid endpoints");

    clang::SourceRange cross(lineMapped->getBeginLoc(), header->getEndLoc());
    auto crossRange =
        check.take(builder.range(clang::CharSourceRange::getTokenRange(cross),
                                 source::LocationProjection::Spelling),
                   "cross-file range");
    check.require(crossRange && crossRange->begin && crossRange->end &&
                      crossRange->begin->file != crossRange->end->file &&
                      !crossRange->normalizedHalfOpen,
                  "cross-file normalization failure");

    clang::CharSourceRange sameNamedCross =
        clang::CharSourceRange::getCharRange(
            manager.getLocForStartOfFile(duplicateFileA),
            manager.getLocForStartOfFile(duplicateFileB));
    auto sameNamedCrossRange = check.take(
        builder.range(sameNamedCross, source::LocationProjection::Spelling),
        "same-named distinct-buffer range");
    check.require(sameNamedCrossRange && sameNamedCrossRange->begin &&
                      sameNamedCrossRange->end &&
                      sameNamedCrossRange->begin->file !=
                          sameNamedCrossRange->end->file &&
                      !sameNamedCrossRange->normalizedHalfOpen,
                  "same-named distinct buffers remain cross-file");

    clang::CharSourceRange incompatibleMacros =
        clang::CharSourceRange::getCharRange(
            leftLiteral->getLocation().getLocWithOffset(1),
            rightLiteral->getLocation().getLocWithOffset(1));
    auto originalMacroConversion = clang::Lexer::makeFileCharRange(
        incompatibleMacros, manager, ast->getLangOpts());
    clang::CharSourceRange projectedIncompatibleMacros =
        clang::CharSourceRange::getCharRange(
            manager.getExpansionLoc(incompatibleMacros.getBegin()),
            manager.getExpansionLoc(incompatibleMacros.getEnd()));
    auto projectedMacroConversion = clang::Lexer::makeFileCharRange(
        projectedIncompatibleMacros, manager, ast->getLangOpts());
    auto incompatibleMacroRange =
        check.take(builder.range(incompatibleMacros,
                                 source::LocationProjection::Expansion),
                   "same-file incompatible macro range");
    check.require(originalMacroConversion.isInvalid() &&
                      projectedMacroConversion.isValid() &&
                      incompatibleMacroRange && incompatibleMacroRange->begin &&
                      incompatibleMacroRange->end &&
                      incompatibleMacroRange->begin->file ==
                          incompatibleMacroRange->end->file &&
                      incompatibleMacroRange->endSemantics ==
                          source::RangeKind::Character &&
                      !incompatibleMacroRange->normalizedHalfOpen,
                  "failed original incompatible macro conversion blocks a "
                  "successful projected same-file conversion");

    auto invalidOrigin = check.take(builder.explicitNode(clang::SourceRange()),
                                    "invalid explicit origin");
    auto mappedOrigin =
        check.take(builder.explicitNode(mappedSource), "mapped origin");
    auto mappedAgain =
        check.take(builder.explicitNode(mappedSource), "mapped origin repeat");
    auto headerOrigin =
        check.take(builder.declarationNode(*header), "header declaration");
    auto systemOrigin =
        check.take(builder.declarationNode(*system), "system declaration");
    auto nestedOrigin =
        check.take(builder.declarationNode(*nested), "nested declaration");
    check.require(mappedOrigin && mappedAgain && headerOrigin && systemOrigin &&
                      nestedOrigin && *mappedOrigin == *mappedAgain,
                  "origin and file interning are stable first-seen");

    auto nestedLiteralOrigin =
        check.take(builder.explicitNode(nestedLiteral->getSourceRange()),
                   "nested argument literal");
    auto bodyLiteralOrigin =
        check.take(builder.explicitNode(bodyLiteral->getSourceRange()),
                   "nested body literal");
    auto headerLiteralOrigin =
        check.take(builder.explicitNode(headerLiteral->getSourceRange()),
                   "header argument literal");
    auto headerBodyLiteralOrigin =
        check.take(builder.explicitNode(headerBodyLiteral->getSourceRange()),
                   "header body literal");

    std::optional<source::OriginId> declarationPoi;
    if (finder.instantiatedFunction && instantiated->getInit())
        declarationPoi =
            check.take(builder.declarationNode(*finder.instantiatedFunction),
                       "declaration POI");
    auto memberRecordPoi =
        finder.instantiatedMemberRecord
            ? check.take(
                  builder.declarationNode(*finder.instantiatedMemberRecord),
                  "instantiated member-record POI")
            : std::nullopt;
    auto memberEnumPoi = finder.instantiatedMemberEnum
                             ? check.take(builder.declarationNode(
                                              *finder.instantiatedMemberEnum),
                                          "instantiated member-enum POI")
                             : std::nullopt;
    check.require(declarationPoi && memberRecordPoi && memberEnumPoi,
                  "function, member-record, and member-enum POIs were found");

    auto typeOrigin =
        check.take(builder.typeSourceInfoNode(typed->getTypeSourceInfo()),
                   "TypeSourceInfo written range");
    auto emptyType =
        check.take(builder.semanticQualTypeOrigins(
                       typed->getType(),
                       source::SemanticTypeOriginPolicy::Empty, std::nullopt),
                   "bare QualType empty policy");
    auto inheritedType =
        mappedOrigin
            ? check.take(builder.semanticQualTypeOrigins(
                             typed->getType(),
                             source::SemanticTypeOriginPolicy::Inherited,
                             *mappedOrigin),
                         "bare QualType inherited policy")
            : std::nullopt;
    check.require(typeOrigin && emptyType && emptyType->empty() &&
                      inheritedType && inheritedType->size() == 1,
                  "written and semantic type policies");

    auto implicit =
        check.take(builder.implicitNode(clang::CharSourceRange::getTokenRange(
                       nested->getSourceRange())),
                   "implicit origin");
    std::vector<source::OriginId> base =
        mappedOrigin ? std::vector<source::OriginId>{*mappedOrigin}
                     : std::vector<source::OriginId>{};
    auto anchoredImplicit =
        mappedOrigin ? check.take(builder.anchoredImplicitNode(
                                      clang::CharSourceRange::getTokenRange(
                                          nested->getSourceRange()),
                                      *mappedOrigin, base),
                                  "anchored implicit origin")
                     : std::nullopt;
    auto transformed = check.take(
        builder.transformedNode(
            clang::CharSourceRange::getTokenRange(nested->getSourceRange()),
            base),
        "transformed origin");
    auto synthesized =
        mappedOrigin ? check.take(builder.synthesizedNode(*mappedOrigin, base),
                                  "synthesized origin")
                     : std::nullopt;
    auto inherited =
        mappedOrigin ? check.take(builder.inheritedNode(*mappedOrigin, base),
                                  "inherited origin")
                     : std::nullopt;
    std::vector<source::OriginId> ordered;
    if (mappedOrigin) {
        source::appendOriginStable(ordered, *mappedOrigin);
        source::appendOriginStable(ordered, *mappedOrigin);
    }
    if (transformed)
        source::appendOriginStable(ordered, *transformed);
    check.require(implicit && anchoredImplicit && transformed && synthesized &&
                      inherited && ordered.size() == 2,
                  "origin factories, edges, and stable append/dedup");

    if (!check.ok)
        return 1;
    auto tablesValue = check.take(std::move(builder).finish(), "finish");
    if (!tablesValue || !check.ok)
        return 1;
    const source::Tables &tables = *tablesValue;

    auto originAt =
        [&](std::optional<source::OriginId> id) -> const source::Origin * {
        return id && id->value() < tables.origins.size()
                   ? &tables.origins[id->value()]
                   : nullptr;
    };
    const auto *invalidValue = originAt(invalidOrigin);
    const auto *mappedValue = originAt(mappedOrigin);
    const auto *poiValue = originAt(declarationPoi);
    const auto *memberRecordValue = originAt(memberRecordPoi);
    const auto *memberEnumValue = originAt(memberEnumPoi);
    const auto *typeValue = originAt(typeOrigin);
    const auto *nestedValue = originAt(nestedOrigin);
    check.require(
        invalidValue && !invalidValue->spelling && !invalidValue->expansion &&
            !invalidValue->presumedBegin && !invalidValue->presumedEnd,
        "invalid origin remains honestly absent");
    check.require(mappedValue && mappedValue->spelling &&
                      mappedValue->presumedBegin &&
                      mappedValue->spelling->begin &&
                      mappedValue->presumedBegin->line == 700 &&
                      mappedValue->presumedBegin->file == "logical.cpp" &&
                      mappedValue->spelling->begin->line != 700,
                  "#line presumed point differs from physical point");
    check.require(poiValue && poiValue->pointOfInstantiation &&
                      poiValue->spelling && poiValue->spelling->begin &&
                      poiValue->pointOfInstantiation->byteOffset !=
                          poiValue->spelling->begin->byteOffset &&
                      memberRecordValue &&
                      memberRecordValue->pointOfInstantiation &&
                      memberEnumValue && memberEnumValue->pointOfInstantiation,
                  "function/member record/member enum POIs are separate from "
                  "spelling");
    check.require(typeValue && typeValue->spelling &&
                      typeValue->spelling->begin && typeValue->spelling->end,
                  "TypeSourceInfo origin preserves its written range");
    check.require(nestedValue && nestedValue->spelling &&
                      nestedValue->spelling->begin &&
                      nestedValue->spelling->end &&
                      !nestedValue->spelling->normalizedHalfOpen &&
                      (nestedValue->spelling->begin->file !=
                           nestedValue->spelling->end->file ||
                       nestedValue->spelling->begin->byteOffset >
                           nestedValue->spelling->end->byteOffset),
                  "non-contiguous macro endpoints remain honest");

    auto mainFile = (**valid).file;
    auto userFile = (**userPoint).file;
    auto systemFile = (**systemPoint).file;
    auto duplicateIdA = (**duplicatePointA).file;
    auto duplicateIdB = (**duplicatePointB).file;
    check.require(mainFile < userFile && userFile < systemFile &&
                      systemFile < duplicateIdA && duplicateIdA < duplicateIdB,
                  "file IDs follow exact stable first-seen order");
    check.require(
        tables.files[mainFile.value()].isMain &&
            tables.files[userFile.value()].kind == source::FileKind::User &&
            tables.files[systemFile.value()].kind == source::FileKind::System &&
            tables.files[userFile.value()].includeParent ==
                std::make_optional(
                    std::make_pair(mainFile, userIncludeOffset)) &&
            tables.files[systemFile.value()].includeParent ==
                std::make_optional(
                    std::make_pair(mainFile, systemIncludeOffset)),
        "exact include-parent IDs, offsets, and classifications");
    check.require(duplicateIdA != duplicateIdB &&
                      tables.files[duplicateIdA.value()] ==
                          tables.files[duplicateIdB.value()],
                  "equal serialized files preserve distinct live identities");

    const auto *nestedLiteralValue = originAt(nestedLiteralOrigin);
    const auto *bodyLiteralValue = originAt(bodyLiteralOrigin);
    const auto *headerLiteralValue = originAt(headerLiteralOrigin);
    const auto *headerBodyLiteralValue = originAt(headerBodyLiteralOrigin);
    auto allFrameRanges = [](const source::Origin *origin) {
        return origin &&
               std::all_of(origin->macroStack.begin(), origin->macroStack.end(),
                           [](const auto &frame) {
                               return frame.spelling && frame.expansion;
                           });
    };
    check.require(
        nestedLiteralValue && bodyLiteralValue && headerLiteralValue &&
            headerBodyLiteralValue &&
            frameFacts(*nestedLiteralValue) ==
                std::vector<FrameFact>{
                    {"INNER_MACRO", source::MacroOriginKind::Argument},
                    {"OUTER_MACRO", source::MacroOriginKind::Argument},
                    {"PASS_MACRO", source::MacroOriginKind::Argument}} &&
            frameFacts(*bodyLiteralValue) ==
                std::vector<FrameFact>{
                    {"BODY_INNER_MACRO", source::MacroOriginKind::Body},
                    {"BODY_OUTER_MACRO", source::MacroOriginKind::Body}} &&
            frameFacts(*headerLiteralValue) ==
                std::vector<FrameFact>{
                    {"HEADER_MACRO", source::MacroOriginKind::Argument},
                    {"PASS_MACRO", source::MacroOriginKind::Argument}} &&
            frameFacts(*headerBodyLiteralValue) ==
                std::vector<FrameFact>{
                    {"HEADER_MACRO", source::MacroOriginKind::Body}} &&
            allFrameRanges(nestedLiteralValue) &&
            allFrameRanges(bodyLiteralValue) &&
            allFrameRanges(headerLiteralValue) &&
            allFrameRanges(headerBodyLiteralValue),
        "exact nearest-first nested argument/body and header macro stacks");

    const auto *anchoredImplicitValue = originAt(anchoredImplicit);
    const auto *transformedValue = originAt(transformed);
    const auto *syntheticValue = originAt(synthesized);
    const auto *inheritedValue = originAt(inherited);
    check.require(
        mappedOrigin && anchoredImplicitValue &&
            anchoredImplicitValue->kind == source::OriginKind::Implicit &&
            anchoredImplicitValue->anchor == mappedOrigin &&
            anchoredImplicitValue->derivedFrom ==
                std::vector<source::OriginId>{*mappedOrigin} &&
            transformedValue &&
            transformedValue->derivedFrom ==
                std::vector<source::OriginId>{*mappedOrigin} &&
            syntheticValue && syntheticValue->anchor == mappedOrigin &&
            syntheticValue->derivedFrom ==
                std::vector<source::OriginId>{*mappedOrigin} &&
            inheritedValue && inheritedValue->anchor == mappedOrigin &&
            inheritedValue->derivedFrom ==
                std::vector<source::OriginId>{*mappedOrigin},
        "exact transformed/synthetic/inherited provenance edges");

    auto rocqFirst = check.take(renderRocqValues(tables), "render Rocq values");
    auto rocqSecond =
        check.take(renderRocqValues(tables), "repeat Rocq rendering");
    check.require(
        rocqFirst && rocqSecond && *rocqFirst == *rocqSecond &&
            contains(*rocqFirst, "presumed_file := \"logical.cpp\"") &&
            contains(*rocqFirst, "macro_name := (Some \"PASS_MACRO\")") &&
            contains(*rocqFirst, "anchor_origin := (Some") &&
            contains(*rocqFirst, "derived_from := (") &&
            contains(*rocqFirst, "spelling_range := (Some") &&
            contains(*rocqFirst, "expansion_range := (Some"),
        "faithful deterministic production source serialization");
    if (!rocqOutput.empty())
        check.require(rocqFirst && writeRocqValues(rocqOutput, *rocqFirst),
                      "write Rocq source tables");
    if (!check.ok)
        return 1;

    std::cout << "points: valid and invalid projections\n"
                 "ranges: token character partial cross-file and incompatible "
                 "same-file macro normalization\n"
                 "files: exact first-seen include ancestry and distinct "
                 "same-named buffers\n"
                 "line-directive: physical differs from logical.cpp:700\n"
                 "macros: exact nearest-first nested argument body and header "
                 "frames\n"
                 "declarations: function member-record member-enum POIs "
                 "separated\n"
                 "origins: exact explicit implicit transformed synthesized and "
                 "inherited edges\n"
                 "types: TypeSourceInfo written; QualType policy explicit\n";
    if (!rocqOutput.empty())
        std::cout << "rocq-values: all source files and origins faithfully "
                     "emitted\n";
    return 0;
}
