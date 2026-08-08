/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "ClangSourceInfo.hpp"

#include <algorithm>
#include <system_error>
#include <utility>

#include <clang/AST/Decl.h>
#include <clang/AST/DeclBase.h>
#include <clang/AST/DeclCXX.h>
#include <clang/AST/DeclTemplate.h>
#include <clang/AST/Type.h>
#include <clang/AST/TypeLoc.h>
#include <clang/Basic/FileEntry.h>
#include <clang/Basic/LangOptions.h>
#include <clang/Basic/SourceManager.h>
#include <clang/Lex/Lexer.h>
#include <llvm/ADT/StringRef.h>

namespace source {
namespace {

llvm::Error error(const std::string &message) {
    return llvm::createStringError(std::errc::invalid_argument, "%s",
                                   message.c_str());
}

clang::SourceLocation project(const clang::SourceManager &manager,
                              clang::SourceLocation location,
                              LocationProjection projection) {
    if (location.isInvalid())
        return {};
    return projection == LocationProjection::Spelling
               ? manager.getSpellingLoc(location)
               : manager.getExpansionLoc(location);
}

FileKind classify(const clang::SourceManager &manager,
                  clang::SourceLocation location, llvm::StringRef name) {
    if (name == "<built-in>")
        return FileKind::Builtin;
    if (name == "<command line>")
        return FileKind::CommandLine;
    if (name == "<scratch space>")
        return FileKind::Scratch;
    if (name == "<predefines>" || name == "<predefined>")
        return FileKind::Predefined;

    switch (manager.getFileCharacteristic(location)) {
    case clang::SrcMgr::C_User:
        return FileKind::User;
    case clang::SrcMgr::C_System:
        return FileKind::System;
    case clang::SrcMgr::C_ExternCSystem:
        return FileKind::ExternCSystem;
    case clang::SrcMgr::C_User_ModuleMap:
        return FileKind::UserModuleMap;
    case clang::SrcMgr::C_System_ModuleMap:
        return FileKind::SystemModuleMap;
    }
    return FileKind::Other;
}

clang::CharSourceRange tokenRange(clang::SourceRange range) {
    return clang::CharSourceRange::getTokenRange(range);
}

std::optional<clang::SourceLocation>
pointOfInstantiation(const clang::Decl &declaration) {
    clang::SourceLocation location;
    if (const auto *function =
            llvm::dyn_cast<clang::FunctionDecl>(&declaration))
        location = function->getPointOfInstantiation();
    else if (const auto *variable =
                 llvm::dyn_cast<clang::VarDecl>(&declaration))
        location = variable->getPointOfInstantiation();
    else if (const auto *specialization =
                 llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(
                     &declaration))
        location = specialization->getPointOfInstantiation();
    else if (const auto *record =
                 llvm::dyn_cast<clang::CXXRecordDecl>(&declaration)) {
        if (const auto *member = record->getMemberSpecializationInfo())
            location = member->getPointOfInstantiation();
    } else if (const auto *enumeration =
                   llvm::dyn_cast<clang::EnumDecl>(&declaration)) {
        if (const auto *member = enumeration->getMemberSpecializationInfo())
            location = member->getPointOfInstantiation();
    }
    return location.isValid() ? std::optional<clang::SourceLocation>(location)
                              : std::nullopt;
}

} // namespace

class ClangTableBuilder::Impl {
    struct LiveFileIdentity {
        const clang::FileEntry *fileEntry = nullptr;
        const char *bufferStart = nullptr;
        std::string physicalName;

        bool operator==(const LiveFileIdentity &other) const {
            return fileEntry == other.fileEntry &&
                   bufferStart == other.bufferStart &&
                   physicalName == other.physicalName;
        }
    };

public:
    Impl(const clang::SourceManager &sourceManager,
         const clang::LangOptions &langOptions)
        : manager(sourceManager), options(langOptions) {}

    llvm::Expected<FileId> internFile(clang::FileID clangFile) {
        for (const auto &known : knownFiles)
            if (known.first == clangFile)
                return known.second;
        if (clangFile.isInvalid())
            return error("cannot intern an invalid Clang file");
        if (std::find(filesBeingInterned.begin(), filesBeingInterned.end(),
                      clangFile) != filesBeingInterned.end())
            return error("Clang include-parent graph contains a cycle");

        bool invalidEntry = false;
        const auto &entry = manager.getSLocEntry(clangFile, &invalidEntry);
        if (invalidEntry || !entry.isFile())
            return error("source point did not resolve to a physical file");

        filesBeingInterned.push_back(clangFile);
        File file;
        const clang::SourceLocation start =
            manager.getLocForStartOfFile(clangFile);
        llvm::StringRef requested = entry.getFile().getName();
        if (requested.empty())
            requested = manager.getBufferName(start);

        if (auto fileEntry = manager.getFileEntryRefForID(clangFile)) {
            file.requestedName = fileEntry->getName().str();
            llvm::StringRef real =
                fileEntry->getFileEntry().tryGetRealPathName();
            file.physicalName =
                (real.empty() ? fileEntry->getName() : real).str();
        } else {
            file.physicalName = requested.str();
        }
        if (file.physicalName.empty())
            file.physicalName = "<unknown>";

        file.kind = classify(manager, start, requested);
        file.isMain = clangFile == manager.getMainFileID();

        LiveFileIdentity identity;
        if (auto fileEntry = manager.getFileEntryRefForID(clangFile))
            identity.fileEntry = &fileEntry->getFileEntry();
        if (auto buffer = manager.getBufferOrNone(clangFile, start))
            identity.bufferStart = buffer->getBufferStart();
        identity.physicalName = file.physicalName;

        clang::SourceLocation include = manager.getIncludeLoc(clangFile);
        if (include.isValid()) {
            include = manager.getSpellingLoc(include);
            auto decomposed = manager.getDecomposedLoc(include);
            auto parent = internFile(decomposed.first);
            if (!parent) {
                filesBeingInterned.pop_back();
                return parent.takeError();
            }
            file.includeParent = std::make_pair(
                *parent, static_cast<std::uint64_t>(decomposed.second));
        }

        for (const auto &known : knownIdentities) {
            if ((identity.fileEntry || identity.bufferStart) &&
                known.first == identity) {
                filesBeingInterned.pop_back();
                knownFiles.emplace_back(clangFile, known.second);
                return known.second;
            }
        }

        auto id = tables.appendDistinctFile(std::move(file));
        filesBeingInterned.pop_back();
        if (!id)
            return id.takeError();
        knownFiles.emplace_back(clangFile, *id);
        knownIdentities.emplace_back(std::move(identity), *id);
        return *id;
    }

    llvm::Expected<std::optional<PhysicalPoint>>
    physicalPoint(clang::SourceLocation location,
                  LocationProjection projectionKind) {
        location = project(manager, location, projectionKind);
        if (location.isInvalid() || !location.isFileID())
            return std::optional<PhysicalPoint>{};

        auto decomposed = manager.getDecomposedLoc(location);
        auto file = internFile(decomposed.first);
        if (!file)
            return file.takeError();
        bool invalidLine = false;
        bool invalidColumn = false;
        unsigned line = manager.getLineNumber(decomposed.first,
                                              decomposed.second, &invalidLine);
        unsigned column = manager.getColumnNumber(
            decomposed.first, decomposed.second, &invalidColumn);
        if (invalidLine || invalidColumn)
            return std::optional<PhysicalPoint>{};
        return std::optional<PhysicalPoint>(
            PhysicalPoint{*file, static_cast<std::uint64_t>(decomposed.second),
                          line, column});
    }

    std::optional<PresumedPoint>
    presumedPoint(clang::SourceLocation location) const {
        if (location.isInvalid())
            return std::nullopt;
        clang::PresumedLoc presumed = manager.getPresumedLoc(location);
        if (presumed.isInvalid())
            return std::nullopt;
        return PresumedPoint{presumed.getFilename(), presumed.getLine(),
                             presumed.getColumn()};
    }

    llvm::Expected<Range> range(clang::CharSourceRange sourceRange,
                                LocationProjection projectionKind) {
        Range result;
        result.endSemantics = sourceRange.isTokenRange() ? RangeKind::Token
                                                         : RangeKind::Character;

        // Conversion of the original macro-aware range is a necessary first
        // gate. Projecting its endpoints before conversion can otherwise
        // disguise incompatible macro boundaries as an ordinary file range.
        clang::CharSourceRange originalNormalized =
            clang::Lexer::makeFileCharRange(sourceRange, manager, options);

        auto begin = physicalPoint(sourceRange.getBegin(), projectionKind);
        if (!begin)
            return begin.takeError();
        result.begin = std::move(*begin);
        auto end = physicalPoint(sourceRange.getEnd(), projectionKind);
        if (!end)
            return end.takeError();
        result.end = std::move(*end);

        if (originalNormalized.isInvalid())
            return result;

        clang::SourceLocation projectedBegin =
            project(manager, sourceRange.getBegin(), projectionKind);
        clang::SourceLocation projectedEnd =
            project(manager, sourceRange.getEnd(), projectionKind);
        if (!result.begin || !result.end ||
            result.begin->file != result.end->file ||
            projectedBegin.isInvalid() || projectedEnd.isInvalid())
            return result;

        clang::CharSourceRange projected(
            clang::SourceRange(projectedBegin, projectedEnd),
            sourceRange.isTokenRange());
        clang::CharSourceRange projectedNormalized =
            clang::Lexer::makeFileCharRange(projected, manager, options);
        if (projectedNormalized.isInvalid())
            return result;

        auto normalizedBegin = physicalPoint(projectedNormalized.getBegin(),
                                             LocationProjection::Spelling);
        if (!normalizedBegin)
            return normalizedBegin.takeError();
        auto normalizedEnd = physicalPoint(projectedNormalized.getEnd(),
                                           LocationProjection::Spelling);
        if (!normalizedEnd)
            return normalizedEnd.takeError();
        if (*normalizedBegin && *normalizedEnd &&
            (*normalizedBegin)->file == (*normalizedEnd)->file &&
            (*normalizedBegin)->file == result.begin->file)
            result.normalizedHalfOpen =
                std::make_pair(**normalizedBegin, **normalizedEnd);
        return result;
    }

    llvm::Expected<std::optional<Range>>
    optionalRange(clang::CharSourceRange sourceRange,
                  LocationProjection projectionKind) {
        auto extracted = range(sourceRange, projectionKind);
        if (!extracted)
            return extracted.takeError();
        if (!extracted->begin && !extracted->end)
            return std::optional<Range>{};
        return std::optional<Range>(std::move(*extracted));
    }

    llvm::Expected<std::vector<MacroFrame>>
    macroStack(clang::CharSourceRange sourceRange) {
        std::vector<MacroFrame> result;
        clang::SourceLocation current = sourceRange.getBegin().isValid()
                                            ? sourceRange.getBegin()
                                            : sourceRange.getEnd();
        while (current.isValid() && current.isMacroID()) {
            MacroFrame frame;
            frame.kind = manager.isMacroArgExpansion(current)
                             ? MacroOriginKind::Argument
                             : MacroOriginKind::Body;
            clang::CharSourceRange immediateExpansion =
                manager.getImmediateExpansionRange(current);
            clang::SourceLocation nameLocation =
                manager.isMacroArgExpansion(current)
                    ? immediateExpansion.getBegin()
                    : current;
            llvm::StringRef name = clang::Lexer::getImmediateMacroName(
                nameLocation, manager, options);
            if (name.empty() && nameLocation != current)
                name = clang::Lexer::getImmediateMacroName(current, manager,
                                                           options);
            if (!name.empty())
                frame.name = name.str();

            clang::SourceLocation spelling =
                manager.getImmediateSpellingLoc(current);
            auto spellingRange = optionalRange(
                clang::CharSourceRange::getTokenRange(spelling, spelling),
                LocationProjection::Spelling);
            if (!spellingRange)
                return spellingRange.takeError();
            frame.spelling = std::move(*spellingRange);

            auto expansionRange = optionalRange(immediateExpansion,
                                                LocationProjection::Expansion);
            if (!expansionRange)
                return expansionRange.takeError();
            frame.expansion = std::move(*expansionRange);
            result.push_back(std::move(frame));

            clang::SourceLocation caller =
                manager.getImmediateMacroCallerLoc(current);
            if (caller == current)
                break;
            current = caller;
        }
        return result;
    }

    llvm::Expected<OriginId>
    writtenNode(OriginKind kind, clang::CharSourceRange sourceRange,
                std::optional<clang::SourceLocation> pointOfInstantiation,
                std::optional<OriginId> anchor,
                llvm::ArrayRef<OriginId> derivedFrom) {
        Origin origin;
        origin.kind = kind;
        auto spelling =
            optionalRange(sourceRange, LocationProjection::Spelling);
        if (!spelling)
            return spelling.takeError();
        origin.spelling = std::move(*spelling);
        auto expansion =
            optionalRange(sourceRange, LocationProjection::Expansion);
        if (!expansion)
            return expansion.takeError();
        origin.expansion = std::move(*expansion);
        origin.presumedBegin = presumedPoint(sourceRange.getBegin());
        origin.presumedEnd = presumedPoint(sourceRange.getEnd());
        auto stack = macroStack(sourceRange);
        if (!stack)
            return stack.takeError();
        origin.macroStack = std::move(*stack);
        if (pointOfInstantiation) {
            auto point = physicalPoint(*pointOfInstantiation,
                                       LocationProjection::Expansion);
            if (!point)
                return point.takeError();
            origin.pointOfInstantiation = std::move(*point);
        }
        origin.anchor = anchor;
        origin.derivedFrom.assign(derivedFrom.begin(), derivedFrom.end());
        return tables.internOrigin(std::move(origin));
    }

    const clang::SourceManager &manager;
    const clang::LangOptions &options;
    TableBuilder tables;
    std::vector<std::pair<clang::FileID, FileId>> knownFiles;
    std::vector<std::pair<LiveFileIdentity, FileId>> knownIdentities;
    std::vector<clang::FileID> filesBeingInterned;
};

ClangTableBuilder::ClangTableBuilder(const clang::SourceManager &sourceManager,
                                     const clang::LangOptions &langOptions)
    : impl_(std::make_unique<Impl>(sourceManager, langOptions)) {}

ClangTableBuilder::~ClangTableBuilder() = default;
ClangTableBuilder::ClangTableBuilder(ClangTableBuilder &&) noexcept = default;
ClangTableBuilder &
ClangTableBuilder::operator=(ClangTableBuilder &&) noexcept = default;

llvm::Expected<std::optional<PhysicalPoint>>
ClangTableBuilder::physicalPoint(clang::SourceLocation location,
                                 LocationProjection projectionKind) {
    if (!impl_)
        return error("source extractor is already finished");
    return impl_->physicalPoint(location, projectionKind);
}

std::optional<PresumedPoint>
ClangTableBuilder::presumedPoint(clang::SourceLocation location) const {
    return impl_ ? impl_->presumedPoint(location) : std::nullopt;
}

llvm::Expected<Range>
ClangTableBuilder::range(clang::CharSourceRange sourceRange,
                         LocationProjection projectionKind) {
    if (!impl_)
        return error("source extractor is already finished");
    return impl_->range(sourceRange, projectionKind);
}

llvm::Expected<OriginId> ClangTableBuilder::explicitNode(
    clang::CharSourceRange sourceRange,
    std::optional<clang::SourceLocation> pointOfInstantiation,
    llvm::ArrayRef<OriginId> derivedFrom) {
    if (!impl_)
        return error("source extractor is already finished");
    return impl_->writtenNode(OriginKind::Explicit, sourceRange,
                              pointOfInstantiation, std::nullopt, derivedFrom);
}

llvm::Expected<OriginId> ClangTableBuilder::explicitNode(
    clang::SourceRange sourceRange,
    std::optional<clang::SourceLocation> pointOfInstantiation,
    llvm::ArrayRef<OriginId> derivedFrom) {
    return explicitNode(tokenRange(sourceRange), pointOfInstantiation,
                        derivedFrom);
}

llvm::Expected<OriginId>
ClangTableBuilder::implicitNode(clang::CharSourceRange sourceRange,
                                llvm::ArrayRef<OriginId> derivedFrom) {
    if (!impl_)
        return error("source extractor is already finished");
    return impl_->writtenNode(OriginKind::Implicit, sourceRange, std::nullopt,
                              std::nullopt, derivedFrom);
}

llvm::Expected<OriginId>
ClangTableBuilder::anchoredImplicitNode(clang::CharSourceRange sourceRange,
                                        OriginId anchor,
                                        llvm::ArrayRef<OriginId> derivedFrom) {
    if (!impl_)
        return error("source extractor is already finished");
    return impl_->writtenNode(OriginKind::Implicit, sourceRange, std::nullopt,
                              anchor, derivedFrom);
}

llvm::Expected<OriginId>
ClangTableBuilder::transformedNode(clang::CharSourceRange sourceRange,
                                   llvm::ArrayRef<OriginId> derivedFrom) {
    if (!impl_)
        return error("source extractor is already finished");
    return impl_->writtenNode(OriginKind::ClangTransformed, sourceRange,
                              std::nullopt, std::nullopt, derivedFrom);
}

llvm::Expected<OriginId>
ClangTableBuilder::synthesizedNode(std::optional<OriginId> anchor,
                                   llvm::ArrayRef<OriginId> derivedFrom) {
    if (!impl_)
        return error("source extractor is already finished");
    Origin origin;
    origin.kind = OriginKind::Cpp2vSynthesized;
    origin.anchor = anchor;
    origin.derivedFrom.assign(derivedFrom.begin(), derivedFrom.end());
    return impl_->tables.internOrigin(std::move(origin));
}

llvm::Expected<OriginId>
ClangTableBuilder::inheritedNode(std::optional<OriginId> anchor,
                                 llvm::ArrayRef<OriginId> derivedFrom) {
    if (!impl_)
        return error("source extractor is already finished");
    Origin origin;
    origin.kind = OriginKind::Inherited;
    origin.anchor = anchor;
    origin.derivedFrom.assign(derivedFrom.begin(), derivedFrom.end());
    return impl_->tables.internOrigin(std::move(origin));
}

llvm::Expected<OriginId> ClangTableBuilder::declarationNode(
    const clang::Decl &declaration,
    std::optional<clang::SourceLocation> pointOfInstantiation,
    OriginKind kind) {
    if (!impl_)
        return error("source extractor is already finished");
    if (kind != OriginKind::Explicit && kind != OriginKind::Implicit &&
        kind != OriginKind::ClangTransformed)
        return error("written declaration requires a written origin kind");
    if (!pointOfInstantiation)
        pointOfInstantiation = source::pointOfInstantiation(declaration);
    return impl_->writtenNode(kind, tokenRange(declaration.getSourceRange()),
                              pointOfInstantiation, std::nullopt, {});
}

llvm::Expected<OriginId>
ClangTableBuilder::typeLocNode(const clang::TypeLoc &typeLoc, OriginKind kind) {
    if (!impl_)
        return error("source extractor is already finished");
    if (kind != OriginKind::Explicit && kind != OriginKind::Implicit &&
        kind != OriginKind::ClangTransformed)
        return error("written TypeLoc requires a written origin kind");
    return impl_->writtenNode(kind, tokenRange(typeLoc.getSourceRange()),
                              std::nullopt, std::nullopt, {});
}

llvm::Expected<OriginId> ClangTableBuilder::typeSourceInfoNode(
    const clang::TypeSourceInfo *typeSourceInfo, OriginKind kind) {
    if (!typeSourceInfo)
        return error("null TypeSourceInfo has no written source range");
    clang::TypeLoc location = typeSourceInfo->getTypeLoc();
    return typeLocNode(location, kind);
}

llvm::Expected<std::vector<OriginId>>
ClangTableBuilder::semanticQualTypeOrigins(
    const clang::QualType &type, SemanticTypeOriginPolicy policy,
    std::optional<OriginId> inheritedFrom) {
    (void)type;
    if (policy == SemanticTypeOriginPolicy::Empty) {
        if (inheritedFrom)
            return error("empty QualType origin policy cannot take an anchor");
        return std::vector<OriginId>{};
    }
    if (!inheritedFrom)
        return error("inherited QualType origin policy requires an anchor");
    auto inherited = inheritedNode(inheritedFrom);
    if (!inherited)
        return inherited.takeError();
    return std::vector<OriginId>{*inherited};
}

llvm::Expected<Tables> ClangTableBuilder::finish() && {
    if (!impl_)
        return error("source extractor is already finished");
    auto result = std::move(impl_->tables).finish();
    impl_.reset();
    return result;
}

} // namespace source
