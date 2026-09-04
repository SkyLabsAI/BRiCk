/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "LocationTable.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include <clang/Basic/FileEntry.h>
#include <clang/Basic/SourceManager.h>
#include <limits>
#include <llvm/ADT/SmallString.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/Path.h>
#include <system_error>

using namespace clang;

namespace {

constexpr LocationTable::Index MAX_UINT63 =
    (std::numeric_limits<LocationTable::Index>::max() >> 1);

std::size_t hashCombine(std::size_t seed, LocationTable::Index value) {
    return seed ^ (std::hash<LocationTable::Index>{}(value) +
                   0x9e3779b97f4a7c15ULL + (seed << 6) + (seed >> 2));
}

[[noreturn]] void tableTooLarge(llvm::StringRef table) {
    logging::fatal() << "source location " << table
                     << " exceeds the uint63 index range\n";
    logging::die();
}

std::optional<std::string> physicalPath(const SourceManager &source_manager,
                                        FileID file_id) {
    auto entry = source_manager.getFileEntryRefForID(file_id);
    if (!entry)
        return std::nullopt;

    auto name = entry->getFileEntry().tryGetRealPathName();
    if (name.empty())
        name = entry->getName();
    if (name.empty())
        return std::nullopt;

    llvm::SmallString<256> path{name};
    if (auto error = llvm::sys::fs::make_absolute(path)) {
        logging::fatal() << "could not make source path '" << name
                         << "' absolute: " << error.message() << "\n";
        logging::die();
    }
    llvm::sys::path::remove_dots(path, /*remove_dot_dot=*/true);

    // TODO: Make source paths relative in a later iteration.
    return path.str().str();
}

} // namespace

std::size_t
LocationTable::LocationHash::operator()(const Location &location) const {
    std::size_t seed = 0;
    seed = hashCombine(seed, location.file);
    seed = hashCombine(seed, location.byte);
    seed = hashCombine(seed, location.line);
    return hashCombine(seed, location.column);
}

std::size_t
LocationTable::LocationsHash::operator()(const Locations &locations) const {
    LocationHash hash;
    auto seed = hash(locations.file_loc);
    return hashCombine(seed, hash(locations.spelling_loc));
}

LocationTable::Index LocationTable::internFile(std::string file_name) {
    if (auto found = file_name_indices_.find(file_name);
        found != file_name_indices_.end())
        return found->second;

    if (file_names_.size() >= MAX_UINT63)
        tableTooLarge("file-name table");

    auto index = static_cast<Index>(file_names_.size());
    file_names_.push_back(std::move(file_name));
    file_name_indices_.emplace(file_names_.back(), index);
    return index;
}

LocationTable::Location LocationTable::project(SourceLocation location) {
    const Location dummy{MAX_UINT63, MAX_UINT63, MAX_UINT63, MAX_UINT63};
    if (location.isInvalid())
        return dummy;

    auto decomposed = source_manager_.getDecomposedLoc(location);
    auto file_id = decomposed.first;
    auto byte = static_cast<Index>(decomposed.second);
    auto path = physicalPath(source_manager_, file_id);
    if (!path)
        return dummy;

    bool invalid_line = false;
    bool invalid_column = false;
    auto line = source_manager_.getLineNumber(file_id, decomposed.second,
                                              &invalid_line);
    auto column = source_manager_.getColumnNumber(file_id, decomposed.second,
                                                  &invalid_column);
    if (invalid_line || invalid_column)
        return dummy;

    // Byte offsets are zero-based; Clang's physical line and column numbers
    // are one-based.
    return {internFile(std::move(*path)), byte, static_cast<Index>(line),
            static_cast<Index>(column)};
}

LocationTable::Index LocationTable::internLocations(Locations locations) {
    if (auto found = location_indices_.find(locations);
        found != location_indices_.end())
        return found->second;

    if (locations_.size() >= MAX_UINT63)
        tableTooLarge("row table");

    auto index = static_cast<Index>(locations_.size());
    locations_.push_back(locations);
    location_indices_.emplace(locations, index);
    return index;
}

std::optional<LocationTable::Index> LocationTable::intern(loc::loc token) {
    if (!token)
        return std::nullopt;

    auto concrete = token->getLoc();
    if (concrete.isInvalid())
        return std::nullopt;

    auto file_location = source_manager_.getFileLoc(concrete);
    auto spelling_location = source_manager_.getSpellingLoc(concrete);
    auto main_file = source_manager_.getMainFileID();
    auto in_main_file = [&](SourceLocation location) {
        return location.isValid() &&
               source_manager_.getFileID(location) == main_file;
    };

    if (!in_main_file(file_location) && !in_main_file(spelling_location))
        return std::nullopt;

    return internLocations(
        {project(file_location), project(spelling_location)});
}

LocationTable::Guard::Guard(LocationTable *table, CoqPrinter &print,
                            llvm::StringRef ctor, loc::loc token)
    : print_{print} {
    if (!table)
        return;
    if (auto index = table->intern(token)) {
        print_.ctor(ctor);
        print_.output() << *index << "%uint63" << fmt::nbsp;
        opened_ = true;
    }
}

LocationTable::Guard::~Guard() {
    if (opened_)
        print_.end_ctor();
}

void LocationTable::emit(CoqPrinter &print) const {
    auto &out = print.output();

    out << fmt::line
        << "Definition file_names : array PrimString.string :=" << fmt::indent
        << fmt::line << "let result := PArray.make " << file_names_.size()
        << "%uint63 ";
    print.str("unknown_file") << "%pstring in";
    for (Index index = 0; index < file_names_.size(); ++index) {
        out << fmt::line << "let result := PArray.set result " << index
            << "%uint63 ";
        print.str(file_names_[index]) << "%pstring in";
    }
    out << fmt::line << "result." << fmt::outdent << fmt::line << fmt::line;

    out << "Definition loc_table : array locations :=" << fmt::indent
        << fmt::line << "let result := PArray.make " << locations_.size()
        << "%uint63 dummy_locations in";
    auto emit_location = [&](const Location &location) {
        out << "(Build_location " << location.file << "%uint63" << fmt::nbsp
            << location.byte << "%uint63" << fmt::nbsp << location.line
            << "%uint63" << fmt::nbsp << location.column << "%uint63)";
    };
    for (Index index = 0; index < locations_.size(); ++index) {
        const auto &locations = locations_[index];
        out << fmt::line << "let result := PArray.set result " << index
            << "%uint63 (Build_locations ";
        emit_location(locations.file_loc);
        out << fmt::nbsp;
        emit_location(locations.spelling_loc);
        out << ") in";
    }
    out << fmt::line << "result." << fmt::outdent << fmt::line;
}
