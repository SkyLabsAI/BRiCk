/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include "Location.hpp"
#include <cstdint>
#include <optional>
#include <string>
#include <unordered_map>
#include <vector>

namespace clang {
class SourceManager;
}

namespace llvm {
class StringRef;
}

class CoqPrinter;

enum class LocInfoMode : unsigned {
    None,
    Local,
};

class LocationTable final {
public:
    using Index = std::uint64_t;

    explicit LocationTable(clang::SourceManager &source_manager)
        : source_manager_{source_manager} {}

    std::optional<Index> intern(loc::loc token);
    void emit(CoqPrinter &print) const;

    class Guard final {
    public:
        Guard(LocationTable *table, CoqPrinter &print, llvm::StringRef ctor,
              loc::loc token);
        ~Guard();

        Guard(const Guard &) = delete;
        Guard &operator=(const Guard &) = delete;

    private:
        CoqPrinter &print_;
        bool opened_{false};
    };

private:
    struct Location final {
        Index file;
        Index byte;
        Index line;
        Index column;

        bool operator==(const Location &other) const {
            return file == other.file && byte == other.byte &&
                   line == other.line && column == other.column;
        }
    };

    struct Locations final {
        Location file_loc;
        Location spelling_loc;

        bool operator==(const Locations &other) const {
            return file_loc == other.file_loc &&
                   spelling_loc == other.spelling_loc;
        }
    };

    struct LocationHash final {
        std::size_t operator()(const Location &location) const;
    };

    struct LocationsHash final {
        std::size_t operator()(const Locations &locations) const;
    };

    Index internFile(std::string file_name);
    Location project(clang::SourceLocation location);
    Index internLocations(Locations locations);

private:
    clang::SourceManager &source_manager_;
    std::vector<std::string> file_names_;
    std::unordered_map<std::string, Index> file_name_indices_;
    std::vector<Locations> locations_;
    std::unordered_map<Locations, Index, LocationsHash> location_indices_;
};
