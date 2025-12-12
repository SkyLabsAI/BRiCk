/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

namespace llvm {
class raw_ostream;
};

namespace logging {
enum Level : int {
    FATAL = -1,
    NONE = 0,
    UNSUPPORTED = 5,
    VERBOSE = 10,
    VERBOSER = 20,
    ALL = 1000,
};

llvm::raw_ostream &log(Level level = VERBOSE);

static inline llvm::raw_ostream &fatal() { return log(FATAL); }
static inline llvm::raw_ostream &unsupported() { return log(UNSUPPORTED); }
static inline llvm::raw_ostream &verbose() { return log(VERBOSE); }
static inline llvm::raw_ostream &debug() { return log(VERBOSER); }

void set_level(Level level);

[[noreturn]] void die();
} // namespace logging
