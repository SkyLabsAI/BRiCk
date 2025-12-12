/*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "Logging.hpp"
#include <llvm/Support/raw_ostream.h>

namespace logging {
static Level log_level = Level::NONE;

llvm::raw_ostream &log(Level level) {
    if (level <= log_level) {
        return llvm::errs();
    } else {
        return llvm::nulls();
    }
}

void set_level(Level level) { log_level = level; }

[[noreturn]] void die() {
    llvm::outs().flush();
    llvm::errs().flush();
    exit(1);
}
} // namespace logging