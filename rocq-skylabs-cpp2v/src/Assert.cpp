/*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */

#include "Assert.hpp"
#include "Logging.hpp"
#include <llvm/Support/raw_ostream.h>

void assertion_failed(const char *e, const char *func, const char *file,
                      int line) {
    llvm::errs() << "Assertion failed: " << e << ", function " << func
                 << ", file " << file << ", line " << line << ".\n";
    logging::die();
}
