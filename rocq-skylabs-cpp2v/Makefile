#
# Copyright (c) 2019-2024 BlueRock Security, Inc.
#
# This software is distributed under the terms of the BedRock Open-Source
# License. See the LICENSE-BedRock file in the repository root for details.
#

CMAKE ?= cmake
BUILD_DIR ?= build
BUILD_ARGS ?=
BUILD_TYPE ?= Release

all: $(BUILD_DIR)/Makefile
	+@$(MAKE) -C $(BUILD_DIR) cpp2v
.PHONY: cpp2v

$(BUILD_DIR)/Makefile: $(MAKEFILE_LIST) CMakeLists.txt
	@$(CMAKE) -B $(BUILD_DIR) $(BUILD_ARGS) -DCMAKE_BUILD_TYPE=$(BUILD_TYPE)

clean:
	@rm -rf $(BUILD_DIR)
.PHONY: clean
