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
.PHONY: all cpp2v

cpp2v-unit-tests: $(BUILD_DIR)/Makefile
	+@$(MAKE) -C $(BUILD_DIR) cpp2v-unit-tests
.PHONY: cpp2v-unit-tests

cpp2v-source-info-probe: $(BUILD_DIR)/Makefile
	+@$(MAKE) -C $(BUILD_DIR) cpp2v-source-info-probe
.PHONY: cpp2v-source-info-probe

cpp2v-name-builder-probe: $(BUILD_DIR)/Makefile
	+@$(MAKE) -C $(BUILD_DIR) cpp2v-name-builder-probe
.PHONY: cpp2v-name-builder-probe

cpp2v-type-expr-builder-probe: $(BUILD_DIR)/Makefile
	+@$(MAKE) -C $(BUILD_DIR) cpp2v-type-expr-builder-probe
.PHONY: cpp2v-type-expr-builder-probe

cpp2v-sharing-builder-probe: $(BUILD_DIR)/Makefile
	+@$(MAKE) -C $(BUILD_DIR) cpp2v-sharing-builder-probe
.PHONY: cpp2v-sharing-builder-probe

cpp2v-declaration-builder-probe: $(BUILD_DIR)/Makefile
	+@$(MAKE) -C $(BUILD_DIR) cpp2v-declaration-builder-probe
.PHONY: cpp2v-declaration-builder-probe

test-binaries: $(BUILD_DIR)/Makefile
	+@$(MAKE) -C $(BUILD_DIR) cpp2v-unit-tests cpp2v-source-info-probe cpp2v-name-builder-probe cpp2v-type-expr-builder-probe cpp2v-sharing-builder-probe cpp2v-declaration-builder-probe
.PHONY: test-binaries

$(BUILD_DIR)/Makefile: $(MAKEFILE_LIST) CMakeLists.txt
	@$(CMAKE) -B $(BUILD_DIR) $(BUILD_ARGS) -DCMAKE_BUILD_TYPE=$(BUILD_TYPE)

clean:
	@rm -rf $(BUILD_DIR)
.PHONY: clean
