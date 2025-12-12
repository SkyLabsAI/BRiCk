ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))

.PHONY: all _downloads tangle

all: coq

include ../rules.mk

_downloads:
	@echo "~NOTE~NOTE~NOTE~NOTE~NOTE~NOTE~NOTE~NOTE~NOTE~NOTE~NOTE~NOTE~"
	@echo
	@echo "  Directory: " $(shell pwd)
	@echo "  We allow consumers of our documentation to set up a local"
	@echo "  env for running the standalone examples. We expose these"
	@echo "  examples as zipped archives which are generated and stored"
	@echo "  in 'fm-docs/src/_downloads'; these archives can be exposed"
	@echo "  within the documentation using the 'download' role. This"
	@echo "  directory is guaranteed to exist at this point. YOU are"
	@echo "  responsible for updating this rule s.t. a zip archive is"
	@echo "  generated (if you plan to expose your example to clients)."
	@echo
	@echo "~NOTE~NOTE~NOTE~NOTE~NOTE~NOTE~NOTE~NOTE~NOTE~NOTE~NOTE~NOTE~"

TANGLE_DIR_NAME = $(shell basename $(ROOT_DIR))
# Fill in which of your .v files you want to tangle into
# `fm-docs/sphinx/tangles/foo/` (if your subfolder is
# `src/foo`).
TANGLE_PUBLIC_INPUTS :=
TANGLE_PUBLIC_OUTPUTS = $(patsubst %.v, \
                                $(SPHINXTANGLEDIR)/$(TANGLE_DIR_NAME)/%.rst, \
                                $(TANGLE_PUBLIC_INPUTS))

# Fill in which of your .v files you want to tangle into
# `fm-docs/sphinx/tangles/foo/private` (if your subfolder is
# `src/foo`).
TANGLE_PRIVATE_INPUTS :=
TANGLE_PRIVATE_OUTPUTS = $(patsubst %.v, \
                                $(SPHINXTANGLEDIR)/$(TANGLE_DIR_NAME)/private/%.rst, \
                                $(TANGLE_PRIVATE_INPUTS))

$(SPHINXTANGLEDIR)/$(TANGLE_DIR_NAME)/%.rst: %.v
	@mkdir -p $(SPHINXTANGLEDIR)/$(TANGLE_DIR_NAME)
	python3 $(ALECTRYON) --frontend coq+rst --backend rst $< -o $@

$(SPHINXTANGLEDIR)/$(TANGLE_DIR_NAME)/private/%.rst: %.v
	@mkdir -p $(SPHINXTANGLEDIR)/$(TANGLE_DIR_NAME)/private
	python3 $(ALECTRYON) --frontend coq+rst --backend rst $< -o $@

tangle: _downloads $(TANGLE_PUBLIC_OUTPUTS) $(TANGLE_PRIVATE_OUTPUTS)
