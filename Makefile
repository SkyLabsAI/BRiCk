#
# Copyright (c) 2019-2024 BlueRock Security, Inc.
#
# This software is distributed under the terms of the BedRock Open-Source
# License. See the LICENSE-BedRock file in the repository root for details.
#

# Use "make ... Q=" to show more commands.
Q = @

# You can override this with a different program which you can use to preview
# html files within your filesystem.
DOCOPEN ?= xdg-open

all:
	dune build @default @runtest
.PHONY: all

_CoqProject: _CoqProject.template
	$(Q)cp $< $@

SHELL := /bin/bash

dune_build_folder = ../../_build
BUILD_ROOT=$(dune_build_folder)/default/fmdeps/BRiCk
# Beware:
# 1. ROCQLIB must be absolute
# 2. dune caching does _not_ track the dependency on ROCQLIB, so CI won't help
# you if you break rule 1.
ROCQLIB=${PWD}/$(dune_build_folder)/install/default/lib/coq
DOC_PATH = rocq-skylabs-brick/doc
COQDOC_DIR = $(DOC_PATH)/sphinx/_static/coqdoc

SED = $(shell (which gsed || which sed) 2> /dev/null)
CP = $(shell (which gcp || which cp) 2> /dev/null)

doc:
	$(Q)rm -rf /tmp/coqdocjs
	$(Q)mkdir -p /tmp/coqdocjs/extra
# Referenced in `flags/coqdoc`
	$(Q)echo '{{{HEADER}}}' > /tmp/coqdocjs/extra/fake-header.html
	$(Q)echo '{{{FOOTER}}}' > /tmp/coqdocjs/extra/fake-footer.html
	$(Q)rm -rf $(DOC_PATH)/sphinx/_static/coqdoc
	$(Q)mkdir -p $(DOC_PATH)/sphinx/_static/css/coqdocjs $(DOC_PATH)/sphinx/_static/js/coqdocjs
	$(Q)$(CP) -r coqdocjs/extra/resources/*.css $(DOC_PATH)/sphinx/_static/css/coqdocjs
	$(Q)$(CP) -r coqdocjs/extra/resources/*.js $(DOC_PATH)/sphinx/_static/js/coqdocjs
	$(Q)dune build @../vendored/rocq/install
# Can't be merged with the previous step, due to `coqc --config` failure
	$(Q)dune build
	$(Q)ROCQLIB=${ROCQLIB} dune build @doc
	$(Q)rm -rf ${COQDOC_DIR}
	$(Q)mkdir -p ${COQDOC_DIR}
	$(Q)$(CP) -r -t ${COQDOC_DIR} $$(find ${BUILD_ROOT} -type d -name '*.html')
	$(Q)find ${COQDOC_DIR} -type f -name '*.html' \
		| xargs $(SED) -i \
		-e '/{{{FOOTER}}}/{' -e 'r coqdocjs/extra/footer.html' -e 'd' -e '}' \
		-e '/{{{HEADER}}}/{' -e 'r coqdocjs/extra/header.html' -e 'd' -e '}'
	$(Q)uv run --with-requirements python_requirements.txt $(MAKE) -C $(DOC_PATH) html
.PHONY: doc

doc-open: doc
	$(DOCOPEN) $(DOC_PATH)/sphinx/_build/html/index.html
.PHONY: doc-open

doc-clean:
	$(Q)$(MAKE) -C $(DOC_PATH) clean
.PHONY: doc-clean

clean: doc-clean
	$(Q)dune clean || echo "dune not found; not cleaning dune-generated documentation files"
	$(Q)rm -f _CoqProject
.PHONY: clean
