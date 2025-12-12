# Copyright (c) 2020 BlueRock Security, Inc.
# This software is distributed under the terms of the BedRock Open-Source License.
# See the LICENSE-BedRock file in the repository root for details.

ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))

# cf. <https://github.com/cpitclaudel/alectryon#setup>
ALECTRYON = $(shell which alectryon)
export ALECTRYON

COQBIN       = ${PWD}/../../../_build/install/default/bin
ROCQLIB       = ${PWD}/../../../_build/install/default/lib/coq
# NOTE: We will likely want to re-enable this when we have a src/ subdirectory
#COQPATHEXTRA = $(ROOT_DIR)/src

######################################################################
### Variables
######################################################################

# Sphinx-related variables
SPHINXENV:=COQBIN="$(COQBIN)" ROCQLIB="$(ROCQLIB)" ROCQPATH="$(ROCQPATH):$(COQPATHEXTRA)"
SPHINXWARNERROR ?= 1
ifeq ($(SPHINXWARNERROR),1)
SPHINXOPTS= -W
else
SPHINXOPTS=
endif

SPHINXDIR ?= $(ROOT_DIR)/sphinx
SPHINXTANGLEDIR = $(SPHINXDIR)/tangles
export SPHINXTANGLEDIR

SPHINXBUILD= $(shell which sphinx-build)
SPHINXBUILDDIR = $(SPHINXDIR)/_build

ALLSPHINXOPTS= -d $(SPHINXBUILDDIR)/doctrees $(SPHINXOPTS)

######################################################################
### General rules
######################################################################

all: html
html: doc

.PHONY: doc doc-private doc-public html redoc src tangle-src tangle

TANGLE_DIR     = $(SPHINXDIR)/orphans
TANGLE_INPUTS  = $(wildcard $(TANGLE_DIR)/*.v)
TANGLE_OUTPUTS = $(patsubst $(TANGLE_DIR)/%.v,$(SPHINXTANGLEDIR)/%.rst,$(TANGLE_INPUTS))

# This is responsible for building .rst files from .v files with Alectryon comments
$(SPHINXTANGLEDIR)/%.rst: $(TANGLE_DIR)/%.v
	@mkdir -p $(SPHINXDIR)/tangles
	$(ALECTRYON) --frontend coq+rst --backend rst $< -o $@

tangle: $(TANGLE_OUTPUTS)

src:
	$(MAKE) -C src all
tangle-src:
	$(MAKE) -C src tangle-all

doc-public: tangle-src tangle refman-public
doc-private: tangle-src tangle refman-private

html: doc
doc: doc-private
redoc: clean doc

refman-public-%:
	@echo $(COQBIN) $(ROCQLIB)
	@echo 'SPHINXBUILD sphinx ($*)'
	$(HIDE)$(SPHINXENV) $(SPHINXBUILD) -b $* \
		$(ALLSPHINXOPTS) sphinx $(SPHINXBUILDDIR)/$*

# NOTE: in sphinx/conf.py, the `private` tag is used to conditionally allow the sphinx/private directory
refman-private-%:
	@echo 'SPHINXBUILD sphinx ($*)'
	@echo 'ROOT DIR: $(ROOT_DIR)'
	$(HIDE)$(SPHINXENV) $(SPHINXBUILD) -b $* \
		-t private \
		$(ALLSPHINXOPTS) sphinx $(SPHINXBUILDDIR)/$*

refman-public: | tangle-src tangle
	+$(MAKE) refman-public-html

refman-private: | tangle-src tangle
	+$(MAKE) refman-private-html


clean:
	+$(MAKE) -C src clean
	rm -rf $(SPHINXBUILDDIR)
	rm -rf $(SPHINXDIR)/tangles
.PHONY: clean
