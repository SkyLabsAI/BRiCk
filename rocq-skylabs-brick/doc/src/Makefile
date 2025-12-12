#
# Copyright (c) 2019 BlueRock Security, Inc.
#
# This software is distributed under the terms of the BedRock Open-Source License.
# See the LICENSE-BedRock file in the repository root for details.
#

DIRS=
TANGLE_DIRS = $(addprefix tangle-, $(DIRS))

all: $(DIRS)
tangle-all: $(DIRS) _downloads $(TANGLE_DIRS)

_DOWNLOADS_DIR:=_downloads
_DOWNLOADS_FILES:=coq.mk rules.mk
_downloads:
	mkdir -p $(_DOWNLOADS_DIR)/cpp2v-core-docs-toplevel
	cp template/Makefile.toplevel $(_DOWNLOADS_DIR)/cpp2v-core-docs-toplevel/Makefile
	cp $(_DOWNLOADS_FILES) $(_DOWNLOADS_DIR)/cpp2v-core-docs-toplevel
	zip -rj $(_DOWNLOADS_DIR)/cpp2v-core-docs-toplevel.zip $(_DOWNLOADS_DIR)/cpp2v-core-docs-toplevel
	zip -r $(_DOWNLOADS_DIR)/cpp2v-core-docs-full.zip . -x "_downloads/*" "*/.*" "*/*.vo*" \
								"*/*.glob" "*/Makefile.coq" "*/Makefile.coq.conf"

$(DIRS):
	$(MAKE) -C $@ coq

$(TANGLE_DIRS):
	$(MAKE) -C $(subst tangle-,,$@) tangle

.PHONY: $(DIRS) $(TANGLE_DIRS)

clean:
	rm -rf _downloads/
	$(foreach d,$(DIRS), $(MAKE) -C $(d) clean;)
