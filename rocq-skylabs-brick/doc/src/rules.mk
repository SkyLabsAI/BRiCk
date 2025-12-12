#
# Copyright (c) 2019 BlueRock Security, Inc.
#
# This software is distributed under the terms of the BedRock Open-Source License.
# See the LICENSE-BedRock file in the repository root for details.
#
coq: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	@ $(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f *_names.v *_hpp.v *_cpp.v *_c.v *_h.v

Makefile.coq:
	coq_makefile -f _CoqProject.template -o Makefile.coq
