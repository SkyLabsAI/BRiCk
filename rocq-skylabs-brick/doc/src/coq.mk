#
# Copyright (c) 2019 BlueRock Security, Inc.
#
# This software is distributed under the terms of the BedRock Open-Source License.
# See the LICENSE-BedRock file in the repository root for details.
#
ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
CPP2V ?= $(shell which cpp2v)

CPPFLAGS=-std=c++17
CFLAGS=-std=c99

%_c.v: %.c $(CPP2V)
	$(CPP2V) -v -o $@ $< -- $(CFLAGS)
%_h.v: %.h $(CPP2V)
	$(CPP2V) -v -o $@ $< -- $(CFLAGS)
%_cpp.v: %.cpp $(CPP2V)
	$(CPP2V) -v -o $@ $< -- $(CPPFLAGS)
%_hpp.v: %.hpp $(CPP2V)
	$(CPP2V) -v -o $@ $< -- $(CPPFLAGS)

%_c_names.v: %.c $(CPP2V)
	$(CPP2V) -v -names $@ $< -- $(CFLAGS)
%_h_names.v: %.h $(CPP2V)
	$(CPP2V) -v -names $@ $< -- $(CFLAGS)
%_cpp_names.v: %.cpp $(CPP2V)
	$(CPP2V) -v -names $@ $< -- $(CPPFLAGS)
%_hpp_names.v: %.hpp $(CPP2V)
	$(CPP2V) -v -names $@ $< -- $(CPPFLAGS)
