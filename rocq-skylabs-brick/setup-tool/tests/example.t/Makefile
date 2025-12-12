all: client server

client: src/client/client.cpp include/util.hpp src/client/include/client.hpp
	clang++ -o $@ -Isrc/client/include -Iinclude $<

server: src/server/server.cpp include/util.hpp src/server/include/server.hpp
	clang++ -o $@ -Isrc/server/include -Iinclude $<

.PHONY: clean
clean:
	rm -rf client server
