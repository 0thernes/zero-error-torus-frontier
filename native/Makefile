# SPDX-License-Identifier: Apache-2.0
CC ?= cc
CFLAGS := -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror -Iinclude
SAN_FLAGS := -std=c11 -O1 -g -Wall -Wextra -Wpedantic -Werror -fsanitize=address,undefined -fno-omit-frame-pointer -Iinclude

.PHONY: all test sanitize fuzz libfuzzer clean

all: build/torus_cli build/test_torus build/fuzz_torus

build:
	mkdir -p build

build/torus_cli: src/torus_frontier.c src/cli.c include/torus_frontier.h | build
	$(CC) $(CFLAGS) src/torus_frontier.c src/cli.c -o $@

build/test_torus: src/torus_frontier.c tests/test_torus.c include/torus_frontier.h | build
	$(CC) $(CFLAGS) src/torus_frontier.c tests/test_torus.c -o $@

build/fuzz_torus: src/torus_frontier.c tests/fuzz_torus.c include/torus_frontier.h | build
	$(CC) $(CFLAGS) src/torus_frontier.c tests/fuzz_torus.c -o $@

test: build/test_torus build/torus_cli
	./build/test_torus
	./build/torus_cli --verify-all

sanitize: src/torus_frontier.c tests/test_torus.c tests/fuzz_torus.c include/torus_frontier.h | build
	$(CC) $(SAN_FLAGS) src/torus_frontier.c tests/test_torus.c -o build/test_torus_san
	$(CC) $(SAN_FLAGS) src/torus_frontier.c tests/fuzz_torus.c -o build/fuzz_torus_san
	./build/test_torus_san
	./build/fuzz_torus_san 25000

fuzz: build/fuzz_torus
	./build/fuzz_torus 100000

libfuzzer: src/torus_frontier.c tests/libfuzzer_torus.c include/torus_frontier.h | build
	clang -std=c11 -O1 -g -Wall -Wextra -Wpedantic -Werror -fsanitize=fuzzer,address,undefined -Iinclude src/torus_frontier.c tests/libfuzzer_torus.c -o build/libfuzzer_torus
	./build/libfuzzer_torus -max_total_time=10

clean:
	rm -rf build
