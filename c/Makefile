# SPDX-License-Identifier: Apache-2.0
CC ?= gcc
NASM ?= nasm
CFLAGS := -std=c11 -O2 -Wall -Wextra -Werror -Iinclude
MOON_CFLAGS := -std=c11 -D_DEFAULT_SOURCE -O2 -Wall -Wextra -Ithird_party/moonlab -Ithird_party/moonlab/applications
LDFLAGS := -lm
BUILD_DIR := build

ifeq ($(OS),Windows_NT)
  EXE := .exe
  NASM_FLAGS := -f win64 -DWIN64
else
  EXE :=
  NASM_FLAGS := -f elf64
endif

MOON_OBJS := $(BUILD_DIR)/sha3.o $(BUILD_DIR)/aes.o $(BUILD_DIR)/ctr_drbg.o $(BUILD_DIR)/health_tests.o
CORE_OBJS := $(BUILD_DIR)/qpr_core.o $(BUILD_DIR)/qgtl_metric.o $(BUILD_DIR)/qrng_fw.o
ASM_OBJ := $(BUILD_DIR)/pauli_popcnt.o

.PHONY: all test sanitize fuzz clean

all: $(BUILD_DIR)/qpr_c$(EXE)

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

$(ASM_OBJ): ../asm/pauli_popcnt.asm | $(BUILD_DIR)
	$(NASM) $(NASM_FLAGS) -o $@ $<

$(BUILD_DIR)/sha3.o: third_party/moonlab/crypto/sha3/sha3.c | $(BUILD_DIR)
	$(CC) $(MOON_CFLAGS) -c -o $@ $<

$(BUILD_DIR)/aes.o: third_party/moonlab/crypto/aes/aes.c | $(BUILD_DIR)
	$(CC) $(MOON_CFLAGS) -c -o $@ $<

$(BUILD_DIR)/ctr_drbg.o: third_party/moonlab/crypto/drbg/ctr_drbg.c | $(BUILD_DIR)
	$(CC) $(MOON_CFLAGS) -c -o $@ $<

$(BUILD_DIR)/health_tests.o: third_party/moonlab/applications/health_tests.c | $(BUILD_DIR)
	$(CC) $(MOON_CFLAGS) -c -o $@ $<

$(BUILD_DIR)/qpr_core.o: src/qpr_core.c include/qpr_c.h | $(BUILD_DIR)
	$(CC) $(CFLAGS) -c -o $@ $<

$(BUILD_DIR)/qgtl_metric.o: src/qgtl_metric.c include/qpr_c.h | $(BUILD_DIR)
	$(CC) $(CFLAGS) -c -o $@ $<

$(BUILD_DIR)/qrng_fw.o: src/qrng_fw.c include/qpr_c.h | $(BUILD_DIR)
	$(CC) $(CFLAGS) -c -o $@ $<

$(BUILD_DIR)/qpr_c$(EXE): src/main.c $(CORE_OBJS) $(MOON_OBJS) $(ASM_OBJ) | $(BUILD_DIR)
	$(CC) $(CFLAGS) -o $@ src/main.c $(CORE_OBJS) $(MOON_OBJS) $(ASM_OBJ) $(LDFLAGS)

$(BUILD_DIR)/fuzz_qpr$(EXE): tests/fuzz_qpr.c $(ASM_OBJ) | $(BUILD_DIR)
	$(CC) $(CFLAGS) -o $@ tests/fuzz_qpr.c $(ASM_OBJ)

test: all $(BUILD_DIR)/fuzz_qpr$(EXE)
	./$(BUILD_DIR)/qpr_c$(EXE) --verify-all
	./$(BUILD_DIR)/fuzz_qpr$(EXE) 100000

fuzz: $(BUILD_DIR)/fuzz_qpr$(EXE)
	./$(BUILD_DIR)/fuzz_qpr$(EXE) 250000

sanitize: | $(BUILD_DIR)
	$(CC) -std=c11 -D_DEFAULT_SOURCE -O1 -g -Wall -Wextra -Werror -DQPR_NO_ASM -fsanitize=address,undefined -Iinclude -Ithird_party/moonlab -Ithird_party/moonlab/applications \
	  -o $(BUILD_DIR)/qpr_c_san$(EXE) src/main.c src/qpr_core.c src/qgtl_metric.c src/qrng_fw.c \
	  third_party/moonlab/crypto/sha3/sha3.c third_party/moonlab/crypto/aes/aes.c \
	  third_party/moonlab/crypto/drbg/ctr_drbg.c third_party/moonlab/applications/health_tests.c $(LDFLAGS)
	./$(BUILD_DIR)/qpr_c_san$(EXE) --verify-all

clean:
	rm -rf $(BUILD_DIR)
