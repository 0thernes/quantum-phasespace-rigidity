# SPDX-License-Identifier: Apache-2.0
CXX ?= g++
CXXFLAGS := -std=c++20 -O2 -Wall -Wextra -Werror -pedantic
BUILD_DIR := build

ifeq ($(OS),Windows_NT)
  EXE := .exe
else
  EXE :=
endif

.PHONY: all test sanitize clean

all: $(BUILD_DIR)/qpr_cpp$(EXE)

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

$(BUILD_DIR)/qpr_cpp$(EXE): src/qpr_cyclotomic.cpp | $(BUILD_DIR)
	$(CXX) $(CXXFLAGS) -o $@ $<

test: all
	./$(BUILD_DIR)/qpr_cpp$(EXE) --verify-all

sanitize: | $(BUILD_DIR)
	$(CXX) -std=c++20 -O1 -g -Wall -Wextra -Werror -fsanitize=address,undefined -o $(BUILD_DIR)/qpr_cpp_san$(EXE) src/qpr_cyclotomic.cpp
	./$(BUILD_DIR)/qpr_cpp_san$(EXE) --verify-all

clean:
	rm -rf $(BUILD_DIR)
