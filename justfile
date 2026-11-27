# SPDX-License-Identifier: Apache-2.0
set shell := ["bash", "-euo", "pipefail", "-c"]

default:
	@just --list

lean:
	cd lean && lake build && lake build PalomarChallenge
	cd lean && lake env lean VerifyAxioms.lean > ../results/lean_axioms.txt
	cd lean && lake env leanchecker --fresh PalomarSolution
	cd lean && lake env leanchecker-paranoid --fresh PalomarSolution

lean-6k:
	cd lean && lake check --paranoid && lake comparator --config comparator.json --paranoid

rust:
	cd rust && cargo clippy --all-targets -- -D warnings && cargo test --release && cargo run --release -- --verify-all

zig:
	cd zig && zig test src/main.zig && zig build-exe -OReleaseSafe src/main.zig -femit-bin=zig-out/qpr_zig && ./zig-out/qpr_zig --verify-all

cpp:
	cd cpp && make test && ./build/qpr_cpp --verify-all

c-asm:
	cd c && make test && ./build/qpr_c --verify-all

eshkol:
	python3 eshkol/run_eshkol_ad.py --verify-all

python-test:
	PYTHONPATH=src:. pytest -v tests/test_all.py
	python3 scripts/check_readme_axioms.py
	python3 scripts/check_citations.py

mutate:
	python3 scripts/mutate.py

figures:
	python3 scripts/generate_figures.py

paper:
	mkdir -p paper/build
	tectonic -X compile paper/main.tex --outdir paper/build --keep-logs

blueprint:
	python3 scripts/build_blueprint.py

audit:
	bash scripts/audit-repo.sh .

verify-all: lean rust zig cpp c-asm eshkol python-test

reproduce: verify-all mutate figures paper blueprint audit
