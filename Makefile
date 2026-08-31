.PHONY: build run lib update

# Library: check every example, theorem and lemma (pulls in Mathlib).
lib:
	@lake build Examples

# Executable only. `Main` imports just `Examples.Hello`, so Mathlib is not linked.
build:
	@lake build exec

# Build and run the executable.
run: build
	@lake exe exec

# Refresh dependencies and the prebuilt Mathlib cache.
update:
	@lake update
	@lake exe cache get
