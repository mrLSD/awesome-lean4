[![Lean Action CI](https://github.com/mrLSD/awesome-lean4/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/mrLSD/awesome-lean4/actions/workflows/lean_action_ci.yml)

# Awesome Lean 4

A small, self-contained playground for learning [Lean 4](https://lean-lang.org) and
[Mathlib](https://github.com/leanprover-community/mathlib4).

The repository contains two things:

- a **library** of worked tactic exercises, each one annotated with a short explanation;
- a **tiny executable**, so the project also shows how a runnable Lean program is wired up.

There is no separate test suite. In Lean, compiling *is* the test: if `make lib` finishes
without errors, every `example`, theorem and lemma in the repository has been proved.

---

## Getting started

Four steps, roughly ten minutes, most of it downloading.

### 1. Install Lean

You never install Lean directly. You install **elan**, a version manager (the Lean
equivalent of `rustup` or `nvm`). It reads the `lean-toolchain` file in this repository
and downloads exactly the version the project pins — currently **Lean 4.33.1**.

macOS and Linux:

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

Windows (PowerShell):

```powershell
curl.exe -sSf -o elan-init.ps1 https://elan.lean-lang.org/elan-init.ps1
.\elan-init.ps1
```

Restart your shell afterwards so that `~/.elan/bin` lands on `PATH`, then check:

```bash
elan --version
```

That is all the setup Lean needs. The first Lean command you run inside this folder
installs the pinned toolchain automatically.

### 2. Install the VS Code extension

In VS Code open **Extensions**, search for `lean4`, and install **Lean 4** (publisher
`leanprover`).

> **Open this folder as the workspace root** — the folder that contains `lakefile.toml`.
> If you open a parent folder instead, the extension starts a Lean server that knows
> nothing about the project's dependencies and every `import` turns red.

Two commands are worth remembering (`Cmd`/`Ctrl` + `Shift` + `P`):

| Command | When you need it |
| --- | --- |
| `Lean 4: Server: Restart Server` | After changing dependencies or the Lean version |
| `Lean 4: Server: Restart File` | When a single file gets stuck |

The **Lean Infoview** panel on the right shows the proof state wherever your cursor is:
hypotheses on top, and the goal after the `⊢` symbol.

### 3. Download the dependencies

```bash
make update
```

This fetches Mathlib and its dependencies, then downloads **prebuilt** Mathlib binaries
(~700 MB) so that you never have to compile Mathlib yourself. Expect a few minutes and
several gigabytes under `.lake/`, which is git-ignored.

### 4. Build it

```bash
make lib     # check every proof in the repository
make run     # build and run the executable
```

If both are green, you are set up correctly.

---

## Make commands

| Command | What it does | Typical time |
| --- | --- | --- |
| `make lib` | Builds the `Examples` library — **this is what verifies all the proofs** | ~40 s |
| `make build` | Builds the `exec` binary only | ~1 s |
| `make run` | `make build`, then runs it (prints `Hello, world!`) | ~4 s |
| `make update` | Re-resolves dependencies and refreshes the Mathlib cache | minutes |

Each target is a thin wrapper over [Lake](https://github.com/leanprover/lean4/tree/master/src/lake),
Lean's build tool — `make lib` is just `lake build Examples`. Use `lake` directly whenever
you need something finer-grained, for example `lake build Examples.Rewrite` for a single
module.

---

## Project structure

```
.
├── lakefile.toml         project definition: build targets + dependencies
├── lean-toolchain        the exact Lean version, read by elan
├── lake-manifest.json    lock file: exact revisions of Mathlib and friends
├── Makefile              thin wrapper over lake
│
├── Examples.lean         root module of the library — imports every submodule
├── Examples/
│   ├── Rewrite.lean      rewriting tactics: rw, rewrite, nth_rw, calc (imports Mathlib)
│   ├── Theorems.lean     the MyNat type and named lemmas, from the Natural Number Game
│   ├── Succ.lean         those lemmas in use: rewriting numerals both ways
│   └── Hello.lean        runtime code for the binary (deliberately no Mathlib)
├── Main.lean             entry point of the executable
│
└── .lake/                build output and downloaded dependencies (git-ignored)
```

### Why it looks like this

**A file's path *is* its module name.** Lean maps the module `Examples.Rewrite` to the
file `Examples/Rewrite.lean` — the dot is a directory separator. There is no `mod`
declaration as in Rust and no list of source files in the build config: rename a folder,
and every `import` naming it breaks.

**`Examples.lean` is the root of the library.** `lakefile.toml` declares
`[[lean_lib]] name = "Examples"`, and Lake derives the root module from that target name,
so it expects a file called `Examples.lean` beside the lakefile. That file imports the
submodules, and *that import is what puts them into the build* — Lake compiles the root
module plus whatever it transitively imports, nothing else.

> **Adding a new exercise file? Add an `import` for it to `Examples.lean`.**
> A file nobody imports is silently skipped, and `make lib` will report success without
> ever having looked at it.

**`Examples/Hello.lean` avoids Mathlib on purpose.** `Main.lean` imports only that module.
Linking an executable requires native object files for *everything* it imports, and
producing those for the whole of Mathlib takes hours. Keeping Mathlib off `Main`'s import
path is what keeps `make run` at a few seconds, while `make lib` still checks the
Mathlib-heavy exercises.

**Namespaces are a separate concept from modules.** Importing a module does not qualify
its names, so without namespaces every definition would land next to Mathlib's many
thousands of global names. Each file therefore opens its own: `Examples`,
`Examples.Hello`, `Examples.Rewrite`, `Examples.Theorems`, `Examples.Succ`. Names are
then pulled in explicitly:

```lean
open Examples.Hello (hello)   -- the equivalent of Rust's `use Examples::Hello::hello`
```

### Adding your own exercises

1. Create `Examples/Induction.lean`.
2. Start it with `import Mathlib`, then `namespace Examples.Induction` … `end Examples.Induction`.
3. Add `import Examples.Induction` to `Examples.lean`.
4. Run `make lib`.

Comments in this repository are written in English, and each example carries a two- or
three-line note explaining what the tactic does and which detail the example exists to
demonstrate.

---

## Troubleshooting

| Symptom | Cause and fix |
| --- | --- |
| `unknown module prefix 'Examples'` | The module belongs to no build target. Check that the file path matches the module name and that `Examples.lean` imports it. |
| Imports are red in VS Code, but `make lib` is green | Stale language server — run `Lean 4: Server: Restart Server`. |
| Everything is red and the search path in the error is short | VS Code was opened above the project root. Open the folder containing `lakefile.toml`. |
| `lake build` starts compiling thousands of Mathlib files | The prebuilt cache is missing or stale — run `make update`. |

> **Do not run bare `lake clean`.** With no arguments it deletes the build outputs of
> *every* package in the workspace, Mathlib included, costing you the whole download.
> To clean only this project, use `rm -rf .lake/build`.

---

## Where to learn more

- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) — the standard introduction
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) — hands-on, Mathlib-first
- [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/) — searchable API reference
- [Lean documentation hub](https://lean-lang.org/documentation/) — language manual and guides

## License

Distributed under the [MIT License](LICENSE).
