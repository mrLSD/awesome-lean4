# Project instructions

## Scope

These instructions apply to the entire repository. Keep changes small, focused,
and consistent with this project as an educational Lean 4 codebase.

Repository comments and documentation are written in English. User-facing
communication may follow the user's language.

## Project map

- `Examples.lean` is the root of the `Examples` library. A new module is not
  checked by `make lib` until this file imports it.
- `Examples/*.lean` contains the tutorial modules and proofs.
- `Examples/Theorems.lean` intentionally rebuilds Peano naturals and addition
  without Mathlib. Do not add a Mathlib import there.
- `Examples/Hello.lean` and `Main.lean` intentionally avoid Mathlib so the
  executable remains fast to build and link.
- `Main.lean` is the executable entry point.
- `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin the toolchain
  and dependencies. Do not upgrade or regenerate them unless explicitly asked.

## Working method

1. Read the relevant modules and check `git status --short` before editing.
2. Preserve all user changes and avoid unrelated cleanup or reformatting.
3. Make the smallest coherent change that satisfies the request.
4. Run the narrowest useful check while iterating.
5. Run every required final gate for the affected area.
6. Check whether source or project changes made any relevant README statement
   inaccurate, contradictory, or materially incomplete; update it when they did.
7. Inspect `git diff`, run `git diff --check`, and report the exact checks run.

Do not create temporary source files inside the repository. Use `/tmp` for
isolated experiments and remove those files after the check.

Keep `README.md` synchronized with the behavior, commands, structure, versions,
and setup it documents. Update it in the same task when a code or project change
makes that information incorrect or misleading. Do not edit the README merely
because source files changed, and do not add implementation details or unrelated
material outside the README's existing purpose and audience.

## Required gates

Compilation is the test suite: every theorem must elaborate without placeholders.
A narrow check is useful during development but does not replace the final gate.

### Library changes

For changes to `Examples.lean` or `Examples/*.lean`:

```sh
lake env lean path/to/ChangedModule.lean
make lib
```

`make lib` is the required final library gate and matches CI's
`lake build Examples`. If a new module was added, verify that `Examples.lean`
imports it before trusting this gate.

### Executable changes

For changes to `Main.lean`:

```sh
make build
make run
```

For changes to `Examples/Hello.lean`, run both the library and executable gates:

```sh
make lib
make build
make run
```

`make run` is required when runtime output or behavior can change. `make build`
alone is sufficient only for a compile-only executable change.

### Configuration and dependency changes

For intentional changes to `lakefile.toml`, `lean-toolchain`, or the manifest,
run all affected library and executable gates. Run `make update` only when the
user explicitly requests a dependency refresh or upgrade; it mutates dependency
state and downloads the Mathlib cache.

### Documentation-only changes

For changes limited to Markdown or agent instructions:

```sh
git diff --check
```

Comments inside `.lean` files are not Markdown-only changes: Lean must still
parse the file, so run the corresponding Lean gates.

### Final repository checks

Always finish with:

```sh
git diff --check
git status --short
```

Review the complete diff and do not introduce new warnings. Never run bare
`lake clean`; it removes dependency build outputs, including Mathlib's cache.

## Lean 4 development rules

- Use the repository-pinned Lean and Mathlib versions through `lake`.
- Keep imports minimal. Do not import Mathlib to solve a theorem intended to use
  only core Lean or declarations already defined in the module.
- Put declarations in the module's namespace. Prefer qualified names or
  selective `open Namespace (name)` when broad `open` risks ambiguity.
- Prefer structural recursion that makes termination evident to Lean.
- Use `rfl` exactly for definitional equality. Use named lemmas, `rw`, `calc`,
  or explicit induction when the equality is propositional rather than
  definitional.
- Prefer stable, explicit proofs. Use `simp only [...]` when a fixed rewrite set
  is sufficient; avoid broad `simp`, `aesop`, `omega`, or similar automation in
  tutorial proofs unless automation is the subject of the example.
- Preserve the pedagogical distinction between unfolding, rewriting, and
  induction. Do not shorten a proof if doing so hides the concept being taught.
- Reuse existing definitions and lemmas instead of duplicating logic.
- Keep theorem statements and public declaration names stable unless the task
  explicitly requires an API change. Check downstream imports after any rename.
- Do not leave `sorry`, `admit`, `by?`, unfinished goals, disabled checks, or
  warning-suppression options in project source. Do not replace a proof with
  an axiom or an `unsafe` escape hatch.
- Keep formatting consistent: spaces around `:`, one declaration per logical
  block, and no incidental whole-file formatting.

## Documentation comments

- Use module documentation comments `/-! ... -/` for a module's purpose and
  high-level context.
- Use declaration documentation comments `/-- ... -/` immediately above named
  `def`, `theorem`, `lemma`, `inductive`, `structure`, `class`, and relevant
  `instance` declarations. A plain `--` comment is not a substitute for API
  documentation.
- Keep declaration docs concise and informative: normally one sentence and one
  or two source lines. State the contract, meaning, recursion argument, or one
  essential proof distinction.
- Do not repeat the declaration verbatim, narrate obvious syntax, or turn a doc
  comment into a tutorial. Put broader motivation in the module doc or README.
- Use ordinary `--` comments for implementation and proof traces only.
- Put a code comment before the line it describes. Do not use trailing comments
  or place a proof-state comment after the tactic that produced it.
- Remove prose that does not change the reader's understanding. Brevity must not
  omit a semantically relevant reduction, hypothesis, or goal transition.

## Full unfold traces in comments

Tutorial comments that explain evaluation or a proof step must show the full,
compact reduction chain. This is a documentation rule; it does not require use
of Lean's `unfold` tactic.

- Start with the expression or complete goal visible in the source.
- Show every semantically relevant project-local layer in order: operation
  notation, local definitions, the selected recursive equation, local lemmas,
  and induction hypotheses.
- Treat numeral decoding as implementation noise. Keep a natural literal as
  `0`; when the constructor matters, write the direct step
  `0` → `MyNat.zero`. Do not insert `OfNat` or `MyNat.ofNat` into a trace unless
  the code being documented is the numeral-decoding implementation itself.
- Expand project-local operations when relevant, for example
  `m + n` → `MyNat.add m n`.
- End at the resulting goal or reflexive equality. Use `⊢` for a goal state
  when it improves clarity.
- Omit kernel implementation noise, standard class projections, and numeral
  decoding outside its own implementation. Apart from this numeral exception,
  include all relevant declarations defined by this project.
- Write chains as expressions separated by `→`; avoid explanatory prose such
  as "this now proves" or "Lean calls" inside the trace.
- Keep the chain complete even when `rfl` or `rw` closes the goal automatically.

Place an `rfl` trace before `rfl`, including pattern branches:

```lean
-- `m + 0 = m`
-- → `MyNat.add m MyNat.zero = m`
-- → `m = m`
rfl
```

For pattern matching, put the trace above the matching branch, never below it:

```lean
-- `0 + 0 = 0`
-- → `MyNat.add MyNat.zero MyNat.zero = MyNat.zero`
-- → `MyNat.zero = MyNat.zero`
| zero => rfl
```

If a compact proof combines rewrites, split it into one rewrite per line. An
optional summary may remain above the branch, but every individual rewrite must
have its own preceding unfold/result trace and show the complete resulting goal:

```lean
-- `rw [add_succ, ih]`
| succ n ih =>
  -- `add_succ 0 n`: `0 + MyNat.succ n = MyNat.succ (0 + n)`
  -- → `MyNat.add MyNat.zero (MyNat.succ n)`
  --   `= MyNat.succ (MyNat.add MyNat.zero n)`
  -- → `MyNat.succ (MyNat.add MyNat.zero n)`
  --   `= MyNat.succ (MyNat.add MyNat.zero n)`
  -- `⊢ MyNat.succ (0 + n) = MyNat.succ n`
  rw [add_succ]
  -- `ih`: `0 + n = n`
  -- → `MyNat.add MyNat.zero n = n`
  -- `⊢ MyNat.succ n = MyNat.succ n`
  rw [ih]
```

Apply the same rule to `simp`, `calc`, induction, and other combined proof steps
when the file is teaching the intermediate reasoning. Prefer the shortest trace
that is still complete.

## Git and workspace safety

- Never run `git commit`, `git push`, `git tag`, or create/publish a pull request.
  Leave repository publication and history changes to the user.
- Do not stage changes with `git add`.
- Do not run `git pull`, `git merge`, `git rebase`, `git cherry-pick`,
  `git revert`, `git reset`, `git checkout`, `git switch`, or `git stash`.
- Do not delete branches, tags, tracked files, user changes, or untracked work.
- Read-only Git commands such as `git status`, `git diff`, `git log`, and
  `git show` are allowed and encouraged for inspection.
- Treat a dirty worktree as user-owned state. Modify only files required by the
  task, preserve overlapping edits, and report unrelated changes without
  altering them.
- Do not edit `.gitignore` merely to hide generated or unexplained files. Do not
  add `.lake` build artifacts or editor metadata to the repository.

## Completion criteria

A task is complete only when the requested behavior is implemented, relevant
proofs compile without placeholders, required gates pass, the final diff is
focused, and the handoff names both changed files and checks run. If a gate
cannot run, report the exact blocker and do not claim completion.
