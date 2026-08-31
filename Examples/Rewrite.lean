import Mathlib

-- Exercises on the rewriting tactics: `rw`, `rewrite`, `nth_rw`, `nth_rewrite`
-- and `calc`. Everything lives in `Examples.Rewrite`, so these names never
-- collide with Mathlib's root namespace.
namespace Examples.Rewrite

-- `rw` rewrites left-to-right and then tries `rfl` to finish the goal.
-- Supplying the arguments (`b c a`) pins the lemma instance, so the rewrite
-- lands on the intended subterm instead of the first syntactic match.
example (a b c : Nat) : b + c + a = b + (a + c) := by
  rw [Nat.add_assoc b c a]
  rw [Nat.add_comm a c]

-- `repeat` reapplies a tactic until it fails: `Nat.add_zero` strips `+ 0`
-- twice here. One `rw` call rewrites every occurrence it can match at once,
-- which is why the two zeros need two passes rather than one.
example (a b: Nat): a + (b + 0) + 0 = a + b := by
  repeat rw [Nat.add_zero]

-- The same goal written as an explicit `calc` chain. Each `_` stands for the
-- previous right-hand side, so every intermediate term is visible in the proof.
-- Verbose compared to `repeat`, but it documents the reasoning step by step.
example (a b: Nat): a + (b + 0) + 0 = a + b := by
  calc
    a + (b + 0) + 0 = a + (b + 0) := by
      rw [Nat.add_zero]
    _ = a + b := by
      rw [Nat.add_zero]

-- Associativity first, then commutativity on the inner sum. `Nat.add_comm c a`
-- names its operands to fix the rewrite direction: without them the tactic
-- could just as well swap the outer sum and loop back to the start.
example (a b c : Nat) : b + c + a = b + (a + c) := by
  calc
    (b + c) + a = b + (c + a) := by
      rw [Nat.add_assoc]
    _ = (b + (a + c)) := by
      rw [Nat.add_comm c a]

-- `rw ... at h` rewrites inside a hypothesis instead of the goal.
-- `h₁ : x = y + 3` turns `h₂ : 2 * y = x` into `2 * y = y + 3`, which `exact`
-- then hands to the goal unchanged.
example (x y : Nat)
  (h₁ : x = y + 3)
  (h₂ : 2 * y = x) : 2 * y = y + 3 := by
    rw [h₁] at h₂
    exact h₂

-- `←` flips the equation and rewrites right-to-left: `x` becomes `2 * y`.
-- Same conclusion as above, but reached by editing `h₁` instead of `h₂` —
-- the direction of the arrow decides which hypothesis gets rewritten.
example (x y : Nat)
  (h₁ : x = y + 3)
  (h₂ : 2 * y = x) : 2 * y = y + 3 := by
    rw [← h₂] at h₁
    exact h₁

-- `at` says WHERE to rewrite. A bare `rw [hn]` changes only the goal, whereas
-- `rw [hn] at h₁ h₂` changes those two hypotheses instead of it. `⊢` is simply
-- how Lean writes "the goal": it is the turnstile printed in front of the goal
-- in the info view, so `at h₁ h₂ ⊢` reads "in both hypotheses and in the goal".
-- That is what carries this proof: without `⊢` the goal keeps its `n` and the
-- last step stalls at `21 + 4 + n = 28`, which is not an identity.
-- The list is strict, too: a location without the pattern aborts the whole
-- call; `at *` tolerates it but degrades `hn` itself into a useless `3 = 3`.
example (n price total : Nat)
    (hn : n = 3)
    (h₁ : price * n = 21)
    (h₂ : total = price * n + 4) :
    total + n = 28 := by
  rw [hn] at h₁ h₂ ⊢
  -- h₁ : price * 3 = 21   h₂ : total = price * 3 + 4   ⊢ total + 3 = 28
  rw [h₁] at h₂
  -- h₂ : total = 21 + 4 — a freshly rewritten hypothesis feeds the next rewrite
  rw [h₂]
  -- ⊢ 21 + 4 + 3 = 28, closed by the `rfl` that `rw` always tries at the end

-- Transitivity spelled out: `2 * y = x` from `h₂`, then `x = y + 3` from `h₁`.
-- `calc` stitches the steps together, and each step is justified by its own
-- tactic block.
example (x y : Nat)
  (h₁ : x = y + 3)
  (h₂ : 2 * y = x) : 2 * y = y + 3 := by
  calc
    2 * y = x := by
      exact h₂
    _ = y + 3 := by
      exact h₁

-- The same chain, but each step is given as a proof term rather than a tactic
-- block: `h₂` already *is* a proof of `2 * y = x`. Dropping `by exact` is the
-- idiomatic form whenever the justification is a hypothesis or lemma name.
example (x y : Nat)
  (h₁ : x = y + 3)
  (h₂ : 2 * y = x) : 2 * y = y + 3 := by
  calc
    2 * y = x := h₂
    _ = y + 3 := h₁

-- `nth_rw n` rewrites only the n-th occurrence, counted left to right across
-- the whole goal: in `(a + c) * (a + a) + a = ...` the 3rd `a` is the second
-- one inside `(a + a)`. Like `rw`, it closes the goal with `rfl`.
example (a b c : Nat) (h : a = b) :
    (a + c) * (a + a) + a = (a + c) * (a + b) + a := by
    nth_rw 3 [h]

-- `nth_rewrite` is the `rewrite`-flavoured twin: identical occurrence
-- selection, but it never attempts `rfl`, so the goal has to be closed by
-- hand. Same relationship as between `rewrite` and `rw`.
example (a b c : Nat) (h : a = b) :
    (a + c) * (a + a) + a = (a + c) * (a + b) + a := by
    nth_rewrite 3 [h]
    rfl

end Examples.Rewrite
