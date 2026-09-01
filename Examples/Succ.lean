import Examples.Theorems

/-!
# Rewriting numerals in both directions

The lemmas proved in `Examples.Theorems` are equalities, and every equality is a
rewrite rule that works both ways. This file proves one and the same goal twice
to show the difference between the two directions of `rw`.
-/

namespace Examples.Succ

-- `MyNat` and both lemmas live in `Examples.Theorems`. `open` pulls their short
-- names into scope; without it every mention needs the full `Theorems.` prefix,
-- and a bare `MyNat` does not resolve at all.
open Examples.Theorems

/-- Forward direction: numerals are taken apart into `succ`s.

`rw [h]` replaces the left-hand side of `h` by its right-hand side, so `2`
becomes `succ 1` and then `1` becomes `succ 0`, until both sides of the goal
match and the `rfl` that `rw` always tries at the end closes it. -/
example : (2 : MyNat) = MyNat.succ (MyNat.succ 0) := by
  rw [two_eq_succ_one]
  -- ⊢ MyNat.succ 1 = MyNat.succ (MyNat.succ 0)
  rw [one_eq_succ_zero]

/-- Reverse direction: `succ` chains are folded back into numerals.

`rw [← h]` rewrites right-to-left, so the very same two lemmas apply in the
opposite order — `succ 0` becomes `1`, then `succ 1` becomes `2` — and the goal
ends up as `2 = 2`. Same goal, same lemmas, mirrored steps. -/
example : (2 : MyNat) = MyNat.succ (MyNat.succ 0) := by
  rw [← one_eq_succ_zero]
  -- ⊢ 2 = MyNat.succ 1
  rw [← two_eq_succ_one]

end Examples.Succ
