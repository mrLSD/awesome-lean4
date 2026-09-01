import Examples.Theorems

/-!
# Rewriting numerals in both directions

Changing the direction of `rw` makes the same lemmas expand or fold numerals.
-/
namespace Examples.Succ

-- Brings `MyNat` and its numeral lemmas into scope.
open Examples.Theorems

-- Expands `2` to two successors with forward rewrites.
example : (2 : MyNat) = MyNat.succ (MyNat.succ 0) := by
  -- `2` →[two_eq_succ_one] `MyNat.succ 1`
  -- `⊢ MyNat.succ 1 = MyNat.succ (MyNat.succ 0)`
  rw [two_eq_succ_one]
  -- `1` →[one_eq_succ_zero] `MyNat.succ 0`
  -- `⊢ MyNat.succ (MyNat.succ 0) = MyNat.succ (MyNat.succ 0)`
  rw [one_eq_succ_zero]

-- Folds two successors back to `2` with reverse rewrites.
example : (2 : MyNat) = MyNat.succ (MyNat.succ 0) := by
  -- `MyNat.succ 0` →[← one_eq_succ_zero] `1`
  -- `⊢ 2 = MyNat.succ 1`
  rw [← one_eq_succ_zero]
  -- `MyNat.succ 1` →[← two_eq_succ_one] `2`
  -- `⊢ 2 = 2`
  rw [← two_eq_succ_one]

end Examples.Succ
