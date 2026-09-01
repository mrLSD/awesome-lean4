import Mathlib

/-!
# Rewriting equalities

Focused examples of `rw`, `calc`, `nth_rw`, and `nth_rewrite`.
-/
namespace Examples.Rewrite

-- Rewrites associativity on the left, then commutativity on the right.
example (a b c : Nat) : b + c + a = b + (a + c) := by
  -- `(b + c) + a` →[Nat.add_assoc b c a] `b + (c + a)`
  -- `⊢ b + (c + a) = b + (a + c)`
  rw [Nat.add_assoc b c a]
  -- `a + c` →[Nat.add_comm a c] `c + a`
  -- `⊢ b + (c + a) = b + (c + a)`
  rw [Nat.add_comm a c]

-- Repeats `Nat.add_zero` until both trailing zeros are removed.
example (a b : Nat) : a + (b + 0) + 0 = a + b := by
  -- `a + (b + 0) + 0 = a + b` → `a + (b + 0) = a + b`
  -- → `a + b = a + b`
  repeat rw [Nat.add_zero]

-- Makes both `Nat.add_zero` rewrites explicit in a `calc` chain.
example (a b : Nat) : a + (b + 0) + 0 = a + b := by
  calc
    a + (b + 0) + 0 = a + (b + 0) := by
      -- `a + (b + 0) + 0 = a + (b + 0)`
      -- → `a + (b + 0) = a + (b + 0)`
      rw [Nat.add_zero]
    _ = a + b := by
      -- `a + (b + 0) = a + b` → `a + b = a + b`
      rw [Nat.add_zero]

-- Makes associativity and the selected commutativity rewrite explicit.
example (a b c : Nat) : b + c + a = b + (a + c) := by
  calc
    (b + c) + a = b + (c + a) := by
      -- `(b + c) + a = b + (c + a)` → `b + (c + a) = b + (c + a)`
      rw [Nat.add_assoc]
    _ = b + (a + c) := by
      -- `c + a = a + c`
      -- →[Nat.add_comm c a] `a + c = a + c`
      rw [Nat.add_comm c a]

-- Rewrites `h₂` forward with `h₁`, then uses the resulting hypothesis.
example (x y : Nat)
    (h₁ : x = y + 3)
    (h₂ : 2 * y = x) : 2 * y = y + 3 := by
  -- `h₂ : 2 * y = x` →[h₁] `h₂ : 2 * y = y + 3`
  -- `⊢ 2 * y = y + 3`
  rw [h₁] at h₂
  -- `h₂ : 2 * y = y + 3` → `⊢ 2 * y = y + 3`
  exact h₂

-- Rewrites `h₁` backward with `h₂`, then uses the resulting hypothesis.
example (x y : Nat)
    (h₁ : x = y + 3)
    (h₂ : 2 * y = x) : 2 * y = y + 3 := by
  -- `h₁ : x = y + 3` →[← h₂] `h₁ : 2 * y = y + 3`
  -- `⊢ 2 * y = y + 3`
  rw [← h₂] at h₁
  -- `h₁ : 2 * y = y + 3` → `⊢ 2 * y = y + 3`
  exact h₁

-- Rewrites one equality across selected hypotheses and the goal.
example (n price total : Nat)
    (hn : n = 3)
    (h₁ : price * n = 21)
    (h₂ : total = price * n + 4) :
    total + n = 28 := by
  -- `n` →[hn] `3` in `h₁`, `h₂`, and `⊢`
  -- `h₁ : price * 3 = 21`; `h₂ : total = price * 3 + 4`
  -- `⊢ total + 3 = 28`
  rw [hn] at h₁ h₂ ⊢
  -- `price * 3` →[h₁] `21` in `h₂`
  -- `h₂ : total = 21 + 4`; `⊢ total + 3 = 28`
  rw [h₁] at h₂
  -- `total` →[h₂] `21 + 4`
  -- `⊢ 21 + 4 + 3 = 28` → `25 + 3 = 28` → `28 = 28`
  rw [h₂]

-- Expresses transitivity with tactic proofs for both `calc` steps.
example (x y : Nat)
    (h₁ : x = y + 3)
    (h₂ : 2 * y = x) : 2 * y = y + 3 := by
  calc
    2 * y = x := by
      -- `h₂ : 2 * y = x` → `⊢ 2 * y = x`
      exact h₂
    _ = y + 3 := by
      -- `h₁ : x = y + 3` → `⊢ x = y + 3`
      exact h₁

-- Expresses the same transitivity directly with proof terms.
example (x y : Nat)
    (h₁ : x = y + 3)
    (h₂ : 2 * y = x) : 2 * y = y + 3 := by
  calc
    -- `h₂ : 2 * y = x`
    2 * y = x := h₂
    -- `h₁ : x = y + 3`
    _ = y + 3 := h₁

-- Rewrites only the third occurrence of `a` and closes by reflexivity.
example (a b c : Nat) (h : a = b) :
    (a + c) * (a + a) + a = (a + c) * (a + b) + a := by
  -- occurrence 3: `a` →[h] `b` in the right operand of the left-side `a + a`
  -- `⊢ (a + c) * (a + b) + a = (a + c) * (a + b) + a`
  nth_rw 3 [h]

-- Performs the same selected rewrite without automatic reflexivity.
example (a b c : Nat) (h : a = b) :
    (a + c) * (a + a) + a = (a + c) * (a + b) + a := by
  -- occurrence 3: `a` →[h] `b` in the right operand of the left-side `a + a`
  -- `⊢ (a + c) * (a + b) + a = (a + c) * (a + b) + a`
  nth_rewrite 3 [h]
  -- `(a + c) * (a + b) + a = (a + c) * (a + b) + a`
  rfl

end Examples.Rewrite
