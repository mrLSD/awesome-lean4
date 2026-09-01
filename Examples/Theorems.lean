/-!
# The natural numbers, rebuilt from scratch

Peano naturals, numerals, addition, and its basic laws, without Mathlib. Built-in
`Nat` is used only to decode literals, following the
[Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4).
-/
namespace Examples.Theorems

/-- A Peano natural is either zero or the successor of another natural. -/
inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat
  deriving Repr, DecidableEq

/-- Converts a built-in `Nat` to its Peano representation. -/
def MyNat.ofNat : Nat → MyNat
  -- `MyNat.ofNat Nat.zero` → `MyNat.zero`
  | Nat.zero => MyNat.zero
  -- `MyNat.ofNat (Nat.succ n)` → `MyNat.succ (MyNat.ofNat n)`
  | Nat.succ n => MyNat.succ (MyNat.ofNat n)

/-- Interprets every natural-number literal through `MyNat.ofNat`. -/
instance (n : Nat) : OfNat MyNat n := ⟨MyNat.ofNat n⟩

/-- Adds two naturals by recursion on the second argument. -/
def MyNat.add : MyNat → MyNat → MyNat
  -- `MyNat.add m MyNat.zero` → `m`
  | m, .zero => m
  -- `MyNat.add m (MyNat.succ n)` → `MyNat.succ (MyNat.add m n)`
  | m, .succ n => .succ (MyNat.add m n)

/-- Uses `MyNat.add` as the `+` operation on `MyNat`. -/
instance : Add MyNat := ⟨MyNat.add⟩

/-- Unfolds the numeral `1` to `MyNat.succ 0`. -/
theorem one_eq_succ_zero : (1 : MyNat) = MyNat.succ 0 := by
  -- `(1 : MyNat) = MyNat.succ 0`
  -- → `MyNat.succ 0 = MyNat.succ 0`
  -- → `MyNat.succ MyNat.zero = MyNat.succ MyNat.zero`
  rfl

/-- Unfolds the numeral `2` to `MyNat.succ 1`. -/
theorem two_eq_succ_one : (2 : MyNat) = MyNat.succ 1 := by
  -- `(2 : MyNat) = MyNat.succ 1`
  -- → `MyNat.succ 1 = MyNat.succ 1`
  -- → `MyNat.succ (MyNat.succ MyNat.zero) = MyNat.succ (MyNat.succ MyNat.zero)`
  rfl

/-- Adding zero on the right is definitional equality. -/
theorem add_zero (m : MyNat) : m + 0 = m := by
  -- `m + 0 = m`
  -- → `MyNat.add m MyNat.zero = m`
  -- → `m = m`
  rfl

/-- Adding a successor on the right unfolds to the successor of the sum. -/
theorem add_succ (m n : MyNat) : m + MyNat.succ n = MyNat.succ (m + n) := by
  -- `m + MyNat.succ n = MyNat.succ (m + n)`
  -- → `MyNat.add m (MyNat.succ n) = MyNat.succ (MyNat.add m n)`
  -- → `MyNat.succ (MyNat.add m n) = MyNat.succ (MyNat.add m n)`
  rfl

/-- Zero is a left identity for addition, proved by induction on the right argument. -/
theorem zero_add (n : MyNat) : 0 + n = n := by
  induction n with
  -- `rfl`
  -- `0 + 0 = 0`
  -- → `MyNat.add MyNat.zero MyNat.zero = MyNat.zero`
  -- → `MyNat.zero = MyNat.zero`
  | zero => rfl
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

/-- Moving a successor out of the left argument is proved by induction on the right. -/
theorem succ_add (m n : MyNat) : MyNat.succ m + n = MyNat.succ (m + n) := by
  induction n with
  -- `rfl`
  -- `MyNat.succ m + 0 = MyNat.succ (m + 0)`
  -- → `MyNat.add (MyNat.succ m) MyNat.zero = MyNat.succ (MyNat.add m MyNat.zero)`
  -- → `MyNat.succ m = MyNat.succ m`
  | zero => rfl
  -- `rw [add_succ, ih, add_succ]`
  | succ n ih =>
    -- `MyNat.succ m + MyNat.succ n`
    -- → `MyNat.add (MyNat.succ m) (MyNat.succ n)`
    -- → `MyNat.succ (MyNat.add (MyNat.succ m) n)`
    -- → `MyNat.succ (MyNat.succ m + n)`
    -- `⊢ MyNat.succ (MyNat.succ m + n) = MyNat.succ (m + MyNat.succ n)`
    rw [add_succ]
    -- `MyNat.succ m + n` →[ih] `MyNat.succ (m + n)`
    -- `⊢ MyNat.succ (MyNat.succ (m + n)) = MyNat.succ (m + MyNat.succ n)`
    rw [ih]
    -- `m + MyNat.succ n` → `MyNat.add m (MyNat.succ n)`
    -- → `MyNat.succ (MyNat.add m n)` → `MyNat.succ (m + n)`
    -- `⊢ MyNat.succ (MyNat.succ (m + n)) = MyNat.succ (MyNat.succ (m + n))`
    rw [add_succ]

end Examples.Theorems
