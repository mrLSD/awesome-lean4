/-!
# The natural numbers, rebuilt from scratch

Exercises from the [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4),
Tutorial World.

The game deliberately avoids Lean's built-in `Nat`. It rebuilds the natural
numbers from the Peano axioms, so everything here — the type, its numerals, its
addition — is defined below rather than imported, and Mathlib is not used at all.

The reward for doing it the hard way is that you can see exactly which facts hold
*by definition* (proved by `rfl`, no work at all) and which ones have to be
earned by induction. The four addition lemmas at the bottom come in pairs that
look symmetric but are not.
-/
namespace Examples.Theorems

/-- A natural number is either zero or the successor of another natural number.

That is the entire definition — no digits, no arithmetic, nothing else. It means
`3` is really `succ (succ (succ zero))`: a stack of three `succ`s on top of
`zero`. -/
inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat
  deriving Repr, DecidableEq

/-- Numerals are notation, not values. Writing `0` means nothing until an `OfNat`
instance says which term of the type that digit stands for. -/
instance : OfNat MyNat 0 := ⟨MyNat.zero⟩

/-- `1` is one `succ` away from `0`. The instance above is already in scope, so
the `0` written here is itself the numeral, not the raw constructor. -/
instance : OfNat MyNat 1 := ⟨MyNat.succ 0⟩

/-- `2` builds on `1` the same way. Each numeral you want to write down needs its
own instance — there is no automatic ladder. -/
instance : OfNat MyNat 2 := ⟨MyNat.succ 1⟩

/-- Addition, defined by recursion on the **second** argument.

These two lines are the complete meaning of `+` for `MyNat`: adding zero changes
nothing, and adding `succ n` puts one more `succ` on top of adding `n`.

Which side the recursion runs on is the single most important decision in this
file. It is what makes `add_zero` and `add_succ` below free, while their mirror
images `zero_add` and `succ_add` need induction. -/
def MyNat.add : MyNat → MyNat → MyNat
  | m, .zero   => m                        -- m + 0      = m
  | m, .succ n => .succ (MyNat.add m n)    -- m + succ n = succ (m + n)

/-- Registers `MyNat.add` as the meaning of `+` for this type.

Without this instance Lean rejects even the statement `m + n` with
`failed to synthesize HAdd MyNat MyNat`: `+` is not built into the language, it
is looked up per type, exactly like the numerals above. -/
instance : Add MyNat := ⟨MyNat.add⟩

/-- `1 = succ 0`, true *by definition*.

Unfolding the `OfNat` instance turns the literal `1` into `succ zero`, so the two
sides are the same term and `rfl` ("reflexivity", the proof of `a = a`) closes
the goal without any real work. -/
theorem one_eq_succ_zero : (1 : MyNat) = MyNat.succ 0 := rfl

/-- The same story one step up. Together with `one_eq_succ_zero` this lets a
proof take any numeral apart into `succ`s — see `Examples.Succ` for that in
action. -/
theorem two_eq_succ_one : (2 : MyNat) = MyNat.succ 1 := rfl

/-- `m + 0 = m` — literally the first line of `MyNat.add`, so `rfl` proves it. -/
theorem add_zero (m : MyNat) : m + 0 = m := rfl

/-- `m + succ n = succ (m + n)` — literally the second line of `MyNat.add`, so
`rfl` again.

No induction appears here, which surprises people: the definition already
recurses on the right-hand argument, and the right-hand argument is exactly the
one being taken apart. -/
theorem add_succ (m n : MyNat) : m + MyNat.succ n = MyNat.succ (m + n) := rfl

/-- `0 + n = n` — the mirror image of `add_zero`, and this one is *not* free.

The definition says nothing about a zero on the **left**, so the only way in is
induction on `n`. The base case is `0 + 0 = 0`, which `rfl` handles. The step
turns `0 + succ n` into `succ (0 + n)` via `add_succ`, and the induction
hypothesis `ih : 0 + n = n` finishes it. -/
theorem zero_add (n : MyNat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [add_succ, ih]

/-- `succ m + n = succ (m + n)` — the same asymmetry once more.

A `succ` sitting on the **left** is invisible to the definition, so it has to be
carried across by induction on `n`. The step rewrites with `add_succ` on the
left, applies `ih`, then rewrites with `add_succ` again on the right until both
sides coincide. -/
theorem succ_add (m n : MyNat) : MyNat.succ m + n = MyNat.succ (m + n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [add_succ, ih, add_succ]

end Examples.Theorems
