module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Ring

/-!
# The pairing enumeration has a successor function

`Nat.pair` and `Nat.unpair` are stated with multiplication and `Nat.sqrt`. Taking those
definitions at face value would make a register-machine implementation a verified-arithmetic
project: a multiplier, a square root, and their correctness proofs.

But the pairing is an *enumeration* of `ℕ × ℕ`, and enumerations have successors. `pairNext` is
that successor, and the theorems below say it is correct:

```lean
Nat.pair (pairNext p).1 (pairNext p).2 = Nat.pair p.1 p.2 + 1
pairNext^[n] (0, 0) = Nat.unpair n
```

Neither statement mentions a square root, and neither proof needs one — `pairNext` is built from
comparison, increment and zeroing alone.

## Why this shape

The consumer is #51, which compiles `Nat.unpair` and `Nat.pair` into register machines.

`unpair n` becomes `pairNext` iterated `n` times from `(0, 0)`: a counted loop.

`pair a b` becomes the enumeration run until the state is `(a, b)`, counting steps.
`iterate_pairNext_pair` is what makes that terminate — after exactly `Nat.pair a b` steps the
state *is* `(a, b)` — so termination is proved directly rather than through a general unbounded
search, which would make #51 depend on the `rfind'` compiler it is supposed to precede.

Self-contained, and a plausible mathlib addition: nothing here depends on the rest of this
development. Tracked for upstreaming in #37.

## The enumeration

Values `s ^ 2 .. s ^ 2 + 2 * s` form the shell `max a b = s`: first `(a, s)` for `a < s`, then
`(s, b)` for `b ≤ s`. `pairNext` walks that, and rolls over from `(s, s)` to `(0, s + 1)`.
-/

@[expose] public section

namespace Nat

/-- The successor in the pairing enumeration: the unique step from `p` to the pair whose code is
one greater. -/
def pairNext : ℕ × ℕ → ℕ × ℕ
  | (a, b) =>
      if a < b then (if a + 1 < b then (a + 1, b) else (b, 0))
      else if a = b then (0, a + 1)
      else (a, b + 1)

/-- **`pairNext` is the successor.** Proved by four cases on the shell position; no square root
and no reasoning about `Nat.sqrt` appears. -/
theorem pair_pairNext (p : ℕ × ℕ) :
    Nat.pair (pairNext p).1 (pairNext p).2 = Nat.pair p.1 p.2 + 1 := by
  obtain ⟨a, b⟩ := p
  rcases lt_trichotomy a b with h | h | h
  · by_cases h2 : a + 1 < b
    · rw [show pairNext (a, b) = (a + 1, b) by simp [pairNext, h, h2]]
      simp only [Nat.pair, if_pos h, if_pos h2]
      ring
    · have hb : b = a + 1 := by omega
      subst hb
      rw [show pairNext (a, a + 1) = (a + 1, 0) by simp [pairNext]]
      simp only [Nat.pair, if_pos h, if_neg (by omega : ¬ a + 1 < 0)]
      ring
  · subst h
    rw [show pairNext (a, a) = (0, a + 1) by simp [pairNext]]
    simp only [Nat.pair, if_pos (by omega : (0 : ℕ) < a + 1), if_neg (by omega : ¬ a < a)]
    ring
  · have hnlt : ¬ a < b := by omega
    have hne : ¬ a = b := by omega
    rw [show pairNext (a, b) = (a, b + 1) by simp [pairNext, hnlt, hne]]
    simp only [Nat.pair, if_neg (by omega : ¬ a < b + 1), if_neg (by omega : ¬ a < b)]
    ring

/-- **The `q`th pair of the enumeration has code `q`.** The counted-loop and
terminating-enumeration machines both need this, the second in the contrapositive form
`iterate_pairNext_ne_of_lt`. -/
theorem pair_iterate_pairNext (q : ℕ) :
    Nat.pair (pairNext^[q] (0, 0)).1 (pairNext^[q] (0, 0)).2 = q := by
  induction q with
  | zero => rfl
  | succ q ih => rw [Function.iterate_succ_apply', pair_pairNext, ih]

/-- Iterating from the origin enumerates the pairs in code order. -/
theorem iterate_pairNext (n : ℕ) : pairNext^[n] (0, 0) = Nat.unpair n := by
  conv_rhs => rw [← pair_iterate_pairNext n]
  rw [Nat.unpair_pair]

/-- **No early match.** Before step `Nat.pair a b` the enumeration has not reached `(a, b)`, so a
machine that walks it until its state matches stops exactly there. -/
theorem iterate_pairNext_ne_of_lt {q a b : ℕ} (h : q < Nat.pair a b) :
    pairNext^[q] (0, 0) ≠ (a, b) := by
  intro hq
  rw [← pair_iterate_pairNext q, hq] at h
  exact Nat.lt_irrefl _ h

/-- **The termination certificate for the `pair` direction.** Enumerating from the origin reaches
`(a, b)` after exactly `Nat.pair a b` steps, so a machine that walks the enumeration until its
state matches halts, and does so without an unbounded search. -/
theorem iterate_pairNext_pair (a b : ℕ) : pairNext^[Nat.pair a b] (0, 0) = (a, b) := by
  rw [iterate_pairNext, Nat.unpair_pair]

/-! ## Regression checks against the definitions -/

example : pairNext^[5] (0, 0) = (1, 2) := by decide
example : Nat.pair 1 2 = 5 := by decide
example : pairNext (2, 2) = (0, 3) := by decide

end Nat
