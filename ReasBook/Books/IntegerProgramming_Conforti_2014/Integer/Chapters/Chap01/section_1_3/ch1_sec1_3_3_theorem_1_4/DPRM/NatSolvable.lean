module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.PolynomialCodePrimcodable

/-!
# Hilbert's tenth problem as a decision problem

Issue #13, the last piece of M2. This is the predicate whose undecidability is the
project's headline (#27), and whose RE-completeness is #35 and #26.

## The missing side condition

`HasNatRoot` places **no** constraint relating the length of the root to the arity:

```lean
def HasNatRoot (p : PolynomialCode) : Prop := ∃ x : List ℕ, p.eval x = 0
```

That is equivalent to demanding a root of length exactly `arity` (`hasNatRoot_iff`), because
zero-extension (#8) lets a short root be padded and the arity bound lets a long one be
truncated. The unconstrained form is what every later proof wants, since it never has to
produce or preserve a length invariant.

The name says `Nat` because the development is over natural-number assignments, matching
`Dioph`. Hilbert's original integer formulation is #28 and gets `IntSolvable`; nothing here
is called `H10` unqualified.

## What this module does not yet claim

`NatSolvable` is a predicate on `PolynomialCode`, which carries a `Primcodable` instance, so
it is a decision problem in the sense the computability library expects. That instance is
imported here rather than merely referenced, so this module alone supplies what it advertises
instead of relying on the root bundle to pull it in.

But `REPred NatSolvable` is *not* provable from this module's imports: it needs computability
of `eval`, which needs `Primrec` lemmas about `ℤ` that the pinned mathlib lacks (#36).

So the definition and its semantics are settled here, and the statement that it is
recursively enumerable is a separate theorem with a separate dependency. Do not read the
public `NatSolvable` as already carrying that content.
-/

@[expose] public section

namespace Hilbert10

namespace PolynomialCode

/-- An encoded polynomial has a natural root. No length side condition — see
`hasNatRoot_iff`. -/
def HasNatRoot (p : PolynomialCode) : Prop := ∃ x : List ℕ, p.eval x = 0

/-- A root may always be taken to have length exactly `arity`.

The witness is uniform in both directions: pad with zeros and truncate to `arity`, which is
correct whether the original root was short or long, so no case split on lengths is
needed. -/
theorem hasNatRoot_iff (p : PolynomialCode) :
    p.HasNatRoot ↔ ∃ x : List ℕ, x.length = p.arity ∧ p.eval x = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    set L := x ++ List.replicate p.arity 0 with hL
    refine ⟨L.take p.arity, ?_, ?_⟩
    · simp [hL]
    · have hlen : (L.take p.arity).length = p.arity := by simp [hL]
      have hsplit : p.eval L = p.eval (L.take p.arity) := by
        conv_lhs => rw [← List.take_append_drop p.arity L]
        exact eval_append_of_arity_le (Nat.le_of_eq hlen.symm) _
      rw [← hsplit, hL, eval_append_replicate_zero]
      exact hx
  · rintro ⟨x, _, hx⟩
    exact ⟨x, hx⟩

end PolynomialCode

/-- **Hilbert's tenth problem over the naturals**: does an encoded polynomial have a natural
root? Definitionally `PolynomialCode.HasNatRoot`, so no second semantics exists to drift. -/
def NatSolvable : PolynomialCode → Prop := PolynomialCode.HasNatRoot

theorem natSolvable_iff (p : PolynomialCode) :
    NatSolvable p ↔ ∃ x : List ℕ, p.eval x = 0 := Iff.rfl

theorem natSolvable_iff_arity (p : PolynomialCode) :
    NatSolvable p ↔ ∃ x : List ℕ, x.length = p.arity ∧ p.eval x = 0 :=
  PolynomialCode.hasNatRoot_iff p

/-! ### Sanity checks -/

/-- The tie to `HasNatRoot` is definitional, not an equivalence to be maintained. -/
example (p : PolynomialCode) : NatSolvable p ↔ p.HasNatRoot := Iff.rfl

/-- A solvable instance: `x₀ ^ 2 + x₁ ^ 2 - 25` has the root `[3, 4]`. -/
example : NatSolvable ⟨[(1, [2]), (1, [0, 2]), (-25, [])]⟩ := ⟨[3, 4], by decide⟩

end Hilbert10
