/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.CodeAlgebra

/-!
# The four-square constraint transformation

Issue #28, fourth piece. A natural root of `p` is an integer root of

```
p(x)² + Σ_{i < n} (xᵢ - (aᵢ² + bᵢ² + cᵢ² + dᵢ²))²
```

because over `ℤ` a sum of squares vanishes exactly when every summand does, and Lagrange's
theorem says the naturals are exactly the sums of four squares.

## Constraints, not substitution

The original variables are *kept*. Nothing is substituted into `p`, which is why this direction
does not expand every occurrence of every variable — unlike `x = u - v`, where the difference
really has to be substituted. That asymmetry between the two reductions is real and was expected.

## Layout, frozen in #28

For `n := p.arity`, the transformed code uses `5 * n` variables:

* `0 .. n-1` — the original `xᵢ`;
* `n + 4i .. n + 4i + 3` — the four-square witnesses for `xᵢ`.

## Public, unlike its computability

`fourSquares` is one of the two reductions between the natural and integer formulations, and the
square argument below is meaningful on its own — so this file is API. `Primrec fourSquares` is
what turns the transformation into a many-one reduction; it is unsupported machinery and stays in
`Internal/FourSquaresComp.lean`.

## Main definitions

* `Hilbert10.PolynomialCode.fourSq`
* `Hilbert10.PolynomialCode.fourSquares`

## Main results

* `Hilbert10.PolynomialCode.evalInt_fourSquares_eq_zero_iff`
* `Hilbert10.PolynomialCode.arity_fourSquares_le`
-/

@[expose] public section

namespace Hilbert10

namespace PolynomialCode

/-- The sum of four squares drawn from variable `i`'s witness block. -/
def fourSq (n i : ℕ) : PolynomialCode :=
  add (add (npow (X (n + 4 * i)) 2) (npow (X (n + 4 * i + 1)) 2))
    (add (npow (X (n + 4 * i + 2)) 2) (npow (X (n + 4 * i + 3)) 2))

/-- The constraint forcing `xᵢ` to equal a sum of four squares, as a square so that it is
nonnegative over `ℤ`. -/
def fourSqConstraint (n i : ℕ) : PolynomialCode :=
  npow (add (X i) (neg (fourSq n i))) 2

/-- **The four-square transformation.** -/
def fourSquares (p : PolynomialCode) : PolynomialCode :=
  add (npow p 2)
    (((List.range p.arity).map fun i => fourSqConstraint p.arity i).foldr add zero)

/-! ### Evaluation -/

theorem evalInt_foldr_add {α : Type*} (l : List α) (f : α → PolynomialCode) (y : List ℤ) :
    evalInt ((l.map f).foldr add zero) y = (l.map fun i => evalInt (f i) y).sum := by
  induction l with
  | nil => simp [zero]
  | cons a as ih => simp only [List.map_cons, List.foldr_cons, evalInt_add, ih, List.sum_cons]

@[simp] theorem evalInt_fourSq (n i : ℕ) (y : List ℤ) :
    evalInt (fourSq n i) y
      = (y.getD (n + 4 * i) 0) ^ 2 + (y.getD (n + 4 * i + 1) 0) ^ 2
        + ((y.getD (n + 4 * i + 2) 0) ^ 2 + (y.getD (n + 4 * i + 3) 0) ^ 2) := by
  simp [fourSq]

@[simp] theorem evalInt_fourSqConstraint (n i : ℕ) (y : List ℤ) :
    evalInt (fourSqConstraint n i) y
      = (y.getD i 0 - evalInt (fourSq n i) y) ^ 2 := by
  simp only [fourSqConstraint, evalInt_npow, evalInt_add, evalInt_neg, evalInt_X]
  ring

/-- The value of the transformed code: the original squared, plus one square per variable. -/
theorem evalInt_fourSquares (p : PolynomialCode) (y : List ℤ) :
    evalInt (fourSquares p) y
      = (evalInt p y) ^ 2
        + ((List.range p.arity).map fun i =>
            (y.getD i 0 - evalInt (fourSq p.arity i) y) ^ 2).sum := by
  simp only [fourSquares, evalInt_add, evalInt_npow, evalInt_foldr_add,
    evalInt_fourSqConstraint]

/-! ### The square argument, packaged once

Everything about sums of squares happens here, so neither direction of the root equivalence has
to repeat it. -/

theorem sq_nonneg' (a : ℤ) : 0 ≤ a ^ 2 := by
  rw [pow_two, ← Int.natAbs_mul_self]
  exact Int.natCast_nonneg _

theorem sq_eq_zero' {a : ℤ} (h : a ^ 2 = 0) : a = 0 := by
  by_contra hne
  rw [pow_two] at h
  exact mul_ne_zero hne hne h

theorem list_sum_nonneg : ∀ {l : List ℤ}, (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.sum
  | [], _ => by simp
  | a :: as, h => by
    have hrec := list_sum_nonneg (l := as) fun x hx => h x (by simp [hx])
    have ha := h a (by simp)
    simp only [List.sum_cons]
    omega

theorem sum_eq_zero_of_nonneg : ∀ {l : List ℤ}, (∀ x ∈ l, 0 ≤ x) → l.sum = 0 →
    ∀ x ∈ l, x = 0
  | [], _, _ => by simp
  | a :: as, h, hs => by
    have ha : 0 ≤ a := h a (by simp)
    have has : 0 ≤ as.sum := list_sum_nonneg fun x hx => h x (by simp [hx])
    have hsum : a + as.sum = 0 := by simpa using hs
    have ha0 : a = 0 := by omega
    have has0 : as.sum = 0 := by omega
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ha0
    · exact sum_eq_zero_of_nonneg (fun z hz => h z (by simp [hz])) has0 x hx'

/-- A sum of four squares is nonnegative. Stated here so the root proof learns `0 ≤ y.getD i 0`
from the packaged constraint without unfolding `fourSq`. -/
theorem evalInt_fourSq_nonneg (n i : ℕ) (y : List ℤ) : 0 ≤ evalInt (fourSq n i) y := by
  rw [evalInt_fourSq]
  have h1 := sq_nonneg' (y.getD (n + 4 * i) 0)
  have h2 := sq_nonneg' (y.getD (n + 4 * i + 1) 0)
  have h3 := sq_nonneg' (y.getD (n + 4 * i + 2) 0)
  have h4 := sq_nonneg' (y.getD (n + 4 * i + 3) 0)
  omega

/-- **The transformed code vanishes exactly when the original does and every constraint holds.**
A sum of squares over `ℤ` is zero only if every square is. -/
theorem evalInt_fourSquares_eq_zero_iff (p : PolynomialCode) (y : List ℤ) :
    evalInt (fourSquares p) y = 0 ↔
      evalInt p y = 0 ∧
        ∀ i < p.arity, y.getD i 0 = evalInt (fourSq p.arity i) y := by
  rw [evalInt_fourSquares]
  constructor
  · intro h
    have hsq : (0 : ℤ) ≤ (evalInt p y) ^ 2 := sq_nonneg' _
    have hterms : ∀ z ∈ (List.range p.arity).map fun i =>
        (y.getD i 0 - evalInt (fourSq p.arity i) y) ^ 2, (0 : ℤ) ≤ z := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hz
      exact sq_nonneg' _
    have hsum : (0 : ℤ) ≤ ((List.range p.arity).map fun i =>
        (y.getD i 0 - evalInt (fourSq p.arity i) y) ^ 2).sum := list_sum_nonneg hterms
    have h1 : (evalInt p y) ^ 2 = 0 := by omega
    have h2 : ((List.range p.arity).map fun i =>
        (y.getD i 0 - evalInt (fourSq p.arity i) y) ^ 2).sum = 0 := by omega
    refine ⟨sq_eq_zero' h1, fun i hi => ?_⟩
    have hmem : (y.getD i 0 - evalInt (fourSq p.arity i) y) ^ 2 ∈
        (List.range p.arity).map fun i => (y.getD i 0 - evalInt (fourSq p.arity i) y) ^ 2 :=
      List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
    have := sum_eq_zero_of_nonneg hterms h2 _ hmem
    have hz : y.getD i 0 - evalInt (fourSq p.arity i) y = 0 := sq_eq_zero' this
    omega
  · rintro ⟨hp, hc⟩
    rw [hp]
    have : ((List.range p.arity).map fun i =>
        (y.getD i 0 - evalInt (fourSq p.arity i) y) ^ 2) = (List.range p.arity).map fun _ => 0 := by
      refine List.map_congr_left fun i hi => ?_
      rw [hc i (List.mem_range.mp hi)]
      ring
    rw [this]
    simp

/-! ### Arity -/

theorem arity_fourSq_le (n i : ℕ) : (fourSq n i).arity ≤ n + 4 * i + 4 := by
  have h : ∀ k : ℕ, (npow (X k) 2).arity ≤ k + 1 := fun k =>
    le_trans (arity_npow_le _ 2) (by simp)
  simp only [fourSq, arity_add, max_le_iff]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact le_trans (h _) (by omega)
  · exact le_trans (h _) (by omega)
  · exact le_trans (h _) (by omega)
  · exact le_trans (h _) (by omega)

theorem arity_fourSqConstraint_le (n i : ℕ) :
    (fourSqConstraint n i).arity ≤ max (i + 1) (n + 4 * i + 4) := by
  refine le_trans (arity_npow_le _ 2) ?_
  simp only [arity_add, arity_neg, arity_X, max_le_iff]
  exact ⟨le_max_left _ _, le_trans (arity_fourSq_le n i) (le_max_right _ _)⟩

theorem arity_foldr_add_le {α : Type*} (l : List α) (f : α → PolynomialCode) (m : ℕ)
    (h : ∀ a ∈ l, (f a).arity ≤ m) : (((l.map f).foldr add zero)).arity ≤ m := by
  induction l with
  | nil => simp [zero, arity]
  | cons a as ih =>
    simp only [List.map_cons, List.foldr_cons, arity_add, max_le_iff]
    exact ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

/-- **The frozen arity bound.** -/
theorem arity_fourSquares_le (p : PolynomialCode) : (fourSquares p).arity ≤ 5 * p.arity := by
  simp only [fourSquares, arity_add, max_le_iff]
  refine ⟨le_trans (arity_npow_le _ 2) (by omega), ?_⟩
  refine arity_foldr_add_le _ _ _ fun i hi => ?_
  have hi' : i < p.arity := by simpa using hi
  refine le_trans (arity_fourSqConstraint_le p.arity i) ?_
  simp only [max_le_iff]
  omega

end PolynomialCode

end Hilbert10
