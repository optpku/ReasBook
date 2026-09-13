/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Denumerable
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Rational-time enumeration

This module fixes the countable enumeration of rational points in `(0, 1)` and
its real-valued sequence.
-/

/-- The rational points strictly between `0` and `1`. -/
public abbrev RationalTime : Type := Set.Ioo (0 : ℚ) 1

/-- A fixed zero-based enumeration of the rational points in `(0, 1)`. -/
public noncomputable def rationalTimeEquiv : ℕ ≃ RationalTime :=
  let denumerable : Denumerable RationalTime :=
    @Denumerable.ofEncodableOfInfinite RationalTime inferInstance
      (Set.Ioo.infinite (zero_lt_one : (0 : ℚ) < 1))
  @Denumerable.equiv₂ ℕ RationalTime Denumerable.nat denumerable

/-- The real-valued sequence obtained from `rationalTimeEquiv`. -/
public noncomputable def rationalTime (n : ℕ) : ℝ :=
  ((rationalTimeEquiv n).1 : ℝ)

/-- Distinct indices give distinct real rational times. -/
public theorem rationalTime_injective : Function.Injective rationalTime := by
  -- Equality after casting back to `ℝ` already forces equality in the rational subtype.
  intro m n hmn
  apply rationalTimeEquiv.injective
  apply Subtype.ext
  apply Rat.cast_injective (α := ℝ)
  simpa only [rationalTime] using hmn

/-- Every enumerated real rational time lies strictly between `0` and `1`. -/
public theorem rationalTime_mem_Ioo (n : ℕ) :
    rationalTime n ∈ Set.Ioo (0 : ℝ) 1 := by
  -- Cast the two strict inequalities carried by the rational subtype to `ℝ`.
  constructor
  · unfold rationalTime
    exact_mod_cast (rationalTimeEquiv n).property.1
  · unfold rationalTime
    exact_mod_cast (rationalTimeEquiv n).property.2

/-- Every rational point strictly between `0` and `1` occurs in `rationalTime`. -/
public theorem exists_rationalTime_eq (q : RationalTime) :
    ∃ n : ℕ, rationalTime n = (q.1 : ℝ) := by
  -- The inverse of the fixed equivalence supplies the required index.
  refine ⟨rationalTimeEquiv.symm q, ?_⟩
  simp only [rationalTime, Equiv.apply_symm_apply]

/-- Every nondegenerate open subinterval of `(0, 1)` contains enumerated times
with arbitrarily large indices. -/
public theorem exists_gt_rationalTime_mem_Ioo {a b : ℝ} (hab : a < b)
    (hsub : Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) 1) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ rationalTime n ∈ Set.Ioo a b := by
  -- Place a rational interval strictly inside `(a, b)`.
  obtain ⟨q₁ : ℚ, ha₁, h₁b⟩ := exists_rat_btwn hab
  obtain ⟨q₂ : ℚ, h₁₂, h₂b⟩ := exists_rat_btwn h₁b
  let forbidden : Finset ℚ :=
    (Finset.range (N + 1)).image (fun n ↦ (rationalTimeEquiv n).1)
  -- Infinitude of the rational interval lets us avoid every index through `N`.
  obtain ⟨q, hq, hqForbidden⟩ :=
    (Set.Ioo_infinite (Rat.cast_lt.mp h₁₂)).exists_notMem_finset forbidden
  have hqReal : (q : ℝ) ∈ Set.Ioo a b := by
    constructor
    · exact ha₁.trans (Rat.cast_lt.mpr hq.1)
    · exact (Rat.cast_lt.mpr hq.2).trans h₂b
  have hqUnitReal : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := hsub hqReal
  have hqUnit : q ∈ Set.Ioo (0 : ℚ) 1 := by
    constructor
    · exact_mod_cast hqUnitReal.1
    · exact_mod_cast hqUnitReal.2
  let qTime : RationalTime := ⟨q, hqUnit⟩
  obtain ⟨n, hnq⟩ := exists_rationalTime_eq qTime
  refine ⟨n, ?_, ?_⟩
  · -- Otherwise `q` would be one of the explicitly forbidden rational values.
    by_contra hnLarge
    have hnRange : n ∈ Finset.range (N + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.not_lt.mp hnLarge))
    have hnImage : (rationalTimeEquiv n).1 ∈ forbidden := by
      unfold forbidden
      exact Finset.mem_image.mpr ⟨n, hnRange, rfl⟩
    have hRat : (rationalTimeEquiv n).1 = q := by
      apply Rat.cast_injective (α := ℝ)
      simpa only [rationalTime, qTime] using hnq
    exact hqForbidden (hRat ▸ hnImage)
  · -- The chosen index has the same real value as `q`, hence lies in `(a, b)`.
    simpa only [hnq] using hqReal
