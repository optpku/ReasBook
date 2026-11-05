/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Data.Real.Basic
public import Mathlib.RingTheory.Localization.Integer

public section

open scoped BigOperators
open IsLocalization

section Proposition17

universe u

/-- Helper for Proposition 1.7: rewriting a tableau row into its fractional remainder
and its integral floor correction. -/
private lemma tableauFractionalRowSplit
    {ι : Type u}
    (N : Finset ι) (a x : ι → ℝ) (xB b : ℝ)
    (hrow : xB + (∑ j ∈ N, a j * x j) = b) :
    (∑ j ∈ N, Int.fract (a j) * x j) +
        (xB + ∑ j ∈ N, (((⌊a j⌋ : ℤ) : ℝ) * x j)) = b := by
  -- Rewrite each coefficient as floor plus fractional part and then regroup the row.
  calc
    (∑ j ∈ N, Int.fract (a j) * x j) + (xB + ∑ j ∈ N, (((⌊a j⌋ : ℤ) : ℝ) * x j))
        = xB + ((∑ j ∈ N, (((⌊a j⌋ : ℤ) : ℝ) * x j)) + (∑ j ∈ N, Int.fract (a j) * x j)) := by
            simp [add_left_comm, add_comm]
    _ = xB + ∑ j ∈ N, ((((⌊a j⌋ : ℤ) : ℝ) * x j) + Int.fract (a j) * x j) := by
          rw [← Finset.sum_add_distrib]
    _ = xB + ∑ j ∈ N, ((((⌊a j⌋ : ℤ) : ℝ) + Int.fract (a j)) * x j) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [add_mul]
    _ = xB + ∑ j ∈ N, a j * x j := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [Int.floor_add_fract]
    _ = b := hrow

/-- Helper for Proposition 1.7: the floor contribution of the tableau row is integral. -/
private lemma tableauFloorCorrection_isInteger
    {ι : Type u}
    (N : Finset ι) (a x : ι → ℝ) (xB : ℝ)
    (hx_integral : ∀ j ∈ N, IsInteger ℤ (x j))
    (hxB_integral : IsInteger ℤ xB) :
    IsInteger ℤ (xB + ∑ j ∈ N, (((⌊a j⌋ : ℤ) : ℝ) * x j)) := by
  -- Build the finite sum from integral summands and then add the integral basic variable.
  have hsum :
      IsInteger ℤ (∑ j ∈ N, (((⌊a j⌋ : ℤ) : ℝ) * x j)) := by
    classical
    revert hx_integral
    refine Finset.induction_on N ?_ ?_
    · intro hx_integral
      simpa using (IsLocalization.isInteger_zero : IsInteger ℤ (0 : ℝ))
    · intro j s hj hs hx_integral
      have hfloor : IsInteger ℤ ((((⌊a j⌋ : ℤ) : ℝ))) := by
        change ((((⌊a j⌋ : ℤ) : ℝ))) ∈ (algebraMap ℤ ℝ).rangeS
        exact RingHom.mem_rangeS_self (algebraMap ℤ ℝ) (⌊a j⌋)
      have hxj : IsInteger ℤ (x j) := hx_integral j (Finset.mem_insert_self j s)
      have hs_integral : IsInteger ℤ (∑ j ∈ s, (((⌊a j⌋ : ℤ) : ℝ) * x j)) := by
        refine hs ?_
        intro k hk
        exact hx_integral k (Finset.mem_insert_of_mem hk)
      have hmul : IsInteger ℤ ((((⌊a j⌋ : ℤ) : ℝ) * x j)) :=
        IsLocalization.isInteger_mul hfloor hxj
      simpa [Finset.sum_insert hj] using IsLocalization.isInteger_add hmul hs_integral
  -- Package the whole correction term as one integral quantity.
  exact IsLocalization.isInteger_add hxB_integral hsum

/-- Helper for Proposition 1.7: the fractional-part remainder sum is nonnegative. -/
private lemma sumFractMul_nonneg
    {ι : Type u}
    (N : Finset ι) (a x : ι → ℝ)
    (hx_nonneg : ∀ j ∈ N, 0 ≤ x j) :
    0 ≤ ∑ j ∈ N, Int.fract (a j) * x j := by
  -- Each summand is a product of two nonnegative terms.
  classical
  revert hx_nonneg
  refine Finset.induction_on N ?_ ?_
  · intro hx_nonneg
    simp
  · intro j s hj hs hx_nonneg
    have hs_nonneg : 0 ≤ ∑ k ∈ s, Int.fract (a k) * x k := by
      refine hs ?_
      intro k hk
      exact hx_nonneg k (Finset.mem_insert_of_mem hk)
    have hj_nonneg : 0 ≤ x j := hx_nonneg j (Finset.mem_insert_self j s)
    rw [Finset.sum_insert hj]
    exact add_nonneg
      (mul_nonneg (Int.fract_nonneg (a j)) hj_nonneg) hs_nonneg

/-- Helper for Proposition 1.7: a nonnegative real dominates its fractional part. -/
private lemma fract_le_self_of_nonneg {t : ℝ} (ht : 0 ≤ t) : Int.fract t ≤ t := by
  -- Compare `t` with `Int.fract t + ⌊t⌋`, using that the floor is nonnegative.
  have hfloor_nonneg : 0 ≤ (⌊t⌋ : ℤ) := Int.floor_nonneg.mpr ht
  have hfloor_nonneg_real : 0 ≤ (((⌊t⌋ : ℤ) : ℝ)) := by
    exact_mod_cast hfloor_nonneg
  calc
    Int.fract t ≤ Int.fract t + (((⌊t⌋ : ℤ) : ℝ)) := le_add_of_nonneg_right hfloor_nonneg_real
    _ = t := Int.fract_add_floor t

/-- Proposition 1.7 (Gomory fractional cut from a tableau row). If a tableau row
`xB + ∑ j ∈ N, a j * x j = b` has `IsInteger ℤ xB` and each `x j` on `N` is a
nonnegative integer, then `∑ j ∈ N, Int.fract (a j) * x j ≥ Int.fract b`.

The source states the conclusion for nonintegral `b`; that extra hypothesis is
mathematically redundant because `Int.fract b = 0` when `b` is integral. -/
theorem gomoryFractionalCut_valid_of_tableauRow
    {ι : Type u}
    (N : Finset ι) (a x : ι → ℝ) (xB b : ℝ)
    (hrow : xB + (∑ j ∈ N, a j * x j) = b)
    (hx_nonneg : ∀ j ∈ N, 0 ≤ x j)
    (hx_integral : ∀ j ∈ N, IsInteger ℤ (x j))
    (hxB_integral : IsInteger ℤ xB) :
    ∑ j ∈ N, Int.fract (a j) * x j ≥ Int.fract b := by
  let s : ℝ := ∑ j ∈ N, Int.fract (a j) * x j
  let c : ℝ := xB + ∑ j ∈ N, (((⌊a j⌋ : ℤ) : ℝ) * x j)
  -- Split the tableau row into the nonnegative fractional remainder and an integral correction.
  have hsplit : s + c = b := by
    simpa [s, c] using tableauFractionalRowSplit N a x xB b hrow
  have hc_integral : IsInteger ℤ c := by
    simpa [c] using tableauFloorCorrection_isInteger N a x xB hx_integral hxB_integral
  rcases (show ∃ z : ℤ, (z : ℝ) = c by
    simpa [IsLocalization.IsInteger, RingHom.mem_rangeS] using hc_integral) with ⟨z, hz⟩
  -- Rewrite away the integral correction before comparing the remaining fractional sum with itself.
  have hfract_eq : Int.fract b = Int.fract s := by
    rw [← hz] at hsplit
    have hfract_row : Int.fract (s + (z : ℝ)) = Int.fract b := by
      exact congrArg Int.fract hsplit
    simpa using hfract_row.symm
  have hs_nonneg : 0 ≤ s := by
    simpa [s] using sumFractMul_nonneg N a x hx_nonneg
  -- The final inequality is `Int.fract s ≤ s`, transported along the row split.
  calc
    Int.fract b = Int.fract s := hfract_eq
    _ ≤ s := fract_le_self_of_nonneg hs_nonneg

end Proposition17
