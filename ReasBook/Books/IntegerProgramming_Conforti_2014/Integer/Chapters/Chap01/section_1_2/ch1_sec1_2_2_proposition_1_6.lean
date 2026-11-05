/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.MixedSpace
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Data.Real.Basic

public section

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators IntegerVectorNotation

section Proposition16

/-- Helper for Proposition 1.6: rewriting the row equality isolates the weighted fractional part
sum as the fractional part of `a0` plus an integer gap. -/
private lemma fractWeightedSum_eq_fract_rhs_add_integerGap
    {n : ℕ}
    (a : Fin n → ℝ)
    (a0 : ℝ)
    (z : Fin n → ℤ)
    (hz_eq : ∑ j : Fin n, a j * (z j : ℝ) = a0) :
    ∑ j : Fin n, Int.fract (a j) * (z j : ℝ) =
      Int.fract a0 + ((Int.floor a0 - ∑ j : Fin n, Int.floor (a j) * z j : ℤ) : ℝ) := by
  have hsplit :
      a0 =
        ((∑ j : Fin n, Int.floor (a j) * z j : ℤ) : ℝ) +
          ∑ j : Fin n, Int.fract (a j) * (z j : ℝ) := by
    -- Split each coefficient into its floor and fractional parts, then collect the integer block.
    calc
      a0 = ∑ j : Fin n, a j * (z j : ℝ) := hz_eq.symm
      _ = ∑ j : Fin n, (((Int.floor (a j) : ℝ) + Int.fract (a j)) * (z j : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [Int.floor_add_fract]
      _ = ∑ j : Fin n, ((Int.floor (a j) : ℝ) * (z j : ℝ) +
            Int.fract (a j) * (z j : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [add_mul]
      _ = ∑ j : Fin n, (Int.floor (a j) : ℝ) * (z j : ℝ) +
            ∑ j : Fin n, Int.fract (a j) * (z j : ℝ) := by
            rw [Finset.sum_add_distrib]
      _ = ((∑ j : Fin n, Int.floor (a j) * z j : ℤ) : ℝ) +
            ∑ j : Fin n, Int.fract (a j) * (z j : ℝ) := by
            congr 1
            calc
              ∑ j : Fin n, (Int.floor (a j) : ℝ) * (z j : ℝ)
                  = ∑ j : Fin n, ((Int.floor (a j) * z j : ℤ) : ℝ) := by
                      refine Finset.sum_congr rfl ?_
                      intro j _
                      simp
              _ = ((∑ j : Fin n, Int.floor (a j) * z j : ℤ) : ℝ) := by
                    rw [Int.cast_sum]
  have hfractSum :
      ∑ j : Fin n, Int.fract (a j) * (z j : ℝ) =
        a0 - ((∑ j : Fin n, Int.floor (a j) * z j : ℤ) : ℝ) := by
    -- Move the integer block to the right-hand side to expose the fractional residual.
    rw [eq_sub_iff_add_eq]
    simpa [add_comm, add_left_comm, add_assoc] using hsplit.symm
  -- Rewrite the residual with the decomposition `a0 = floor a0 + fract a0`.
  calc
    ∑ j : Fin n, Int.fract (a j) * (z j : ℝ)
        = a0 - ((∑ j : Fin n, Int.floor (a j) * z j : ℤ) : ℝ) := hfractSum
    _ = ((Int.floor a0 : ℝ) + Int.fract a0) -
          ((∑ j : Fin n, Int.floor (a j) * z j : ℤ) : ℝ) := by
          congr 1
          exact (Int.floor_add_fract a0).symm
    _ = Int.fract a0 +
          ((Int.floor a0 : ℝ) - ((∑ j : Fin n, Int.floor (a j) * z j : ℤ) : ℝ)) := by
          rw [sub_eq_add_neg]
          rw [add_assoc]
          rw [add_left_comm (Int.floor a0 : ℝ) (Int.fract a0)
            (-((∑ j : Fin n, Int.floor (a j) * z j : ℤ) : ℝ))]
          rfl
    _ = Int.fract a0 +
          ((Int.floor a0 - ∑ j : Fin n, Int.floor (a j) * z j : ℤ) : ℝ) := by
          rw [Int.cast_sub]

/-- Helper for Proposition 1.6: a nonnegative quantity of the form `Int.fract a0 + k`
forces the integer shift `k` to be nonnegative. -/
private lemma integerGap_nonneg_of_fractionalSum_nonneg
    (a0 : ℝ)
    (k : ℤ)
    (h_nonneg : 0 ≤ Int.fract a0 + (k : ℝ)) :
    0 ≤ k := by
  by_cases hk : 0 ≤ k
  · exact hk
  · -- A negative integer shift is at most `-1`, which contradicts `fract a0 < 1`.
    have hk_lt : k < 0 := lt_of_not_ge hk
    have hk_le : k ≤ -1 := by
      exact Int.lt_add_one_iff.mp (by simpa using hk_lt)
    have hk_real : (k : ℝ) ≤ -1 := by
      exact_mod_cast hk_le
    have hsum_lt : Int.fract a0 + (k : ℝ) < 0 := by
      have hbound : Int.fract a0 + (k : ℝ) ≤ Int.fract a0 + (-1 : ℝ) := by
        simpa [add_comm] using add_le_add_left hk_real (Int.fract a0)
      have hright_lt : Int.fract a0 + (-1 : ℝ) < 0 := by
        simpa [sub_eq_add_neg] using sub_neg.mpr (Int.fract_lt_one a0)
      exact lt_of_le_of_lt hbound hright_lt
    exact False.elim ((not_lt_of_ge h_nonneg) hsum_lt)

/-- Helper for Proposition 1.6: the Gomory fractional-cut inequality for an explicit
integer vector. -/
private lemma gomoryFractionalCutCore
    {n : ℕ}
    (a : Fin n → ℝ)
    (a0 : ℝ)
    (z : Fin n → ℤ)
    (hz_nonneg : 0 ≤ z)
    (hz_eq : ∑ j : Fin n, a j * (z j : ℝ) = a0) :
    ∑ j : Fin n, Int.fract (a j) * (z j : ℝ) ≥ Int.fract a0 := by
  let k : ℤ := Int.floor a0 - ∑ j : Fin n, Int.floor (a j) * z j
  have hsum_eq :
      ∑ j : Fin n, Int.fract (a j) * (z j : ℝ) = Int.fract a0 + (k : ℝ) := by
    -- Normalize the row equation to a fractional sum plus an integer gap.
    simpa [k] using fractWeightedSum_eq_fract_rhs_add_integerGap a a0 z hz_eq
  have hsum_nonneg : 0 ≤ ∑ j : Fin n, Int.fract (a j) * (z j : ℝ) := by
    -- Every summand is nonnegative because both the coefficient fractions and coordinates are.
    refine Finset.sum_nonneg ?_
    intro j _
    have hzj_nonneg : (0 : ℝ) ≤ (z j : ℝ) := by
      exact_mod_cast hz_nonneg j
    exact mul_nonneg (Int.fract_nonneg (a j)) hzj_nonneg
  have hk_nonneg : 0 ≤ k := by
    -- The normalized sum cannot be negative, so the integer gap cannot be negative either.
    refine integerGap_nonneg_of_fractionalSum_nonneg a0 k ?_
    simpa [hsum_eq] using hsum_nonneg
  have hk_real : 0 ≤ (k : ℝ) := by
    exact_mod_cast hk_nonneg
  -- Adding a nonnegative integer gap to `fract a0` preserves the desired lower bound.
  calc
    ∑ j : Fin n, Int.fract (a j) * (z j : ℝ) = Int.fract a0 + (k : ℝ) := hsum_eq
    _ ≥ Int.fract a0 := by
          exact le_add_of_nonneg_right hk_real

/-- Proposition 1.6 (Gomory fractional cut): if `x : Fin n → ℝ` is a nonnegative point of `ℤ^n`
and satisfies `∑ j : Fin n, a j * x j = a0`, then
`∑ j : Fin n, Int.fract (a j) * x j ≥ Int.fract a0`.

The source states the conclusion for nonintegral `a0`; that extra hypothesis is mathematically
redundant because `Int.fract a0 = 0` when `a0` is integral. -/
theorem gomoryFractionalCutValid
    {n : ℕ}
    (a : Fin n → ℝ)
    (a0 : ℝ)
    (x : Fin n → ℝ)
    (hx_nonneg : 0 ≤ x)
    (hx_int : x ∈ ℤ^n)
    (hx_eq : ∑ j : Fin n, a j * x j = a0) :
    ∑ j : Fin n, Int.fract (a j) * x j ≥ Int.fract a0 := by
  rcases (mem_integerVectors_iff.mp hx_int) with ⟨z, rfl⟩
  have hz_nonneg : 0 ≤ z := by
    -- Transfer the ambient nonnegativity hypothesis to the integer coordinates.
    intro j
    have hzj_nonneg : (0 : ℝ) ≤ (z j : ℝ) := by
      simpa using hx_nonneg j
    exact_mod_cast hzj_nonneg
  -- The main theorem is the lattice-owner wrapper around the explicit integer-coordinate core.
  simpa using gomoryFractionalCutCore a a0 z hz_nonneg hx_eq

/-- Proposition 1.6 specialized to an explicitly integer-valued point `z : Fin n → ℤ`. This is
the direct source-facing integer-coordinate form of the Gomory fractional-cut validity statement.

As in `gomoryFractionalCutValid`, no nonintegrality hypothesis on `a0` is needed. -/
theorem gomoryFractionalCutValid_of_int
    {n : ℕ}
    (a : Fin n → ℝ)
    (a0 : ℝ)
    (z : Fin n → ℤ)
    (hz_nonneg : 0 ≤ z)
    (hz_eq : ∑ j : Fin n, a j * (z j : ℝ) = a0) :
    ∑ j : Fin n, Int.fract (a j) * (z j : ℝ) ≥ Int.fract a0 := by
  refine gomoryFractionalCutValid a a0 (fun j ↦ (z j : ℝ)) ?_ ?_ hz_eq
  · intro j
    change (0 : ℝ) ≤ (z j : ℝ)
    exact_mod_cast hz_nonneg j
  · exact mem_integerVectors_iff.mpr ⟨z, rfl⟩

end Proposition16
