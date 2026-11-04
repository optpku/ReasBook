/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.CommonDenominator
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3.ch6_sec6_3_definition_6_3_extra_1

open scoped BigOperators

section Remark63Extra2

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ
local notation "Qq" => Fin q → ℚ
local notation "NatAssignment" => Rq →₀ ℕ
local notation "ContAssignment" => Rq →₀ NNReal

/-- Helper for Remark 6.3-extra-2: the common denominator of a rational vector is nonzero. -/
lemma rationalVectorCommonDenominator_ne_zero
    (r : Qq) :
    rational_vector_common_denominator r ≠ 0 := by
  -- Every rational coordinate has positive denominator, so the finite lcm cannot vanish.
  have hden :
      ∀ i ∈ (Finset.univ : Finset (Fin q)), (r i).den ≠ 0 := by
    intro i hi
    exact Nat.ne_of_gt (Rat.den_pos (r i))
  change Finset.univ.lcm (fun i : Fin q ↦ (r i).den) ≠ 0
  exact Finset.lcm_ne_zero_iff.2 hden

/-- Helper for Remark 6.3-extra-2: after casting to `ℝ`, the denominator-cleared integer vector is
the corresponding real scalar multiple of the original rational vector. -/
lemma commonDenominatorScaledVector_eq_smulReal
    (r : Qq) :
    (fun i ↦ (common_denominator_scaled_vector r i : ℝ)) =
      (rational_vector_common_denominator r : ℝ) • (fun i ↦ (r i : ℝ)) := by
  -- Cast the rational common-denominator identity coordinatewise into `ℝ`.
  ext i
  change ((common_denominator_scaled_vector r i : ℤ) : ℝ) =
      (rational_vector_common_denominator r : ℝ) * (r i : ℝ)
  have hi :
      ((common_denominator_scaled_vector r i : ℤ) : ℚ) =
        (rational_vector_common_denominator r : ℚ) * r i := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      congrFun (common_denominator_scaled_vector_eq_smul r) i
  exact_mod_cast hi

/-- Helper for Remark 6.3-extra-2: the standard test point obtained by adding
`M * rational_vector_common_denominator r` copies of the rational direction `r`
is feasible for the mixed-integer relaxation. -/
lemma rationalSliceTestPoint_memMixedIntegerRelaxationSet
    (f r : Qq) (M : ℕ) :
    ( Finsupp.single (fun i ↦ -(f i : ℝ)) 1 +
        Finsupp.single (fun i ↦ (r i : ℝ))
          (M * rational_vector_common_denominator r),
      (0 : ContAssignment)) ∈ mixed_integer_relaxation_set (fun i ↦ (f i : ℝ)) := by
  rw [mem_mixed_integer_relaxation_set_iff]
  refine ⟨fun i ↦ (M : ℤ) * common_denominator_scaled_vector r i, ?_⟩
  have hbase :
      (Finsupp.single (fun i ↦ -(f i : ℝ)) 1).sum (fun s n ↦ (n : ℝ) • s) =
        (fun i ↦ -(f i : ℝ)) := by
    -- The base singleton contributes exactly one copy of `-f`.
    rw [Finsupp.sum_single_index]
    · ext i
      simp
    · simp
  have hdir :
      (Finsupp.single (fun i ↦ (r i : ℝ))
          (M * rational_vector_common_denominator r)).sum
        (fun s n ↦ (n : ℝ) • s) =
        (((M * rational_vector_common_denominator r : ℕ) : ℝ)) •
          (fun i ↦ (r i : ℝ)) := by
    -- The directional singleton contributes the expected scalar multiple of `r`.
    rw [Finsupp.sum_single_index]
    ext i
    simp [Pi.smul_apply, smul_eq_mul]
  have hscaled :
      (((M * rational_vector_common_denominator r : ℕ) : ℝ)) •
          (fun i ↦ (r i : ℝ)) =
        fun i ↦ (((M : ℤ) * common_denominator_scaled_vector r i : ℤ) : ℝ) := by
    -- Convert the denominator-cleared rational direction into the integer witness on `ℤ^q`.
    ext i
    have hi :
        ((common_denominator_scaled_vector r i : ℤ) : ℝ) =
          (rational_vector_common_denominator r : ℝ) * (r i : ℝ) := by
      simpa [Pi.smul_apply, smul_eq_mul] using
        congrFun (commonDenominatorScaledVector_eq_smulReal r) i
    calc
      ((((M * rational_vector_common_denominator r : ℕ) : ℝ)) • (fun i ↦ (r i : ℝ))) i =
          (((M * rational_vector_common_denominator r : ℕ) : ℝ)) * (r i : ℝ) := by
            simp [Pi.smul_apply, smul_eq_mul]
      _ = (M : ℝ) * ((rational_vector_common_denominator r : ℝ) * (r i : ℝ)) := by
            simp [Nat.cast_mul, mul_assoc]
      _ = (M : ℝ) * ((common_denominator_scaled_vector r i : ℤ) : ℝ) := by
            rw [hi.symm]
      _ = (((M : ℤ) * common_denominator_scaled_vector r i : ℤ) : ℝ) := by
            simp
  have hxsum :
      (Finsupp.single (fun i ↦ -(f i : ℝ)) 1 +
          Finsupp.single (fun i ↦ (r i : ℝ))
            (M * rational_vector_common_denominator r)).sum
        (fun s n ↦ (n : ℝ) • s) =
        (fun i ↦ -(f i : ℝ)) +
          fun i ↦ (((M : ℤ) * common_denominator_scaled_vector r i : ℤ) : ℝ) := by
    calc
      (Finsupp.single (fun i ↦ -(f i : ℝ)) 1 +
            Finsupp.single (fun i ↦ (r i : ℝ))
              (M * rational_vector_common_denominator r)).sum
          (fun s n ↦ (n : ℝ) • s) =
          (Finsupp.single (fun i ↦ -(f i : ℝ)) 1).sum (fun s n ↦ (n : ℝ) • s) +
            (Finsupp.single (fun i ↦ (r i : ℝ))
              (M * rational_vector_common_denominator r)).sum
              (fun s n ↦ (n : ℝ) • s) := by
            rw [Finsupp.sum_add_index]
            · simp
            · simp
            · intro s hs b₁ b₂
              ext i
              simp [Nat.cast_add, add_mul]
      _ = (fun i ↦ -(f i : ℝ)) +
            ((((M * rational_vector_common_denominator r : ℕ) : ℝ)) •
              (fun i ↦ (r i : ℝ))) := by
            rw [hbase, hdir]
      _ = (fun i ↦ -(f i : ℝ)) +
            fun i ↦ (((M : ℤ) * common_denominator_scaled_vector r i : ℤ) : ℝ) := by
            rw [hscaled]
  -- The `-f` singleton cancels the shift, leaving the denominator-cleared multiple of `r`.
  rw [hxsum]
  ext i
  simp

/-- Helper for Remark 6.3-extra-2: the cut value of the canonical rational-slice test point
separates into the base contribution at `-f` and the contribution of the added copies of `r`. -/
lemma rationalSliceTestPoint_cutValue
    (f : Qq) (π : Rq → ℝ) (r : Qq) (M : ℕ) :
    (Finsupp.single (fun i ↦ -(f i : ℝ)) 1 +
        Finsupp.single (fun i ↦ (r i : ℝ))
          (M * rational_vector_common_denominator r)).sum
      (fun s n ↦ π s * (n : ℝ)) =
      π (fun i ↦ -(f i : ℝ)) +
        π (fun i ↦ (r i : ℝ)) *
          (((M * rational_vector_common_denominator r : ℕ) : ℝ)) := by
  have hbase :
      (Finsupp.single (fun i ↦ -(f i : ℝ)) 1).sum
        (fun s n ↦ π s * (n : ℝ)) =
        π (fun i ↦ -(f i : ℝ)) := by
    -- The base singleton contributes a single copy of `π (-f)`.
    rw [Finsupp.sum_single_index]
    · simp
    · simp
  have hdir :
      (Finsupp.single (fun i ↦ (r i : ℝ))
          (M * rational_vector_common_denominator r)).sum
        (fun s n ↦ π s * (n : ℝ)) =
        π (fun i ↦ (r i : ℝ)) *
          (((M * rational_vector_common_denominator r : ℕ) : ℝ)) := by
    -- The directional singleton contributes the slope `π r` times the chosen step size.
    rw [Finsupp.sum_single_index]
    simp
  have hsum :
      (Finsupp.single (fun i ↦ -(f i : ℝ)) 1 +
          Finsupp.single (fun i ↦ (r i : ℝ))
            (M * rational_vector_common_denominator r)).sum
        (fun s n ↦ π s * (n : ℝ)) =
        π (fun i ↦ -(f i : ℝ)) +
          π (fun i ↦ (r i : ℝ)) *
            (((M * rational_vector_common_denominator r : ℕ) : ℝ)) := by
    calc
      (Finsupp.single (fun i ↦ -(f i : ℝ)) 1 +
            Finsupp.single (fun i ↦ (r i : ℝ))
              (M * rational_vector_common_denominator r)).sum
          (fun s n ↦ π s * (n : ℝ)) =
          (Finsupp.single (fun i ↦ -(f i : ℝ)) 1).sum
              (fun s n ↦ π s * (n : ℝ)) +
            (Finsupp.single (fun i ↦ (r i : ℝ))
              (M * rational_vector_common_denominator r)).sum
              (fun s n ↦ π s * (n : ℝ)) := by
            rw [Finsupp.sum_add_index]
            · simp
            · simp
            · intro s hs a b
              simp [Nat.cast_add, left_distrib]
      _ = π (fun i ↦ -(f i : ℝ)) +
            π (fun i ↦ (r i : ℝ)) *
              (((M * rational_vector_common_denominator r : ℕ) : ℝ)) := by
            rw [hbase, hdir]
  -- Linearize the finitely supported sum so the two singleton contributions appear separately.
  exact hsum

/-- Helper for Remark 6.3-extra-2: a negative slope along a positive integer step eventually drives
an affine expression below `1`. -/
lemma exists_nat_cutViolation_of_negativeSlope
    {a b : ℝ} {D : ℕ}
    (hb : b < 0)
    (hD : 0 < D) :
    ∃ M : ℕ, a + b * (((M * D : ℕ) : ℝ)) < 1 := by
  have hstep : 0 < (D : ℝ) * (-b) := by
    have hb' : 0 < -b := by
      linarith
    exact mul_pos (by exact_mod_cast hD) hb'
  obtain ⟨M, hM⟩ := exists_nat_gt ((a - 1) / ((D : ℝ) * (-b)))
  refine ⟨M, ?_⟩
  have hM' : ((a - 1) / ((D : ℝ) * (-b))) < (M : ℝ) := by
    exact_mod_cast hM
  have hbound : a - 1 < (((M * D : ℕ) : ℝ)) * (-b) := by
    have hbound' : a - 1 < (M : ℝ) * ((D : ℝ) * (-b)) := by
      exact (div_lt_iff₀ hstep).mp hM'
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hbound'
  nlinarith

/-- Remark 6.3-extra-2: if `(π, ψ)` satisfies the validity inequality
`∑ π(r) x_r + ∑ ψ(r) y_r ≥ 1` for every `(x, y) ∈ M_f`, then `π` is nonnegative on every
rational vector. This source-facing nonnegative slice is stated directly over the Chapter 6
mixed-integer owner `mixed_integer_relaxation_set`. -/
theorem valid_function_nonneg_on_rational_vectors
    (f : Qq)
    (π ψ : Rq → ℝ)
    (hvalid :
      ∀ {x : NatAssignment} {y : ContAssignment},
        (x, y) ∈ mixed_integer_relaxation_set (fun i ↦ (f i : ℝ)) →
          1 ≤ x.sum (fun r n ↦ π r * (n : ℝ)) + y.sum (fun r a ↦ ψ r * (a : ℝ)))
    (r : Qq) :
    0 ≤ π (fun i ↦ (r i : ℝ)) := by
  -- Route correction: contradict validity by sending a feasible rational-slice test point
  -- far enough in a direction where `π` is assumed negative.
  by_contra hnonneg
  have hneg : π (fun i ↦ (r i : ℝ)) < 0 := by
    exact lt_of_not_ge hnonneg
  have hDpos : 0 < rational_vector_common_denominator r := by
    exact Nat.pos_of_ne_zero (rationalVectorCommonDenominator_ne_zero r)
  -- Choose enough denominator-cleared copies of `r` to force the cut value below `1`.
  obtain ⟨M, hM⟩ :=
    exists_nat_cutViolation_of_negativeSlope
      (a := π (fun i ↦ -(f i : ℝ)))
      (b := π (fun i ↦ (r i : ℝ)))
      (D := rational_vector_common_denominator r)
      hneg hDpos
  have hvalidM :
      1 ≤
        (Finsupp.single (fun i ↦ -(f i : ℝ)) 1 +
            Finsupp.single (fun i ↦ (r i : ℝ))
              (M * rational_vector_common_denominator r)).sum
            (fun s n ↦ π s * (n : ℝ)) +
          (0 : ContAssignment).sum (fun s a ↦ ψ s * (a : ℝ)) := by
    exact hvalid
      (rationalSliceTestPoint_memMixedIntegerRelaxationSet (f := f) (r := r) (M := M))
  -- Normalize the cut expression at the chosen feasible test point.
  rw [rationalSliceTestPoint_cutValue (f := f) (π := π) (r := r) (M := M)] at hvalidM
  have hvalidM' :
      1 ≤
        π (fun i ↦ -(f i : ℝ)) +
          π (fun i ↦ (r i : ℝ)) *
            (((M * rational_vector_common_denominator r : ℕ) : ℝ)) := by
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hvalidM
  nlinarith

namespace IsValidGomoryJohnsonPair

/-- A valid Gomory--Johnson pair is, in particular, nonnegative on the rational slice singled out in
Remark 6.3-extra-2. -/
theorem nonneg_on_rational_vectors
    {f : Qq}
    {π ψ : Rq → ℝ}
    (hπψ : IsValidGomoryJohnsonPair (fun i ↦ (f i : ℝ)) π ψ)
    (r : Qq) :
    0 ≤ π (fun i ↦ (r i : ℝ)) :=
  hπψ.nonneg (fun i ↦ (r i : ℝ))

end IsValidGomoryJohnsonPair

end Remark63Extra2
