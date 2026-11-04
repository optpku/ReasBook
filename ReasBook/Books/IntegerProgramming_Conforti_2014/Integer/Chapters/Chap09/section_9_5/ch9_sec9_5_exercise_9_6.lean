/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_5.ch9_sec9_5_exercise_9_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open InnerProductSpace Module

-- This file reuses the Chapter 9 owner `IsReducedBasis` together with the reusable lattice owner
-- `B.integerSpan` and shortest-vector predicate `Submodule.IsShortestNonzeroVector`.

universe u

section Exercise96

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Exercise 9.6: the normalized `i`-th Gram-Schmidt vector pairs with `B i` by the
length of the unnormalized Gram-Schmidt vector. -/
lemma gramSchmidtNormed_inner_self_eq_norm
    {n : ℕ}
    (B : Basis (Fin n) ℝ E)
    (i : Fin n) :
    ⟪gramSchmidtNormed ℝ B i, B i⟫_ℝ = ‖gramSchmidt ℝ B i‖ := by
  have hg_ne : gramSchmidt ℝ B i ≠ 0 :=
    InnerProductSpace.gramSchmidt_ne_zero (𝕜 := ℝ) (f := B) i B.linearIndependent
  have hnorm_ne : ‖gramSchmidt ℝ B i‖ ≠ 0 := norm_ne_zero_iff.mpr hg_ne
  -- Normalize the diagonal Gram-Schmidt pairing from Exercise 9.5.
  calc
    ⟪gramSchmidtNormed ℝ B i, B i⟫_ℝ
        = (‖gramSchmidt ℝ B i‖ : ℝ)⁻¹ * ⟪gramSchmidt ℝ B i, B i⟫_ℝ := by
            simp [gramSchmidtNormed, inner_smul_left]
    _ = (‖gramSchmidt ℝ B i‖ : ℝ)⁻¹ * ‖gramSchmidt ℝ B i‖ ^ 2 := by
          rw [gramSchmidtSelfInner_eq_normSq B i]
    _ = ‖gramSchmidt ℝ B i‖ := by
          rw [pow_two]
          field_simp [hnorm_ne]

/-- Helper for Exercise 9.6: an upper-triangular Gram-Schmidt coordinate of `B j` along the
earlier normalized direction `i` is `μ_{j,i} ‖g_i‖`. -/
lemma gramSchmidtNormed_inner_basis_eq_coefficient_mul_norm
    {n : ℕ}
    (B : Basis (Fin n) ℝ E)
    (i j : Fin n) :
    ⟪gramSchmidtNormed ℝ B i, B j⟫_ℝ =
      gram_schmidt_coefficient B j i * ‖gramSchmidt ℝ B i‖ := by
  have hg_ne : gramSchmidt ℝ B i ≠ 0 :=
    InnerProductSpace.gramSchmidt_ne_zero (𝕜 := ℝ) (f := B) i B.linearIndependent
  have hnorm_ne : ‖gramSchmidt ℝ B i‖ ≠ 0 := norm_ne_zero_iff.mpr hg_ne
  -- Rewrite the normalized coordinate through the Gram-Schmidt coefficient definition.
  calc
    ⟪gramSchmidtNormed ℝ B i, B j⟫_ℝ
        = (‖gramSchmidt ℝ B i‖ : ℝ)⁻¹ * ⟪gramSchmidt ℝ B i, B j⟫_ℝ := by
            simp [gramSchmidtNormed, inner_smul_left]
    _ = (‖gramSchmidt ℝ B i‖ : ℝ)⁻¹ * ⟪B j, gramSchmidt ℝ B i⟫_ℝ := by
          rw [real_inner_comm]
    _ = gram_schmidt_coefficient B j i * ‖gramSchmidt ℝ B i‖ := by
          rw [gram_schmidt_coefficient, coe_gramSchmidtBasis, div_eq_mul_inv]
          field_simp [hnorm_ne]

/-- Helper for Exercise 9.6: pairing `u` with the normalized `i`-th Gram-Schmidt direction
extracts the triangular coefficient expression at index `i`. -/
lemma gramSchmidtCoordinateExpansion
    {n : ℕ}
    (B : Basis (Fin n) ℝ E)
    (coeff : Fin n → ℤ)
    (u : E)
    (hu_eq : u = ∑ i, coeff i • B i)
    (i : Fin n) :
    ⟪gramSchmidtNormed ℝ B i, u⟫_ℝ =
      ((coeff i : ℝ) + (∑ j ∈ Finset.Ioi i,
          (coeff j : ℝ) * gram_schmidt_coefficient B j i)) *
        ‖gramSchmidt ℝ B i‖ := by
  let f : Fin n → ℝ := fun j ↦ ⟪gramSchmidtNormed ℝ B i, (coeff j : ℝ) • B j⟫_ℝ
  have hu_eq_real : u = ∑ j, (coeff j : ℝ) • B j := by
    simpa [← Int.cast_smul_eq_zsmul ℝ] using hu_eq
  have hsplit :
      ∑ j : Fin n, f j =
        ∑ j ∈ Finset.Iio i, f j + (f i + ∑ j ∈ Finset.Ioi i, f j) := by
    -- Split the full basis expansion into the indices below `i`, the diagonal term, and the tail.
    calc
      ∑ j : Fin n, f j = ∑ j ∈ Finset.Iio i, f j + ∑ j ∈ (Finset.Iio i)ᶜ, f j := by
        symm
        exact Finset.sum_add_sum_compl (Finset.Iio i) f
      _ = ∑ j ∈ Finset.Iio i, f j + ∑ j ∈ Finset.Ici i, f j := by
        have hcompl : (Finset.Iio i)ᶜ = Finset.Ici i := by
          ext j
          simp
        rw [hcompl]
      _ = ∑ j ∈ Finset.Iio i, f j + (f i + ∑ j ∈ Finset.Ioi i, f j) := by
        rw [Finset.add_sum_Ioi_eq_sum_Ici]
  have hIio_zero : ∑ j ∈ Finset.Iio i, f j = 0 := by
    -- Lower-index terms are orthogonal to the `i`-th Gram-Schmidt direction.
    apply Finset.sum_eq_zero
    intro j hj
    have hji : j < i := Finset.mem_Iio.mp hj
    have htri : ⟪gramSchmidt ℝ B i, B j⟫_ℝ = 0 :=
      gramSchmidt_inv_triangular ℝ B hji
    rw [show f j = ⟪gramSchmidtNormed ℝ B i, (coeff j : ℝ) • B j⟫_ℝ by rfl]
    rw [inner_smul_right, gramSchmidtNormed, inner_smul_left, htri]
    ring
  have hdiag : f i = (coeff i : ℝ) * ‖gramSchmidt ℝ B i‖ := by
    -- The diagonal term contributes the current coefficient times `‖g_i‖`.
    rw [show f i = ⟪gramSchmidtNormed ℝ B i, (coeff i : ℝ) • B i⟫_ℝ by rfl]
    rw [inner_smul_right, gramSchmidtNormed_inner_self_eq_norm B i]
  have hIoi :
      ∑ j ∈ Finset.Ioi i, f j =
        (∑ j ∈ Finset.Ioi i,
            (coeff j : ℝ) * gram_schmidt_coefficient B j i) *
          ‖gramSchmidt ℝ B i‖ := by
    -- Upper-index terms keep exactly the Gram-Schmidt coefficients from the reduced-basis data.
    calc
      ∑ j ∈ Finset.Ioi i, f j
          = ∑ j ∈ Finset.Ioi i,
              ((coeff j : ℝ) * gram_schmidt_coefficient B j i) *
                ‖gramSchmidt ℝ B i‖ := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [show f j = ⟪gramSchmidtNormed ℝ B i, (coeff j : ℝ) • B j⟫_ℝ by rfl]
              rw [inner_smul_right, gramSchmidtNormed_inner_basis_eq_coefficient_mul_norm B i j]
              ring
      _ = (∑ j ∈ Finset.Ioi i,
              (coeff j : ℝ) * gram_schmidt_coefficient B j i) *
            ‖gramSchmidt ℝ B i‖ := by
              rw [Finset.sum_mul]
  -- Assemble the three pieces of the coordinate expansion.
  calc
    ⟪gramSchmidtNormed ℝ B i, u⟫_ℝ = ∑ j : Fin n, f j := by
      rw [hu_eq_real, inner_sum]
    _ = ∑ j ∈ Finset.Iio i, f j + (f i + ∑ j ∈ Finset.Ioi i, f j) := hsplit
    _ = ((coeff i : ℝ) + ∑ j ∈ Finset.Ioi i,
          (coeff j : ℝ) * gram_schmidt_coefficient B j i) *
        ‖gramSchmidt ℝ B i‖ := by
          rw [hIio_zero, hdiag, hIoi]
          ring

/-- Helper for Exercise 9.6: the triangular Gram-Schmidt coordinate of a shortest nonzero lattice
vector is bounded by the coarse reduced-basis factor `2^i`. -/
lemma gramSchmidtCoordinateAbs_le_powTwoIndex
    {n : ℕ}
    (hn : 0 < n)
    (B : Basis (Fin n) ℝ E)
    (hBred : IsReducedBasis B)
    (u : E)
    (hu_shortest : B.integerSpan.IsShortestNonzeroVector u)
    (coeff : Fin n → ℤ)
    (hu_eq : u = ∑ i, coeff i • B i)
    (i : Fin n) :
    |(coeff i : ℝ) + (∑ j ∈ Finset.Ioi i,
        (coeff j : ℝ) * gram_schmidt_coefficient B j i)|
      ≤ (2 : ℝ) ^ i.1 := by
  let α : ℝ :=
    (coeff i : ℝ) + ∑ j ∈ Finset.Ioi i,
      (coeff j : ℝ) * gram_schmidt_coefficient B j i
  let b0 : Fin n := ⟨0, hn⟩
  have hmem_b0 : B b0 ∈ B.integerSpan := by
    refine Submodule.subset_span ?_
    exact ⟨b0, rfl⟩
  have hshort : ‖u‖ ≤ ‖B b0‖ :=
    hu_shortest.norm_le hmem_b0 (B.ne_zero b0)
  have hcoord :
      ⟪gramSchmidtNormed ℝ B i, u⟫_ℝ = α * ‖gramSchmidt ℝ B i‖ := by
    simpa [α] using gramSchmidtCoordinateExpansion B coeff u hu_eq i
  have hcoord_norm : |α| * ‖gramSchmidt ℝ B i‖ ≤ ‖u‖ := by
    -- The normalized Gram-Schmidt direction has unit norm, so the coordinate is controlled by
    -- the norm of `u`.
    calc
      |α| * ‖gramSchmidt ℝ B i‖ = ‖⟪gramSchmidtNormed ℝ B i, u⟫_ℝ‖ := by
        rw [hcoord, norm_mul, Real.norm_eq_abs, norm_norm]
      _ ≤ ‖gramSchmidtNormed ℝ B i‖ * ‖u‖ := norm_inner_le_norm _ _
      _ = ‖u‖ := by
        simp [gramSchmidtNormed_unit_length i B.linearIndependent]
  have hcoord_sq : |α| ^ 2 * ‖gramSchmidt ℝ B i‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    have hsquare : (|α| * ‖gramSchmidt ℝ B i‖) ^ 2 ≤ ‖u‖ ^ 2 :=
      (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 hcoord_norm
    nlinarith [hsquare]
  have hshort_sq : ‖u‖ ^ 2 ≤ ‖B b0‖ ^ 2 := by
    have hsquare := mul_self_le_mul_self (norm_nonneg u) hshort
    simpa [pow_two] using hsquare
  have hfirst :
      ‖B b0‖ ^ 2 ≤ (2 : ℝ) ^ i.1 * ‖gramSchmidt ℝ B i‖ ^ 2 :=
    firstBasisVector_normSq_le_pow_two_mul_gramSchmidt hn B hBred i
  have hg_ne : gramSchmidt ℝ B i ≠ 0 :=
    InnerProductSpace.gramSchmidt_ne_zero (𝕜 := ℝ) (f := B) i B.linearIndependent
  have hnorm_sq_pos : 0 < ‖gramSchmidt ℝ B i‖ ^ 2 := by
    positivity
  have hsq : |α| ^ 2 ≤ (2 : ℝ) ^ i.1 := by
    nlinarith [hcoord_sq, hshort_sq, hfirst, hnorm_sq_pos]
  have hpow_one : (1 : ℝ) ≤ (2 : ℝ) ^ i.1 := by
    exact one_le_pow₀ (by norm_num)
  -- `|α|^2 ≤ 2^i` is stronger than needed; use `2^i ≥ 1` to return to a linear bound.
  nlinarith [hsq, abs_nonneg α, hpow_one]

/-- Helper for Exercise 9.6: reducedness converts the Gram-Schmidt coordinate bound into a
recursive inequality for the absolute values of the integer coefficients. -/
lemma coeffAbsRecurrenceOfReducedBasis
    {n : ℕ}
    (hn : 0 < n)
    (B : Basis (Fin n) ℝ E)
    (hBred : IsReducedBasis B)
    (u : E)
    (hu_shortest : B.integerSpan.IsShortestNonzeroVector u)
    (coeff : Fin n → ℤ)
    (hu_eq : u = ∑ i, coeff i • B i)
    (i : Fin n) :
    (|coeff i| : ℝ) ≤
      (2 : ℝ) ^ i.1 + (1 / 2 : ℝ) * (∑ j ∈ Finset.Ioi i, (|coeff j| : ℝ)) := by
  let tail : ℝ :=
    ∑ j ∈ Finset.Ioi i, (coeff j : ℝ) * gram_schmidt_coefficient B j i
  have halpha :
      |(coeff i : ℝ) + tail| ≤ (2 : ℝ) ^ i.1 := by
    simpa [tail] using
      gramSchmidtCoordinateAbs_le_powTwoIndex hn B hBred u hu_shortest coeff hu_eq i
  have htail :
      |tail| ≤ (1 / 2 : ℝ) * ∑ j ∈ Finset.Ioi i, (|coeff j| : ℝ) := by
    -- Bound the tail by the size-reduction inequalities `|μ_{j,i}| ≤ 1 / 2`.
    calc
      |tail|
          = |∑ j ∈ Finset.Ioi i,
              (coeff j : ℝ) * gram_schmidt_coefficient B j i| := by
                simp [tail]
      _ ≤ ∑ j ∈ Finset.Ioi i,
            |(coeff j : ℝ) * gram_schmidt_coefficient B j i| := by
              exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ Finset.Ioi i,
            |(coeff j : ℝ)| * |gram_schmidt_coefficient B j i| := by
              simp [abs_mul]
      _ ≤ ∑ j ∈ Finset.Ioi i,
            |(coeff j : ℝ)| * (1 / 2 : ℝ) := by
              refine Finset.sum_le_sum ?_
              intro j hj
              exact mul_le_mul_of_nonneg_left
                (hBred.condition_i (Finset.mem_Ioi.mp hj))
                (abs_nonneg _)
      _ = ∑ j ∈ Finset.Ioi i, (|coeff j| : ℝ) * (1 / 2 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rfl
      _ = (∑ j ∈ Finset.Ioi i, (|coeff j| : ℝ)) * (1 / 2 : ℝ) := by
            rw [Finset.sum_mul]
      _ = (1 / 2 : ℝ) * ∑ j ∈ Finset.Ioi i, (|coeff j| : ℝ) := by
            ring
  have hsplit :
      (|coeff i| : ℝ) ≤ |(coeff i : ℝ) + tail| + |tail| := by
    -- Rewrite `coeff i` as the difference between the whole coordinate and the tail.
    have hcoeff_eq : ((coeff i : ℝ) + tail) - tail = (coeff i : ℝ) := by
      ring
    calc
      (|coeff i| : ℝ) = |(coeff i : ℝ)| := by
        rfl
      _ = |((coeff i : ℝ) + tail) - tail| := by
        rw [hcoeff_eq]
      _ ≤ |(coeff i : ℝ) + tail| + |tail| := by
        simpa using abs_sub ((coeff i : ℝ) + tail) tail
  exact le_trans hsplit (add_le_add halpha htail)

/-- Helper for Exercise 9.6: the tail sums of the coefficient absolutes satisfy a reverse
induction bound with ratio `3`. -/
lemma coeffAbsTailSumBound
    {m : ℕ}
    (B : Basis (Fin (m + 1)) ℝ E)
    (hBred : IsReducedBasis B)
    (u : E)
    (hu_shortest : B.integerSpan.IsShortestNonzeroVector u)
    (coeff : Fin (m + 1) → ℤ)
    (hu_eq : u = ∑ i, coeff i • B i) :
    ∀ i : Fin (m + 1),
      (∑ j ∈ Finset.Ici i, (|coeff j| : ℝ))
        ≤ (2 : ℝ) ^ i.1 * ((3 : ℝ) ^ ((m + 1) - i.1) - 1) := by
  intro i
  refine Fin.reverseInduction ?_ ?_ i
  · have hlast :
        (|coeff (Fin.last m)| : ℝ) ≤ (2 : ℝ) ^ (Fin.last m).1 := by
      -- At the last index there is no remaining tail term.
      have hrecur :=
        coeffAbsRecurrenceOfReducedBasis (Nat.succ_pos m) B hBred u hu_shortest coeff hu_eq
          (Fin.last m)
      have htail_zero : ∑ j ∈ Finset.Ioi (Fin.last m), (|coeff j| : ℝ) = 0 := by
        have hset : Finset.Ioi (Fin.last m) = ∅ := by
          ext j
          simp [Fin.lt_def, Fin.last]
          omega
        rw [hset]
        simp
      rw [htail_zero] at hrecur
      simpa using hrecur
    calc
      ∑ j ∈ Finset.Ici (Fin.last m), (|coeff j| : ℝ) = (|coeff (Fin.last m)| : ℝ) := by
        have hset : Finset.Ici (Fin.last m) = {Fin.last m} := by
          ext j
          simp only [Finset.mem_Ici, Finset.mem_singleton]
          constructor
          · intro hj
            apply Fin.ext
            have hj' : m ≤ j.1 := by
              simpa [Fin.last] using hj
            have hj'' : j.1 ≤ m := Nat.le_of_lt_succ j.2
            simp [Fin.last]
            omega
          · intro hj
            subst hj
            simp
        rw [hset]
        simp
      _ ≤ (2 : ℝ) ^ (Fin.last m).1 := hlast
      _ ≤ (2 : ℝ) ^ (Fin.last m).1 * ((3 : ℝ) ^ ((m + 1) - (Fin.last m).1) - 1) := by
        simp [Fin.last]
        nlinarith [show 0 ≤ (2 : ℝ) ^ m by positivity]
  · intro j ih
    have hrecur :
        (|coeff j.castSucc| : ℝ) ≤
          (2 : ℝ) ^ j.1 + (1 / 2 : ℝ) * ∑ k ∈ Finset.Ioi j.castSucc, (|coeff k| : ℝ) := by
      simpa using
        coeffAbsRecurrenceOfReducedBasis (Nat.succ_pos m) B hBred u hu_shortest coeff hu_eq
          j.castSucc
    have htail_eq :
        ∑ k ∈ Finset.Ioi j.castSucc, (|coeff k| : ℝ) =
          ∑ k ∈ Finset.Ici j.succ, (|coeff k| : ℝ) := by
      -- Moving one step to the right replaces the strict tail by the inclusive tail.
      have hset : Finset.Ioi j.castSucc = Finset.Ici j.succ := by
        ext k
        simp only [Finset.mem_Ioi, Finset.mem_Ici]
        change j.1 < k.1 ↔ j.1 + 1 ≤ k.1
        omega
      rw [hset]
    have ih' :
        ∑ k ∈ Finset.Ici j.succ, (|coeff k| : ℝ) ≤
          (2 : ℝ) ^ (j.1 + 1) * ((3 : ℝ) ^ (m - j.1) - 1) := by
      simpa using ih
    have hpow2 : (2 : ℝ) ^ (j.1 + 1) = 2 * (2 : ℝ) ^ j.1 := by
      rw [pow_succ]
      ring
    have hpow3 : (3 : ℝ) ^ ((m + 1) - j.1) = 3 * (3 : ℝ) ^ (m - j.1) := by
      have hj : j.1 < m := j.2
      have hNat : (m + 1) - j.1 = (m - j.1) + 1 := by
        omega
      rw [hNat, pow_succ]
      ring
    -- The current tail is the current coefficient plus the next tail.
    calc
      ∑ k ∈ Finset.Ici j.castSucc, (|coeff k| : ℝ)
          = (|coeff j.castSucc| : ℝ) + ∑ k ∈ Finset.Ioi j.castSucc, (|coeff k| : ℝ) := by
              symm
              exact Finset.add_sum_Ioi_eq_sum_Ici (a := j.castSucc)
                (f := fun k ↦ (|coeff k| : ℝ))
      _ ≤ (2 : ℝ) ^ j.1 + (3 / 2 : ℝ) * ∑ k ∈ Finset.Ioi j.castSucc, (|coeff k| : ℝ) := by
            nlinarith [hrecur]
      _ = (2 : ℝ) ^ j.1 + (3 / 2 : ℝ) * ∑ k ∈ Finset.Ici j.succ, (|coeff k| : ℝ) := by
            rw [htail_eq]
      _ ≤ (2 : ℝ) ^ j.1 +
            (3 / 2 : ℝ) * ((2 : ℝ) ^ (j.1 + 1) * ((3 : ℝ) ^ (m - j.1) - 1)) := by
              gcongr
      _ ≤ (2 : ℝ) ^ j.1 * ((3 : ℝ) ^ ((m + 1) - j.1) - 1) := by
            rw [hpow2, hpow3]
            have hpow_nonneg : 0 ≤ (2 : ℝ) ^ j.1 := by
              positivity
            nlinarith

/-- Exercise 9.6. Intrinsically, if `B` is a reduced basis, `u` is a shortest nonzero vector in
the corresponding `ℤ`-span, and `u = ∑ i, λ i • B i`, then every coefficient satisfies
`|λ i| ≤ 3^n`. -/
theorem shortest_nonzero_vector_coeff_bound_of_reduced_basis
    {n : ℕ}
    (B : Basis (Fin n) ℝ E)
    (hBred : IsReducedBasis B)
    (u : E)
    (hu_shortest : B.integerSpan.IsShortestNonzeroVector u)
    (coeff : Fin n → ℤ)
    (hu_eq : u = ∑ i, coeff i • B i) :
    ∀ i : Fin n, |coeff i| ≤ (3 : ℤ) ^ n := by
  cases n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ m =>
      intro i
      -- Route correction: instead of forcing a direct closed form for each coefficient, bound the
      -- whole coefficient tail by reverse induction and then read off the current term.
      have htail :
          (∑ j ∈ Finset.Ici i, (|coeff j| : ℝ))
            ≤ (2 : ℝ) ^ i.1 * ((3 : ℝ) ^ ((m + 1) - i.1) - 1) :=
        coeffAbsTailSumBound B hBred u hu_shortest coeff hu_eq i
      have hterm :
          (|coeff i| : ℝ) ≤ ∑ j ∈ Finset.Ici i, (|coeff j| : ℝ) := by
        -- The current coefficient is one nonnegative term inside the tail sum.
        simpa using
          (Finset.single_le_sum
            (f := fun j ↦ (|coeff j| : ℝ))
            (fun j _ ↦ by positivity)
            (by simp : i ∈ Finset.Ici i))
      have hpow3_nonneg : 0 ≤ (3 : ℝ) ^ ((m + 1) - i.1) := by
        positivity
      have hmain_real :
          (|coeff i| : ℝ) ≤ (2 : ℝ) ^ i.1 * (3 : ℝ) ^ ((m + 1) - i.1) := by
        calc
          (|coeff i| : ℝ) ≤ ∑ j ∈ Finset.Ici i, (|coeff j| : ℝ) := hterm
          _ ≤ (2 : ℝ) ^ i.1 * ((3 : ℝ) ^ ((m + 1) - i.1) - 1) := htail
          _ ≤ (2 : ℝ) ^ i.1 * (3 : ℝ) ^ ((m + 1) - i.1) := by
                gcongr
                nlinarith
      have hpow2_le :
          (2 : ℝ) ^ i.1 ≤ (3 : ℝ) ^ i.1 := by
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) i.1
      have hreal :
          (|coeff i| : ℝ) ≤ (3 : ℝ) ^ (m + 1) := by
        calc
          (|coeff i| : ℝ) ≤ (2 : ℝ) ^ i.1 * (3 : ℝ) ^ ((m + 1) - i.1) := hmain_real
          _ ≤ (3 : ℝ) ^ i.1 * (3 : ℝ) ^ ((m + 1) - i.1) := by
                have hpow3_nonneg' : 0 ≤ (3 : ℝ) ^ ((m + 1) - i.1) := by
                  positivity
                exact mul_le_mul_of_nonneg_right hpow2_le hpow3_nonneg'
          _ = (3 : ℝ) ^ (m + 1) := by
                rw [← pow_add]
                have hi_le : i.1 ≤ m + 1 := Nat.le_of_lt i.2
                rw [Nat.add_sub_of_le hi_le]
      have hreal_int :
          (|coeff i| : ℝ) ≤ (((3 : ℤ) ^ (m + 1) : ℤ) : ℝ) := by
        simpa using hreal
      exact_mod_cast hreal_int

end Exercise96
