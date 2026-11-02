import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_1_theorem_9_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_1_theorem_9_4
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.LinearAlgebra.Basis.SMul

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix
open InnerProductSpace Module

section Exercise94

/-
Domain sampling for this exercise:
* primary domain: reduced bases of rank-`2` lattices in Euclidean space
* core/canonical owner: `IsReducedBasis`
* intrinsic lattice owners: `matrix_generated_lattice B` in coordinates and
  `Submodule.span ℤ (Set.range b)` in Euclidean space
* bridge/view: `image_span_cols_eq_euclidean_span_cols`
-/

namespace IsReducedBasis

/-- Helper for Exercise 9.4: in dimension `2`, the first Gram-Schmidt basis vector of `b` is
just `b 0`. -/
lemma gramSchmidtBasis_zero_eq
    (b : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2))) :
    InnerProductSpace.gramSchmidtBasis b 0 = b 0 := by
  rw [InnerProductSpace.coe_gramSchmidtBasis]
  exact InnerProductSpace.gramSchmidt_bot (𝕜 := ℝ) (f := b)

/-- Helper for Exercise 9.4: in dimension `2`, the coefficient `μ₁₀` is the normalized inner
product `⟪b 0, b 1⟫ / ‖b 0‖²`. -/
lemma gramSchmidtCoefficient_one_zero_eq_inner_div_normSq
    (b : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2))) :
    gram_schmidt_coefficient b 1 0 = ⟪b 0, b 1⟫_ℝ / ‖b 0‖ ^ 2 := by
  rw [gram_schmidt_coefficient, gramSchmidtBasis_zero_eq, real_inner_comm]

/-- Helper for Exercise 9.4: in dimension `2`, the second basis vector is exactly the unique
Gram-Schmidt Step 2 combination. -/
lemma secondVector_eq_gramSchmidtBasis_add_coefficient_smul_first
    (b : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2))) :
    b 1 = InnerProductSpace.gramSchmidtBasis b 1 + gram_schmidt_coefficient b 1 0 • b 0 := by
  have hIio : Finset.Iio (1 : Fin 2) = {0} := by
    decide
  have h_gs0 : InnerProductSpace.gramSchmidt ℝ (⇑b) 0 = b 0 := by
    exact InnerProductSpace.gramSchmidt_bot (𝕜 := ℝ) (f := b)
  have h_gs1 :
      b 1 =
        InnerProductSpace.gramSchmidt ℝ (⇑b) 1 +
          gram_schmidt_coefficient b 1 0 • b 0 := by
    calc
      b 1 = InnerProductSpace.gramSchmidt ℝ (⇑b) 1 +
            (⟪InnerProductSpace.gramSchmidt ℝ (⇑b) 0, b 1⟫_ℝ /
                ‖InnerProductSpace.gramSchmidt ℝ (⇑b) 0‖ ^ 2) •
              InnerProductSpace.gramSchmidt ℝ (⇑b) 0 := by
            have hdecomp := InnerProductSpace.gramSchmidt_def'' (𝕜 := ℝ) (f := b) (n := 1)
            rw [hIio, Finset.sum_singleton] at hdecomp
            exact hdecomp
      _ = InnerProductSpace.gramSchmidt ℝ (⇑b) 1 +
            gram_schmidt_coefficient b 1 0 • b 0 := by
            rw [gramSchmidtCoefficient_one_zero_eq_inner_div_normSq, h_gs0]
  rw [InnerProductSpace.coe_gramSchmidtBasis]
  exact h_gs1

/-- Helper for Exercise 9.4: in dimension `2`, the reduced-basis conditions imply the explicit
coefficient and norm bounds that no longer mention the `Fin 2` Gram-Schmidt indices. -/
lemma twoDimensionalReducedBasisBounds
    {b : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2))}
    (hb : IsReducedBasis b) :
    |2 * ⟪b 0, b 1⟫_ℝ| ≤ ‖b 0‖ ^ 2 ∧ ‖b 0‖ ≤ ‖b 1‖ := by
  have h_coeff :
      |gram_schmidt_coefficient b 1 0| ≤ (1 : ℝ) / 2 :=
    hb.condition_i (j := 1) (k := 0) (by decide)
  have h_norm_sq_pos : 0 < ‖b 0‖ ^ 2 := by
    have h_norm_pos : 0 < ‖b 0‖ := norm_pos_iff.mpr (b.ne_zero 0)
    nlinarith
  have h_gs0 : InnerProductSpace.gramSchmidt ℝ (⇑b) 0 = b 0 := by
    exact InnerProductSpace.gramSchmidt_bot (𝕜 := ℝ) (f := b)
  have h_coeff' :
      |⟪b 0, b 1⟫_ℝ / ‖b 0‖ ^ 2| ≤ (1 : ℝ) / 2 := by
    -- Normalize the unique `j = 1`, `k = 0` Gram-Schmidt coefficient.
    rw [gramSchmidtCoefficient_one_zero_eq_inner_div_normSq] at h_coeff
    exact h_coeff
  have h_abs_inner : |⟪b 0, b 1⟫_ℝ| ≤ ‖b 0‖ ^ 2 / 2 := by
    have h_mul :
        |⟪b 0, b 1⟫_ℝ / ‖b 0‖ ^ 2| * (‖b 0‖ ^ 2) ≤
          ((1 : ℝ) / 2) * (‖b 0‖ ^ 2) :=
      mul_le_mul_of_nonneg_right h_coeff' (le_of_lt h_norm_sq_pos)
    -- Clear the positive denominator to recover a bound on the inner product itself.
    have h_cancel :
        |⟪b 0, b 1⟫_ℝ / ‖b 0‖ ^ 2| * (‖b 0‖ ^ 2) = |⟪b 0, b 1⟫_ℝ| := by
      rw [abs_div, abs_of_pos h_norm_sq_pos, div_eq_mul_inv, mul_assoc,
        inv_mul_cancel₀ h_norm_sq_pos.ne', mul_one]
    rw [h_cancel] at h_mul
    nlinarith
  have h_abs :
      |2 * ⟪b 0, b 1⟫_ℝ| ≤ ‖b 0‖ ^ 2 := by
    have : 2 * |⟪b 0, b 1⟫_ℝ| ≤ ‖b 0‖ ^ 2 := by
      nlinarith
    simpa [abs_mul] using this
  have h_step2 :
      ‖b 0‖ ≤ ‖b 1‖ := by
    have h_raw := hb.condition_ii 0
    -- Rewrite the unique Step 2 inequality in dimension `2` back to `‖b 0‖ ≤ ‖b 1‖`.
    dsimp at h_raw
    rw [gramSchmidtBasis_zero_eq,
      ← secondVector_eq_gramSchmidtBasis_add_coefficient_smul_first] at h_raw
    exact h_raw
  exact ⟨h_abs, h_step2⟩

/-- The bridge from the Chapter 9 reduced-basis owner to the textbook `60°`-to-`120°` angle
condition in dimension `2`, expressed by inner-product inequalities. -/
theorem angle_bounds
    {b : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2))}
    (hb : IsReducedBasis b) :
    -‖b 0‖ * ‖b 1‖ ≤ 2 * ⟪b 0, b 1⟫_ℝ ∧
      2 * ⟪b 0, b 1⟫_ℝ ≤ ‖b 0‖ * ‖b 1‖ := by
  obtain ⟨h_abs, h_norm⟩ := twoDimensionalReducedBasisBounds hb
  have h_prod : |2 * ⟪b 0, b 1⟫_ℝ| ≤ ‖b 0‖ * ‖b 1‖ := by
    -- Compare the norm square bound with the product bound using the reduced-basis norm order.
    have h_mul : ‖b 0‖ ^ 2 ≤ ‖b 0‖ * ‖b 1‖ := by
      nlinarith [norm_nonneg (b 0), norm_nonneg (b 1), h_norm]
    exact le_trans h_abs h_mul
  have h_prod' := abs_le.mp h_prod
  exact ⟨by nlinarith [h_prod'.1], by nlinarith [h_prod'.2]⟩

/-- In dimension `2`, changing the sign of one vector in a reduced basis preserves its intrinsic
`ℤ`-span and yields a basis whose angle lies between `60°` and `90°`. -/
theorem exists_same_span_basis_with_acute_angle_bounds
    {b : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2))}
    (hb : IsReducedBasis b) :
    ∃ b' : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)),
      Submodule.span ℤ (Set.range b) = Submodule.span ℤ (Set.range b') ∧
      0 ≤ ⟪b' 0, b' 1⟫_ℝ ∧
      2 * ⟪b' 0, b' 1⟫_ℝ ≤ ‖b' 0‖ * ‖b' 1‖ := by
  obtain ⟨h_left, h_right⟩ := angle_bounds hb
  by_cases h_nonneg : 0 ≤ ⟪b 0, b 1⟫_ℝ
  · -- If the angle is already acute, keep the original reduced basis.
    exact ⟨b, rfl, h_nonneg, h_right⟩
  · let s : Fin 2 → ℝ := ![1, -1]
    have hs : ∀ i : Fin 2, IsUnit (s i) := by
      intro i
      fin_cases i <;> simp [s]
    let b' := b.isUnitSMul hs
    have hb0 : b' 0 = b 0 := by
      simp [b', s, Module.Basis.isUnitSMul_apply]
    have hb1 : b' 1 = -b 1 := by
      simp [b', s, Module.Basis.isUnitSMul_apply]
    have h_span :
        Submodule.span ℤ (Set.range b) = Submodule.span ℤ (Set.range b') := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro x ⟨i, rfl⟩
        fin_cases i
        · simpa [hb0] using
            (Submodule.subset_span ⟨0, rfl⟩ :
              b' 0 ∈ Submodule.span ℤ (Set.range b'))
        · have hx : -(b' 1) ∈ Submodule.span ℤ (Set.range b') := by
            exact Submodule.neg_mem _ (Submodule.subset_span ⟨1, rfl⟩)
          simpa [hb1] using hx
      · apply Submodule.span_le.mpr
        rintro x ⟨i, rfl⟩
        fin_cases i
        · simpa [hb0] using
            (Submodule.subset_span ⟨0, rfl⟩ :
              b 0 ∈ Submodule.span ℤ (Set.range b))
        · have hx : -(b 1) ∈ Submodule.span ℤ (Set.range b) := by
            exact Submodule.neg_mem _ (Submodule.subset_span ⟨1, rfl⟩)
          simpa [hb1] using hx
    have h_inner_nonneg : 0 ≤ ⟪b' 0, b' 1⟫_ℝ := by
      -- Negating the second vector flips the sign of the inner product.
      rw [hb0, hb1, inner_neg_right]
      linarith
    have h_bound : 2 * ⟪b' 0, b' 1⟫_ℝ ≤ ‖b' 0‖ * ‖b' 1‖ := by
      -- Reuse the lower angle bound after the sign flip.
      rw [hb0, hb1, inner_neg_right, norm_neg]
      nlinarith
    exact ⟨b', h_span, h_inner_nonneg, h_bound⟩

end IsReducedBasis

/-- Helper for Exercise 9.4: a norm minimizer on a closed-ball slice of a set already minimizes
norm on the whole set. -/
lemma normMinOnClosedBallSlice_global
    {S : Set (EuclideanSpace ℝ (Fin 2))} {r : ℝ} {u : EuclideanSpace ℝ (Fin 2)}
    (hu : u ∈ Metric.closedBall 0 r ∩ S)
    (hu_min : ∀ v ∈ Metric.closedBall 0 r ∩ S, ‖u‖ ≤ ‖v‖) :
    ∀ v ∈ S, ‖u‖ ≤ ‖v‖ := by
  intro v hv
  by_cases hv_ball : v ∈ Metric.closedBall 0 r
  · -- Inside the closed ball, the original slice minimality applies directly.
    exact hu_min v ⟨hv_ball, hv⟩
  · have hu_le : ‖u‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hu.1
    have hr_lt : r < ‖v‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hv_ball
    linarith

/-- Helper for Exercise 9.4: a subset of the lattice generated by a basis has only finitely many
points in any closed ball. -/
lemma finite_closedBall_inter_of_subset_integerSpan
    (b : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)))
    {S : Set (EuclideanSpace ℝ (Fin 2))} {r : ℝ}
    (hS : S ⊆ Submodule.span ℤ (Set.range b)) :
    Set.Finite (Metric.closedBall 0 r ∩ S) := by
  have h_lattice_slice :
      Set.Finite
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r ∩
          (Submodule.span ℤ (Set.range b) : Set (EuclideanSpace ℝ (Fin 2)))) := by
    simpa using
      (ZSpan.setFinite_inter b
        (Metric.isBounded_closedBall :
          Bornology.IsBounded
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r)))
  exact h_lattice_slice.subset (fun x hx ↦ ⟨hx.1, hS hx.2⟩)

/-- Helper for Exercise 9.4: the real shear matrix `!![1, -(m : ℝ); 0, 1]` has determinant `1`. -/
lemma shearMatrix_isUnit_det (m : ℤ) :
    IsUnit ((!![1, -(m : ℝ); 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det) := by
  simp [Matrix.det_fin_two]

/-- Helper for Exercise 9.4: applying the integral shear `b² ↦ b² - m b¹` to an ambient basis of
`ℝ²` gives another ambient basis. -/
noncomputable def shearBasis
    (b : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)))
    (m : ℤ) :
    Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  b.map (((!![1, -(m : ℝ); 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).toLinearEquiv b
    (shearMatrix_isUnit_det m)))

/-- Helper for Exercise 9.4: the shear basis leaves the first basis vector unchanged. -/
lemma shearBasis_zero
    (b : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)))
    (m : ℤ) :
    shearBasis b m 0 = b 0 := by
  simp [shearBasis, Matrix.toLinearEquiv_apply, Matrix.toLin_self]

/-- Helper for Exercise 9.4: the shear basis replaces `b 1` by `b 1 - m • b 0`. -/
lemma shearBasis_one
    (b : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)))
    (m : ℤ) :
    shearBasis b m 1 = b 1 - (m : ℝ) • b 0 := by
  simp [shearBasis, Matrix.toLinearEquiv_apply, Matrix.toLin_self, sub_eq_add_neg, add_comm]

/-- Helper for Exercise 9.4: the shear `b² ↦ b² - m b¹` preserves the intrinsic `ℤ`-span of a
basis of `ℝ²`. -/
lemma span_shearBasis_eq
    (b : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)))
    (m : ℤ) :
    Submodule.span ℤ (Set.range (shearBasis b m)) = Submodule.span ℤ (Set.range b) := by
  have h0 : shearBasis b m 0 = b 0 := shearBasis_zero b m
  have h1 : shearBasis b m 1 = b 1 - m • b 0 := by
    simpa [Int.cast_smul_eq_zsmul] using shearBasis_one b m
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    fin_cases i
    · simpa [h0] using
        (Submodule.subset_span ⟨0, rfl⟩ :
          b 0 ∈ Submodule.span ℤ (Set.range b))
    · simpa [h1] using
        (Submodule.sub_mem _
          (Submodule.subset_span ⟨1, rfl⟩)
          (Submodule.smul_mem _ m (Submodule.subset_span ⟨0, rfl⟩)) :
            b 1 - m • b 0 ∈ Submodule.span ℤ (Set.range b))
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    fin_cases i
    · simpa [h0] using
        (Submodule.subset_span ⟨0, rfl⟩ :
          shearBasis b m 0 ∈ Submodule.span ℤ (Set.range (shearBasis b m)))
    · have hx :
          shearBasis b m 1 + m • shearBasis b m 0 ∈
            Submodule.span ℤ (Set.range (shearBasis b m)) := by
        exact Submodule.add_mem _
          (Submodule.subset_span ⟨1, rfl⟩)
          (Submodule.smul_mem _ m (Submodule.subset_span ⟨0, rfl⟩))
      have hx' : b 1 ∈ Submodule.span ℤ (Set.range (shearBasis b m)) := by
        simpa [h0, h1] using hx
      simpa using hx'

/-- Helper for Exercise 9.4: in dimension `2`, the Step 2 reduced-basis inequality is exactly the
ambient norm comparison `‖b 0‖ ≤ ‖b 1‖`. -/
lemma basisReductionConditionII_of_norm_le
    {b : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2))}
    (h_norm : ‖b 0‖ ≤ ‖b 1‖) :
    basis_reduction_condition_ii b := by
  intro j
  fin_cases j
  dsimp
  -- Rewrite the unique Step 2 inequality back to the ambient norm comparison.
  rw [IsReducedBasis.gramSchmidtBasis_zero_eq,
    ← IsReducedBasis.secondVector_eq_gramSchmidtBasis_add_coefficient_smul_first]
  exact h_norm

/-- Helper for Exercise 9.4: choosing the nearest-integer shear coefficient enforces the Step 1
size-reduction inequality in dimension `2`. -/
lemma basisReductionConditionI_shearBasis
    {b : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2))}
    (h_norm_sq_pos : 0 < ‖b 0‖ ^ 2) :
    basis_reduction_condition_i
      (shearBasis b (round (⟪b 0, b 1⟫_ℝ / ‖b 0‖ ^ 2))) := by
  let m : ℤ := round (⟪b 0, b 1⟫_ℝ / ‖b 0‖ ^ 2)
  have hbShear0 : shearBasis b m 0 = b 0 := shearBasis_zero b m
  have hbShear1 : shearBasis b m 1 = b 1 - (m : ℝ) • b 0 := shearBasis_one b m
  have h_conditionI_coeff :
      |gram_schmidt_coefficient (shearBasis b m) 1 0| ≤ (1 : ℝ) / 2 := by
    have h_coeff0 :
        gram_schmidt_coefficient (shearBasis b m) 1 0 =
          ⟪shearBasis b m 0, shearBasis b m 1⟫_ℝ / ‖shearBasis b m 0‖ ^ 2 := by
      rw [IsReducedBasis.gramSchmidtCoefficient_one_zero_eq_inner_div_normSq]
    have h_coeff :
        gram_schmidt_coefficient (shearBasis b m) 1 0 =
          (⟪b 0, b 1⟫_ℝ / ‖b 0‖ ^ 2) - m := by
      calc
        gram_schmidt_coefficient (shearBasis b m) 1 0
            = ⟪shearBasis b m 0, shearBasis b m 1⟫_ℝ / ‖shearBasis b m 0‖ ^ 2 := h_coeff0
        _ = (⟪b 0, b 1⟫_ℝ - (m : ℝ) * ‖b 0‖ ^ 2) / ‖b 0‖ ^ 2 := by
              rw [hbShear0, hbShear1, inner_sub_right, inner_smul_right,
                real_inner_self_eq_norm_sq]
        _ = ⟪b 0, b 1⟫_ℝ / ‖b 0‖ ^ 2 - (m : ℝ) := by
              rw [sub_div, mul_div_assoc, div_self h_norm_sq_pos.ne', mul_one]
        _ = (⟪b 0, b 1⟫_ℝ / ‖b 0‖ ^ 2) - m := by
              rfl
    -- The shear parameter is the nearest integer to the unique size-reduction coefficient.
    rw [h_coeff]
    simpa [m] using (abs_sub_round (⟪b 0, b 1⟫_ℝ / ‖b 0‖ ^ 2))
  intro j k hj
  fin_cases j
  · simp at hj
  · fin_cases k
    · exact h_conditionI_coeff
    · simp at hj

/-- Helper for Exercise 9.4: transporting `matrix_generated_lattice B` to Euclidean space gives
the intrinsic `ℤ`-span of `euclideanBasisOfMatrix B hB`. -/
lemma euclideanBasisOfMatrix_span_eq_image_matrixGeneratedLattice
    (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : IsUnit B.det) :
    (EuclideanSpace.equiv (Fin 2) ℝ).symm '' matrix_generated_lattice B =
      Submodule.span ℤ (Set.range (euclideanBasisOfMatrix B hB)) := by
  have hb_apply (i : Fin 2) :
      euclideanBasisOfMatrix B hB i = (EuclideanSpace.equiv (Fin 2) ℝ).symm (B.col i) := by
    ext j
    have hcoord :=
      congrFun
        (Matrix.toLin_self
          (v₁ := Pi.basisFun ℝ (Fin 2))
          (v₂ := Pi.basisFun ℝ (Fin 2))
          (M := B)
          (i := i))
        j
    fin_cases j
    · simpa [euclideanBasisOfMatrix, basisOfMatrix, Pi.basisFun_apply] using hcoord
    · simpa [euclideanBasisOfMatrix, basisOfMatrix, Pi.basisFun_apply] using hcoord
  have h_range :
      Set.range (euclideanBasisOfMatrix B hB) =
        Set.range ((EuclideanSpace.equiv (Fin 2) ℝ).symm ∘ B.col) := by
    ext x
    constructor <;> rintro ⟨i, rfl⟩ <;> refine ⟨i, ?_⟩
    · simp [hb_apply i]
    · simp [hb_apply i]
  simpa [h_range] using image_span_cols_eq_euclidean_span_cols B

/-- Exercise 9.4. Any lattice in `ℝ²` given by a nonsingular basis matrix admits a reduced basis
for the same intrinsic lattice, viewed as the Euclidean-space transport of
`matrix_generated_lattice B`. -/
theorem exercise_9_4_exists_reduced_basis
    (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : IsUnit B.det) :
    ∃ b : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)),
      (EuclideanSpace.equiv (Fin 2) ℝ).symm '' matrix_generated_lattice B =
        Submodule.span ℤ (Set.range b) ∧
      IsReducedBasis b := by
  let b₀ : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) := euclideanBasisOfMatrix B hB
  let L : Submodule ℤ (EuclideanSpace ℝ (Fin 2)) := Submodule.span ℤ (Set.range b₀)
  let firstBasisVectors : Set (EuclideanSpace ℝ (Fin 2)) :=
    {u | ∃ b : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)),
      Submodule.span ℤ (Set.range b) = L ∧ b 0 = u}
  let slice : Set (EuclideanSpace ℝ (Fin 2)) :=
    Metric.closedBall 0 ‖b₀ 0‖ ∩ firstBasisVectors
  have h_first_subset :
      firstBasisVectors ⊆ (L : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro u hu
    rcases hu with ⟨b, hb_span, hb0⟩
    rw [← hb0, ← hb_span]
    exact Submodule.subset_span ⟨0, rfl⟩
  have h_slice_nonempty : slice.Nonempty := by
    refine ⟨b₀ 0, ?_⟩
    refine ⟨?_, ⟨b₀, rfl, rfl⟩⟩
    simp [b₀, Metric.mem_closedBall, dist_zero_right]
  have h_slice_finite : Set.Finite slice := by
    exact finite_closedBall_inter_of_subset_integerSpan b₀ h_first_subset
  obtain ⟨u, hu_slice, hu_min⟩ :=
    Set.exists_min_image slice (fun v ↦ ‖v‖) h_slice_finite h_slice_nonempty
  rcases hu_slice.2 with ⟨b, hb_span, hb₀⟩
  have hu_global : ∀ v ∈ firstBasisVectors, ‖u‖ ≤ ‖v‖ :=
    normMinOnClosedBallSlice_global hu_slice hu_min
  have h_norm_sq_pos : 0 < ‖b 0‖ ^ 2 := by
    have h_norm_pos : 0 < ‖b 0‖ := norm_pos_iff.mpr (b.ne_zero 0)
    nlinarith
  let m : ℤ := round (⟪b 0, b 1⟫_ℝ / ‖b 0‖ ^ 2)
  let bShear : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) := shearBasis b m
  have hbShear0 : bShear 0 = b 0 := shearBasis_zero b m
  have h_span_bShear :
      Submodule.span ℤ (Set.range bShear) = L := by
    rw [← hb_span, span_shearBasis_eq b m]
  have hbShear1_first : bShear 1 ∈ firstBasisVectors := by
    -- Swapping the sheared lattice basis makes `bShear 1` into a first basis vector of `L`.
    refine ⟨bShear.reindex (Equiv.swap 0 1), ?_, ?_⟩
    · simpa [Module.Basis.range_reindex] using h_span_bShear
    · simp
  have h_norm_order : ‖bShear 0‖ ≤ ‖bShear 1‖ := by
    -- The global first-vector minimizer bounds the swapped sheared first vector as well.
    have hmin := hu_global (bShear 1) hbShear1_first
    rw [hbShear0, hb₀]
    exact hmin
  have h_conditionI : basis_reduction_condition_i bShear := by
    simpa [bShear, m] using basisReductionConditionI_shearBasis h_norm_sq_pos
  have h_conditionII : basis_reduction_condition_ii bShear :=
    basisReductionConditionII_of_norm_le h_norm_order
  have hReduced : IsReducedBasis bShear :=
    basis_reduction_algorithm_terminates_with_reduced_basis h_conditionI h_conditionII
  have h_span_bShear_set :
      (L : Set (EuclideanSpace ℝ (Fin 2))) = Submodule.span ℤ (Set.range bShear) := by
    simpa using congrArg (fun S : Submodule ℤ (EuclideanSpace ℝ (Fin 2)) ↦
      (S : Set (EuclideanSpace ℝ (Fin 2)))) h_span_bShear.symm
  have h_lattice :
      (EuclideanSpace.equiv (Fin 2) ℝ).symm '' matrix_generated_lattice B = L := by
    simpa [L, b₀] using euclideanBasisOfMatrix_span_eq_image_matrixGeneratedLattice B hB
  exact ⟨bShear, h_lattice.trans h_span_bShear_set, hReduced⟩

/-- Exercise 9.4. Rewriting the reduced-basis existence theorem through the dimension-`2` bridge
and then changing the sign of one basis vector if needed gives a basis whose angle lies between
`60°` and `90°`, encoded by the equivalent inner-product bounds. -/
theorem exercise_9_4_exists_lattice_basis_with_angle_between_pi_div_three_and_pi_div_two
    (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : IsUnit B.det) :
    ∃ b : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)),
      (EuclideanSpace.equiv (Fin 2) ℝ).symm '' matrix_generated_lattice B =
        Submodule.span ℤ (Set.range b) ∧
      0 ≤ ⟪b 0, b 1⟫_ℝ ∧
      2 * ⟪b 0, b 1⟫_ℝ ≤ ‖b 0‖ * ‖b 1‖ := by
  obtain ⟨b, hb_lattice, hb_reduced⟩ := exercise_9_4_exists_reduced_basis B hB
  obtain ⟨b', hb_span, h_nonneg, h_bound⟩ :=
    IsReducedBasis.exists_same_span_basis_with_acute_angle_bounds hb_reduced
  have hb_span_set :
      (Submodule.span ℤ (Set.range b) : Set (EuclideanSpace ℝ (Fin 2))) =
        Submodule.span ℤ (Set.range b') := by
    simpa using congrArg (fun S : Submodule ℤ (EuclideanSpace ℝ (Fin 2)) ↦
      (S : Set (EuclideanSpace ℝ (Fin 2)))) hb_span
  exact ⟨b', hb_lattice.trans hb_span_set, h_nonneg, h_bound⟩

end Exercise94
