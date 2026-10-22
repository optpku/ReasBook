/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Lemma_5_4_5
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric

noncomputable section

open scoped InnerProductSpace
open scoped Matrix.Norms.Frobenius

/-
Domain sampling across Chapter 5:
- source-facing layer: the inverse-secant residual estimates and the matrix right-multiplication
  bounds from Lemma 5.4.17;
- core/canonical owners already present upstream:
  `satisfiesCurvatureCondition` for secant positivity
  (`Definition_5_1_extra_1`) and the intrinsic inner-product inequalities of
  `Lemma_5_4_5`;
- bridge/view layer used here: `Matrix.toEuclideanLin` for the concrete Euclidean matrix model,
  and the standard continuous-linear-map operator estimate behind the normalized angle ratio.

Accordingly, this file keeps the matrix formulas only where the source is genuinely matrix-based,
while the curvature and normalized-angle statements are organized through the intrinsic owner
abstractions first and only then specialized back to `Matrix (Fin n) (Fin n) ℝ`.
-/

section Intrinsic

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inner-product bounds underlying Lemma 5.4.17 (1): if `v` stays within
`β * ‖u‖` of `u`, then `⟪u, v⟫_ℝ` lies between `(1 - β) * ‖u‖ ^ 2` and
`(1 + β) * ‖u‖ ^ 2`. -/
theorem inner_bounds_of_norm_sub_le
    (u v : E) (β : ℝ) (hclose : ‖v - u‖ ≤ β * ‖u‖) :
    (1 - β) * ‖u‖ ^ 2 ≤ ⟪u, v⟫_ℝ ∧
      ⟪u, v⟫_ℝ ≤ (1 + β) * ‖u‖ ^ 2 := by
  -- Split `⟪u, v⟫` into the main norm square and the residual error term `⟪u, v - u⟫`.
  have hcs : |⟪u, v - u⟫_ℝ| ≤ ‖u‖ * ‖v - u‖ := absRealInnerLeNorm u (v - u)
  have hmul : ‖u‖ * ‖v - u‖ ≤ β * ‖u‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hclose (norm_nonneg u)
    nlinarith
  have hupper_err : ⟪u, v - u⟫_ℝ ≤ β * ‖u‖ ^ 2 :=
    (abs_le.mp hcs).2.trans hmul
  have hlower_err : -β * ‖u‖ ^ 2 ≤ ⟪u, v - u⟫_ℝ := by
    have hleft : -(‖u‖ * ‖v - u‖) ≤ ⟪u, v - u⟫_ℝ := (abs_le.mp hcs).1
    have hneg : -(β * ‖u‖ ^ 2) ≤ -(‖u‖ * ‖v - u‖) := by
      linarith
    have : -β * ‖u‖ ^ 2 ≤ ⟪u, v - u⟫_ℝ := by
      nlinarith
    exact this
  have hrewrite : ⟪u, v⟫_ℝ = ⟪u, v - u⟫_ℝ + ‖u‖ ^ 2 := by
    calc
      ⟪u, v⟫_ℝ = ⟪u, v - u + u⟫_ℝ := by rw [sub_add_cancel]
      _ = ⟪u, v - u⟫_ℝ + ⟪u, u⟫_ℝ := by rw [inner_add_right]
      _ = ⟪u, v - u⟫_ℝ + ‖u‖ ^ 2 := by rw [realInnerSelfEqNormSq]
  constructor <;> nlinarith [hrewrite, hlower_err, hupper_err]

/-- Rewriting `Lemma_5_4_5.inner_pos_of_norm_sub_le` through the Chapter 5 owner
`satisfiesCurvatureCondition`. -/
theorem satisfiesCurvatureCondition_of_norm_sub_le
    (u v : E) (β : ℝ) (hβ : β < 1)
    (hclose : ‖v - u‖ ≤ β * ‖u‖) (hu : u ≠ 0) :
    satisfiesCurvatureCondition u v := by
  rw [satisfiesCurvatureCondition]
  exact inner_pos_of_norm_sub_le u v hu β hβ <| by
    simpa [norm_sub_rev] using hclose

end Intrinsic

section OperatorEstimate

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The normalized operator-apply ratio for a continuous linear map always belongs to `[0, 1]`. -/
theorem normalizedOperatorApplyRatio_mem_Icc
    (A : E →L[ℝ] F) (u : E) :
    ‖A u‖ / (‖A‖ * ‖u‖) ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hden : ‖A‖ * ‖u‖ = 0
  · -- If the denominator vanishes, either `A = 0` or `u = 0`, so the ratio is exactly `0`.
    rcases mul_eq_zero.mp hden with hA | hu
    · have hA0 : A = 0 := norm_eq_zero.mp hA
      subst hA0
      simp
    · have hu0 : u = 0 := norm_eq_zero.mp hu
      subst hu0
      simp
  · -- Otherwise use the operator norm estimate and divide through by the positive denominator.
    have hden_nonneg : 0 ≤ ‖A‖ * ‖u‖ := mul_nonneg (norm_nonneg A) (norm_nonneg u)
    have hden_pos : 0 < ‖A‖ * ‖u‖ := lt_of_le_of_ne hden_nonneg (Ne.symm hden)
    constructor
    · exact div_nonneg (norm_nonneg (A u)) hden_nonneg
    · refine (div_le_iff₀ hden_pos).2 ?_
      simpa using A.le_opNorm u

end OperatorEstimate

section EuclideanMatrix

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- Chapter05 Lemma 5.4.17 (1): if `M` is symmetric and nonsingular and
`‖M y - M⁻¹ s‖ ≤ β * ‖M⁻¹ s‖`, then the curvature pairing `dotProduct s y`
lies between `(1 - β) * ‖M⁻¹ s‖ ^ 2` and `(1 + β) * ‖M⁻¹ s‖ ^ 2`. This is the Euclidean
matrix bridge of `inner_bounds_of_norm_sub_le`, specialized to
`u = (M⁻¹).toEuclideanLin s` and `v = M.toEuclideanLin y`. -/
theorem curvaturePairing_bounds_of_inverseSecantResidual_le
    (M : MatrixN) (hM : M.IsSymm) (hMdet : IsUnit M.det)
    (β : ℝ)
    (s y : Point)
    (hres : ‖M.toEuclideanLin y - (M⁻¹).toEuclideanLin s‖ ≤ β * ‖(M⁻¹).toEuclideanLin s‖) :
    (1 - β) * ‖(M⁻¹).toEuclideanLin s‖ ^ 2 ≤ dotProduct s y ∧
      dotProduct s y ≤ (1 + β) * ‖(M⁻¹).toEuclideanLin s‖ ^ 2 := by
  have hHermitian : M.IsHermitian := by
    simpa [Matrix.isHermitian_iff_isSymm] using hM
  have hSymmLin : M.toEuclideanLin.IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff (A := M)).2 hHermitian
  have hinv_apply : M.toEuclideanLin ((M⁻¹).toEuclideanLin s) = s := by
    -- Apply `ofLp` once so the inverse relation becomes the matrix identity `M * M⁻¹ = 1`.
    apply WithLp.ofLp_injective
    have hmul :
        (M * M⁻¹).mulVec s.ofLp = (1 : MatrixN).mulVec s.ofLp := by
      simpa using congrArg (fun A : MatrixN ↦ A.mulVec s.ofLp) (Matrix.mul_nonsing_inv M hMdet)
    simpa [Matrix.ofLp_toLpLin (p := (2 : ENNReal)) (q := (2 : ENNReal)), Matrix.mulVec_mulVec]
      using hmul
  have hpair : dotProduct s y = ⟪(M⁻¹).toEuclideanLin s, M.toEuclideanLin y⟫_ℝ := by
    -- Transport the textbook scalar pairing through symmetry of `M.toEuclideanLin`.
    calc
      dotProduct s y = ⟪s, y⟫_ℝ := by simp [PiLp.inner_apply, dotProduct, mul_comm]
      _ = ⟪M.toEuclideanLin ((M⁻¹).toEuclideanLin s), y⟫_ℝ := by rw [hinv_apply]
      _ = ⟪(M⁻¹).toEuclideanLin s, M.toEuclideanLin y⟫_ℝ := by
        simpa using hSymmLin ((M⁻¹).toEuclideanLin s) y
  simpa [hpair] using
    inner_bounds_of_norm_sub_le ((M⁻¹).toEuclideanLin s) (M.toEuclideanLin y) β hres

/-- Chapter05 Lemma 5.4.17 (2): for `β ∈ [0, 1 / 3]`, the scalar
`(1 - 2 * β) / (1 - β^2)` belongs to `[3 / 8, 1]`. -/
theorem residualControlAlpha_formula_mem_Icc
    (β : ℝ) (hβ : β ∈ Set.Icc (0 : ℝ) (1 / 3)) :
    (1 - 2 * β) / (1 - β ^ 2) ∈ Set.Icc (3 / 8 : ℝ) 1 := by
  rcases hβ with ⟨hβ0, hβ13⟩
  have hden_pos : 0 < 1 - β ^ 2 := by
    nlinarith
  constructor
  · -- The lower endpoint `3 / 8` is the worst case over `β ∈ [0, 1 / 3]`.
    refine (le_div_iff₀ hden_pos).2 ?_
    nlinarith
  · -- The upper endpoint `1` follows because `β^2 ≤ 2β` on `β ≥ 0`.
    refine (div_le_iff₀ hden_pos).2 ?_
    nlinarith

/-- If `M` is symmetric and nonsingular, `β < 1`,
`‖M y - M⁻¹ s‖ ≤ β * ‖M⁻¹ s‖`, and `M⁻¹ s ≠ 0`, then the secant data `(s, y)` satisfy
the Chapter 5 curvature condition. This is the source-facing owner statement for the positivity
part of Lemma 5.4.17. -/
theorem satisfiesCurvatureCondition_of_inverseSecantResidual_le
    (M : MatrixN) (hM : M.IsSymm) (hMdet : IsUnit M.det)
    (β : ℝ) (hβ : β < 1)
    (s y : Point)
    (hres : ‖M.toEuclideanLin y - (M⁻¹).toEuclideanLin s‖ ≤ β * ‖(M⁻¹).toEuclideanLin s‖)
    (hMs : (M⁻¹).toEuclideanLin s ≠ 0) :
    satisfiesCurvatureCondition s y := by
  have hbounds :=
    curvaturePairing_bounds_of_inverseSecantResidual_le M hM hMdet β s y hres
  have hnorm_pos : 0 < ‖(M⁻¹).toEuclideanLin s‖ := norm_pos_iff.mpr hMs
  have hcoef_pos : 0 < 1 - β := by
    linarith
  have hlower_pos : 0 < (1 - β) * ‖(M⁻¹).toEuclideanLin s‖ ^ 2 := by
    exact mul_pos hcoef_pos (pow_pos hnorm_pos 2)
  -- The lower curvature bound is strictly positive, so the Chapter 5 curvature condition holds.
  exact satisfiesCurvatureCondition_iff_dotProduct_pos.mpr <|
    lt_of_lt_of_le hlower_pos hbounds.1

/-- Dot-product restatement of
`satisfiesCurvatureCondition_of_inverseSecantResidual_le`. -/
theorem curvaturePairing_pos_of_inverseSecantResidual_le
    (M : MatrixN) (hM : M.IsSymm) (hMdet : IsUnit M.det)
    (β : ℝ) (hβ : β < 1)
    (s y : Point)
    (hres : ‖M.toEuclideanLin y - (M⁻¹).toEuclideanLin s‖ ≤ β * ‖(M⁻¹).toEuclideanLin s‖)
    (hMs : (M⁻¹).toEuclideanLin s ≠ 0) :
    0 < dotProduct s y := by
  exact satisfiesCurvatureCondition_iff_dotProduct_pos.mp <|
    satisfiesCurvatureCondition_of_inverseSecantResidual_le M hM hMdet β hβ s y hres hMs

/-- The matrix formulas in Lemma 5.4.17 (4) and (5) use the denominator `dotProduct y s`;
this nonzeroness is the direct scalar bridge from the canonical curvature positivity statement
`curvaturePairing_pos_of_inverseSecantResidual_le`. -/
theorem curvaturePairing_ne_zero_of_inverseSecantResidual_le
    (M : MatrixN) (hM : M.IsSymm) (hMdet : IsUnit M.det)
    (β : ℝ) (hβ : β < 1)
    (s y : Point)
    (hres : ‖M.toEuclideanLin y - (M⁻¹).toEuclideanLin s‖ ≤ β * ‖(M⁻¹).toEuclideanLin s‖)
    (hMs : (M⁻¹).toEuclideanLin s ≠ 0) :
    dotProduct y s ≠ 0 := by
  exact ne_of_gt <| by
    simpa [dotProduct_comm] using
      curvaturePairing_pos_of_inverseSecantResidual_le M hM hMdet β hβ s y hres hMs

/-- Chapter05 Lemma 5.4.17 (3): the normalized Frobenius-angle quantity
`‖E.toEuclideanLin u‖ / (‖E‖ * ‖u‖)` belongs to `[0, 1]`. This is the matrix/Frobenius bridge of the
canonical operator-norm estimate `normalizedOperatorApplyRatio_mem_Icc` for
`E.toEuclideanLin.toContinuousLinearMap`, together with
`matrixL2OperatorNorm_le_matrixFrobeniusNorm`. -/
theorem normalizedFrobeniusAngle_mem_Icc
    (E : MatrixN) (u : Point) :
    ‖E.toEuclideanLin u‖ / (‖E‖ * ‖u‖) ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hden : ‖E‖ * ‖u‖ = 0
  · -- A zero denominator forces either the matrix or the vector to vanish, hence the ratio is `0`.
    rcases mul_eq_zero.mp hden with hE | hu
    · have hE0 : E = 0 := norm_eq_zero.mp hE
      subst hE0
      simp
    · have hu0 : u = 0 := norm_eq_zero.mp hu
      subst hu0
      simp
  · -- Otherwise divide the Frobenius-norm matrix-vector estimate by the positive denominator.
    have hden_nonneg : 0 ≤ ‖E‖ * ‖u‖ := mul_nonneg (norm_nonneg E) (norm_nonneg u)
    have hden_pos : 0 < ‖E‖ * ‖u‖ := lt_of_le_of_ne hden_nonneg (Ne.symm hden)
    have hbound : ‖E.toEuclideanLin u‖ ≤ ‖E‖ * ‖u‖ := by
      simpa [Matrix.toLpLin_apply (p := (2 : ENNReal)) (q := (2 : ENNReal)), l2Norm, lpNorm] using
        (matrixMulVecTwoNorm_le_matrixFrobeniusNorm_mul_vectorTwoNorm E u.ofLp)
    constructor
    · exact div_nonneg (norm_nonneg (E.toEuclideanLin u)) hden_nonneg
    · refine (div_le_iff₀ hden_pos).2 ?_
      simpa using hbound

/-- Helper for Chapter05 Lemma 5.4.17: the Frobenius norm of a rank-one matrix
`Matrix.vecMulVec u v` is exactly the product `‖u‖ * ‖v‖`. -/
lemma frobenius_norm_vecMulVec_eq
    (u v : Point) :
    ‖Matrix.vecMulVec u v‖ = ‖u‖ * ‖v‖ := by
  have hsq :
      ‖Matrix.vecMulVec u v‖ ^ 2 = (‖u‖ * ‖v‖) ^ 2 := by
    -- Square the Frobenius norm and expand the rank-one entries row-by-row.
    calc
      ‖Matrix.vecMulVec u v‖ ^ 2
        = ∑ i, ∑ j, ‖Matrix.vecMulVec u v i j‖ ^ 2 := by
            have hsum_nonneg :
                0 ≤ ∑ i, ∑ j, ‖Matrix.vecMulVec u v i j‖ ^ 2 := by
              positivity
            simpa [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow] using
              (Real.sq_sqrt hsum_nonneg)
      _ = ∑ i, ∑ j, (‖u i‖ * ‖v j‖) ^ 2 := by
            simp_rw [Matrix.vecMulVec_apply, norm_mul]
      _ = ∑ i, ∑ j, ‖u i‖ ^ 2 * ‖v j‖ ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
      _ = (∑ i, ‖u i‖ ^ 2) * (∑ j, ‖v j‖ ^ 2) := by
            rw [← Finset.sum_mul_sum]
      _ = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
            rw [← EuclideanSpace.norm_sq_eq, ← EuclideanSpace.norm_sq_eq]
      _ = (‖u‖ * ‖v‖) ^ 2 := by ring
  -- Recover the unsquared identity by taking square roots of both nonnegative sides.
  calc
    ‖Matrix.vecMulVec u v‖ = Real.sqrt (‖Matrix.vecMulVec u v‖ ^ 2) := by
      rw [Real.sqrt_sq (norm_nonneg _)]
    _ = Real.sqrt ((‖u‖ * ‖v‖) ^ 2) := by rw [hsq]
    _ = ‖u‖ * ‖v‖ := by
      rw [Real.sqrt_sq (mul_nonneg (norm_nonneg u) (norm_nonneg v))]

/-- Helper for Chapter05 Lemma 5.4.17: right multiplication by the source projector
`I - ρ⁻¹ uuᵀ` is the rank-one correction `E - ρ⁻¹ (E u) uᵀ`. -/
lemma right_mul_rank_one_projector_eq
    (E : MatrixN) (u : Point) (ρ : ℝ) :
    E * (1 - ρ⁻¹ • Matrix.vecMulVec u u) =
      E - ρ⁻¹ • Matrix.vecMulVec (E.toEuclideanLin u) u := by
  -- Distribute the product and collapse the rank-one factor with `mul_vecMulVec`.
  calc
    E * (1 - ρ⁻¹ • Matrix.vecMulVec u u)
      = E * 1 - E * (ρ⁻¹ • Matrix.vecMulVec u u) := by
          rw [Matrix.mul_sub]
    _ = E - ρ⁻¹ • (E * Matrix.vecMulVec u u) := by
          rw [Matrix.mul_one, Matrix.mul_smul]
    _ = E - ρ⁻¹ • Matrix.vecMulVec (E.toEuclideanLin u) u := by
          congr 1
          ext i j
          simp [Matrix.mul_vecMulVec, Matrix.toEuclideanLin, Matrix.toLpLin_apply]

/-- Helper for Chapter05 Lemma 5.4.17: each column of a rank-one correction has the textbook
Euclidean square expansion. -/
lemma frobenius_column_sub_sq
    (E : MatrixN) (z : Point) (j : Fin n) (c : ℝ) :
    ‖fun i : Fin n => E i j - c * z i‖₂ ^ 2 =
      ‖E.col j‖₂ ^ 2 - 2 * (c * dotProduct (E.col j) z.ofLp) + ‖c • z‖ ^ 2 := by
  -- Convert the column identity to the Euclidean `WithLp 2` model once, then apply the
  -- standard norm-square expansion there.
  have hsub :
      WithLp.toLp (2 : ENNReal) (fun i : Fin n => E i j - c * z i) =
        WithLp.toLp (2 : ENNReal) (E.col j) - c • z := rfl
  have hsq := norm_sub_sq_real (WithLp.toLp (2 : ENNReal) (E.col j)) (c • z)
  rw [← hsub, toLpInner_eq_dotProduct] at hsq
  simpa [l2Norm, lpNorm, Matrix.col, dotProduct, Finset.mul_sum, Finset.sum_mul,
    sub_eq_add_neg, mul_left_comm, mul_assoc] using hsq

/-- Helper for Chapter05 Lemma 5.4.17: the projector `I - ρ⁻¹ uuᵀ` has the exact Frobenius
square identity from the source proof. -/
lemma frobenius_right_mul_self_rank_one_sq
    (E : MatrixN) (u : Point) (ρ : ℝ) :
    ‖E * (1 - ρ⁻¹ • Matrix.vecMulVec u u)‖ ^ 2 =
      ‖E‖ ^ 2 + ((-2 * ρ + ‖u‖ ^ 2) / ρ ^ 2) * ‖E.toEuclideanLin u‖ ^ 2 := by
  by_cases hρ : ρ = 0
  · -- The singular scalar case collapses immediately because the inverse coefficient is `0`.
    simp [hρ]
  · set z : Point := E.toEuclideanLin u
    have hproj := right_mul_rank_one_projector_eq E u ρ
    have hcolsq :
        ∀ j : Fin n,
          ‖(E * (1 - ρ⁻¹ • Matrix.vecMulVec u u)).col j‖₂ ^ 2 =
            ‖E.col j‖₂ ^ 2 - 2 * (ρ⁻¹ * u j * dotProduct (E.col j) z.ofLp) +
              (ρ⁻¹ * u j) ^ 2 * ‖z‖ ^ 2 := by
      intro j
      -- Rewrite the `j`th column into the source rank-one correction shape and expand it.
      have hcol :
          (E * (1 - ρ⁻¹ • Matrix.vecMulVec u u)).col j =
            fun i : Fin n => E i j - (ρ⁻¹ * u j) * z i := by
        ext i
        rw [hproj]
        simp [Matrix.col, Matrix.vecMulVec_apply, z, mul_comm, mul_left_comm]
      rw [hcol]
      have hsq := frobenius_column_sub_sq E z j (ρ⁻¹ * u j)
      have hz :
          ‖(ρ⁻¹ * u j) • z‖ ^ 2 = (ρ⁻¹ * u j) ^ 2 * ‖z‖ ^ 2 := by
        rw [norm_smul]
        calc
          (‖ρ⁻¹ * u j‖ * ‖z‖) ^ 2 = ‖ρ⁻¹ * u j‖ ^ 2 * ‖z‖ ^ 2 := by ring
          _ = (ρ⁻¹ * u j) ^ 2 * ‖z‖ ^ 2 := by
            rw [show ‖ρ⁻¹ * u j‖ ^ 2 = (ρ⁻¹ * u j) ^ 2 by
              simpa [Real.norm_eq_abs, pow_two] using (sq_abs (ρ⁻¹ * u j))]
      simpa [hz] using hsq
    have hnorm_proj :
        ‖E * (1 - ρ⁻¹ • Matrix.vecMulVec u u)‖ ^ 2 =
          ∑ j : Fin n, ‖(E * (1 - ρ⁻¹ • Matrix.vecMulVec u u)).col j‖₂ ^ 2 := by
      simpa using
        (matrixFrobeniusNorm_sq_eq_sum_columnVectorTwoNorm_sq
          (E * (1 - ρ⁻¹ • Matrix.vecMulVec u u)))
    have hnorm_E : ∑ j : Fin n, ‖E.col j‖₂ ^ 2 = ‖E‖ ^ 2 := by
      simpa using (matrixFrobeniusNorm_sq_eq_sum_columnVectorTwoNorm_sq E).symm
    rw [hnorm_proj]
    have hsum_cols :
        ∑ j : Fin n, ‖(E * (1 - ρ⁻¹ • Matrix.vecMulVec u u)).col j‖₂ ^ 2 =
          ∑ j : Fin n, (‖E.col j‖₂ ^ 2 - 2 * (ρ⁻¹ * u j * dotProduct (E.col j) z.ofLp) +
            (ρ⁻¹ * u j) ^ 2 * ‖z‖ ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      exact hcolsq j
    rw [hsum_cols]
    have hdotself : dotProduct z.ofLp z.ofLp = ‖z‖ ^ 2 := by
      -- Collapse the dot product of `z` with itself to the Euclidean norm square.
      calc
        dotProduct z.ofLp z.ofLp = ∑ i : Fin n, z.ofLp i * z.ofLp i := rfl
        _ = ∑ i : Fin n, z.ofLp i ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro i _
              ring
        _ = ‖z‖ ^ 2 := by
              simpa [EuclideanSpace.norm_sq_eq]
    have hcross :
        ∑ j : Fin n, ρ⁻¹ * u j * dotProduct (E.col j) z.ofLp = ρ⁻¹ * ‖z‖ ^ 2 := by
      -- Repackage the summed cross term as a matrix-vector pairing and then evaluate it on `z = E u`.
      calc
        ∑ j : Fin n, ρ⁻¹ * u j * dotProduct (E.col j) z.ofLp
            = ρ⁻¹ * ∑ j : Fin n, u j * dotProduct (E.col j) z.ofLp := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro j _
                ring
        _ = ρ⁻¹ * dotProduct u.ofLp (E.transpose.mulVec z.ofLp) := by
              simp [Matrix.mulVec, dotProduct, Matrix.col]
        _ = ρ⁻¹ * dotProduct (E.mulVec u.ofLp) z.ofLp := by
              rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
        _ = ρ⁻¹ * dotProduct z.ofLp z.ofLp := by
              simp [z, Matrix.toLpLin_apply]
        _ = ρ⁻¹ * ‖z‖ ^ 2 := by rw [hdotself]
    have hu_sq :
        ∑ j : Fin n, (ρ⁻¹ * u j) ^ 2 = ρ⁻¹ ^ 2 * ‖u‖ ^ 2 := by
      -- The quadratic coefficient factors through the Euclidean norm square of `u`.
      calc
        ∑ j : Fin n, (ρ⁻¹ * u j) ^ 2 = ρ⁻¹ ^ 2 * ∑ j : Fin n, (u j) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
        _ = ρ⁻¹ ^ 2 * ‖u‖ ^ 2 := by
          congr 1
          simpa [EuclideanSpace.norm_sq_eq]
    have hcross2 :
        ∑ j : Fin n, 2 * (ρ⁻¹ * u j * dotProduct (E.col j) z.ofLp) =
          2 * (ρ⁻¹ * ‖z‖ ^ 2) := by
      simpa [Finset.mul_sum] using congrArg (fun t : ℝ => 2 * t) hcross
    have hquad :
        ∑ j : Fin n, (ρ⁻¹ * u j) ^ 2 * ‖z‖ ^ 2 =
          (ρ⁻¹ ^ 2 * ‖u‖ ^ 2) * ‖z‖ ^ 2 := by
      rw [← Finset.sum_mul, hu_sq]
    -- Summing the column expansions yields the exact Frobenius identity.
    calc
      ∑ j : Fin n,
          (‖E.col j‖₂ ^ 2 - 2 * (ρ⁻¹ * u j * dotProduct (E.col j) z.ofLp) +
            (ρ⁻¹ * u j) ^ 2 * ‖z‖ ^ 2)
          = (∑ j : Fin n, ‖E.col j‖₂ ^ 2) - 2 * (ρ⁻¹ * ‖z‖ ^ 2) +
              (ρ⁻¹ ^ 2 * ‖u‖ ^ 2) * ‖z‖ ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hcross2, hquad]
      _ = ‖E‖ ^ 2 - 2 * (ρ⁻¹ * ‖z‖ ^ 2) + (ρ⁻¹ ^ 2 * ‖u‖ ^ 2) * ‖z‖ ^ 2 := by
            rw [hnorm_E]
      _ = ‖E‖ ^ 2 + ((-2 * ρ + ‖u‖ ^ 2) / ρ ^ 2) * ‖z‖ ^ 2 := by
            field_simp [hρ]
            ring

/-- Helper for Chapter05 Lemma 5.4.17: the residual rank-one correction term in part (c) is
controlled by the Frobenius norm of `E` and the residual vector `u - v`. -/
lemma frobenius_rank_one_residual_correction_le
    (E : MatrixN) (u v : Point) (ρ : ℝ) :
    ‖ρ⁻¹ • Matrix.vecMulVec (E.toEuclideanLin u) (u - v)‖ ≤
      |ρ|⁻¹ * ‖E‖ * ‖u‖ * ‖u - v‖ := by
  -- Separate the scalar factor, identify the rank-one Frobenius norm, and then apply the
  -- matrix-vector estimate `‖E u‖ ≤ ‖E‖ ‖u‖`.
  calc
    ‖ρ⁻¹ • Matrix.vecMulVec (E.toEuclideanLin u) (u - v)‖
      = ‖ρ⁻¹‖ * ‖Matrix.vecMulVec (E.toEuclideanLin u) (u - v)‖ := by
          rw [norm_smul]
    _ = |ρ|⁻¹ * (‖E.toEuclideanLin u‖ * ‖u - v‖) := by
          rw [Real.norm_eq_abs, abs_inv, frobenius_norm_vecMulVec_eq]
    _ ≤ |ρ|⁻¹ * ((‖E‖ * ‖u‖) * ‖u - v‖) := by
          have hmulvec : ‖E.toEuclideanLin u‖ ≤ ‖E‖ * ‖u‖ := by
            simpa [Matrix.toLpLin_apply (p := (2 : ENNReal)) (q := (2 : ENNReal)), l2Norm, lpNorm] using
              (matrixMulVecTwoNorm_le_matrixFrobeniusNorm_mul_vectorTwoNorm E u.ofLp)
          gcongr
    _ = |ρ|⁻¹ * ‖E‖ * ‖u‖ * ‖u - v‖ := by ring

/-- Helper for Chapter05 Lemma 5.4.17: the lower curvature bound gives the first scalar
projector-coefficient comparison used in part (b). -/
lemma projector_coefficient_le_of_lower_curvature
    (β ρ : ℝ) (u : Point)
    (hβ : β ∈ Set.Icc (0 : ℝ) (1 / 3))
    (hρpos : 0 < ρ)
    (hlower : (1 - β) * ‖u‖ ^ 2 ≤ ρ) :
    ((1 - 2 * β) / (1 - β)) / ρ ≤ (2 * ρ - ‖u‖ ^ 2) / ρ ^ 2 := by
  rcases hβ with ⟨hβ0, hβ13⟩
  have hβlt1 : β < 1 := by
    nlinarith
  have h1mb_pos : 0 < 1 - β := by
    nlinarith
  have hmult : ‖u‖ ^ 2 * (1 - β) ≤ ρ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlower
  have hnorm_le : ‖u‖ ^ 2 ≤ ρ / (1 - β) := by
    exact (le_div_iff₀ h1mb_pos).2 hmult
  have hρsq_pos : 0 < ρ ^ 2 := by
    positivity
  have hρne : ρ ≠ 0 := ne_of_gt hρpos
  have hrewrite :
      ((1 - 2 * β) / (1 - β)) / ρ =
        (((1 - 2 * β) / (1 - β)) * ρ) / ρ ^ 2 := by
    field_simp [pow_two, hρne]
  -- Put both sides over the common positive denominator `ρ²`.
  rw [hrewrite]
  refine (div_le_iff₀ hρsq_pos).2 ?_
  rw [show (2 * ρ - ‖u‖ ^ 2) / ρ ^ 2 * ρ ^ 2 = 2 * ρ - ‖u‖ ^ 2 by
    field_simp [pow_two, hρne]]
  have hgap :
      2 * ρ - ‖u‖ ^ 2 - (((1 - 2 * β) / (1 - β)) * ρ) = ρ / (1 - β) - ‖u‖ ^ 2 := by
    field_simp [h1mb_pos.ne']
    ring
  nlinarith [hnorm_le, hgap]

/-- Helper for Chapter05 Lemma 5.4.17: the upper curvature bound turns the intermediate
projector coefficient into the published `α / ‖u‖²` coefficient. -/
lemma alpha_div_norm_sq_le_projector_bridge
    (β ρ : ℝ) (u : Point)
    (hβ : β ∈ Set.Icc (0 : ℝ) (1 / 3))
    (hu : u ≠ 0)
    (hρpos : 0 < ρ)
    (hupper : ρ ≤ (1 + β) * ‖u‖ ^ 2) :
    ((1 - 2 * β) / (1 - β ^ 2)) / ‖u‖ ^ 2 ≤ ((1 - 2 * β) / (1 - β)) / ρ := by
  rcases hβ with ⟨hβ0, hβ13⟩
  have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hu_sq_pos : 0 < ‖u‖ ^ 2 := by
    positivity
  have h1mb_pos : 0 < 1 - β := by
    nlinarith
  have h1pb_pos : 0 < 1 + β := by
    nlinarith
  have hcoef_nonneg : 0 ≤ (1 - 2 * β) / (1 - β) := by
    refine div_nonneg ?_ h1mb_pos.le
    nlinarith
  have hrecip : 1 / ((1 + β) * ‖u‖ ^ 2) ≤ 1 / ρ := by
    -- The upper curvature bound reverses under reciprocals because both sides are positive.
    exact one_div_le_one_div_of_le hρpos hupper
  have hscaled :
      ((1 - 2 * β) / (1 - β)) * (1 / ((1 + β) * ‖u‖ ^ 2)) ≤
        ((1 - 2 * β) / (1 - β)) * (1 / ρ) := by
    exact mul_le_mul_of_nonneg_left hrecip hcoef_nonneg
  have hbeta_sq : 1 - β ^ 2 = (1 - β) * (1 + β) := by
    ring
  have hleft :
      ((1 - 2 * β) / (1 - β ^ 2)) / ‖u‖ ^ 2 =
        ((1 - 2 * β) / (1 - β)) * (1 / ((1 + β) * ‖u‖ ^ 2)) := by
    rw [hbeta_sq]
    field_simp [pow_two, h1mb_pos.ne', h1pb_pos.ne', hu_sq_pos.ne']
  have hright :
      ((1 - 2 * β) / (1 - β)) / ρ =
        ((1 - 2 * β) / (1 - β)) * (1 / ρ) := by
    field_simp [hρpos.ne', h1mb_pos.ne']
  -- Rewriting both sides isolates the reciprocal comparison `1 / ((1 + β) ‖u‖²) ≤ 1 / ρ`.
  rw [hleft, hright]
  exact hscaled

/-- Helper for Chapter05 Lemma 5.4.17: the lower curvature bound also yields the reciprocal
scalar estimate needed for the residual rank-one correction in part (c). -/
lemma residual_coefficient_le_of_lower_curvature
    (β ρ : ℝ) (u : Point)
    (hβ : β < 1)
    (hu : u ≠ 0)
    (hlower : (1 - β) * ‖u‖ ^ 2 ≤ ρ) :
    |ρ|⁻¹ * ‖u‖ ≤ (1 - β)⁻¹ / ‖u‖ := by
  have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hu_sq_pos : 0 < ‖u‖ ^ 2 := by
    positivity
  have h1mb_pos : 0 < 1 - β := by
    nlinarith
  have hlower_pos : 0 < (1 - β) * ‖u‖ ^ 2 := by
    exact mul_pos h1mb_pos hu_sq_pos
  have hρpos : 0 < ρ := lt_of_lt_of_le hlower_pos hlower
  have hrecip : 1 / ρ ≤ 1 / ((1 - β) * ‖u‖ ^ 2) := by
    -- The lower curvature bound reverses under reciprocals because both sides are positive.
    exact one_div_le_one_div_of_le hlower_pos hlower
  have hscaled :
      ‖u‖ * (1 / ρ) ≤ ‖u‖ * (1 / ((1 - β) * ‖u‖ ^ 2)) := by
    exact mul_le_mul_of_nonneg_left hrecip (norm_nonneg u)
  have hlhs : |ρ|⁻¹ * ‖u‖ = ‖u‖ * (1 / ρ) := by
    rw [abs_of_pos hρpos]
    ring
  have hrhs : ‖u‖ * (1 / ((1 - β) * ‖u‖ ^ 2)) = (1 - β)⁻¹ / ‖u‖ := by
    field_simp [pow_two, h1mb_pos.ne', hu_norm_pos.ne']
  -- Rewrite both sides into a single reciprocal comparison and apply the scaled inequality.
  calc
    |ρ|⁻¹ * ‖u‖ = ‖u‖ * (1 / ρ) := hlhs
    _ ≤ ‖u‖ * (1 / ((1 - β) * ‖u‖ ^ 2)) := hscaled
    _ = (1 - β)⁻¹ / ‖u‖ := hrhs

/-- Chapter05 Lemma 5.4.17 (4): if `M` is symmetric and nonsingular, `β ∈ [0, 1 / 3]`,
`‖M y - M⁻¹ s‖ ≤ β * ‖M⁻¹ s‖`, and `M⁻¹ s ≠ 0`, then
`‖E * (1 - (dotProduct y s)⁻¹ • Matrix.vecMulVec (M⁻¹ s) (M⁻¹ s))‖ ≤
  Real.sqrt (1 - ((1 - 2 * β) / (1 - β ^ 2)) *
    (‖E.toEuclideanLin ((M⁻¹).toEuclideanLin s)‖ / (‖E‖ * ‖(M⁻¹).toEuclideanLin s‖)) ^ 2) * ‖E‖`,
and the curvature denominator nonzeroness is derived from
`curvaturePairing_ne_zero_of_inverseSecantResidual_le`. -/
theorem frobenius_rightMul_rankOneProjector_le
    (M : MatrixN) (hM : M.IsSymm) (hMdet : IsUnit M.det)
    (β : ℝ) (hβ : β ∈ Set.Icc (0 : ℝ) (1 / 3))
    (s y : Point)
    (hres : ‖M.toEuclideanLin y - (M⁻¹).toEuclideanLin s‖ ≤ β * ‖(M⁻¹).toEuclideanLin s‖)
    (hMs : (M⁻¹).toEuclideanLin s ≠ 0)
    (E : MatrixN) :
    ‖E *
        (1 - (dotProduct y s)⁻¹ •
          Matrix.vecMulVec ((M⁻¹).toEuclideanLin s) ((M⁻¹).toEuclideanLin s))‖ ≤
      Real.sqrt
          (1 - ((1 - 2 * β) / (1 - β ^ 2)) *
            (‖E.toEuclideanLin ((M⁻¹).toEuclideanLin s)‖ / (‖E‖ * ‖(M⁻¹).toEuclideanLin s‖)) ^
              2) * ‖E‖ := by
  by_cases hE : E = 0
  · -- The zero matrix is the trivial endpoint of the Frobenius estimate.
    simp [hE]
  · let u : Point := (M⁻¹).toEuclideanLin s
    let ρ : ℝ := dotProduct y s
    let α : ℝ := (1 - 2 * β) / (1 - β ^ 2)
    let θ : ℝ := ‖E.toEuclideanLin u‖ / (‖E‖ * ‖u‖)
    have hu : u ≠ 0 := hMs
    have hβlt1 : β < 1 := by
      nlinarith [hβ.2]
    have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hE_norm_pos : 0 < ‖E‖ := norm_pos_iff.mpr hE
    have hρpos : 0 < ρ := by
      simpa [u, ρ, dotProduct_comm] using
        curvaturePairing_pos_of_inverseSecantResidual_le M hM hMdet β hβlt1 s y hres hMs
    have hbounds :=
      curvaturePairing_bounds_of_inverseSecantResidual_le M hM hMdet β s y hres
    have hlower : (1 - β) * ‖u‖ ^ 2 ≤ ρ := by
      simpa [u, ρ, dotProduct_comm] using hbounds.1
    have hupper : ρ ≤ (1 + β) * ‖u‖ ^ 2 := by
      simpa [u, ρ, dotProduct_comm] using hbounds.2
    have hαIcc : α ∈ Set.Icc (3 / 8 : ℝ) 1 := by
      simpa [α] using residualControlAlpha_formula_mem_Icc β hβ
    have hθIcc : θ ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [θ] using normalizedFrobeniusAngle_mem_Icc E u
    have hcoeff :
        α / ‖u‖ ^ 2 ≤ (2 * ρ - ‖u‖ ^ 2) / ρ ^ 2 := by
      exact le_trans
        (by
          simpa [α] using
            alpha_div_norm_sq_le_projector_bridge β ρ u hβ hu hρpos hupper)
        (projector_coefficient_le_of_lower_curvature β ρ u hβ hρpos hlower)
    have hθsq_le_one : θ ^ 2 ≤ 1 := by
      nlinarith [hθIcc.1, hθIcc.2]
    have hsqrt_arg_nonneg : 0 ≤ 1 - α * θ ^ 2 := by
      nlinarith [hαIcc.1, hαIcc.2, hθsq_le_one]
    have htheta_expand :
        (1 - α * θ ^ 2) * ‖E‖ ^ 2 =
          ‖E‖ ^ 2 + (-(α / ‖u‖ ^ 2)) * ‖E.toEuclideanLin u‖ ^ 2 := by
      -- Expand the normalized angle only once, using that `‖E‖` and `‖u‖` are nonzero.
      dsimp [θ]
      field_simp [pow_two, hE_norm_pos.ne', hu_norm_pos.ne']
      ring
    have hsq_core :
        ‖E * (1 - ρ⁻¹ • Matrix.vecMulVec u u)‖ ^ 2 ≤
          (1 - α * θ ^ 2) * ‖E‖ ^ 2 := by
      have hcoeff_neg :
          ((-2 * ρ + ‖u‖ ^ 2) / ρ ^ 2) ≤ -(α / ‖u‖ ^ 2) := by
        have hrewrite :
            ((-2 * ρ + ‖u‖ ^ 2) / ρ ^ 2) = -((2 * ρ - ‖u‖ ^ 2) / ρ ^ 2) := by
          ring
        rw [hrewrite]
        nlinarith [hcoeff]
      have hmul :
          ((-2 * ρ + ‖u‖ ^ 2) / ρ ^ 2) * ‖E.toEuclideanLin u‖ ^ 2 ≤
            (-(α / ‖u‖ ^ 2)) * ‖E.toEuclideanLin u‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right hcoeff_neg (sq_nonneg ‖E.toEuclideanLin u‖)
      -- Route correction: after the exact Frobenius identity, only the two scalar coefficient
      -- comparisons from the source proof remain.
      calc
        ‖E * (1 - ρ⁻¹ • Matrix.vecMulVec u u)‖ ^ 2
            = ‖E‖ ^ 2 + ((-2 * ρ + ‖u‖ ^ 2) / ρ ^ 2) * ‖E.toEuclideanLin u‖ ^ 2 := by
                rw [frobenius_right_mul_self_rank_one_sq]
        _ ≤ ‖E‖ ^ 2 + (-(α / ‖u‖ ^ 2)) * ‖E.toEuclideanLin u‖ ^ 2 := by
              nlinarith [hmul]
        _ = (1 - α * θ ^ 2) * ‖E‖ ^ 2 := by
              exact htheta_expand.symm
    have hmain :
        ‖E * (1 - ρ⁻¹ • Matrix.vecMulVec u u)‖ ≤ Real.sqrt (1 - α * θ ^ 2) * ‖E‖ := by
      -- Compare squares first, then take square roots at the very end.
      refine
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg E))).1 ?_
      calc
        ‖E * (1 - ρ⁻¹ • Matrix.vecMulVec u u)‖ ^ 2 ≤ (1 - α * θ ^ 2) * ‖E‖ ^ 2 := hsq_core
        _ = (Real.sqrt (1 - α * θ ^ 2) * ‖E‖) ^ 2 := by
              calc
                (1 - α * θ ^ 2) * ‖E‖ ^ 2
                    = (Real.sqrt (1 - α * θ ^ 2)) ^ 2 * ‖E‖ ^ 2 := by
                        rw [Real.sq_sqrt hsqrt_arg_nonneg]
                _ = (Real.sqrt (1 - α * θ ^ 2) * ‖E‖) ^ 2 := by
                        ring
    simpa only [u, ρ, α, θ] using hmain

/-- Chapter05 Lemma 5.4.17 (5): under the hypotheses of
`frobenius_rightMul_rankOneProjector_le`, the mixed rank-one factor with
`(M.toEuclideanLin y)ᵀ` satisfies
`‖E * (1 - (dotProduct y s)⁻¹ • Matrix.vecMulVec (M⁻¹ s) (M y))‖ ≤
  (Real.sqrt (1 - ((1 - 2 * β) / (1 - β ^ 2)) *
      (‖E.toEuclideanLin ((M⁻¹).toEuclideanLin s)‖ / (‖E‖ * ‖(M⁻¹).toEuclideanLin s‖)) ^ 2) +
    (1 - β)⁻¹ * ‖M.toEuclideanLin y - (M⁻¹).toEuclideanLin s‖ / ‖(M⁻¹).toEuclideanLin s‖) * ‖E‖`;
the denominator `dotProduct y s ≠ 0` is derived from
`curvaturePairing_ne_zero_of_inverseSecantResidual_le`. -/
theorem frobenius_rightMul_mixedRankOne_le
    (M : MatrixN) (hM : M.IsSymm) (hMdet : IsUnit M.det)
    (β : ℝ) (hβ : β ∈ Set.Icc (0 : ℝ) (1 / 3))
    (s y : Point)
    (hres : ‖M.toEuclideanLin y - (M⁻¹).toEuclideanLin s‖ ≤ β * ‖(M⁻¹).toEuclideanLin s‖)
    (hMs : (M⁻¹).toEuclideanLin s ≠ 0)
    (E : MatrixN) :
    ‖E *
        (1 - (dotProduct y s)⁻¹ •
          Matrix.vecMulVec ((M⁻¹).toEuclideanLin s) (M.toEuclideanLin y))‖ ≤
      (Real.sqrt
            (1 - ((1 - 2 * β) / (1 - β ^ 2)) *
              (‖E.toEuclideanLin ((M⁻¹).toEuclideanLin s)‖ / (‖E‖ * ‖(M⁻¹).toEuclideanLin s‖)) ^
                2) +
          (1 - β)⁻¹ * ‖M.toEuclideanLin y - (M⁻¹).toEuclideanLin s‖ /
            ‖(M⁻¹).toEuclideanLin s‖) * ‖E‖ := by
  let u : Point := (M⁻¹).toEuclideanLin s
  let v : Point := M.toEuclideanLin y
  let ρ : ℝ := dotProduct y s
  let α : ℝ := (1 - 2 * β) / (1 - β ^ 2)
  have hu : u ≠ 0 := hMs
  have hβlt1 : β < 1 := by
    nlinarith [hβ.2]
  have hbounds :=
    curvaturePairing_bounds_of_inverseSecantResidual_le M hM hMdet β s y hres
  have hlower : (1 - β) * ‖u‖ ^ 2 ≤ ρ := by
    simpa [u, ρ, dotProduct_comm] using hbounds.1
  have hproj :
      ‖E * (1 - ρ⁻¹ • Matrix.vecMulVec u u)‖ ≤
        Real.sqrt (1 - α * (‖E.toEuclideanLin u‖ / (‖E‖ * ‖u‖)) ^ 2) * ‖E‖ := by
    simpa [u, ρ, α] using
      frobenius_rightMul_rankOneProjector_le M hM hMdet β hβ s y hres hMs E
  have hresidual_scalar :
      |ρ|⁻¹ * ‖u‖ ≤ (1 - β)⁻¹ / ‖u‖ := by
    simpa [u, ρ] using residual_coefficient_le_of_lower_curvature β ρ u hβlt1 hu hlower
  have hcorr :
      ‖ρ⁻¹ • Matrix.vecMulVec (E.toEuclideanLin u) (u - v)‖ ≤
        ((1 - β)⁻¹ * ‖u - v‖ / ‖u‖) * ‖E‖ := by
    calc
      ‖ρ⁻¹ • Matrix.vecMulVec (E.toEuclideanLin u) (u - v)‖
          ≤ |ρ|⁻¹ * ‖E‖ * ‖u‖ * ‖u - v‖ := by
            exact frobenius_rank_one_residual_correction_le E u v ρ
      _ ≤ ((1 - β)⁻¹ / ‖u‖) * ‖E‖ * ‖u - v‖ := by
            have hscaled :
                (|ρ|⁻¹ * ‖u‖) * (‖E‖ * ‖u - v‖) ≤
                  ((1 - β)⁻¹ / ‖u‖) * (‖E‖ * ‖u - v‖) := by
              exact mul_le_mul_of_nonneg_right hresidual_scalar
                (mul_nonneg (norm_nonneg E) (norm_nonneg (u - v)))
            simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled
      _ = ((1 - β)⁻¹ * ‖u - v‖ / ‖u‖) * ‖E‖ := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
  have hsplit :
      E * (1 - ρ⁻¹ • Matrix.vecMulVec u v) =
        E * (1 - ρ⁻¹ • Matrix.vecMulVec u u) +
          ρ⁻¹ • Matrix.vecMulVec (E.toEuclideanLin u) (u - v) := by
    -- Route correction: decompose the mixed rank-one factor exactly as in the source proof,
    -- then treat the projector term and the residual term separately.
    calc
      E * (1 - ρ⁻¹ • Matrix.vecMulVec u v)
          = E * ((1 - ρ⁻¹ • Matrix.vecMulVec u u) + ρ⁻¹ • Matrix.vecMulVec u (u - v)) := by
              congr 1
              ext i j
              simp [Matrix.vecMulVec_apply]
              ring
      _ = E * (1 - ρ⁻¹ • Matrix.vecMulVec u u) + E * (ρ⁻¹ • Matrix.vecMulVec u (u - v)) := by
            rw [Matrix.mul_add]
      _ = E * (1 - ρ⁻¹ • Matrix.vecMulVec u u) +
            ρ⁻¹ • (E * Matrix.vecMulVec u (u - v)) := by
            rw [Matrix.mul_smul]
      _ = E * (1 - ρ⁻¹ • Matrix.vecMulVec u u) +
            ρ⁻¹ • Matrix.vecMulVec (E.toEuclideanLin u) (u - v) := by
            congr 1
            ext i j
            simp [Matrix.mul_vecMulVec, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  calc
    ‖E * (1 - ρ⁻¹ • Matrix.vecMulVec u v)‖
        = ‖E * (1 - ρ⁻¹ • Matrix.vecMulVec u u) +
            ρ⁻¹ • Matrix.vecMulVec (E.toEuclideanLin u) (u - v)‖ := by
              rw [hsplit]
    _ ≤ ‖E * (1 - ρ⁻¹ • Matrix.vecMulVec u u)‖ +
          ‖ρ⁻¹ • Matrix.vecMulVec (E.toEuclideanLin u) (u - v)‖ := by
            exact norm_add_le _ _
    _ ≤ Real.sqrt (1 - α * (‖E.toEuclideanLin u‖ / (‖E‖ * ‖u‖)) ^ 2) * ‖E‖ +
          (((1 - β)⁻¹ * ‖u - v‖ / ‖u‖) * ‖E‖) := by
            exact add_le_add hproj hcorr
    _ = (Real.sqrt (1 - α * (‖E.toEuclideanLin u‖ / (‖E‖ * ‖u‖)) ^ 2) +
          (1 - β)⁻¹ * ‖u - v‖ / ‖u‖) * ‖E‖ := by
            ring
    _ = (Real.sqrt
            (1 - ((1 - 2 * β) / (1 - β ^ 2)) *
              (‖E.toEuclideanLin ((M⁻¹).toEuclideanLin s)‖ /
                  (‖E‖ * ‖(M⁻¹).toEuclideanLin s‖)) ^ 2) +
          (1 - β)⁻¹ * ‖M.toEuclideanLin y - (M⁻¹).toEuclideanLin s‖ /
            ‖(M⁻¹).toEuclideanLin s‖) * ‖E‖ := by
            simp [u, v, α, norm_sub_rev]

end EuclideanMatrix
