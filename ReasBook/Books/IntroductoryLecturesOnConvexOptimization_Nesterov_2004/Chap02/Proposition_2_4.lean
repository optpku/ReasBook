/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Matrix.Order
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_5_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Example_2_1_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient MatrixOrder StrongConvexSmooth
open Matrix

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Proposition 2.4 lies in finite-dimensional quadratic optimization on `ℝⁿ`.

Sampled owner-style declarations:
* `quadraticObjective` and `symmetric_quadratic_contDiff_and_gradient_lipschitz`
* `IsStrongConvexSmoothObjective`
* `Matrix.PosSemidef.convexOn_quadraticObjective`
* `strongConvexOn_iff_convex`

Best owner abstraction:
* `IsStrongConvexSmoothObjective μ L` for the objective class

Primitive data:
* the quadratic data `α`, `a`, `A`
* the matrix Loewner bounds `μ I ≤ A ≤ L I`

Derived API:
* symmetry of `A`, recovered from the Loewner lower bound via `Matrix.PosSemidef`
* `C¹` regularity and gradient Lipschitzness from
  `symmetric_quadratic_contDiff_and_gradient_lipschitz`
* `μ`-strong convexity by rewriting
  `quadraticObjective α a A - (μ / 2) * ‖·‖²` as the shifted quadratic
  `quadraticObjective α a (A - μ • 1)` and applying `strongConvexOn_iff_convex`

Source/core/bridge triage:
* source-facing: a quadratic objective satisfying the textbook Hessian bounds
* core/canonical: `quadraticObjective`, `StrongConvexOn`, `IsStrongConvexSmoothObjective`
* bridge/view: positivity of `A - μ • 1` and the induced operator-order estimate on
  `A.toEuclideanLin`
-/

/-- Proposition 2.4: if `A` satisfies `μ I ≤ A ≤ L I` with `0 < μ`, then the canonical quadratic
objective `quadraticObjective α a A` belongs to the source-facing class `𝓢[μ, L]¹¹`. -/
-- Proof sketch: use the owner definition `quadraticObjective α a A` with constant Hessian
-- `A.toEuclideanLin`. Proposition 1.5.7 supplies the `C¹` and gradient-Lipschitz parts, while
-- the lower matrix bound makes `A - μ I` positive semidefinite, so
-- `strongConvexOn_iff_convex` reduces `μ`-strong convexity of `quadraticObjective α a A` to
-- convexity of the shifted quadratic `quadraticObjective α a (A - μ I)`. The Loewner lower bound
-- already forces symmetry of `A`, so that input is derived rather than primitive. The positivity
-- hypothesis `0 < μ` matches the chapter owner predicate `IsStrongConvexSmoothObjective`, and the
-- theorem surface is the chapter notation `𝓢[μ, L]¹¹`.
theorem quadraticObjective_mem_S11
    (μ L α : ℝ) (a : E) (A : Mat)
    (hμ : 0 < μ)
    (hμA : μ • (1 : Mat) ≤ A)
    (hAL : A ≤ L • (1 : Mat)) :
    quadraticObjective α a A ∈ 𝓢[μ, L]¹¹ := by
  let B : E →L[ℝ] E := A.toEuclideanLin.toContinuousLinearMap
  have hshift : (A - μ • (1 : Mat)).PosSemidef := by
    simpa [Matrix.le_iff] using hμA
  have hA : A.IsSymm := by
    have hshift_symm : (A - μ • (1 : Mat)).IsSymm := by
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using hshift.isHermitian
    rw [← sub_add_cancel A (μ • (1 : Mat))]
    exact hshift_symm.add (Matrix.isSymm_one.smul μ)
  obtain ⟨hcontDiff, hgradLip⟩ :=
    symmetric_quadratic_contDiff_and_gradient_lipschitz α a A hA
  have hshifted_eq :
      (fun x : E ↦ quadraticObjective α a A x - (μ / 2) * ‖x‖ ^ (2 : ℕ)) =
        quadraticObjective α a (A - μ • (1 : Mat)) := by
    ext x
    simp [quadraticObjective, inner_sub_left, inner_smul_left]
    ring
  have hstrong : StrongConvexOn Set.univ μ (quadraticObjective α a A) := by
    rw [strongConvexOn_iff_convex, hshifted_eq]
    exact hshift.convexOn_quadraticObjective α a
  have hshift_toEuclideanLin :
      (A - μ • (1 : Mat)).toEuclideanLin =
        (A.toEuclideanLin : E →ₗ[ℝ] E) - μ • LinearMap.id := by
    ext x i
    simp [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  have hμB : μ • (1 : E →L[ℝ] E) ≤ B := by
    have hpos :
        ((A.toEuclideanLin : E →ₗ[ℝ] E) - μ • LinearMap.id).IsPositive := by
      rw [← hshift_toEuclideanLin]
      exact Matrix.isPositive_toEuclideanLin_iff.2 hshift
    rw [ContinuousLinearMap.le_def]
    change ((B : E →ₗ[ℝ] E) - μ • LinearMap.id).IsPositive
    simpa [B] using hpos
  have hB_nonneg : (0 : E →L[ℝ] E) ≤ B := by
    have hμI_nonneg : (0 : E →L[ℝ] E) ≤ μ • (1 : E →L[ℝ] E) := by
      rw [ContinuousLinearMap.nonneg_iff_isPositive]
      simpa using ContinuousLinearMap.isPositive_one.smul_of_nonneg hμ.le
    exact le_trans hμI_nonneg hμB
  have hupper_toEuclideanLin :
      (L • (1 : Mat) - A).toEuclideanLin =
        (L : ℝ) • LinearMap.id - (A.toEuclideanLin : E →ₗ[ℝ] E) := by
    ext x i
    simp [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  have hB_le : B ≤ L • (1 : E →L[ℝ] E) := by
    have hLA_pos : (L • (1 : Mat) - A).PosSemidef := by
      simpa [Matrix.le_iff] using hAL
    have hpos :
        ((L : ℝ) • LinearMap.id - (A.toEuclideanLin : E →ₗ[ℝ] E)).IsPositive := by
      rw [← hupper_toEuclideanLin]
      exact Matrix.isPositive_toEuclideanLin_iff.2 hLA_pos
    rw [ContinuousLinearMap.le_def]
    change ((L : ℝ) • LinearMap.id - (B : E →ₗ[ℝ] E)).IsPositive
    simpa [B] using hpos
  have hcore : IsStrongConvexSmoothObjective μ L (quadraticObjective α a A) := by
    refine ⟨hμ, hcontDiff, hstrong, ?_⟩
    intro x y
    by_cases hxy : x = y
    · simp [hxy]
    · have hL_nonneg : 0 ≤ L := by
        have hLI_nonneg : (0 : E →L[ℝ] E) ≤ L • (1 : E →L[ℝ] E) := le_trans hB_nonneg hB_le
        have hposLI : (L • (1 : E →L[ℝ] E)).IsPositive :=
          (ContinuousLinearMap.nonneg_iff_isPositive _).1 hLI_nonneg
        have hquad : 0 ≤ inner ℝ ((L • (1 : E →L[ℝ] E)) (x - y)) (x - y) :=
          hposLI.inner_nonneg_left (x - y)
        have hquad' : 0 ≤ L * ‖x - y‖ ^ (2 : ℕ) := by
          simpa [inner_smul_left, inner_self_eq_norm_sq_to_K] using hquad
        exact nonneg_of_mul_nonneg_left hquad'
          (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) 2)
      have hnorm : ‖B‖ ≤ L := by
        have hsymm : (B : E →ₗ[ℝ] E).IsSymmetric := by
          have hAherm : A.IsHermitian := by
            simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA
          have hsymm0 : A.toEuclideanLin.IsSymmetric :=
            Matrix.isSymmetric_toEuclideanLin_iff.mpr hAherm
          simpa [B] using hsymm0
        have hbound : ∀ z : E, |B.rayleighQuotient z| ≤ L := by
          intro z
          by_cases hz : z = 0
          · simpa [hz] using hL_nonneg
          · have hz_norm_sq_pos : 0 < ‖z‖ ^ (2 : ℕ) := by
              positivity
            have hLI_pos : (L • (1 : E →L[ℝ] E) - B).IsPositive := by
              simpa [ContinuousLinearMap.le_def] using hB_le
            have hquad : inner ℝ (B z) z ≤ L * ‖z‖ ^ (2 : ℕ) := by
              have hnonneg := hLI_pos.inner_nonneg_left z
              simpa [inner_smul_left, inner_sub_left, inner_self_eq_norm_sq_to_K] using hnonneg
            have hnonneg : 0 ≤ inner ℝ (B z) z :=
              ((ContinuousLinearMap.nonneg_iff_isPositive _).1 hB_nonneg).inner_nonneg_left z
            rw [ContinuousLinearMap.rayleighQuotient, abs_of_nonneg]
            · exact (div_le_iff₀ hz_norm_sq_pos).2 hquad
            · exact div_nonneg hnonneg hz_norm_sq_pos.le
        rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient B hsymm]
        exact ciSup_le hbound
      have hnnorm : (‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖₊ : ℝ) ≤ L := by
        change (‖B‖₊ : ℝ) ≤ L
        exact_mod_cast hnorm
      exact (hgradLip.norm_sub_le x y).trans <|
        mul_le_mul_of_nonneg_right hnnorm (norm_nonneg _)
  exact mem_S11_iff.mpr hcore
