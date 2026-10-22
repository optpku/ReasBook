/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped Gradient

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 1.5.7 is `source-facing` in first-order smooth optimization for quadratic
objectives on `ℝⁿ`.

Source/core/bridge triage:
* source-facing: the symmetric quadratic objective `quadraticObjective α a A`
* core/canonical: the owner predicates `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)` from
  Definition 1.5.2
* bridge/view: the pointwise gradient formula `quadraticObjective_gradient_eq`

Primary domain:
* symmetric quadratic objectives on finite-dimensional real inner-product spaces

Sampled owner-style declarations:
* `quadraticObjective` in Definition 1.9.1
* `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)` in Definition 1.5.2
* `UnconstrainedQuadraticMinimizationProblem.gradient_eq` in Proposition 1.9.11, which gives the
  same gradient owner-side under the stronger positive-definite hypothesis
* `ContinuousLinearMap.lipschitz`, the canonical linear-map Lipschitz API

Best owner abstraction:
* `quadraticObjective`

Primitive data:
* the scalar `α`
* the linear coefficient `a`
* the symmetric matrix `A`

Derived API:
* the explicit gradient formula
* `C¹` regularity
* the global Lipschitz bound for the gradient
-/

/-- The gradient of a symmetric quadratic objective is `x ↦ a + A x`. -/
theorem quadraticObjective_gradient_eq
    (α : ℝ) (a : E) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    ∇ (quadraticObjective α a A) = fun x ↦ a + A.toEuclideanLin x := by
  let B : E →L[ℝ] E := A.toEuclideanLin.toContinuousLinearMap
  have hBsymm : (B : E →ₗ[ℝ] E).IsSymmetric := by
    have hAherm : A.IsHermitian := by
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA
    change A.toEuclideanLin.IsSymmetric
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hAherm
  have hgradAt : ∀ x : E, HasGradientAt (quadraticObjective α a A) (a + B x) x := by
    intro x
    have hAffine : HasFDerivAt (fun y : E ↦ inner ℝ a y) (innerSL ℝ a) x := by
      simpa using (innerSL ℝ a).hasFDerivAt
    have hQuad' : HasFDerivAt (fun y : E ↦ inner ℝ (B y) y) (2 • innerSL ℝ (B x)) x := by
      convert (B.hasFDerivAt.inner ℝ (hasFDerivAt_id x))
      ext y
      simp only [ContinuousLinearMap.coe_smul', coe_innerSL_apply, Pi.smul_apply, nsmul_eq_mul,
        Nat.cast_ofNat, id_eq, ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', fderivInnerCLM_apply]
      calc
        2 * inner ℝ (B x) y = inner ℝ y (B x) + inner ℝ y (B x) := by
          rw [real_inner_comm y (B x)]
          ring
        _ = inner ℝ y (B x) + inner ℝ (B y) x := by
          congr 1
          exact (hBsymm y x).symm
        _ = inner ℝ (B x) y + inner ℝ (B y) x := by
          rw [real_inner_comm y (B x)]
    have hQuad0 : HasFDerivAt (fun y : E ↦ (1 / 2 : ℝ) • inner ℝ (B y) y)
        ((1 / 2 : ℝ) • (2 • innerSL ℝ (B x))) x :=
      hQuad'.const_smul (1 / 2 : ℝ)
    have hlin : ((1 / 2 : ℝ) • (2 • innerSL ℝ (B x))) = innerSL ℝ (B x) := by
      apply ContinuousLinearMap.ext
      intro y
      simp
    have hQuad : HasFDerivAt (fun y : E ↦ (1 / 2 : ℝ) • inner ℝ (B y) y)
        (innerSL ℝ (B x)) x :=
      hlin ▸ hQuad0
    have hSum : HasFDerivAt
        (fun y : E ↦ inner ℝ a y + (1 / 2 : ℝ) • inner ℝ (B y) y)
        (innerSL ℝ a + innerSL ℝ (B x)) x := by
      simpa [Pi.add_apply, add_assoc] using hAffine.add hQuad
    have hDeriv0 : HasFDerivAt
        (fun y : E ↦ α + (inner ℝ a y + (1 / 2 : ℝ) • inner ℝ (B y) y))
        (innerSL ℝ a + innerSL ℝ (B x)) x :=
      hSum.const_add α
    have hDeriv : HasFDerivAt (quadraticObjective α a A) (innerSL ℝ a + innerSL ℝ (B x)) x := by
      convert hDeriv0 using 1
      funext y
      simp [quadraticObjective, B, add_assoc, smul_eq_mul]
    have hdual : (InnerProductSpace.toDual ℝ E).symm (innerSL ℝ a + innerSL ℝ (B x)) = a + B x := by
      apply (InnerProductSpace.toDual ℝ E).injective
      ext z
      simp [innerSL_apply_apply]
    simpa [hdual] using hDeriv.hasGradientAt
  exact gradient_eq hgradAt

/-- Proposition 1.5.7: if `A` is symmetric, then the quadratic objective
`quadraticObjective α a A` is `C¹` on `ℝⁿ` and its gradient is globally Lipschitz
with constant equal to the operator norm of `A`, i.e. it belongs to `C^{1,1}_L(ℝⁿ)` for
`L = ‖A‖`. -/
-- Proof sketch: differentiate the affine and quadratic parts to obtain
-- `∇ (quadraticObjective α a A) x = a + (Matrix.toEuclideanLin A) x`, where
-- symmetry identifies the Hessian with `A`. Then the quadratic objective is `C¹`, and the linear
-- estimate `‖A (x - y)‖ ≤ ‖A‖ ‖x - y‖` gives the global Lipschitz bound for the gradient.
theorem symmetric_quadratic_contDiff_and_gradient_lipschitz
    (α : ℝ) (a : E) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    ContDiff ℝ 1 (quadraticObjective α a A) ∧
      LipschitzWith ‖A.toEuclideanLin.toContinuousLinearMap‖₊
        (∇ (quadraticObjective α a A)) := by
  let B : E →L[ℝ] E := A.toEuclideanLin.toContinuousLinearMap
  have hAffineContDiff : ContDiff ℝ 1 (fun x : E ↦ inner ℝ a x) := by
    simpa using (innerSL ℝ a).contDiff
  have hcontQuad : ContDiff ℝ 1 (fun x : E ↦ inner ℝ (B x) x) := by
    simpa using ContDiff.inner ℝ B.contDiff contDiff_id
  have hcontSum : ContDiff ℝ 1
      (fun x : E ↦ inner ℝ a x + (1 / 2 : ℝ) • inner ℝ (B x) x) := by
    simpa [Pi.add_apply, add_assoc] using hAffineContDiff.add (hcontQuad.const_smul (1 / 2 : ℝ))
  have hcontDiff0 : ContDiff ℝ 1
      (fun x : E ↦ α + (inner ℝ a x + (1 / 2 : ℝ) • inner ℝ (B x) x)) :=
    contDiff_const.add hcontSum
  have hcontDiff : ContDiff ℝ 1 (quadraticObjective α a A) := by
    convert hcontDiff0 using 1
    funext x
    simp [quadraticObjective, B, add_assoc, smul_eq_mul]
  have hgradLip' : LipschitzWith ‖B‖₊ (fun x : E ↦ B x + a) := by
    simpa [Function.comp] using
      ((IsometryEquiv.vaddConst a).isometry.lipschitz.comp B.lipschitz)
  have hgradLip : LipschitzWith ‖B‖₊ (fun x : E ↦ a + B x) := by
    simpa [add_comm] using hgradLip'
  refine ⟨hcontDiff, ?_⟩
  simpa [B] using (quadraticObjective_gradient_eq α a A hA ▸ hgradLip)

end
