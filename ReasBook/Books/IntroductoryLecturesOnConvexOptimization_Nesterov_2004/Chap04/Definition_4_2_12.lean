/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Text_4_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Text_4_2_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open scoped ConstrainedArgmin
open scoped CubicRegularizationResidual
open scoped CubicRegularizationModelNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 4.2.12 lies in the cubic-regularization / unconstrained minimizer domain on
complete real inner-product spaces.

Sampled owner-style declarations:
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`, the chapter owner of the
  cubic model `y ↦ f₂(x; y) + (M / 6) ‖y - x‖³`;
* `IsMinOn` in mathlib, the canonical global-minimizer owner on the ambient space;
* `argmin[Set.univ]` in `Chap01/Definition_1_3_3`, the set-valued constrained-argmin bridge built
  from feasibility and `IsMinOn`;
* `hessian` in `Chap01/Definition_1_4_16`, the intrinsic Hessian operator used in the displayed
  stationarity equation;
* `CubicNewtonEstimatingSequence.x_isMin` in `Definition_4_2_14`, a nearby source-facing owner
  that also stores chosen whole-space minimizers through `IsMinOn`.

Source/core/bridge triage:
* source-facing: the cubic regularization mapping `T_M : E → E`;
* core/canonical: the chosen-minimizer owner
  `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ (T_M x)`;
* bridge/view: membership in `argmin[Set.univ] (cubicRegularizationQuadraticApproximation f M x)`
  and the first-order optimality equation for the value `T_M x`.

Primitive data:
* the objective `f`;
* the regularization parameter `M`;
* the chosen map `T_M`.

Derived API:
* the canonical whole-space minimizer relation for `T_M x`;
* membership of `T_M x` in the cubic-model argmin set;
* the stationarity equation under the primitive self-adjointness condition on `hessian f x`,
  and hence under the canonical `C²` bridge
  `hessian_isSelfAdjoint_of_contDiffAt`
  `∇ f(x) + ∇² f(x)(T_M(x) - x) + (M / 2) ‖T_M(x) - x‖ (T_M(x) - x) = 0`.

Positivity of `M` is not primitive data of the owner here: it matters only in separate existence /
coercivity results for the cubic model, not in the definition of a chosen minimizer map once the
argmin property is already supplied.

This file therefore keeps the source-facing owner as a chosen map together with its canonical
whole-space minimizer property, while reusing `argmin[Set.univ]` only as the derived set-valued
bridge exposed elsewhere in the chapter. -/

/-- A cubic regularization mapping for `f` with parameter `M` in Definition 4.2.12 is a map
`T_M : E → E` such that, for every base point `x`, the value `T_M x` globally minimizes the cubic
model
`cubicRegularizationQuadraticApproximation f M x = (y ↦ f₂(x; y) + (M / 6) ‖y - x‖^3)`. -/
structure CubicRegularizationMapping (f : E → ℝ) (M : ℝ) where
  /-- The cubic regularization map `T_M`. -/
  toFun : E → E
  /-- For each base point `x`, `T_M x` globally minimizes the cubic model centered at `x`. -/
  isMinOn (x : E) :
    IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ (toFun x)

namespace CubicRegularizationMapping

variable {f : E → ℝ} {M : ℝ}

/-- A cubic regularization mapping acts on a base point by evaluation of its underlying map. -/
instance : CoeFun (CubicRegularizationMapping f M) (fun _ ↦ E → E) where
  coe T := T.toFun

-- Proof sketch: this is exactly the `isMinOn` field of the structure.
/-- Evaluating a cubic regularization mapping at `x` gives a global minimizer of
`cubicRegularizationQuadraticApproximation f M x`. -/
theorem isMinOn_apply
    (T : CubicRegularizationMapping f M) (x : E) :
    IsMinOn (m[f; M](x)) Set.univ (T x) :=
  T.isMinOn x

-- Proof sketch: combine `isMinOn_apply` with `mem_constrainedArgmin_iff`, using that the feasible
-- set is `Set.univ`.
/-- Evaluating a cubic regularization mapping at `x` gives a point of the canonical whole-space
argmin set of the cubic model centered at `x`. -/
theorem mem_argmin_apply
    (T : CubicRegularizationMapping f M) (x : E) :
    T x ∈ argmin[Set.univ] (m[f; M](x)) := by
  exact mem_constrainedArgmin_iff.mpr ⟨by simp, T.isMinOn_apply x⟩

/-- The residual function `r_M` attached to a cubic regularization mapping. -/
def residual (T : CubicRegularizationMapping f M) : E → ℝ :=
  fun x ↦ r[T x] x

/-- Evaluating `T.residual` recovers the textbook formula `r_M(x) = ‖T_M(x) - x‖`. -/
@[simp] theorem residual_apply
    (T : CubicRegularizationMapping f M) (x : E) :
    T.residual x = ‖T x - x‖ := by
  simp [residual, norm_sub_rev]

/-- Helper for Definition 4.2.12: the residual of a cubic regularization mapping is nonnegative
because it is a norm distance to the base point. -/
theorem residual_nonneg
    (T : CubicRegularizationMapping f M) (x : E) :
    0 ≤ T.residual x := by
  -- Rewrite the residual to the norm formula and use norm nonnegativity.
  rw [residual_apply]
  exact norm_nonneg (T x - x)

end CubicRegularizationMapping

/-- Helper for Definition 4.2.12: the shifted second-order Taylor model
`z ↦ secondOrderTaylorModelAt f x z - f x` has the expected dual-valued derivative once the
frozen Hessian is self-adjoint. -/
lemma secondOrderTaylorModel_sub_hasFDerivAt_of_isSelfAdjoint
    {f : E → ℝ} {x y : E}
    (hH : IsSelfAdjoint (hessian f x)) :
    HasFDerivAt (fun z : E ↦ secondOrderTaylorModelAt f x z - f x)
      (InnerProductSpace.toDual ℝ E (∇ f x + hessian f x (y - x))) y := by
  let a : E := y - x
  let g : E := ∇ f x
  let H : E →L[ℝ] E := hessian f x
  have hsub : HasFDerivAt (fun z : E ↦ z - x) (ContinuousLinearMap.id ℝ E) y := by
    simpa using (hasFDerivAt_id y).sub_const x
  have hlin : HasFDerivAt (fun z : E ↦ inner ℝ g z) (innerSL ℝ g) a := by
    simpa using (innerSL ℝ g).hasFDerivAt
  have hquad' : HasFDerivAt (fun z : E ↦ inner ℝ (H z) z) (2 • innerSL ℝ (H a)) a := by
    -- Symmetry of the Hessian merges the two bilinear cross terms into `2 • innerSL (H a)`.
    convert (H.hasFDerivAt.inner ℝ (hasFDerivAt_id a))
    ext v
    simp only [ContinuousLinearMap.coe_smul', coe_innerSL_apply, Pi.smul_apply, nsmul_eq_mul,
      Nat.cast_ofNat, id_eq, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', fderivInnerCLM_apply]
    calc
      2 * inner ℝ (H a) v = inner ℝ v (H a) + inner ℝ v (H a) := by
        rw [real_inner_comm v (H a)]
        ring
      _ = inner ℝ v (H a) + inner ℝ (H v) a := by
        have hs : inner ℝ v (H a) = inner ℝ (H v) a := by
          simpa [H] using (hH.isSymmetric v a).symm
        rw [hs]
      _ = inner ℝ (H a) v + inner ℝ (H v) a := by
        rw [real_inner_comm v (H a)]
  have hquad0 : HasFDerivAt (fun z : E ↦ (1 / 2 : ℝ) * inner ℝ (H z) z)
      ((1 / 2 : ℝ) • (2 • innerSL ℝ (H a))) a := by
    simpa [smul_eq_mul] using hquad'.const_mul (1 / 2 : ℝ)
  have hquadLin : ((1 / 2 : ℝ) • (2 • innerSL ℝ (H a))) = innerSL ℝ (H a) := by
    ext v
    simp
  have hquad : HasFDerivAt (fun z : E ↦ (1 / 2 : ℝ) * inner ℝ (H z) z)
      (innerSL ℝ (H a)) a := by
    exact hquadLin ▸ hquad0
  have hmodel : HasFDerivAt
      (fun z : E ↦ inner ℝ g z + (1 / 2 : ℝ) * inner ℝ (H z) z)
      (innerSL ℝ g + innerSL ℝ (H a)) a := by
    -- Route correction: differentiate the Taylor pieces before a single composition with
    -- the displacement map, rather than shifting each piece separately.
    simpa [Pi.add_apply, add_assoc] using hlin.add hquad
  have hdual :
      innerSL ℝ g + innerSL ℝ (H a) =
        InnerProductSpace.toDual ℝ E (g + H a) := by
    ext v
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  have hcomp0 :
      HasFDerivAt
        ((fun z : E ↦ inner ℝ g z + (1 / 2 : ℝ) * inner ℝ (H z) z) ∘ fun z : E ↦ z - x)
        ((innerSL ℝ g + innerSL ℝ (H a)).comp (ContinuousLinearMap.id ℝ E)) y := by
    exact hmodel.comp y hsub
  have hcomp :
      HasFDerivAt
        (fun z : E ↦ inner ℝ g (z - x) + (1 / 2 : ℝ) * inner ℝ (H z - H x) (z - x))
        (InnerProductSpace.toDual ℝ E (g + H a)) y := by
    -- Compose the differentiated Taylor model once with the ambient displacement map `z ↦ z - x`.
    convert (hdual ▸ hcomp0) using 1
    · funext z
      simp [Function.comp, map_sub]
  -- Re-expand the Taylor owner only at the end so the proof stays organized by the displacement.
  convert hcomp using 1
  · funext z
    rw [secondOrderTaylorModelAt_apply]
    simp [g, H, map_sub]
    ring

/-- Helper for Definition 4.2.12: under self-adjointness of the frozen Hessian, the second-order
Taylor model centered at `x` has gradient `∇ f x + hessian f x (y - x)` at `y`. -/
lemma hasGradientAt_secondOrderTaylorModelAt_of_isSelfAdjoint
    {f : E → ℝ} {x y : E}
    (hH : IsSelfAdjoint (hessian f x)) :
    HasGradientAt (secondOrderTaylorModelAt f x)
      (∇ f x + hessian f x (y - x)) y := by
  have hmodelSub :
      HasFDerivAt (fun z : E ↦ secondOrderTaylorModelAt f x z - f x)
        (InnerProductSpace.toDual ℝ E (∇ f x + hessian f x (y - x))) y :=
    secondOrderTaylorModel_sub_hasFDerivAt_of_isSelfAdjoint (f := f) (x := x) (y := y) hH
  have hmodel :
      HasFDerivAt (secondOrderTaylorModelAt f x)
        (InnerProductSpace.toDual ℝ E (∇ f x + hessian f x (y - x))) y := by
    -- Add back the frozen constant term `f x`; it does not affect the derivative.
    convert hmodelSub.const_add (f x) using 1
    funext z
    rw [secondOrderTaylorModelAt_apply]
    ring
  simpa using hmodel.hasGradientAt

/-- Helper for Definition 4.2.12: the cubic penalty contributes the vector
`((M / 2) * ‖y - x‖) • (y - x)` to the gradient at `y`. -/
lemma hasGradientAt_cubic_regularization_penalty
    {M : ℝ} {x y : E} :
    HasGradientAt
      (fun z : E ↦ (M / 6 : ℝ) * ‖z - x‖ ^ (3 : ℕ))
      (((M / 2 : ℝ) * ‖y - x‖) • (y - x)) y := by
  -- Rewrite the cubic term through the chapter owner `powerDistance` and reuse its gradient API.
  have hscaled :
      HasFDerivAt
        (fun z : E ↦ (M / 2 : ℝ) * powerDistance (3 : ℝ) x z)
        ((M / 2 : ℝ) •
          InnerProductSpace.toDual ℝ E
            (‖y - x‖ ^ ((3 : ℝ) - 2) • (y - x))) y := by
    simpa [smul_eq_mul, mul_assoc] using
      (hasGradientAt_powerDistance (E := E) (p := (3 : ℝ)) (by norm_num) x y).hasFDerivAt.const_smul
        (M / 2 : ℝ)
  have hscaled' :
      HasFDerivAt
        (fun z : E ↦ (M / 2 : ℝ) * powerDistance (3 : ℝ) x z)
        (InnerProductSpace.toDual ℝ E (((M / 2 : ℝ) * ‖y - x‖) • (y - x))) y := by
    have hdual :
        ((M / 2 : ℝ) •
            InnerProductSpace.toDual ℝ E (‖y - x‖ ^ ((3 : ℝ) - 2) • (y - x))) =
          InnerProductSpace.toDual ℝ E (((M / 2 : ℝ) * ‖y - x‖) • (y - x)) := by
      ext w
      rw [show ((3 : ℝ) - 2) = 1 by norm_num, Real.rpow_one]
      simp [InnerProductSpace.toDual_apply_apply]
      ring
    exact hdual ▸ hscaled
  have hpower :
      HasGradientAt
        (fun z : E ↦ (M / 2 : ℝ) * powerDistance (3 : ℝ) x z)
        (((M / 2 : ℝ) * ‖y - x‖) • (y - x)) y := by
    simpa using hscaled'.hasGradientAt
  convert hpower using 1
  · funext z
    rw [powerDistance_apply]
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring

/-- Helper for Definition 4.2.12: the cubic regularization model has the explicit textbook
gradient at every point once the frozen Hessian is self-adjoint. -/
lemma hasGradientAt_cubicRegularizationQuadraticApproximation_of_isSelfAdjoint
    {f : E → ℝ} {M : ℝ} {x y : E}
    (hH : IsSelfAdjoint (hessian f x)) :
    HasGradientAt (m[f; M](x))
      (∇ f x + hessian f x (y - x) + ((M / 2 : ℝ) * ‖y - x‖) • (y - x)) y := by
  -- Add the Taylor-model gradient and the cubic-penalty gradient.
  have hsum :
      HasFDerivAt (m[f; M](x))
        (InnerProductSpace.toDual ℝ E
          (∇ f x + hessian f x (y - x) + ((M / 2 : ℝ) * ‖y - x‖) • (y - x))) y := by
    simpa [cubicRegularizationQuadraticApproximation_apply, add_assoc, add_left_comm, add_comm]
      using
      (hasGradientAt_secondOrderTaylorModelAt_of_isSelfAdjoint
          (f := f) (x := x) (y := y) hH).hasFDerivAt.add
        (hasGradientAt_cubic_regularization_penalty (M := M) (x := x) (y := y)).hasFDerivAt
  simpa using hsum.hasGradientAt

-- Proof sketch: apply the first-order optimality condition for a global minimizer of
-- `cubicRegularizationQuadraticApproximation f M x`; when `hessian f x` is self-adjoint, the
-- derivative of the quadratic term is `hessian f x (y - x)`, while the cubic term contributes
-- `((M / 2) * ‖y - x‖) • (y - x)`.
/-- If `hessian f x` is self-adjoint, then a global minimizer of the cubic model centered at `x`
satisfies the textbook stationarity equation. -/
theorem cubicRegularization_firstOrderOptimalityCondition_of_isMinOn_of_isSelfAdjoint
    {x y : E}
    (hH : IsSelfAdjoint (hessian f x))
    (hy : IsMinOn (m[f; M](x)) Set.univ y) :
    ∇ f x + hessian f x (y - x) + ((M / 2 : ℝ) * ‖y - x‖) • (y - x) = 0 := by
  -- Differentiate the cubic model explicitly at the minimizer.
  have hgrad :
      HasGradientAt (m[f; M](x))
        (∇ f x + hessian f x (y - x) + ((M / 2 : ℝ) * ‖y - x‖) • (y - x)) y :=
    hasGradientAt_cubicRegularizationQuadraticApproximation_of_isSelfAdjoint
      (f := f) (M := M) (x := x) (y := y) hH
  -- A global minimizer on the whole space has zero totalized gradient.
  have hstationary : ∇ (m[f; M](x)) y = 0 :=
    isMinOn_gradient_eq_zero hy
  -- Replace the totalized gradient by the explicit formula computed above.
  rw [hgrad.gradient] at hstationary
  exact hstationary

-- Proof sketch: first obtain self-adjointness of `hessian f x` from
-- `hessian_isSelfAdjoint_of_contDiffAt`, then apply the self-adjoint owner theorem above.
/-- If `f` is `C²` at `x`, then a global minimizer of the cubic model centered at `x` satisfies
the textbook stationarity equation. -/
theorem cubicRegularization_firstOrderOptimalityCondition_of_isMinOn
    {x y : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hy : IsMinOn (m[f; M](x)) Set.univ y) :
    ∇ f x + hessian f x (y - x) + ((M / 2 : ℝ) * ‖y - x‖) • (y - x) = 0 := by
  exact cubicRegularization_firstOrderOptimalityCondition_of_isMinOn_of_isSelfAdjoint
    (hessian_isSelfAdjoint_of_contDiffAt f x hf) hy

/-- If `f` is `C²` at `x`, then any point of `argmin[Set.univ] (m[f; M](x))` satisfies the
textbook stationarity equation for the cubic model centered at `x`. -/
theorem cubicRegularization_firstOrderOptimalityCondition_of_mem_argmin
    {x y : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hy : y ∈ argmin[Set.univ] (m[f; M](x))) :
    ∇ f x + hessian f x (y - x) + ((M / 2 : ℝ) * ‖y - x‖) • (y - x) = 0 := by
  exact cubicRegularization_firstOrderOptimalityCondition_of_isMinOn
    hf (mem_constrainedArgmin_iff.mp hy).2

namespace CubicRegularizationMapping

-- Proof sketch: combine `T.isMinOn_apply x` with the `C²` stationarity theorem
-- `cubicRegularization_firstOrderOptimalityCondition_of_isMinOn`.
/-- Definition 4.2.12: if `f` is `C²` at `x`, then the cubic-regularization point `T x` satisfies
the textbook
stationarity equation for the cubic model centered at `x`. -/
theorem firstOrderOptimalityCondition
    (T : CubicRegularizationMapping f M) (x : E) (hf : ContDiffAt ℝ 2 f x) :
    ∇ f x + hessian f x (T x - x) + ((M / 2 : ℝ) * ‖T x - x‖) • (T x - x) = 0 :=
  cubicRegularization_firstOrderOptimalityCondition_of_isMinOn hf (T.isMinOn_apply x)

end CubicRegularizationMapping
