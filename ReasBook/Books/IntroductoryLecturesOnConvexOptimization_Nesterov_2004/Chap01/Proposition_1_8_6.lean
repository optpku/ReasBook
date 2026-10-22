/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_8_4

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped Gradient

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "PosMat" => {A : Mat // Matrix.PosDef A}

/- Proposition 1.8.6 is a bridge/view statement in weighted differential calculus.

Source/core/bridge triage:
* source-facing: the formulas expressing the gradient and Hessian in the inner product induced by a
  positive-definite matrix `A`
* core/canonical: the intrinsic owners `gradient` and `hessian` for the weighted inner-product
  structure determined by `A`
* bridge/view: the Euclidean carrier owners `weightedGradient A` and `weightedHessian A`, which
  make the metric parameter explicit and record the weighted owners through Euclidean formulas

Primary domain:
* weighted first- and second-order differential calculus on finite-dimensional real inner-product
  spaces

Sampled owner-style declarations:
* `Matrix.PosDef.WeightedSpace` from Definition 1.8.3
* `HasWeightedGradientSecondOrderExpansionAt.iff_hasGradientAt_and_hasFDerivAt_gradient` from
  Definition 1.8.4
* `gradient` from mathlib's gradient API
* `hessian` from Definition 1.4.16

Best owner abstraction:
* the weighted-space `gradient`/`hessian` pair as core owners
* the coordinate transport `EuclideanSpace.equiv (Fin n) ℝ`, used only as a bridge from the
  weighted coordinate model to the Euclidean formulas

Primitive data:
* `A : PosMat`
* `f : Matrix.PosDef.WeightedSpace A → ℝ`
* `x : E`

Derived API:
* the transported weighted gradient `e.symm (∇ f (e x))`
* the transported weighted Hessian
  `(e.symm : _ →L[ℝ] _).comp (hessian f (e x)).comp (e : _ →L[ℝ] _)`
* the Euclidean formulas identifying those intrinsic weighted owners with `A⁻¹` applied to the
  Euclidean gradient/Hessian of the transported function

The proposition therefore stays at the `bridge/view` layer: it keeps the chapter's canonical
weighted `gradient`/`hessian` owners central, and records only their coordinate transport to the
Euclidean formulas. -/

namespace Matrix.PosDef

section
variable (A : PosMat)

/-- Helper for Proposition 1.8.6: the fixed coordinate equivalence from Euclidean coordinates to
the weighted coordinate model. -/
private abbrev coordEquiv (A : PosMat) : E ≃L[ℝ] WeightedSpace A :=
  (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.toContinuousLinearEquiv

/-- Helper for Proposition 1.8.6: composing the weighted Riesz map with the coordinate
equivalence gives the Euclidean Riesz map after applying the metric operator `A`. -/
private theorem weighted_toDual_comp_coordEquiv (g : WeightedSpace A) :
    (InnerProductSpace.toDual ℝ (WeightedSpace A) g).comp
        (coordEquiv (n := n) A : E →L[ℝ] WeightedSpace A) =
      InnerProductSpace.toDual ℝ E
        (A.1.toEuclideanLin ((coordEquiv (n := n) A).symm g)) := by
  let e : E ≃L[ℝ] WeightedSpace A := coordEquiv (n := n) A
  ext h
  -- Both functionals evaluate to the same quadratic-form coordinate expression.
  have hinner :
      inner ℝ (A.1.toEuclideanLin (e.symm g)) h = dotProduct (e h) (A.1 *ᵥ g) := by
    simpa [e, coordEquiv, Matrix.ofLp_toLpLin] using
      (EuclideanSpace.inner_eq_star_dotProduct (A.1.toEuclideanLin (e.symm g)) h)
  rw [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
    InnerProductSpace.toDual_apply_apply, Matrix.PosDef.inner_eq_dotProduct_mulVec, hinner,
    dotProduct_comm]

/-- Helper for Proposition 1.8.6: in Euclidean coordinates, the transported weighted gradient is
the metric operator `A` applied to the intrinsic weighted gradient. -/
private theorem euclidean_gradient_eq_metric_transport (f : WeightedSpace A → ℝ) (x : E) :
    ∇ (f ∘ coordEquiv (n := n) A) x =
      A.1.toEuclideanLin ((coordEquiv (n := n) A).symm (∇ f ((coordEquiv (n := n) A) x))) := by
  let e : E ≃L[ℝ] WeightedSpace A := coordEquiv (n := n) A
  -- Unfold both gradients and compare the derivatives through the two Riesz maps.
  change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (f ∘ e) x) =
      A.1.toEuclideanLin
        (e.symm ((InnerProductSpace.toDual ℝ (WeightedSpace A)).symm (fderiv ℝ f (e x))))
  rw [ContinuousLinearEquiv.comp_right_fderiv]
  apply (InnerProductSpace.toDual ℝ E).injective
  simpa [e, coordEquiv] using
    weighted_toDual_comp_coordEquiv (A := A)
      (g := (InnerProductSpace.toDual ℝ (WeightedSpace A)).symm (fderiv ℝ f (e x)))

/-- Helper for Proposition 1.8.6: the inverse metric cancels the metric operator on Euclidean
vectors. -/
private theorem inverse_metric_toEuclideanLin_cancel (A : PosMat) (v : E) :
    (A.1⁻¹).toEuclideanLin (A.1.toEuclideanLin v) = v := by
  -- Rewrite the Euclidean action as matrix multiplication and use nonsingular inverse
  -- cancellation for the positive-definite matrix `A`.
  have hdet : IsUnit A.1.det := isUnit_iff_ne_zero.mpr (ne_of_gt A.2.det_pos)
  have hmul : A.1⁻¹ * A.1 = 1 := Matrix.nonsing_inv_mul A.1 hdet
  ext i
  simp [Matrix.mulVec_mulVec, hmul]

/-- Helper for Proposition 1.8.6: differentiating the transported weighted gradient field
produces the transported weighted Hessian. -/
private theorem transported_weighted_gradient_fderiv (f : WeightedSpace A → ℝ) (x : E) :
    fderiv ℝ (fun y : E ↦ (coordEquiv (n := n) A).symm (∇ f ((coordEquiv (n := n) A) y))) x =
      (((coordEquiv (n := n) A).symm : WeightedSpace A →L[ℝ] E).comp
        (hessian f ((coordEquiv (n := n) A) x))).comp
        (coordEquiv (n := n) A : E →L[ℝ] WeightedSpace A) := by
  let e : E ≃L[ℝ] WeightedSpace A := coordEquiv (n := n) A
  -- Differentiate `e.symm ∘ ∇ f ∘ e` by the totalized `fderiv` rules for continuous linear
  -- equivalences on the left and on the right.
  rw [show (fun y : E ↦ e.symm (∇ f (e y))) = e.symm ∘ fun y : E ↦ ∇ f (e y) by rfl]
  rw [ContinuousLinearEquiv.comp_fderiv, ContinuousLinearEquiv.comp_right_fderiv]
  simpa [e, coordEquiv, hessian, ContinuousLinearMap.comp_assoc]

/-- Proposition 1.8.6 (1): after transporting the intrinsic weighted gradient on
`Matrix.PosDef.WeightedSpace A` to Euclidean coordinates, one obtains `A⁻¹` applied to the
Euclidean gradient of the transported function. -/
theorem gradient_eq_inverse_gradient (f : WeightedSpace A → ℝ) (x : E) :
    let e : E ≃L[ℝ] WeightedSpace A :=
      (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.toContinuousLinearEquiv
    e.symm (∇ f (e x)) = (A.1⁻¹).toEuclideanLin (∇ (f ∘ e) x) := by
  -- Route correction: first prove the stronger `A`-transport formula, then cancel `A`.
  change (coordEquiv (n := n) A).symm (∇ f ((coordEquiv (n := n) A) x)) =
    (A.1⁻¹).toEuclideanLin (∇ (f ∘ coordEquiv (n := n) A) x)
  rw [euclidean_gradient_eq_metric_transport (A := A) (f := f) (x := x)]
  exact (inverse_metric_toEuclideanLin_cancel A
    ((coordEquiv (n := n) A).symm (∇ f ((coordEquiv (n := n) A) x)))).symm

/-- Proposition 1.8.6 (2): after transporting the intrinsic weighted Hessian on
`Matrix.PosDef.WeightedSpace A` to Euclidean coordinates, one obtains the inverse metric composed
with the Euclidean Hessian of the transported function. -/
theorem hessian_eq_inverse_comp_hessian (f : WeightedSpace A → ℝ) (x : E) :
    let e : E ≃L[ℝ] WeightedSpace A :=
      (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.toContinuousLinearEquiv
    let K : WeightedSpace A →L[ℝ] WeightedSpace A := hessian f (e x)
    let H₀ : WeightedSpace A →L[ℝ] E := (e.symm : WeightedSpace A →L[ℝ] E).comp K
    let H : E →L[ℝ] E :=
      H₀.comp (e : E →L[ℝ] WeightedSpace A)
    H =
      (A.1⁻¹).toEuclideanLin.toContinuousLinearMap.comp (hessian (f ∘ e) x) := by
  let e : E ≃L[ℝ] WeightedSpace A := coordEquiv (n := n) A
  let K : WeightedSpace A →L[ℝ] WeightedSpace A := hessian f (e x)
  let H₀ : WeightedSpace A →L[ℝ] E := (e.symm : WeightedSpace A →L[ℝ] E).comp K
  let H : E →L[ℝ] E := H₀.comp (e : E →L[ℝ] WeightedSpace A)
  let M : E ≃L[ℝ] E := (A.1.toEuclideanLin).toContinuousLinearEquiv
  -- Route correction: differentiate the stronger gradient transport, then apply `A⁻¹`.
  have hgrad_eq :
      (fun y : E ↦ ∇ (f ∘ e) y) =
        fun y : E ↦ A.1.toEuclideanLin (e.symm (∇ f (e y))) := by
    funext y
    simpa [e, coordEquiv] using
      euclidean_gradient_eq_metric_transport (A := A) (f := f) (x := y)
  have hright' :
      hessian (f ∘ e) x = M.toContinuousLinearMap.comp H := by
    -- Rewrite the gradient field by the stronger transport identity and differentiate once more.
    rw [hessian, hgrad_eq]
    rw [show (fun y : E ↦ A.1.toEuclideanLin (e.symm (∇ f (e y)))) =
        M ∘ fun y : E ↦ e.symm (∇ f (e y)) by
        rfl]
    rw [ContinuousLinearEquiv.comp_fderiv]
    simpa [M, e, coordEquiv, H, H₀, K] using
      transported_weighted_gradient_fderiv (A := A) (f := f) (x := x)
  have hmetric :
      (hessian (f ∘ e) x) = (A.1.toEuclideanLin).toContinuousLinearMap.comp H := by
    simpa [M] using hright'
  -- Apply the inverse metric pointwise to the differentiated identity.
  ext v
  have hv := congrArg (fun T : E →L[ℝ] E ↦ (A.1⁻¹).toEuclideanLin (T v)) hmetric.symm
  simpa [coordEquiv, H, H₀, K, ContinuousLinearMap.comp_apply,
    inverse_metric_toEuclideanLin_cancel A] using hv

end

end Matrix.PosDef

end
