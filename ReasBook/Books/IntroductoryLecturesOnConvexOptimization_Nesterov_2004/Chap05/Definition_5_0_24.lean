/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_23

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped Gradient HessianDualLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/- Definition 5.0.24 lies in the Newton-decrement / Hessian-dual-norm domain.

Sampled owner declarations:
* `dualLocalNorm` and `‖g‖*[f; x | hPos; hInv]` in `Definition_5_0_20`, the chapter owner for the
  Hessian-metric dual norm of a covector;
* `ContinuousLinearMap.IsInvertible` and `ContinuousLinearMap.inverse` in mathlib, the canonical
  owner abstraction for an invertible Hessian operator;
* `InnerProductSpace.toDual_apply_apply` in mathlib, the canonical Riesz-evaluation bridge from a
  covector formula back to the intrinsic inner-product pairing.

Best owner abstraction:
* source-facing: the Newton decrement of `f` at `x`;
* core/canonical: the dual local norm of the gradient covector;
* bridge/view: the inverse-Hessian gradient-pairing formula.

Primitive data:
* a function `f`;
* a base point `x`;
* Hessian positivity and invertibility at `x`.

Derived API:
* the source-facing notation `λ[f; x | hPos; hInv]`;
* the source-facing self-concordant-domain notation `ndec(f, x, Mf, hx, hH)`;
* the determinant bridge `NewtonDecrement.ofDetNeZero`;
* the positive-definite-domain bridge `NewtonDecrement.ofPosDefMem`;
* the bridge theorem `newtonDecrement_def`.

This file keeps `newtonDecrement` as the source-facing owner, reusing the upstream dual-local-norm
owner directly. Determinant nonvanishing survives only in the explicit bridge
`NewtonDecrement.ofDetNeZero`; the main public surface uses the intrinsic invertibility witness
and the canonical inverse operator. The stronger `CompleteSpace` layer is localized below to the
self-concordant and positive-definite bridge declarations whose owner classes require it. -/

/-- Definition 5.0.24: when the Hessian of `f` at `x` is positive and invertible, the Newton
decrement is the dual local norm of the gradient at `x`. -/
abbrev newtonDecrement (f : E → ℝ) (x : E)
    (hPos : (hessian f x).IsPositive) (hInv : (hessian f x).IsInvertible) : ℝ :=
  ‖(toDual ℝ E) (∇ f x)‖*[f; x | hPos; hInv]

namespace NewtonDecrement

/-- Source-facing notation for the Newton decrement of `f` at `x`. -/
scoped notation:max "λ[" f "; " x " | " hPos "; " hInv "]" =>
  newtonDecrement f x hPos hInv

section CompleteSpaceBridge

variable [CompleteSpace E]

/-- When `f` is self-concordant on `dom` and the Hessian is nondegenerate at `x ∈ dom`, the
Newton decrement is defined using the Hessian positivity canonically supplied by
self-concordance. -/
abbrev ofDetNeZero (Mf : NNReal) (f : E → ℝ) {dom : Set E} {x : E}
    [IsSelfConcordantOnWith dom Mf f] (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) : ℝ :=
  HessianDualLocalNorm.ofDetNeZero f x
    (IsSelfConcordantOnWith.hessian_isPositive_of_mem Mf hx)
    hH ((toDual ℝ E) (∇ f x))

/-- Source-facing notation for the Newton decrement at a self-concordant domain point `x ∈ dom`
with Hessian nondegeneracy witness `hH`. The self-concordance parameter `M_f` remains explicit in
this surface because it is not inferable from the point data alone. -/
scoped notation:max "ndec(" f:arg ", " x:arg ", " Mf:arg ", " hx:arg ", " hH:arg ")" =>
  (fun _ ↦ ofDetNeZero Mf f hx hH) x

/-- The Newton decrement supplied by self-concordance is nonnegative. -/
@[simp] theorem ofDetNeZero_nonneg
    (Mf : NNReal) (f : E → ℝ) {dom : Set E} {x : E}
    [IsSelfConcordantOnWith dom Mf f] (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    0 ≤ ndec(f, x, Mf, hx, hH) := by
  simpa [ofDetNeZero, HessianDualLocalNorm.ofDetNeZero] using
    dualLocalNorm_nonneg f x
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem Mf hx)
      (hessian_isInvertible_of_det_ne_zero hH)
      ((toDual ℝ E) (∇ f x))

/-- The canonical `ω` argument attached to `NewtonDecrement.ofDetNeZero Mf f hx hH`. -/
  abbrev omegaArgOfDetNeZero
    (Mf : NNReal) (f : E → ℝ) {dom : Set E} {x : E}
    [IsSelfConcordantOnWith dom Mf f] (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    Set.Ioi (-1 : ℝ) :=
  selfConcordantOmegaArg Mf (ofDetNeZero Mf f hx hH)
    (neg_one_lt_mf_mul_of_nonneg (ofDetNeZero_nonneg Mf f hx hH))

/-- Coercing `omegaArgOfDetNeZero` back to `ℝ` recovers `M_f λ_f(x)`. -/
@[simp] theorem coe_omegaArgOfDetNeZero
    (Mf : NNReal) (f : E → ℝ) {dom : Set E} {x : E}
    [IsSelfConcordantOnWith dom Mf f] (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    ↑(omegaArgOfDetNeZero Mf f hx hH) = (Mf : ℝ) * ndec(f, x, Mf, hx, hH) := by
  rfl

/-- When `f` has positive-definite Hessian on `dom`, the Newton decrement at `x ∈ dom` uses only
the domain membership witness; Hessian positivity and invertibility are derived canonically from
that owner hypothesis. -/
abbrev ofPosDefMem (f : E → ℝ) (x : E) {dom : Set E}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom) : ℝ :=
  HessianDualLocalNorm.ofPosDefMem f hx ((toDual ℝ E) (∇ f x))

/-- Source-facing notation for the Newton decrement at a domain point `x ∈ dom` in the
positive-definite-Hessian regime. -/
scoped notation:max "λ[" f "; " x " | " hx "]" =>
  ofPosDefMem f x hx

end CompleteSpaceBridge

end NewtonDecrement

open scoped NewtonDecrement

-- Proof sketch: unfold `newtonDecrement` and then expand `dualLocalNorm` at the gradient covector
-- corresponding to `∇ f x` under the Riesz identification.
/-- Expanding `λ[f; x | hPos; hInv]` gives the square root of the inverse-Hessian pairing
of the gradient with itself, i.e. the local dual norm of `∇ f x`. -/
@[simp]
theorem newtonDecrement_def (f : E → ℝ) (x : E) (hPos : (hessian f x).IsPositive)
    (hInv : (hessian f x).IsInvertible) :
    λ[f; x | hPos; hInv] =
      Real.sqrt (inner ℝ (∇ f x) ((hessian f x).inverse (∇ f x))) := by
  simpa [newtonDecrement, InnerProductSpace.toDual_apply_apply] using
    dualLocalNorm_def f x hPos hInv ((toDual ℝ E) (∇ f x))

namespace NewtonDecrement

section CompleteSpaceBridge

variable [CompleteSpace E]

/-- Expanding `NewtonDecrement.ofDetNeZero Mf f hx hH` recovers the inverse-Hessian gradient
pairing formula with the Hessian positivity supplied by self-concordance. -/
@[simp] theorem ofDetNeZero_def (Mf : NNReal) (f : E → ℝ) {dom : Set E} {x : E}
    [IsSelfConcordantOnWith dom Mf f] (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    ndec(f, x, Mf, hx, hH) =
      Real.sqrt (inner ℝ (∇ f x) ((hessian f x).inverse (∇ f x))) := by
  change newtonDecrement f x
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem Mf hx)
      (hessian_isInvertible_of_det_ne_zero hH) =
    Real.sqrt (inner ℝ (∇ f x) ((hessian f x).inverse (∇ f x)))
  exact newtonDecrement_def f x
    (IsSelfConcordantOnWith.hessian_isPositive_of_mem Mf hx)
    (hessian_isInvertible_of_det_ne_zero hH)

/-- Expanding `NewtonDecrement.ofPosDefMem f x hx` recovers the inverse-Hessian gradient pairing
formula with the Hessian witnesses derived from positive definiteness on `dom`. -/
@[simp] theorem ofPosDefMem_def (f : E → ℝ) (x : E) {dom : Set E}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom) :
    λ[f; x | hx] =
      Real.sqrt (inner ℝ (∇ f x) ((hessian f x).inverse (∇ f x))) := by
  simp [ofPosDefMem]

/-- The positive-definite-domain Newton decrement is nonnegative. -/
@[simp] theorem ofPosDefMem_nonneg (f : E → ℝ) (x : E) {dom : Set E}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom) :
    0 ≤ λ[f; x | hx] := by
  rw [ofPosDefMem_def]
  exact Real.sqrt_nonneg _

/-- The canonical `ω` argument attached to `λ[f; x | hx]`. -/
abbrev omegaArgOfPosDefMem
    (Mf : NNReal) (f : E → ℝ) (x : E) {dom : Set E}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom) :
    Set.Ioi (-1 : ℝ) :=
  selfConcordantOmegaArg Mf (λ[f; x | hx])
    (neg_one_lt_mf_mul_of_nonneg (ofPosDefMem_nonneg f x hx))

/-- Coercing `omegaArgOfPosDefMem Mf f x hx` back to `ℝ` recovers `M_f λ_f(x)`. -/
@[simp] theorem coe_omegaArgOfPosDefMem
    (Mf : NNReal) (f : E → ℝ) (x : E) {dom : Set E}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom) :
    ↑(omegaArgOfPosDefMem Mf f x hx) = (Mf : ℝ) * (λ[f; x | hx]) := by
  rfl

/-- The canonical `ω_*` argument attached to `λ[f; x | hx]` under the small-decrement
hypothesis. -/
abbrev omegaStarArgOfPosDefMem
    (Mf : NNReal) (f : E → ℝ) (x : E) {dom : Set E}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom)
    (hlt : ofPosDefMem f x hx < 1 / (Mf : ℝ)) :
    Set.Iio (1 : ℝ) :=
  selfConcordantOmegaStarArg Mf (ofPosDefMem f x hx) (mf_mul_lt_one_of_lt_inv hlt)

/-- Coercing `omegaStarArgOfPosDefMem Mf f x hx hlt` back to `ℝ` recovers `M_f λ_f(x)`. -/
@[simp] theorem coe_omegaStarArgOfPosDefMem
    (Mf : NNReal) (f : E → ℝ) (x : E) {dom : Set E}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom)
    (hlt : ofPosDefMem f x hx < 1 / (Mf : ℝ)) :
    ↑(omegaStarArgOfPosDefMem Mf f x hx hlt) = (Mf : ℝ) * ofPosDefMem f x hx := by
  rfl

end CompleteSpaceBridge

end NewtonDecrement

end
