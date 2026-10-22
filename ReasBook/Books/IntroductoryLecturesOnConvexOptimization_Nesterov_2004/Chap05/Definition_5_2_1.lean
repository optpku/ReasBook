/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_7_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_24

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open NewtonDecrement

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Definition 5.2.1 lies in the Chapter 5 self-concordant Newton-iteration domain.

Sampled owner declarations:
* `NewtonDecrement.ofDetNeZero` in `Definition_5_0_24`, the chapter owner for the Newton
  decrement on a self-concordant domain;
* `DampedNewton.step` in Chapter 1, the canonical one-step Newton-update owner;
* `DampedNewton.Method` in Chapter 1, the recursive damped-Newton owner on the Hessian-
  nondegenerate admissible domain.

Best owner abstraction:
* source-facing: the variant-dependent step-size rule and the self-concordant Newton method on
  `dom`;
* core/canonical: `DampedNewton.step`, `DampedNewton.Method`,
  `DampedNewton.Method.IsSelfConcordant`, and `NewtonDecrement.ofDetNeZero`;
* bridge/view: the explicit inverse-Hessian update formula recovered from
  `DampedNewton.step_def`.

Primitive data:
* the Chapter 1 damped-Newton method in the admissible Hessian-nondegenerate domain.

Derived API:
* membership of its iterates in `dom`;
* the fact that its step-size schedule is the self-concordant one prescribed by the chosen
  variant;
* the canonical one-step update `selfConcordantNewtonNextPoint f Mf variant x hx hH`;
* iterate-wise Hessian nondegeneracy, inherited from `DampedNewton.Method`;
* the self-concordant recursion `xₖ₊₁ = selfConcordantNewtonNextPoint ...`.

This file keeps the source-facing Chapter 5 method as a property of the canonical Chapter 1 owner
`DampedNewton.Method`, rather than duplicating that method structure with extra
proof-bookkeeping fields. -/

/-- The three damping choices used in the local-convergence variants of Newton's method. -/
inductive SelfConcordantNewtonVariant
  /-- The standard Newton method with no damping shift. -/
  | standard
  /-- The damped Newton method with shift `M_f λ`. -/
  | damped
  /-- The intermediate Newton method with shift `M_f^2 λ^2 / (1 + M_f λ)`. -/
  | intermediate
deriving DecidableEq

/-- The damping shift `ξ` attached to a Newton variant for self-concordance parameter `M_f` and
Newton decrement `λ`. -/
def selfConcordantNewtonShift
    (variant : SelfConcordantNewtonVariant) (Mf : NNReal) (decrement : ℝ) : ℝ :=
  match variant with
  | .standard => 0
  | .damped => (Mf : ℝ) * decrement
  | .intermediate =>
      ((Mf : ℝ) ^ (2 : ℕ) * decrement ^ (2 : ℕ)) / (1 + (Mf : ℝ) * decrement)

/-- The self-concordant Newton step size attached to `variant` at `x`. -/
def selfConcordantNewtonStepSize
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) [IsSelfConcordantOnWith dom Mf f]
    (variant : SelfConcordantNewtonVariant) (x : E) (hx : x ∈ dom)
    (hH : (hessian f x).det ≠ 0) : ℝ :=
  1 / (1 + selfConcordantNewtonShift variant Mf (ofDetNeZero Mf f hx hH))

theorem selfConcordantNewtonShift_nonneg
    (variant : SelfConcordantNewtonVariant) (Mf : NNReal) {decrement : ℝ}
    (hdecrement : 0 ≤ decrement) :
    0 ≤ selfConcordantNewtonShift variant Mf decrement := by
  have hMf : 0 ≤ (Mf : ℝ) := Mf.2
  cases variant with
  | standard =>
      simp [selfConcordantNewtonShift]
  | damped =>
      simpa [selfConcordantNewtonShift] using mul_nonneg hMf hdecrement
  | intermediate =>
      have hnum : 0 ≤ (Mf : ℝ) ^ (2 : ℕ) * decrement ^ (2 : ℕ) := by positivity
      have hden : 0 ≤ 1 + (Mf : ℝ) * decrement := by
        nlinarith [mul_nonneg hMf hdecrement]
      exact div_nonneg hnum hden

/-- The self-concordant Newton step size is always positive. -/
theorem selfConcordantNewtonStepSize_pos
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) [IsSelfConcordantOnWith dom Mf f]
    (variant : SelfConcordantNewtonVariant) (x : E) (hx : x ∈ dom)
    (hH : (hessian f x).det ≠ 0) :
    0 < selfConcordantNewtonStepSize f Mf variant x hx hH := by
  have hshift :
      0 ≤
        selfConcordantNewtonShift variant Mf
          (ofDetNeZero Mf f hx hH) :=
    selfConcordantNewtonShift_nonneg variant Mf
      (ofDetNeZero_nonneg Mf f hx hH)
  have hdenom :
      0 <
        1 + selfConcordantNewtonShift variant Mf
          (ofDetNeZero Mf f hx hH) := by
    linarith
  simpa [selfConcordantNewtonStepSize] using one_div_pos.mpr hdenom

/-- The one-step self-concordant Newton update of variant `variant` from the point `x`. -/
def selfConcordantNewtonNextPoint
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) [IsSelfConcordantOnWith dom Mf f]
    (variant : SelfConcordantNewtonVariant) (x : E) (hx : x ∈ dom)
    (hH : (hessian f x).det ≠ 0) : E :=
  DampedNewton.step f ⟨x, hH⟩
    (selfConcordantNewtonStepSize f Mf variant x hx hH)

-- Proof sketch: unfold `selfConcordantNewtonNextPoint`; this is exactly the update formula from
-- Definition 5.2.1 with the variant-dependent shift `ξ = selfConcordantNewtonShift variant Mf
-- λ_f(x)`.
/-- Expanding `selfConcordantNewtonNextPoint f Mf variant x hx hH` gives the textbook one-step
self-concordant Newton update
`x - (1 + ξ)⁻¹ [∇² f(x)]⁻¹ ∇ f(x)`. -/
@[simp]
theorem selfConcordantNewtonNextPoint_def
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) [IsSelfConcordantOnWith dom Mf f]
    (variant : SelfConcordantNewtonVariant) (x : E) (hx : x ∈ dom)
    (hH : (hessian f x).det ≠ 0) :
    selfConcordantNewtonNextPoint f Mf variant x hx hH =
      x -
        (1 /
          (1 + selfConcordantNewtonShift variant Mf
            (ofDetNeZero Mf f hx hH))) •
          (hessian f x).inverse (∇ f x) := by
  have happly :
      (hessian f x).inverse (∇ f x) =
        ((hessian f x).toContinuousLinearEquivOfDetNeZero hH).symm (∇ f x) := by
    simpa using
      congrArg (fun T : E →L[ℝ] E ↦ T (∇ f x))
        (ContinuousLinearMap.inverse_equiv
          ((hessian f x).toContinuousLinearEquivOfDetNeZero hH))
  rw [selfConcordantNewtonNextPoint, DampedNewton.step_def]
  simp [selfConcordantNewtonStepSize, happly, hessian]

/-- Definition 5.2.1: a self-concordant Newton method of variant `variant` for `f` on `dom`
with parameter `M_f` is a Chapter 1 damped Newton method whose iterates stay in `dom` and whose
step-size schedule is the canonical self-concordant one
`(1 + ξ_k)⁻¹`, where
(A) `ξ_k = 0` for the standard Newton method,
(B) `ξ_k = M_f λ_f(x_k)` for the damped Newton method,
(C) `ξ_k = M_f^2 λ_f(x_k)^2 / (1 + M_f λ_f(x_k))` for the intermediate Newton method. -/
structure DampedNewton.Method.IsSelfConcordant
    (dom : Set E) {f : E → ℝ} (Mf : NNReal) [IsSelfConcordantOnWith dom Mf f]
    (variant : SelfConcordantNewtonVariant) {x0 : E} (method : DampedNewton.Method f x0) :
    Prop where
  /-- Every iterate belongs to `dom`. -/
  iterates_mem : ∀ k : ℕ, method k ∈ dom
  /-- The Chapter 1 damping factors are exactly the canonical self-concordant step sizes from
  Definition 5.2.1. -/
  stepSize_eq : ∀ k : ℕ,
    method.stepSize k =
      selfConcordantNewtonStepSize f Mf variant (method k) (iterates_mem k)
        (method.hessian_nondegenerate k)

namespace DampedNewton.Method.IsSelfConcordant

/-- The Newton decrement of a self-concordant Newton method at step `k`. -/
def decrement
    {dom : Set E} {f : E → ℝ} {Mf : NNReal}
    [IsSelfConcordantOnWith dom Mf f] {variant : SelfConcordantNewtonVariant} {x0 : E}
    {method : DampedNewton.Method f x0}
    (hmethod : method.IsSelfConcordant dom Mf variant) (k : ℕ) : ℝ :=
  NewtonDecrement.ofDetNeZero Mf f (hmethod.iterates_mem k)
    (method.hessian_nondegenerate k)

/-- Expanding `hmethod.decrement k` recovers the canonical Newton decrement of the `k`th
self-concordant iterate. -/
@[simp] theorem decrement_def
    {dom : Set E} {f : E → ℝ} {Mf : NNReal}
    [IsSelfConcordantOnWith dom Mf f] {variant : SelfConcordantNewtonVariant} {x0 : E}
    {method : DampedNewton.Method f x0}
    (hmethod : method.IsSelfConcordant dom Mf variant) (k : ℕ) :
    hmethod.decrement k =
      NewtonDecrement.ofDetNeZero Mf f (hmethod.iterates_mem k)
        (method.hessian_nondegenerate k) :=
  rfl

/-- Each successor iterate of a self-concordant Newton method is the canonical self-concordant
Newton update of the previous one. -/
theorem succ_eq_nextPoint
    {dom : Set E} {f : E → ℝ} {Mf : NNReal}
    [IsSelfConcordantOnWith dom Mf f] {variant : SelfConcordantNewtonVariant} {x0 : E}
    {method : DampedNewton.Method f x0}
    (hmethod : method.IsSelfConcordant dom Mf variant) (k : ℕ) :
    method (k + 1) =
      selfConcordantNewtonNextPoint f Mf variant (method k) (hmethod.iterates_mem k)
        (method.hessian_nondegenerate k) := by
  have hx :
      (⟨method k, method.hessian_nondegenerate k⟩ : NewtonSystem.AdmissiblePoint (∇ f)) =
        method.x k := by
    ext
    rfl
  rw [selfConcordantNewtonNextPoint]
  simpa [hx, hmethod.stepSize_eq k] using method.step_eq k

end DampedNewton.Method.IsSelfConcordant

end
