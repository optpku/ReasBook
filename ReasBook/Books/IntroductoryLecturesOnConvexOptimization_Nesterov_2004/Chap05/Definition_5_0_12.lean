/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u

/- Definition 5.0.12 lies in the self-concordant local-norm / directional-slice domain.

Sampled owner declarations:
* `hessianLocalNorm` in `Definition_5_1_1`, the chapter owner for the Hessian-induced local norm;
* the notation `‖u‖[f; x]`, the source-facing surface for that owner;
* `hessianLocalNorm_def`, the bridge from the owner to the square root of the Hessian quadratic
  form;
* `directionalSlice` in `Definition_5_0_10`, the chapter's source-facing owner for restricting a
  function to an affine line;
* `Set.restrict`, the canonical mathlib owner for viewing an ambient function on a subtype domain.

Source/core/bridge triage:
* source-facing: the associated univariate reciprocal local-norm function along the line
  `t ↦ x + t • h`;
* core/canonical: the Hessian local norm `‖h‖[f; x + t • h]`;
* bridge/view: the expansion of that local norm as
  `Real.sqrt (inner ℝ h ((fderiv ℝ (∇ f) (x + t • h)) h))`.

Primitive data:
* a domain `dom`;
* a function `f`;
* a base point `x`;
* a direction `h`.

Derived API:
* the natural parameter set where the shifted point stays in `dom` and the local norm is
  positive;
* the reciprocal local-norm function as the canonical restriction of the ambient slice
  `t ↦ 1 / ‖h‖[f; x + t • h]` to that parameter set;
* companion theorems expanding the owner-level statements to the textbook Hessian formula.

This file therefore keeps the associated univariate function as the source-facing owner, but it is
implemented by the canonical restriction owner `Set.restrict` rather than by a bespoke subtype
lambda. The core owner is the chapter local norm `hessianLocalNorm`, and the raw square-root
formula is kept only as bridge API.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The natural parameter domain of the associated univariate function along the line
`t ↦ x + t • h`. -/
def associatedUnivariateFunctionDomain (dom : Set E) (f : E → ℝ) (x h : E) : Set ℝ :=
  {t | x + t • h ∈ dom ∧ 0 < ‖h‖[f; x + t • h]}

/-- Membership in `associatedUnivariateFunctionDomain dom f x h` means that the shifted point
`x + t • h` lies in `dom` and the Hessian local norm of `h` there is strictly positive. -/
theorem mem_associatedUnivariateFunctionDomain_iff
    (dom : Set E) (f : E → ℝ) (x h : E) (t : ℝ) :
    t ∈ associatedUnivariateFunctionDomain dom f x h ↔
      x + t • h ∈ dom ∧ 0 < ‖h‖[f; x + t • h] :=
  Iff.rfl

/-- Expanding membership in `associatedUnivariateFunctionDomain dom f x h` recovers the textbook
positivity condition on the Hessian quadratic form in the direction `h`. -/
theorem mem_associatedUnivariateFunctionDomain_iff_hessian
    (dom : Set E) (f : E → ℝ) (x h : E) (t : ℝ) :
    t ∈ associatedUnivariateFunctionDomain dom f x h ↔
      x + t • h ∈ dom ∧ 0 < inner ℝ h ((fderiv ℝ (∇ f) (x + t • h)) h) := by
  simp [mem_associatedUnivariateFunctionDomain_iff, hessianLocalNorm_def, hessian, Real.sqrt_pos]

/-- Definition 5.0.12: the associated univariate function is the reciprocal of the square root of
the Hessian quadratic form of `f` in the direction `h`, along the line `t ↦ x + t • h`, with
domain consisting of those `t` for which `x + t • h ∈ dom` and the quadratic form is positive. -/
def associatedUnivariateFunction (dom : Set E) (f : E → ℝ) (x h : E) :
    associatedUnivariateFunctionDomain dom f x h → ℝ :=
  (associatedUnivariateFunctionDomain dom f x h).restrict
    (directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h)

/-- Evaluating the associated univariate function gives the reciprocal of the Hessian local norm
of `h` along the line `t ↦ x + t • h`. -/
@[simp] theorem associatedUnivariateFunction_apply
    (dom : Set E) (f : E → ℝ) (x h : E)
    (t : associatedUnivariateFunctionDomain dom f x h) :
    associatedUnivariateFunction dom f x h t = 1 / ‖h‖[f; x + (t : ℝ) • h] :=
  rfl

/-- Expanding `associatedUnivariateFunction dom f x h t` recovers the textbook formula
`1 / ⟨∇² f (x + t h) h, h⟩^(1/2)`. -/
theorem associatedUnivariateFunction_apply_eq_inv_sqrt_hessian
    (dom : Set E) (f : E → ℝ) (x h : E)
    (t : associatedUnivariateFunctionDomain dom f x h) :
    associatedUnivariateFunction dom f x h t =
      1 / Real.sqrt (inner ℝ h ((fderiv ℝ (∇ f) (x + (t : ℝ) • h)) h)) := by
  simp [associatedUnivariateFunction, hessianLocalNorm_def, hessian]

/-- If `x ∈ dom` and the Hessian quadratic form of `f` at `x` is positive along `h`, then `0`
belongs to the natural domain of the associated univariate function. -/
theorem zero_mem_associatedUnivariateFunctionDomain
    {dom : Set E} {f : E → ℝ} {x h : E}
    (hx : x ∈ dom)
    (hh : 0 < inner ℝ h ((fderiv ℝ (∇ f) x) h)) :
    (0 : ℝ) ∈ associatedUnivariateFunctionDomain dom f x h := by
  exact
    (mem_associatedUnivariateFunctionDomain_iff_hessian dom f x h 0).2
      ⟨by simpa, by simpa⟩

end
