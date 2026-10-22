/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped HessianLocalNorm

universe u

variable {E₁ : Type u}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]

/-
Definition 5.4.6.8 lies in the chapter's Hessian local-norm domain.

Source/core/bridge triage:
* source-facing: `sigmaThree F x h`, the local squared norm `σ₃`
* core/canonical: `hessianLocalNorm` / `‖h‖[F; x]`
* bridge/view: the comparison of `sigmaThree` with the raw Hessian quadratic form via
  `hessianLocalNorm_def` together with `Real.sq_sqrt`

Sampled owner declarations:
* `hessian` in `Chap01/Definition_1_4_16`, the intrinsic Hessian operator owner
* `hessianLocalNorm` in `Chap05/Definition_5_1_1`, the chapter owner for the local norm
* `hessianLocalNorm_def` in `Chap05/Definition_5_1_1`, the canonical owner expansion

Best owner abstraction:
* `hessianLocalNorm`

Primitive data:
* a function `F`
* a base point `x`
* a direction `h`

Derived API:
* the local squared norm `sigmaThree F x h = ‖h‖[F; x]^2`
* the bridge back to `inner ℝ h (hessian F x h)` under the standard nonnegativity hypothesis,
  obtained by squaring `hessianLocalNorm_def`

The source-facing name `sigmaThree` therefore remains, but only as a thin view of the chapter
owner `hessianLocalNorm`, not as a second raw Hessian-level owner. -/

/-- Definition 5.4.6.8: the local squared norm in `\mathbb E_1` is the square of the chapter's
canonical Hessian local norm. -/
abbrev sigmaThree (F : E₁ → ℝ) (x h : E₁) : ℝ :=
  ‖h‖[F; x] ^ (2 : ℕ)

/- Expanding `sigmaThree F x h` gives the square of the canonical Hessian local norm. -/
theorem sigmaThree_def (F : E₁ → ℝ) (x h : E₁) :
    sigmaThree F x h = ‖h‖[F; x] ^ (2 : ℕ) :=
  rfl

/-- The local squared norm `sigmaThree F x h` is always nonnegative. -/
theorem sigmaThree_nonneg (F : E₁ → ℝ) (x h : E₁) :
    0 ≤ sigmaThree F x h :=
  sq_nonneg ‖h‖[F; x]

/-- Taking the square root of the local squared norm recovers the canonical Hessian local norm. -/
@[simp] theorem sqrt_sigmaThree (F : E₁ → ℝ) (x h : E₁) :
    Real.sqrt (sigmaThree F x h) = ‖h‖[F; x] := by
  rw [sigmaThree_def, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  exact hessianLocalNorm_nonneg F x h

/-- Under the standard pointwise nonnegativity hypothesis on the Hessian quadratic form,
`sigmaThree F x h` agrees with that quadratic form. -/
theorem sigmaThree_eq_inner_hessian
    (F : E₁ → ℝ) (x h : E₁) (hh : 0 ≤ inner ℝ h (hessian F x h)) :
    sigmaThree F x h = inner ℝ h (hessian F x h) := by
  simpa [sigmaThree, hessianLocalNorm_def] using Real.sq_sqrt hh

end
