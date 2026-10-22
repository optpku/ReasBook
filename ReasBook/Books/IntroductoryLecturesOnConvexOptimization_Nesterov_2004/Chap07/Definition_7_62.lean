/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/-- Definition 7.62: for a strictly positive function `ψ`, its logarithmic transform is
the function `x ↦ ln (ψ x)`. Since `Real.log` is total in mathlib, the owner is the primitive
pointwise map `Real.log ∘ ψ`; positivity remains a source-level hypothesis when needed. -/
def logarithmicTransform {X : Type u} (ψ : X → ℝ) : X → ℝ :=
  Real.log ∘ ψ

/-- The logarithmic transform is exactly composition of `ψ` with the real logarithm. -/
theorem logarithmicTransform_def {X : Type u} (ψ : X → ℝ) :
    logarithmicTransform ψ = Real.log ∘ ψ :=
  rfl

/-- The logarithmic transform is computed pointwise by taking the real logarithm of `ψ`. -/
@[simp] theorem logarithmicTransform_apply {X : Type u} (ψ : X → ℝ) (x : X) :
    logarithmicTransform ψ x = Real.log (ψ x) :=
  rfl
