/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_9_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u}

/- Definition 5.4.9.8 lies in the Chapter 5 second-order product-calculus / Hessian-block domain.

Sampled owner declarations:
- `hessian` in `Chap01/Definition_1_4_16`, the project owner for second derivatives of
  real-valued functions on real inner-product spaces;
- `auxiliaryGradient` and `auxiliaryTimeDerivative` in `Definition_5_4_9_7`, the immediate
  Chapter 5 source-facing owners for the frozen-slice first derivatives;
- `gradient` in `Mathlib/Analysis/Calculus/Gradient/Basic`, the mathlib owner behind
  `auxiliaryGradient`;
- `deriv` in `Mathlib/Analysis/Calculus/Deriv/Basic`, the canonical owner for the one-variable
  second-order slices.

Best owner abstraction:
- source-facing: the textbook block functions `h₁₁(y, t)`, `h₁₂(y, t)`, and `h₂₂(y, t)`;
- core/canonical: `hessian (fun y' ↦ f (y', t)) y` for the `yy` block, together with `deriv` on
  the frozen one-variable slices for the mixed and scalar blocks;
- bridge/view: the expansion lemmas rewriting these source-facing names to the raw derivative
  formulas built from `auxiliaryGradient` and `auxiliaryTimeDerivative`.

Primitive data:
- the scalar-valued product-space function `f : E × ℝ → ℝ`.

Derived API:
- `secondOrderDerivativeBlock11 f y t`;
- `secondOrderDerivativeBlock12 f y t`;
- `secondOrderDerivativeBlock22 f y t`;
- the textbook notation `h₁₁[f](y, t)`, `h₁₂[f](y, t)`, `h₂₂[f](y, t)`;
- the corresponding `_def` expansion lemmas.

The previous file kept the `yy` block at the lower raw `fderiv`-of-gradient level and carried an
unused finite-dimensionality hypothesis. This refinement keeps the textbook block owners, routes
the `yy` block through the existing Chapter 1 Hessian owner, keeps the mixed block on the sliced
gradient owner, and lets the scalar `tt` block live at the weaker sliced-`deriv` layer where it
belongs. The source-facing theorem surface now uses the textbook block notation instead of leaking
the long raw owner names into immediate downstream statements. -/

section GradientBlocks

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Definition 5.4.9.8: assuming `f` is twice differentiable, `secondOrderDerivativeBlock11 f y t`
is the `yy`-block `h₁₁(y, t) = ∇²_{yy} f(y, t)` of the second derivative of `f`. -/
abbrev secondOrderDerivativeBlock11 (f : E × ℝ → ℝ) (y : E) (t : ℝ) : E →L[ℝ] E :=
  hessian (fun y' ↦ f (y', t)) y

/-- The mixed second-order block `h₁₂(y, t) = ∇²_{yt} f(y, t)`. -/
abbrev secondOrderDerivativeBlock12 (f : E × ℝ → ℝ) (y : E) (t : ℝ) : E :=
  deriv (fun t' ↦ auxiliaryGradient f y t') t

end GradientBlocks

section TimeBlock

/-- The scalar second-order block `h₂₂(y, t) = ∂²_{tt} f(y, t)`. -/
abbrev secondOrderDerivativeBlock22 (f : E × ℝ → ℝ) (y : E) (t : ℝ) : ℝ :=
  deriv (fun t' ↦ auxiliaryTimeDerivative f y t') t

end TimeBlock

namespace SecondOrderDerivativeBlocks

scoped notation:max "h₁₁[" f:arg "](" y:arg ", " t:arg ")" => secondOrderDerivativeBlock11 f y t
scoped notation:max "h₁₂[" f:arg "](" y:arg ", " t:arg ")" => secondOrderDerivativeBlock12 f y t
scoped notation:max "h₂₂[" f:arg "](" y:arg ", " t:arg ")" => secondOrderDerivativeBlock22 f y t

end SecondOrderDerivativeBlocks

open scoped SecondOrderDerivativeBlocks

section GradientBlockLemmas

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Expanding `h₁₁[f](y, t)` recovers the `yy`-block of the second derivative as the derivative
of the first auxiliary derivative with `t` fixed. -/
@[simp] theorem secondOrderDerivativeBlock11_def (f : E × ℝ → ℝ) (y : E) (t : ℝ) :
    h₁₁[f](y, t) =
      fderiv ℝ (fun y' ↦ auxiliaryGradient f y' t) y :=
  rfl

/-- Expanding `h₁₂[f](y, t)` recovers the mixed `yt`-block as the derivative in `t` of the first
auxiliary derivative with `y` fixed. -/
@[simp] theorem secondOrderDerivativeBlock12_def (f : E × ℝ → ℝ) (y : E) (t : ℝ) :
    h₁₂[f](y, t) =
      deriv (fun t' ↦ auxiliaryGradient f y t') t :=
  rfl

end GradientBlockLemmas

section TimeBlockLemmas

/-- Expanding `h₂₂[f](y, t)` recovers the scalar `tt`-block as the second ordinary derivative of
the second auxiliary derivative of the frozen-`y` slice. -/
@[simp] theorem secondOrderDerivativeBlock22_def (f : E × ℝ → ℝ) (y : E) (t : ℝ) :
    h₂₂[f](y, t) =
      deriv (fun t' ↦ auxiliaryTimeDerivative f y t') t :=
  rfl

end TimeBlockLemmas
