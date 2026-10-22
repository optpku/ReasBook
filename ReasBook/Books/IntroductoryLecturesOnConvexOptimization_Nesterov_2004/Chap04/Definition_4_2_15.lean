/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Definition 4.2.15 lies in the unconstrained first-order geometry domain for smooth minimization.

Sampled owner-style declarations:
* mathlib `IsMinOn` and `isMinOn_univ_iff` in `Order/Filter/Extr`, the canonical owner of the
  chosen global-minimizer condition;
* mathlib `HasGradientAt` and `DifferentiableAt.hasGradientAt` in
  `Analysis/Calculus/Gradient/Basic`, the canonical first-order owner and the bridge from
  differentiability to the canonical gradient vector `∇ f x`;
* mathlib `HasGradientAt.gradient` in `Analysis/Calculus/Gradient/Basic`, which identifies the
  totalized gradient with an explicit gradient witness once first-order regularity is known;
* project `Definition_4_2_2`, which already fixes `HasGradientAt` as the chapter owner for
  first-order gradient data.

Best owner abstraction:
* source-facing: `IsFirstOrderNondegenerate f xStar`;
* core/canonical: `IsMinOn f Set.univ xStar` together with `HasGradientAt f (∇ f x) x` away from
  `xStar`;
* bridge/view: the companion theorem `firstOrderNondegeneracyCoefficient_def`.

Primitive data:
* the objective `f`;
* the chosen optimizer `xStar`;
* the global optimality witness `IsMinOn f Set.univ xStar`;
* first-order regularity away from `xStar`, recorded primitively as `DifferentiableAt ℝ f x`;
* a positive scalar `τ` uniformly bounding the coefficient away from `xStar`.

Derived API:
* the explicit textbook formula for the coefficient;
* the canonical gradient witness `HasGradientAt f (∇ f x) x` away from `xStar`;
* the pointwise lower-bound consequences of an admissible coefficient threshold.

This file is therefore an owner file, not a recall file. The refinement target is to keep the
source-facing owner while deleting derived packaging that does not add mathematical content. -/

/-- The cosine-type coefficient comparing the gradient at `x` with the displacement `x - xStar`
toward a chosen optimizer `xStar`. In a Hilbert space, the dual norm of the gradient is
identified with the ordinary norm. -/
def firstOrderNondegeneracyCoefficient
    (f : E → ℝ) (xStar x : E) : ℝ :=
  inner ℝ (∇ f x) (x - xStar) / (‖∇ f x‖ * ‖x - xStar‖)

-- Proof sketch: unfold `firstOrderNondegeneracyCoefficient`.
/-- Expanding `firstOrderNondegeneracyCoefficient f xStar x` recovers the textbook formula for the
coefficient `α(x)`. -/
theorem firstOrderNondegeneracyCoefficient_def
    (f : E → ℝ) (xStar x : E) :
    firstOrderNondegeneracyCoefficient f xStar x =
      inner ℝ (∇ f x) (x - xStar) / (‖∇ f x‖ * ‖x - xStar‖) :=
  rfl

/-- A scalar `τ` is a first-order nondegeneracy lower bound for `f` at `xStar` when it is
positive and uniformly bounds the normalized gradient/displacement coefficient away from the
optimizer. -/
def IsFirstOrderNondegeneracyLowerBound
    (f : E → ℝ) (xStar : E) (τ : ℝ) : Prop :=
  0 < τ ∧
    ∀ ⦃x : E⦄, x ≠ xStar →
      τ ≤ firstOrderNondegeneracyCoefficient f xStar x

namespace IsFirstOrderNondegeneracyLowerBound

variable {f : E → ℝ} {xStar : E} {τ : ℝ}

/-- Every first-order nondegeneracy lower bound is positive. -/
theorem pos (hτ : IsFirstOrderNondegeneracyLowerBound f xStar τ) : 0 < τ :=
  hτ.1

/-- A first-order nondegeneracy lower bound bounds the coefficient at each point away from the
optimizer. -/
theorem le_coefficient
    (hτ : IsFirstOrderNondegeneracyLowerBound f xStar τ) {x : E} (hx : x ≠ xStar) :
    τ ≤ firstOrderNondegeneracyCoefficient f xStar x :=
  hτ.2 hx

end IsFirstOrderNondegeneracyLowerBound

/-- Definition 4.2.15: an unconstrained objective is first-order non-degenerate relative to a
chosen optimal solution `xStar` if `xStar` globally minimizes `f` and the coefficient
`α(x) = ⟪∇ f(x), x - xStar⟫ / (‖∇ f(x)‖ * ‖x - xStar‖)` admits a uniform positive lower bound for
every `x ≠ xStar`. The first-order interpretation of `∇ f(x)` is part of the owner data: away
from `xStar`, `f` is differentiable so the canonical gradient `∇ f x` is the actual gradient. -/
class IsFirstOrderNondegenerate
    (f : E → ℝ) (xStar : E) : Prop where
  /-- The reference point `xStar` is a global minimizer of `f`. -/
  isMinOn : IsMinOn f Set.univ xStar
  /-- Away from the optimizer, `f` is differentiable, hence its canonical gradient is well-defined
  in the first-order sense. -/
  differentiableAt {x : E} (_hx : x ≠ xStar) : DifferentiableAt ℝ f x
  /-- The cosine coefficient has a uniform positive lower bound away from the optimizer. -/
  lowerBound :
    ∃ τ : ℝ, IsFirstOrderNondegeneracyLowerBound f xStar τ

/-- A first-order nondegeneracy hypothesis canonically supplies the global-minimizer fact for the
chosen optimizer `xStar`. -/
instance {f : E → ℝ} {xStar : E} [hf : IsFirstOrderNondegenerate f xStar] :
    Fact (IsMinOn f Set.univ xStar) where
  out := hf.isMinOn

namespace IsFirstOrderNondegenerate

variable {f : E → ℝ} {xStar : E}

/-- Away from the optimizer, the canonical gradient vector `∇ f x` is the actual gradient of
`f` at `x`. -/
theorem hasGradientAt
    (hf : IsFirstOrderNondegenerate f xStar) {x : E} (hx : x ≠ xStar) :
    HasGradientAt f (∇ f x) x :=
  (hf.differentiableAt hx).hasGradientAt

end IsFirstOrderNondegenerate
