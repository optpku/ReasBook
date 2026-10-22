/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 6.59 lies in the Chapter 6 composite first-order optimality / linearization-gap
domain.

Sampled owner-style declarations:
- `supportFunction` in `Chap03/Definition_3_9`, the chapter owner for extended-real suprema of
  affine functionals over a feasible set;
- `scaledRestrictedDualFunction` in `Chap06/Definition_6_56`, the Chapter 6 owner pattern for a
  source-facing supremum over a feasible set using the set image as the index surface;
- `ConditionalGradientContraction.linearizedCompositeGap` in `Chap06/Theorem_6_14`, the later
  Chapter 6 source-facing extended-valued owner exposing the same linearization-gap pattern with
  an arbitrary model vector.

Best owner abstraction:
- source-facing: `linearModelTotalVariation`;
- core/canonical: the same source-facing owner, since no earlier chapter owner directly packages
  this composite linearization gap at a feasible point;
- bridge/view: `linearModelTotalVariation_def`.

Primitive data:
- the feasible set `Q : Set E`;
- the smooth term `f` and regularizer `Ψ`;
- the feasible base point `x : Q`.

Derived API:
- the source-facing owner `linearModelTotalVariation`;
- the textbook notation `δ[Q, f, Ψ](x)`;
- the finite real-part bridge `linearModelTotalVariationReal`;
- the defining expansion theorem `linearModelTotalVariation_def`.

Source/core/bridge triage:
- source-facing: the total variation of the linear model at a feasible point;
- core/canonical: the same owner, expressed as an `EReal` supremum over the feasible set;
- bridge/view: `linearModelTotalVariationReal` and the explicit `sSup` expansion below.

This file keeps Definition 6.59 centered on its source-facing owner. The only refinement needed
here is to use the canonical set-image supremum surface instead of subtype-indexed `Set.range`,
which removes unnecessary bookkeeping without changing the mathematics. The real-valued Chapter 6
theorems that consume this quantity should pass through the generic finite-real-part bridge
`linearModelTotalVariationReal` instead of defining parallel real-valued owners.
-/

/-- Definition 6.59: the total variation `δ(x)` of the linear model at a feasible point `x ∈ Q`
is the supremum over feasible points `y ∈ Q` of
`⟪∇ f(x), x - y⟫ + Ψ(x) - Ψ(y)`, recorded in `EReal` so the owner remains faithful even when
the supremum is not bounded above in `ℝ`. In the finite-dimensional setting where this supremum
is finite and attained, this is the textbook maximum. -/
def linearModelTotalVariation (Q : Set E) (f Ψ : E → ℝ) : Q → EReal :=
  fun x ↦
    sSup
      ((fun y : E ↦
          ((inner ℝ (∇ f x) ((x : E) - y) + Ψ x - Ψ y : ℝ) : EReal)) '' Q)

namespace TotalVariationNotation

/- Source-facing Lean notation for the textbook total variation `δ(x)` with ambient feasible set
and objective data fixed by the surrounding context. -/
scoped notation:max "δ[" Q ", " f ", " Ψ "](" x:arg ")" =>
  linearModelTotalVariation Q f Ψ x

end TotalVariationNotation

open scoped TotalVariationNotation

/-- The finite real part of `δ[Q, f, Ψ](x)`. This is the canonical real-valued bridge used by
real-valued Chapter 6 estimates when the `EReal` owner is known to be finite. -/
abbrev linearModelTotalVariationReal (Q : Set E) (f Ψ : E → ℝ) : Q → ℝ :=
  extendedRealRealPart (linearModelTotalVariation Q f Ψ)

-- Proof sketch: unfold `linearModelTotalVariation`.
/-- Expanding `δ[Q, f, Ψ](x)` recovers the defining supremum of the affine
linearization gap over all feasible points `y ∈ Q`. -/
theorem linearModelTotalVariation_def
    (Q : Set E) (f Ψ : E → ℝ) (x : Q) :
    δ[Q, f, Ψ](x) =
      sSup
        ((fun y : E ↦
            ((inner ℝ (∇ f x) ((x : E) - y) + Ψ x - Ψ y : ℝ) : EReal)) '' Q) :=
  rfl

/-- Expanding the real-valued bridge amounts to taking the finite real part of `δ[Q, f, Ψ](x)`.
-/
@[simp] theorem linearModelTotalVariationReal_def
    (Q : Set E) (f Ψ : E → ℝ) (x : Q) :
    linearModelTotalVariationReal Q f Ψ x = (δ[Q, f, Ψ](x)).toReal :=
  rfl

end
