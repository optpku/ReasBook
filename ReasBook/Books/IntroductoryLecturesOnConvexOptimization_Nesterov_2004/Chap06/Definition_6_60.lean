/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Algorithm_6_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_59

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient TotalVariationNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 6.60 lies in the Chapter 6 contracted conditional-gradient / total-variation
domain.

Sampled owner-style declarations:
- `contractedFeasibleSet` in `Algorithm_6_5`, the chapter owner for the contracted feasible set
  `{(1 - τ) x + τ u | u ∈ Q}`;
- `linearModelTotalVariation` in `Definition_6_59`, the source-facing `EReal` owner for the total
  variation of the linear model at a feasible point;
- `linearModelTotalVariationReal` in `Definition_6_59`, the downstream finite-real-part bridge for
  real-valued estimates;
- `ConditionalGradientContraction.linearizedCompositeGap` in `Theorem_6_14`, the more general
  Chapter 6 extended-valued chosen-dual gap owner for the same contracted affine pattern.

Best owner abstraction:
- source-facing: `contractedLinearModelTotalVariation`;
- core/canonical: `linearModelTotalVariation (contractedFeasibleSet Q x τ) f Ψ`, evaluated at the
  canonical center point `x` of the contracted feasible set;
- bridge/view: the explicit expansion theorem below, and any later real-valued use should pass
  through the finite-real-part bridge rather than redefining a parallel owner.

Primitive data:
- the feasible set `Q : Set E`;
- the smooth term `f` and regularizer `Ψ`;
- the contraction factor `τ : ℝ`;
- the feasible base point `x : Q`.

Derived API:
- the source-facing owner `contractedLinearModelTotalVariation`;
- the textbook Lean notation for `δ_τ(x)`;
- the defining `EReal`-valued supremum expansion over `u ∈ Q`.

Source/core/bridge triage:
- source-facing: the contracted total variation of the linear model at `x`;
- core/canonical: `linearModelTotalVariation` on the contracted feasible set centered at `x`;
- bridge/view: the image-expansion theorem rewriting the contracted feasible-set supremum back to
  the textbook `u ∈ Q` parametrization.

This refinement keeps Definition 6.60 on the same `EReal`-valued owner family as
Definition 6.59. The previous collapse onto the ambient chosen-dual gap owner is removed:
the proof that `x` lies in its contracted feasible set stays internal, and only the source-facing
contracted specialization remains public here. Since the owner is just the total variation on
`contractedFeasibleSet Q x τ`, the contraction bounds `0 ≤ τ ≤ 1` belong in later results that
use them, not in this defining owner itself.
-/

/-- Definition 6.60: the contracted total variation `δ_τ(x)` of the linear model at a feasible
point `x ∈ Q` is the total variation from Definition 6.59, specialized to the contracted feasible
set centered at `x`. It is therefore `EReal`-valued, remaining faithful even when the contracted
supremum is not bounded above in `ℝ`. -/
def contractedLinearModelTotalVariation
    (Q : Set E) (f Ψ : E → ℝ) (τ : ℝ) : Q → EReal :=
  fun x ↦
    linearModelTotalVariation
      (contractedFeasibleSet Q (x : E) τ) f Ψ
      ⟨x, by
        refine ⟨(x : E), x.property, ?_⟩
        simp⟩

namespace TotalVariationNotation

/- Source-facing Lean notation for the textbook contracted total variation `δ_τ(x)` with the
ambient feasible set and objective data fixed by the surrounding context. -/
scoped notation:max "δ_[" τ "; " Q ", " f ", " Ψ "](" x:arg ")" =>
  contractedLinearModelTotalVariation Q f Ψ τ x

end TotalVariationNotation

/-- Expanding `δ_[τ; Q, f, Ψ](x)` recovers the defining `EReal` supremum of the contracted affine
linearization gap over feasible points `u ∈ Q`. -/
theorem contractedLinearModelTotalVariation_def
    (Q : Set E) (f Ψ : E → ℝ) (τ : ℝ) (x : Q) :
    δ_[τ; Q, f, Ψ](x) =
      sSup
        ((fun u : E ↦
            ((inner ℝ (∇ f x) ((x : E) - ((1 - τ) • (x : E) + τ • u)) +
                Ψ x - Ψ ((1 - τ) • (x : E) + τ • u) : ℝ) : EReal)) '' Q) := by
  rw [contractedLinearModelTotalVariation, linearModelTotalVariation_def]
  refine congrArg sSup ?_
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨u, huQ, rfl⟩
    refine ⟨u, huQ, ?_⟩
    simp [AffineMap.lineMap_apply_module]
  · rintro ⟨u, huQ, rfl⟩
    refine ⟨AffineMap.lineMap (x : E) u τ, ?_, ?_⟩
    · exact ⟨u, huQ, rfl⟩
    · simp [AffineMap.lineMap_apply_module]

end
