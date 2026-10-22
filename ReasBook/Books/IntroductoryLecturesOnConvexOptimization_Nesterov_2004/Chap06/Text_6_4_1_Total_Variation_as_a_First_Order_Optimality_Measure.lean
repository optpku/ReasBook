/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_59

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient TotalVariationNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 6.4.1 lies in the Chapter 6 composite first-order optimality / total-variation domain.

Sampled owner-style declarations:
- `linearModelTotalVariation` in `Definition_6_59`, the Chapter 6 owner of the total variation at
  a feasible point `x : Q`, with source-facing notation `δ[Q, f, Ψ](x)` and values faithfully in
  `EReal`;
- `linearModelTotalVariation_def` in `Definition_6_59`, the direct bridge from that owner to its
  defining supremum over feasible comparison points;
- `ConvexOn.lower_tangent_plane_of_hasGradientWithinAt` in `Chap02/Definition_2_2`, the canonical
  first-order lower-support inequality for a convex function on a feasible set;
- mathlib `IsMinOn`, the canonical owner of constrained minimality.

Best owner abstraction:
- source-facing: Text 6.4.1 itself, comparing the Chapter 6 total variation at a feasible point
  with the composite-objective gap to a minimizer;
- core/canonical: `δ[Q, f, Ψ](x)`;
- bridge/view: the explicit `sSup` expansion `linearModelTotalVariation_def`.

Primitive data:
- the feasible set `Q`, the smooth term `f`, the regularizer `Ψ`, the feasible base point
  `x : Q`, and the feasible minimizer `xStar : Q`;
- convexity of `f` on `Q`;
- a within-set gradient witness for `f` at `x`.

Derived API:
- the expansion theorem `linearModelTotalVariation_def`;
- the lower-tangent inequality from convexity;
- the nonnegativity of the composite-objective gap coming from `IsMinOn` on the feasible subtype.

This refinement keeps the source-facing theorem directly on the Chapter 6 total-variation owner,
instead of restating it through the raw linearized-gap bridge expression. The upstream owner in
`Definition_6_59` is now the faithful `EReal` supremum, so this source-facing theorem no
longer needs an ad hoc public boundedness hypothesis just to justify `sSup`.
-/

section

variable {Q : Set E} {f Ψ : E → ℝ}

local notation:max "δ(" x:arg ")" => δ[Q, f, Ψ](x)

-- Proof sketch: evaluate the total-variation supremum at the feasible minimizer `xStar`. The
-- convex lower-tangent inequality at `x` gives
-- `(f x + Ψ x) - (f xStar + Ψ xStar) ≤ ⟪∇ f x, x - xStar⟫ + Ψ x - Ψ xStar`, and the explicit
-- feasible comparison point `xStar` gives a member of the defining supremum set, so the faithful
-- `EReal` owner allows a direct `le_sSup` step.
/-- Text 6 4 1 Total Variation as a First Order Optimality Measure: the Chapter 6 total variation
at a feasible point `x` bounds the
composite-objective gap to any feasible minimizer `xStar`, and that gap is nonnegative. -/
theorem totalVariation_ge_compositeObjective_gap_and_nonneg
    (hf_conv : ConvexOn ℝ Q f) (x xStar : Q)
    (hf_grad : HasGradientWithinAt f (∇ f x) Q x)
    (hxMin : IsMinOn (fun y : Q ↦ f y + Ψ y) Set.univ xStar) :
    δ(x) ≥ (f x + Ψ x) - (f xStar + Ψ xStar) ∧
      0 ≤ (f x + Ψ x) - (f xStar + Ψ xStar) := by
  constructor
  · -- Compare the composite-objective gap with the affine model gap from the tangent plane at `x`.
    have hgap_real :
        (f x + Ψ x) - (f xStar + Ψ xStar) ≤
          inner ℝ (∇ f x) ((x : E) - xStar) + Ψ x - Ψ xStar := by
      have htangent :=
        hf_conv.lower_tangent_plane_of_hasGradientWithinAt (x : E) x.property (∇ f x) hf_grad
          (xStar : E) xStar.property
      have hsub : ((xStar : E) - x) = -((x : E) - xStar) := by
        simp [sub_eq_add_neg]
      have hrewrite :
          inner ℝ (∇ f x) ((xStar : E) - x) =
            -inner ℝ (∇ f x) ((x : E) - xStar) := by
        rw [hsub, inner_neg_right]
      rw [hrewrite] at htangent
      linarith
    -- Coerce the real comparison once, then spend the feasible point `xStar` in the supremum.
    have hgap :
        (((f x + Ψ x) - (f xStar + Ψ xStar) : ℝ) : EReal) ≤
          ((inner ℝ (∇ f x) ((x : E) - xStar) + Ψ x - Ψ xStar : ℝ) : EReal) := by
      exact_mod_cast hgap_real
    have hcomparison :
        ((inner ℝ (∇ f x) ((x : E) - xStar) + Ψ x - Ψ xStar : ℝ) : EReal) ≤ δ(x) := by
      rw [linearModelTotalVariation_def Q f Ψ x]
      exact le_sSup ⟨(xStar : E), xStar.property, rfl⟩
    simpa using hgap.trans hcomparison
  · -- The minimizer property on the feasible subtype gives the nonnegativity of the objective gap.
    have hxMin' : f xStar + Ψ xStar ≤ f x + Ψ x :=
      isMinOn_univ_iff.mp hxMin x
    exact sub_nonneg.mpr hxMin'

end

end
