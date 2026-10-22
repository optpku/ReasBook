/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_33

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Definition 2.35.1 is source-facing in the projected-gradient / metric-projection domain on a
complete real inner-product space.

Owner declarations sampled for this refinement:
* `IsProjectionPointOn` in `Chap07/Definition_7_3`, the primitive nearest-point predicate;
* `IsProjectionPointOn.isMinOn` in `Definition_2_33`, the canonical minimizing-property API;
* `euclideanProjection` and `euclideanProjection_isProjectionPointOn` in `Theorem_2_33`, the
  chapter's chosen projection point and its owner bridge.
* `NNRealˣ`, the project-standard owner for primitive positive real parameters.

Best owner abstraction:
* `gradientStep f xBar γ`, with `γ : NNRealˣ`;
* `IsProjectionPointOn Q (gradientStep f xBar γ) p`.

Source/core/bridge triage:
* source-facing: `gradientMapping` and `reducedGradient`;
* core/canonical: `IsProjectionPointOn` and `euclideanProjection`;
* bridge/view: `gradientMapping_isProjectionPointOn`.

Primitive data:
* the feasible set `Q` with nonempty / closed / convex structure;
* the objective `f`, base point `xBar`, and positive inverse-stepsize / regularization
  parameter `γ`.

Derived API:
* the owner projection-point view `gradientMapping_isProjectionPointOn`;
* feasibility and minimizing properties recovered from that owner bridge;
* the residual formula already built into `reducedGradient`.

This file therefore keeps the source-facing projected-step objects and the single owner bridge
needed for downstream projection-point reasoning, while avoiding any heavier wrapper API.
-/

section

variable [CompleteSpace E]

/-- The explicit gradient step from `xBar` with positive inverse-stepsize parameter `γ`. -/
def gradientStep
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ) :
    E :=
  xBar - ((γ : ℝ)⁻¹) • ∇ f xBar

/-- Definition 2.35.1 (1): the projected-gradient point is the Euclidean projection of the explicit
gradient step `gradientStep f xBar γ` onto `Q`. -/
def gradientMapping
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ)
    :
    E :=
  euclideanProjection Q hQ_nonempty hQ_closed hQ_convex
    (gradientStep f xBar γ)

private abbrev nonemptyOfFact (Q : Set E) [Fact (Set.Nonempty Q)] : Set.Nonempty Q :=
  Fact.out

namespace ProjectedGradient

scoped notation:max
    "x_Q[" Q ";" hQ_nonempty ";" hQ_closed ";" hQ_convex "|" f ";" γ "]" "(" xBar ")" =>
  gradientMapping
    Q hQ_nonempty hQ_closed hQ_convex f xBar γ

scoped notation:max
    "x_f[" Q ";" hQ_nonempty ";" hQ_closed ";" hQ_convex "|" f ";" γ "]" "(" xBar ")" =>
  gradientMapping
    Q hQ_nonempty hQ_closed hQ_convex f xBar γ

scoped notation:max
    "x_Q[" Q ";" hQ_closed ";" hQ_convex "|" f ";" γ "]" "(" xBar ")" =>
  gradientMapping
    Q (nonemptyOfFact Q) hQ_closed hQ_convex f xBar γ

scoped notation:max
    "x_f[" Q ";" hQ_closed ";" hQ_convex "|" f ";" γ "]" "(" xBar ")" =>
  gradientMapping
    Q (nonemptyOfFact Q) hQ_closed hQ_convex f xBar γ

end ProjectedGradient

open scoped ProjectedGradient

section

variable
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (γ : NNRealˣ)

/-- The projected-gradient point is a projection point of the explicit gradient step
`gradientStep f xBar γ` onto `Q`. -/
theorem gradientMapping_isProjectionPointOn
    (xBar : E)
    :
    IsProjectionPointOn Q (gradientStep f xBar γ)
      x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; γ](xBar) :=
  euclideanProjection_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex
    (gradientStep f xBar γ)

/-- Definition 2.35.1 (2): the reduced gradient is the scaled residual from `xBar` to the
projected-gradient point. -/
def reducedGradient
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ)
    :
    E :=
  (γ : ℝ) • (xBar - gradientMapping Q hQ_nonempty hQ_closed hQ_convex f xBar γ)

namespace ProjectedGradient

scoped notation:max
    "g_Q[" Q ";" hQ_nonempty ";" hQ_closed ";" hQ_convex "|" f ";" γ "]" "(" xBar ")" =>
  reducedGradient
    Q hQ_nonempty hQ_closed hQ_convex f xBar γ

scoped notation:max
    "g_f[" Q ";" hQ_nonempty ";" hQ_closed ";" hQ_convex "|" f ";" γ "]" "(" xBar ")" =>
  reducedGradient
    Q hQ_nonempty hQ_closed hQ_convex f xBar γ

scoped notation:max
    "g_Q[" Q ";" hQ_closed ";" hQ_convex "|" f ";" γ "]" "(" xBar ")" =>
  reducedGradient
    Q (nonemptyOfFact Q) hQ_closed hQ_convex f xBar γ

scoped notation:max
    "g_f[" Q ";" hQ_closed ";" hQ_convex "|" f ";" γ "]" "(" xBar ")" =>
  reducedGradient
    Q (nonemptyOfFact Q) hQ_closed hQ_convex f xBar γ

end ProjectedGradient

end

end
