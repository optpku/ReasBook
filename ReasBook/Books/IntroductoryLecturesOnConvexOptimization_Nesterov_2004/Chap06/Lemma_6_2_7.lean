/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Lemma 6.2.7 lies in the Chapter 6 excessive-gap / one-sided smoothing domain.

Mandatory domain-style sampling before refinement:
- `satisfiesExcessiveGapCondition` in `Chap06/Theorem_6_4`, the chapter owner for the
  excessive-gap certificate `fμ₂ xBar ≤ φμ₁ uBar`;
- `raw_duality_gap_le_excessive_gap_budget` in `Chap06/Lemma_6_2_1`, the owner theorem turning a
  local smoothing lower bound and an excessive-gap certificate into a raw-gap upper bound;
- `satisfiesExcessiveGapConditionWithMu1Zero` in `Chap06/Definition_6_38`, the `μ₁ = 0`
  specialization already built on the same owner abstraction.

Best owner abstraction:
- source-facing: the raw primal-dual gap bound at one pair `(xBar, uBar)`;
- core/canonical: `satisfiesExcessiveGapCondition` together with interval membership in
  `Set.Icc`;
- bridge/view: the additional weak-duality lower bound `φ uBar ≤ f xBar`.

Primitive data:
- the local lower smoothing estimate at `xBar`;
- the excessive-gap certificate at `(xBar, uBar)`;
- the weak-duality inequality at `(xBar, uBar)`.

Derived API:
- the canonical interval bound
  `f xBar - φ uBar ∈ Set.Icc 0 (μ₂ * D₂)`.

Source/core/bridge triage:
- source-facing: Lemma 6.2.7's bound on the raw primal-dual gap;
- core/canonical: `satisfiesExcessiveGapCondition` and
  `raw_duality_gap_le_excessive_gap_budget`;
- bridge/view: the weak-duality lower bound furnishing the left endpoint `0`.

The previous version used the opposite inequality `φ uBar ≤ fμ₂ xBar`, which cannot imply the
advertised upper bound `f xBar - φ uBar ≤ μ₂ * D₂`, and it kept unused positivity hypotheses and
a global `∀ x` smoothing assumption. The refined statement keeps only the mathematically necessary
local data and reuses the chapter owner certificate directly.
-/

section

variable {X : Type u} {U : Type v}

-- Proof sketch: the excessive-gap certificate is exactly `fμ₂ xBar ≤ φ uBar`, so
-- `raw_duality_gap_le_excessive_gap_budget` with `μ₁ = 0` yields the upper bound
-- `f xBar - φ uBar ≤ μ₂ * D₂`. The separate weak-duality hypothesis `φ uBar ≤ f xBar` gives the
-- lower bound `0 ≤ f xBar - φ uBar`.
/-- Lemma 6.2.7: if `fμ₂` satisfies the local lower estimate
`f xBar - μ₂ D₂ ≤ fμ₂ xBar`, if `(xBar, uBar)` satisfies the Chapter 6 excessive-gap
certificate `fμ₂ xBar ≤ φ uBar`, and if the raw weak-duality inequality `φ uBar ≤ f xBar`
holds at the same pair, then the primal-dual gap at `(xBar, uBar)` lies in the interval
`[0, μ₂ D₂]`. -/
theorem primal_dual_gap_bound_of_smoothed_lower_estimate
    {Q₁ : Set X} {Q₂ : Set U}
    {f fμ₂ : X → ℝ} {φ : U → ℝ}
    {μ₂ D₂ : ℝ} {xBar : Q₁} {uBar : Q₂}
    (hfμ₂_lower : f xBar - μ₂ * D₂ ≤ fμ₂ xBar)
    (hexcessive_gap : satisfiesExcessiveGapCondition Q₁ Q₂ fμ₂ φ xBar uBar)
    (hweak : φ uBar ≤ f xBar) :
    f xBar - φ uBar ∈ Set.Icc 0 (μ₂ * D₂) := by
  constructor
  -- The weak-duality inequality gives the left endpoint `0 ≤ f xBar - φ uBar`.
  · exact sub_nonneg.mpr hweak
  -- The smoothing lower estimate and the excessive-gap certificate control the right endpoint.
  · have hsandwich : f xBar - μ₂ * D₂ ≤ φ uBar :=
      hfμ₂_lower.trans hexcessive_gap
    linarith

end
