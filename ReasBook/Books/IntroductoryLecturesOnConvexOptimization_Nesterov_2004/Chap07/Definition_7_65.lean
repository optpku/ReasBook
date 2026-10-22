/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_1

-- Declarations for this item will be appended below by the statement pipeline.

section

/- Definition 7.65 lies in the chapter's relative-accuracy / scalar approximation domain.

Sampled owner-style declarations:
- `IsRelativeAccuracy` in `Chap07/Definition_7_1`, the chapter owner for multiplicative
  relative-accuracy bounds on a positive scalar optimum;
- `IsApproximateSolution` in `Chap03/Definition_3_34`, the upstream additive owner for scalar
  objective-gap approximation relative to a chosen minimizer;
- `IsRelativeDeltaApproximateSolutionOn` in `Chap07/Definition_7_92`, the optimization-layer
  relative approximation owner for feasible points on a set-constrained problem.

Best owner abstraction:
- source-facing: the positive-maximization relative-scale predicate from Definition 7.65 itself;
- core/canonical: a direct scalar `Prop` on `(phiStar, δ, phiBar)` over `ℝ`, because the source
  notion is intrinsically the conjunction of positivity and the two-sided exponential bounds;
- bridge/view: the reciprocal-value reformulation as the earlier chapter owner
  `IsRelativeAccuracy`.

Primitive data:
- the positive optimal value `phiStar`;
- the scale parameter `δ`;
- the candidate value `phiBar`.

Derived API:
- positivity of `phiBar`;
- the reciprocal relative-accuracy bridge to `IsRelativeAccuracy`.

Source/core/bridge triage:
- source-facing: `IsRelativeScaleDeltaApproximation`;
- core/canonical: the scalar inequalities themselves;
- bridge/view: `toIsRelativeAccuracy_inv`.

There is no exact upstream owner with the same source semantics, so the public owner stays local.
The duplicate-wheel issue here is not the owner predicate itself, but leaving it disconnected from
the chapter's existing relative-accuracy API. This refinement keeps Definition 7.65 source-facing
and adds the canonical reciprocal bridge instead of introducing a parallel wrapper.
-/

/-- Definition 7.65: a value `phiBar` is a `δ`-approximation of the positive optimal value
`phiStar` in relative scale when `δ > 0` and
`phiStar ≥ phiBar ≥ phiStar * exp (-δ)`. -/
def IsRelativeScaleDeltaApproximation
    (phiStar δ phiBar : ℝ) : Prop :=
  0 < phiStar ∧ 0 < δ ∧ phiStar ≥ phiBar ∧ phiBar ≥ phiStar * Real.exp (-δ)

namespace IsRelativeScaleDeltaApproximation

theorem optimal_pos {phiStar δ phiBar : ℝ}
    (h : IsRelativeScaleDeltaApproximation phiStar δ phiBar) :
    0 < phiStar :=
  h.1

theorem delta_pos {phiStar δ phiBar : ℝ}
    (h : IsRelativeScaleDeltaApproximation phiStar δ phiBar) :
    0 < δ :=
  h.2.1

theorem approx_le {phiStar δ phiBar : ℝ}
    (h : IsRelativeScaleDeltaApproximation phiStar δ phiBar) :
    phiBar ≤ phiStar :=
  h.2.2.1

theorem optimal_mul_exp_neg_le {phiStar δ phiBar : ℝ}
    (h : IsRelativeScaleDeltaApproximation phiStar δ phiBar) :
    phiStar * Real.exp (-δ) ≤ phiBar :=
  h.2.2.2

theorem approx_pos {phiStar δ phiBar : ℝ}
    (h : IsRelativeScaleDeltaApproximation phiStar δ phiBar) :
    0 < phiBar := by
  refine lt_of_lt_of_le ?_ h.optimal_mul_exp_neg_le
  exact mul_pos h.optimal_pos (Real.exp_pos _)

/-- The reciprocal values satisfy the earlier chapter owner `IsRelativeAccuracy`: Definition 7.65
becomes an ordinary multiplicative relative-accuracy statement after inverting the positive
maximization values. -/
theorem toIsRelativeAccuracy_inv {phiStar δ phiBar : ℝ}
    (h : IsRelativeScaleDeltaApproximation phiStar δ phiBar) :
    IsRelativeAccuracy (1 / phiStar) (Real.exp δ - 1) (1 / phiBar) := by
  refine ⟨one_div_pos.mpr h.optimal_pos, ?_, ?_⟩
  · simpa using one_div_le_one_div_of_le h.approx_pos h.approx_le
  · have hrecip : 1 / phiBar ≤ 1 / (phiStar * Real.exp (-δ)) :=
      one_div_le_one_div_of_le (mul_pos h.optimal_pos (Real.exp_pos _))
        h.optimal_mul_exp_neg_le
    calc
      1 / phiBar ≤ 1 / (phiStar * Real.exp (-δ)) := hrecip
      _ = Real.exp δ / phiStar := by
        field_simp [Real.exp_ne_zero]
        ring_nf
        rw [Real.exp_neg]
        field_simp [Real.exp_ne_zero]
      _ = (1 + (Real.exp δ - 1)) * (1 / phiStar) := by ring

end IsRelativeScaleDeltaApproximation

-- Proof sketch: unfold `IsRelativeScaleDeltaApproximation`.
/-- Unfolding `IsRelativeScaleDeltaApproximation phiStar δ phiBar` gives the positivity and
two-sided exponential bounds from the textbook definition. -/
theorem isRelativeScaleDeltaApproximation_iff
    (phiStar δ phiBar : ℝ) :
    IsRelativeScaleDeltaApproximation phiStar δ phiBar ↔
      0 < phiStar ∧ 0 < δ ∧
        phiStar ≥ phiBar ∧ phiBar ≥ phiStar * Real.exp (-δ) :=
  Iff.rfl

end
