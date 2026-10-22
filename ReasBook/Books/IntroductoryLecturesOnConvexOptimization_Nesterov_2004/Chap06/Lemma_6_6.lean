/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_34
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Lemma 6.6 lies in the chapter's excessive-gap/error-bound domain.

Sampled owner-style declarations:
- `raw_duality_gap_le_excessive_gap_budget` in `Lemma_6_2_1`, the chapter owner for the budget
  bound on the raw duality gap;
- `IsLeast` and `IsGreatest`, the canonical order-theoretic owners for attained primal minima and
  dual maxima;
- the source-facing split error bounds in `Lemma_6_2_1`, which already separate the raw-gap bridge
  from the order-theoretic optimality consequences.

Best owner abstraction:
- source-facing: the combined primal/dual error estimate at an excessive-gap pair;
- core/canonical: `raw_duality_gap_le_excessive_gap_budget` together with `IsLeast` and
  `IsGreatest`;
- bridge/view: bundling the two error terms into the interval statement for
  `max (f xBar - fStar) (fStar - φ uBar)`.

Primitive data:
- attained primal/dual optimal values `h_primal` and `h_dual`;
- the local smoothing bounds at the current pair `(xBar, uBar)`;
- the chapter excessive-gap certificate at the current pair.

Derived API:
- the raw duality-gap budget bound;
- the separate primal and dual error bounds against the raw gap;
- the final `Set.Icc` statement for their maximum.

The previous version encoded the local smoothing bounds via extra primitive data
`d₁`, `d₂`, `xOf`, `uOf`, `h_D₁`, `h_D₂`, and defining equations, even though the theorem only
uses the resulting inequalities at `xBar` and `uBar`. This refinement keeps the source-facing
combined conclusion while moving the statement to the canonical owner-level inputs.
-/
-- Proof sketch: apply `raw_duality_gap_le_excessive_gap_budget` to the two local smoothing bounds
-- and the excessive-gap certificate to control `f xBar - φ uBar` by `μ₁ D₁ + μ₂ D₂`. The attained
-- primal minimum and dual maximum give `φ uBar ≤ fStar ≤ f xBar`, so both
-- `f xBar - fStar` and `fStar - φ uBar` are nonnegative and bounded above by the raw duality gap.
/-- Lemma 6.6: if the primal value `fStar` is the minimum of `f` on `Q₁`, the same value is the
maximum of `φ` on `Q₂`, and the local smoothing bounds together with the excessive-gap certificate
hold at `xBar ∈ Q₁` and `uBar ∈ Q₂`, then the primal and dual errors are both controlled by the
raw duality gap, which is at most `μ₁ D₁ + μ₂ D₂`. -/
theorem excessive_gap_bounds_primal_dual_errors
    {X : Type u} {U : Type v}
    {Q₁ : Set X} {Q₂ : Set U}
    {f fμ₂ : X → ℝ} {φ φμ₁ : U → ℝ}
    {xBar : X} {uBar : U}
    {fStar D₁ D₂ μ₁ μ₂ : ℝ}
    (h_primal : IsLeast (f '' Q₁) fStar)
    (h_dual : IsGreatest (φ '' Q₂) fStar)
    (hfμ₂_lower : f xBar - μ₂ * D₂ ≤ fμ₂ xBar)
    (hφμ₁_upper : φμ₁ uBar ≤ φ uBar + μ₁ * D₁)
    (hxBar : xBar ∈ Q₁)
    (huBar : uBar ∈ Q₂)
    (hexcessive_gap :
      satisfiesExcessiveGapCondition Q₁ Q₂ fμ₂ φμ₁ ⟨xBar, hxBar⟩ ⟨uBar, huBar⟩) :
    max (f xBar - fStar) (fStar - φ uBar) ∈ Set.Icc 0 (f xBar - φ uBar) ∧
      f xBar - φ uBar ≤ μ₁ * D₁ + μ₂ * D₂ := by
  let xBarQ : Q₁ := ⟨xBar, hxBar⟩
  let uBarQ : Q₂ := ⟨uBar, huBar⟩
  have hfμ₂_lower' : f xBarQ - μ₂ * D₂ ≤ fμ₂ xBarQ := by
    simpa [xBarQ] using hfμ₂_lower
  have hφμ₁_upper' : φμ₁ uBarQ ≤ φ uBarQ + μ₁ * D₁ := by
    simpa [uBarQ] using hφμ₁_upper
  have hexcessive_gap' :
      satisfiesExcessiveGapCondition Q₁ Q₂ fμ₂ φμ₁ xBarQ uBarQ := by
    simpa [xBarQ, uBarQ] using hexcessive_gap
  have hraw_gap :
      f xBar - φ uBar ≤ μ₁ * D₁ + μ₂ * D₂ :=
    by
      simpa [xBarQ, uBarQ] using
        (raw_duality_gap_le_excessive_gap_budget hfμ₂_lower' hφμ₁_upper' hexcessive_gap')
  have hφ_le_fStar : φ uBar ≤ fStar :=
    h_dual.2 (Set.mem_image_of_mem φ huBar)
  have hfStar_le_f : fStar ≤ f xBar :=
    h_primal.2 (Set.mem_image_of_mem f hxBar)
  have hprimal_nonneg : 0 ≤ f xBar - fStar :=
    sub_nonneg.mpr hfStar_le_f
  have hprimal_le_raw_gap : f xBar - fStar ≤ f xBar - φ uBar :=
    sub_le_sub_left hφ_le_fStar (f xBar)
  have hdual_nonneg : 0 ≤ fStar - φ uBar :=
    sub_nonneg.mpr hφ_le_fStar
  have hdual_le_raw_gap : fStar - φ uBar ≤ f xBar - φ uBar :=
    sub_le_sub_right hfStar_le_f (φ uBar)
  have hmax_nonneg : 0 ≤ max (f xBar - fStar) (fStar - φ uBar) :=
    le_trans hprimal_nonneg (le_max_left _ _)
  have hmax_le_raw_gap :
      max (f xBar - fStar) (fStar - φ uBar) ≤ f xBar - φ uBar :=
    max_le_iff.mpr ⟨hprimal_le_raw_gap, hdual_le_raw_gap⟩
  exact ⟨Set.mem_Icc.mpr ⟨hmax_nonneg, hmax_le_raw_gap⟩, hraw_gap⟩
