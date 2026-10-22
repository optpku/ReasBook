/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {X : Type u} {U : Type v}

/-- The raw duality gap at an excessive-gap pair is bounded by the smoothing budget
`μ₁ D₁ + μ₂ D₂`. -/
-- Proof sketch: combine the pointwise smoothing bounds at `xBar` and `uBar` with
-- `fμ₂ xBar ≤ φμ₁ uBar` to get
-- `f xBar - μ₂ * D₂ ≤ fμ₂ xBar ≤ φμ₁ uBar ≤ φ uBar + μ₁ * D₁`, then rearrange.
theorem raw_duality_gap_le_excessive_gap_budget
    {Q₁ : Set X} {Q₂ : Set U}
    {f fμ₂ : X → ℝ} {φ φμ₁ : U → ℝ}
    {xBar : Q₁} {uBar : Q₂}
    {D₁ D₂ μ₁ μ₂ : ℝ}
    (hfμ₂_lower : f xBar - μ₂ * D₂ ≤ fμ₂ xBar)
    (hφμ₁_upper : φμ₁ uBar ≤ φ uBar + μ₁ * D₁)
    (hexcessive_gap : satisfiesExcessiveGapCondition Q₁ Q₂ fμ₂ φμ₁ xBar uBar) :
    f xBar - φ uBar ≤ μ₁ * D₁ + μ₂ * D₂ := by
  have hgap : f xBar - μ₂ * D₂ ≤ φ uBar + μ₁ * D₁ :=
    (hfμ₂_lower.trans hexcessive_gap).trans hφμ₁_upper
  linarith

/-- Lemma 6.2.1 (1): the primal error at an excessive-gap pair is nonnegative. -/
-- Proof sketch: `h_primal` states that `fStar` is the minimum value of `f` on `Q₁`; apply it to
-- `xBar ∈ Q₁` to get `fStar ≤ f xBar`, then rearrange.
theorem excessive_gap_condition_primal_error_nonneg {Q₁ : Set X} {f : X → ℝ} {xBar : X}
    {fStar : ℝ} (h_primal : IsLeast (f '' Q₁) fStar) (hxBar : xBar ∈ Q₁) :
    0 ≤ f xBar - fStar := by
  exact sub_nonneg.mpr (h_primal.2 (Set.mem_image_of_mem f hxBar))

/-- Lemma 6.2.1 (2): the primal error at an excessive-gap pair is bounded above by the raw duality
gap. -/
-- Proof sketch: `h_dual` gives `φ uBar ≤ fStar`, so subtracting this inequality from `f xBar`
-- yields `f xBar - fStar ≤ f xBar - φ uBar`.
theorem excessive_gap_condition_primal_error_le_raw_gap {Q₂ : Set U} {f : X → ℝ}
    {φ : U → ℝ} {xBar : X} {uBar : U} {fStar : ℝ}
    (h_dual : IsGreatest (φ '' Q₂) fStar) (huBar : uBar ∈ Q₂) :
    f xBar - fStar ≤ f xBar - φ uBar := by
  exact sub_le_sub_left (h_dual.2 (Set.mem_image_of_mem φ huBar)) (f xBar)

/-- Lemma 6.2.1 (3): the dual error at an excessive-gap pair is nonnegative. -/
-- Proof sketch: `h_dual` states that `fStar` is the maximum value of `φ` on `Q₂`; apply it to
-- `uBar ∈ Q₂` to get `φ uBar ≤ fStar`, then rearrange.
theorem excessive_gap_condition_dual_error_nonneg {Q₂ : Set U} {φ : U → ℝ} {uBar : U}
    {fStar : ℝ}
    (h_dual : IsGreatest (φ '' Q₂) fStar) (huBar : uBar ∈ Q₂) :
    0 ≤ fStar - φ uBar := by
  exact sub_nonneg.mpr (h_dual.2 (Set.mem_image_of_mem φ huBar))

/-- Lemma 6.2.1 (4): the dual error at an excessive-gap pair is bounded above by the raw duality
gap. -/
-- Proof sketch: `h_primal` gives `fStar ≤ f xBar`, so subtracting `φ uBar` from this inequality
-- yields `fStar - φ uBar ≤ f xBar - φ uBar`.
theorem excessive_gap_condition_dual_error_le_raw_gap {Q₁ : Set X} {f : X → ℝ}
    {φ : U → ℝ} {xBar : X} {uBar : U} {fStar : ℝ}
    (h_primal : IsLeast (f '' Q₁) fStar) (hxBar : xBar ∈ Q₁) :
    fStar - φ uBar ≤ f xBar - φ uBar := by
  exact sub_le_sub_right (h_primal.2 (Set.mem_image_of_mem f hxBar)) (φ uBar)

end
