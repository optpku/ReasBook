/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_6_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Primary domain: sufficient-decrease and monotonicity for constant-step gradient descent on real
Hilbert spaces.

Owner-style declarations sampled before refining this file:
* `gradientMethod` in `Algorithm_2_1`, the Chapter 2 recall of the recursive trajectory owner;
* `gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient` in `Chap01/Lemma_1_6_6`,
  the arbitrary-point owner theorem from which the chapter iterate theorem is derived;
* `Antitone` and `antitone_nat_of_succ_le`, the canonical decreasing-sequence owner and its
  `ℕ`-successor bridge recalled in `Chap01/Definition_1_4_1`.

Source/core/bridge triage:
* source-facing: Proposition 2.8's monotonicity statement for the constant-step trajectory;
* core/canonical: `Antitone (fun k ↦ f (traj k))`, obtained from the Chapter 1 iterate-wise
  sufficient-decrease theorem plus nonnegativity of the constant-step factor;
* bridge/view: the one-step inequality `f (traj (k + 1)) ≤ f (traj k)` recovered from
  `Nat.le_succ k`.

Primitive data:
* the objective `f`, the constant step `α`, and the initial point `x0`;
* the smoothness hypotheses `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)`.

Derived API:
* the antitone objective-value sequence and its one-step corollary.

This file derives the textbook iterate-wise decrease directly from the Chapter 1 pointwise owner
`gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient`, then packages the
source-facing monotonicity consequence with `Antitone` as the main public owner statement and the
successor-step inequality as a thin bridge. The textbook `ℝⁿ` formulation is recovered by
specializing `E` to `EuclideanSpace ℝ (Fin n)`.
-/
section GradientMethod

variable (f : E → ℝ) {L : NNReal} {α : ℝ} (x0 : E)
variable
  (hf_C1 : ContDiff ℝ 1 f)
  (hgrad : LipschitzWith L (∇ f))
  (hα_nonneg : 0 ≤ α)
  (hα_le : α ≤ 2 / (L : ℝ))

local notation "traj" => gradientMethod (fun _ ↦ α) f x0

section

include hf_C1 hgrad

/-- Helper for Proposition 2.8: along the constant-step trajectory, the pointwise descent lemma
specializes to the textbook one-step value decrease. -/
private lemma gradientMethod_step_value_decrease_of_constant_stepsize
    (k : ℕ) :
    f (traj (k + 1)) ≤
      f (traj k) - (α * (1 - ((L : ℝ) * α) / 2)) * ‖∇ f (traj k)‖ ^ (2 : ℕ) := by
  -- Route correction: use the Chapter 1 pointwise descent owner directly, since the iterate-wise
  -- wrapper module is not available in the current workspace import state.
  -- Rewriting `traj (k + 1)` by the recursion turns the textbook iterate step into the pointwise
  -- antigradient update from Lemma 1.6.6.
  simpa [gradientMethod_succ] using
    gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient
      hf_C1 hgrad (traj k) α

end

section

include hα_nonneg hα_le

/-- Helper for Proposition 2.8: the admissible constant-step range makes the descent coefficient
nonnegative. -/
private lemma stepFactor_nonneg
    : 0 ≤ α * (1 - ((L : ℝ) * α) / 2) := by
  -- Separate the degenerate `L = 0` case from the positive-L case.
  by_cases hL0 : (L : ℝ) = 0
  · have hα_nonpos : α ≤ 0 := by
      simpa [hL0] using hα_le
    have hα_eq : α = 0 := by
      linarith
    simp [hα_eq]
  · have hL_pos : 0 < (L : ℝ) :=
      lt_of_le_of_ne L.2 <| by simpa [eq_comm] using hL0
    have hmul : (L : ℝ) * α ≤ 2 := by
      simpa [mul_comm] using (le_div_iff₀ hL_pos).mp hα_le
    have hscale_nonneg : 0 ≤ 1 - ((L : ℝ) * α) / 2 := by
      nlinarith
    exact mul_nonneg hα_nonneg hscale_nonneg

end

include hf_C1 hgrad hα_nonneg hα_le

/-- Proposition 2.8: on the monotonicity range `0 ≤ α ≤ 2 / L`, the objective values along the
constant-step gradient-method trajectory form an antitone sequence. The source range
`0 < α ≤ 2 / L` is a special case, and the textbook `ℝⁿ` statement is recovered by specializing
`E` to `EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: obtain the one-step decrease from the Chapter 1 constant-step owner theorem, then
-- promote the successor-step inequality to an antitone sequence on `ℕ`.
theorem gradientMethod_value_antitone_of_constant_stepsize
    : Antitone (fun k ↦ f (traj k)) := by
  refine antitone_nat_of_succ_le ?_
  intro k
  have hstep := gradientMethod_step_value_decrease_of_constant_stepsize
    (f := f) (L := L) (α := α) (x0 := x0) (hf_C1 := hf_C1) (hgrad := hgrad) k
  have hterm_nonneg :
      0 ≤ (α * (1 - ((L : ℝ) * α) / 2)) * ‖∇ f (traj k)‖ ^ (2 : ℕ) := by
    -- The decrease term is nonnegative because both the scalar coefficient and the squared norm
    -- are nonnegative on the admissible step-size range.
    exact mul_nonneg
      (stepFactor_nonneg (L := L) (α := α) (hα_nonneg := hα_nonneg) (hα_le := hα_le))
      (by positivity)
  -- Dropping the nonnegative decrease term gives the monotonicity inequality.
  linarith

/-- Companion one-step formulation of Proposition 2.8. -/
theorem gradientMethod_value_nonincreasing_step
    (k : ℕ) :
    f (traj (k + 1)) ≤ f (traj k) := by
  -- The one-step statement is the successor instance of the antitone trajectory-value sequence.
  simpa using
    gradientMethod_value_antitone_of_constant_stepsize
      f x0 hf_C1 hgrad hα_nonneg hα_le (Nat.le_succ k)

end GradientMethod
