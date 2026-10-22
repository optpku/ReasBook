/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.Order.Compact

-- Triage: the transcendental objective is the source-facing datum, `IsMaxOn` is the
-- core/canonical extremum owner, and the negated profile is the bridge from the source
-- maximization statement to the chapter's minimization-oriented method layer.

noncomputable section

open Set

/-- The objective `x ↦ (Real.sin x)^6 * Real.tan (1 - x) * Real.exp (30 * x)` from the line
search exercise. -/
def chapter02Exercise21Objective (x : ℝ) : ℝ :=
  (Real.sin x) ^ (6 : ℕ) * (Real.tan (1 - x) * Real.exp (30 * x))

/-- The minimization profile `x ↦ -(chapter02Exercise21Objective x)` used to attach the
Exercise 2.1 objective to the chapter's minimization-oriented one-dimensional search methods. -/
def chapter02Exercise21MinimizationProfile (x : ℝ) : ℝ :=
  -chapter02Exercise21Objective x

/-- The objective of Exercise 2.1 vanishes at the left endpoint `0`. -/
theorem chapter02Exercise21Objective_zero :
    chapter02Exercise21Objective 0 = 0 := by
  simp [chapter02Exercise21Objective]

/-- The minimization profile of Exercise 2.1 also vanishes at `0`. -/
theorem chapter02Exercise21MinimizationProfile_zero :
    chapter02Exercise21MinimizationProfile 0 = 0 := by
  simp [chapter02Exercise21MinimizationProfile, chapter02Exercise21Objective_zero]

/-- The objective of Exercise 2.1 is continuous on `Icc (0 : ℝ) 1`. -/
theorem chapter02Exercise21Objective_continuousOn_unitInterval :
    ContinuousOn chapter02Exercise21Objective (Icc (0 : ℝ) 1) := by
  have hSin :
      ContinuousOn (fun x : ℝ ↦ (Real.sin x) ^ (6 : ℕ)) (Icc (0 : ℝ) 1) :=
    (Real.continuous_sin.pow 6).continuousOn
  have hTan :
      ContinuousOn (fun x : ℝ ↦ Real.tan (1 - x)) (Icc (0 : ℝ) 1) := by
    refine Real.continuousOn_tan_Ioo.comp (continuousOn_const.sub continuousOn_id) ?_
    intro x hx
    constructor
    · linarith [Real.pi_div_two_pos, hx.2]
    · have hPi : (1 : ℝ) < Real.pi / 2 := by
        linarith [Real.pi_gt_three]
      linarith [hx.1, hPi]
  have hExp :
      ContinuousOn (fun x : ℝ ↦ Real.exp (30 * x)) (Icc (0 : ℝ) 1) :=
    (continuous_const.mul continuous_id).rexp.continuousOn
  change
    ContinuousOn
      (fun x : ℝ ↦ (Real.sin x) ^ (6 : ℕ) * (Real.tan (1 - x) * Real.exp (30 * x)))
      (Icc (0 : ℝ) 1)
  exact hSin.mul (hTan.mul hExp)

/-- The negated Exercise 2.1 profile is continuous on the unit interval. -/
theorem chapter02Exercise21MinimizationProfile_continuousOn_unitInterval :
    ContinuousOn chapter02Exercise21MinimizationProfile (Icc (0 : ℝ) 1) := by
  change ContinuousOn (fun x ↦ -chapter02Exercise21Objective x) (Icc (0 : ℝ) 1)
  exact chapter02Exercise21Objective_continuousOn_unitInterval.neg

/-- Chapter02 Exercise 2.1: the objective
`x ↦ (Real.sin x)^6 * Real.tan (1 - x) * Real.exp (30 * x)` attains its maximum on
`Icc (0 : ℝ) 1`. -/
theorem chapter02Exercise21_exists_isMaxOn_unitInterval :
    ∃ x ∈ Icc (0 : ℝ) 1, IsMaxOn chapter02Exercise21Objective (Icc (0 : ℝ) 1) x := by
  exact isCompact_Icc.exists_isMaxOn ⟨0, by simp⟩
    chapter02Exercise21Objective_continuousOn_unitInterval

/-- Negating the Exercise 2.1 objective converts its maximizers on `Icc (0 : ℝ) 1` into
minimizers of the profile used by the chapter's line-search method owners. -/
theorem chapter02Exercise21_isMaxOn_iff_isMinOn_minimizationProfile
    {x : ℝ} :
    IsMaxOn chapter02Exercise21Objective (Icc (0 : ℝ) 1) x ↔
      IsMinOn chapter02Exercise21MinimizationProfile (Icc (0 : ℝ) 1) x := by
  constructor
  · intro h
    change IsMinOn (fun y ↦ -chapter02Exercise21Objective y) (Icc (0 : ℝ) 1) x
    exact h.neg
  · intro h
    have hneg :
        IsMaxOn (fun y ↦ -chapter02Exercise21MinimizationProfile y) (Icc (0 : ℝ) 1) x :=
      h.neg
    simpa [chapter02Exercise21MinimizationProfile] using hneg

/-- The negated Exercise 2.1 profile attains its minimum on `Icc (0 : ℝ) 1`, matching the
maximizer existence statement for the original objective. -/
theorem chapter02Exercise21_exists_isMinOn_minimizationProfile_unitInterval :
    ∃ x ∈ Icc (0 : ℝ) 1,
      IsMinOn chapter02Exercise21MinimizationProfile (Icc (0 : ℝ) 1) x := by
  rcases chapter02Exercise21_exists_isMaxOn_unitInterval with ⟨x, hx, hmax⟩
  exact ⟨x, hx, (chapter02Exercise21_isMaxOn_iff_isMinOn_minimizationProfile).mp hmax⟩
