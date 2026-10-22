/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_18
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_30

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- The Brownian path space carries its Borel `σ`-algebra. -/
local instance brownianPathSpaceMeasurableSpace : MeasurableSpace BrownianPathSpace :=
  borel BrownianPathSpace

local notation "W" => fun t (ω : BrownianPathSpace) ↦ ω t

/-- Helper for Remark 21.34: every path in `BrownianPathSpace` is continuous, so the coordinate
process has almost surely continuous sample paths under any law on path space. -/
theorem hasAlmostSurelyContinuousPaths_brownianPathCoordinateProcess
    (μ : Measure BrownianPathSpace) :
    HasAlmostSurelyContinuousPaths μ W := by
  filter_upwards with ω
  simpa [HasAlmostSurelyContinuousPaths, processPath] using ω.continuous

/-- Helper for Remark 21.34: translating the coordinate process by a constant preserves almost
sure continuity of paths. -/
theorem hasAlmostSurelyContinuousPaths_shiftedBrownianPathCoordinateProcess
    (μ : Measure BrownianPathSpace) (x : ℝ) :
    HasAlmostSurelyContinuousPaths μ (fun t ω ↦ W t ω - x) := by
  filter_upwards with ω
  simpa [HasAlmostSurelyContinuousPaths, processPath] using ω.continuous.sub continuous_const

/-- Helper for Remark 21.34: the shifted coordinate process starts at `0` exactly on the event
that the original coordinate process starts at `x`. -/
lemma brownianPathCoordinateShift_start_preimage (x : ℝ) :
    ((fun ω : BrownianPathSpace ↦ W 0 ω - x) ⁻¹' ({0} : Set ℝ)) =
      ((fun ω : BrownianPathSpace ↦ W 0 ω) ⁻¹' ({x} : Set ℝ)) := by
  -- Compare the two starting events pointwise and cancel the deterministic shift.
  ext ω
  constructor <;> intro h
  · simp at h ⊢
    linarith
  · simp at h ⊢
    linarith

/-- Helper for Remark 21.34: translating a real-valued process by a constant does not change
independent increments. -/
lemma hasIndepIncrements_sub_const_iff
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (B : NNReal → Ω → ℝ) (x : ℝ) :
    HasIndepIncrements B μ ↔ HasIndepIncrements (fun t ω ↦ B t ω - x) μ := by
  constructor <;> intro hB
  · -- Each increment of the shifted process simplifies to the original increment.
    rw [HasIndepIncrements] at hB ⊢
    intro n t ht
    simpa only [sub_sub_sub_cancel_right] using hB n t ht
  · -- The same cancellation recovers the unshifted process from the shifted one.
    rw [HasIndepIncrements] at hB ⊢
    intro n t ht
    simpa only [sub_sub_sub_cancel_right] using hB n t ht

/-- Helper for Remark 21.34: translating a real-valued process by a constant does not change
stationary increments. -/
lemma hasStationaryIncrements_sub_const_iff
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (B : NNReal → Ω → ℝ) (x : ℝ) :
    HasStationaryIncrements B μ ↔ HasStationaryIncrements (fun t ω ↦ B t ω - x) μ := by
  constructor <;> intro hB
  · -- Every shifted increment pair reduces to the original increment pair.
    rw [HasStationaryIncrements] at hB ⊢
    intro r s t
    simpa only [sub_sub_sub_cancel_right] using hB r s t
  · -- The same normalization removes the shift in the reverse direction as well.
    rw [HasStationaryIncrements] at hB ⊢
    intro r s t
    simpa only [sub_sub_sub_cancel_right] using hB r s t

/-- Remark 21.34: on `C([0, ∞), ℝ)`, translating the canonical coordinate process by its starting
point is an owner-level bridge inside `IsBrownianMotionStartedAt`: the coordinate process is
Brownian motion started at `x` exactly when the shifted coordinate process is Brownian motion
started at `0`. -/
theorem isBrownianMotionStartedAt_brownianPathCoordinateProcess_iff_shifted
    (μ : Measure BrownianPathSpace) (x : ℝ) :
    IsBrownianMotionStartedAt μ W x ↔
      IsBrownianMotionStartedAt μ (fun t ω ↦ W t ω - x) 0 := by
  constructor
  · intro hW
    refine
      { start := ?_
        indepIncrements := ?_
        stationaryIncrements := ?_
        gaussian_marginal := ?_
        continuous_paths := ?_ }
    · -- Rewrite the shifted start event back to the original starting event at `x`.
      simpa [brownianPathCoordinateShift_start_preimage (x := x)] using hW.start
    · -- Independent increments are unchanged by subtracting a deterministic constant.
      exact (hasIndepIncrements_sub_const_iff μ W x).1 hW.indepIncrements
    · -- Stationary increments are likewise invariant under deterministic translation.
      exact (hasStationaryIncrements_sub_const_iff μ W x).1 hW.stationaryIncrements
    · intro t ht
      -- Transport the Gaussian time-`t` marginal by subtracting the initial point.
      simpa using ProbabilityTheory.gaussianReal_sub_const (hW.gaussian_marginal ht) x
    · -- Every path in Brownian path space is continuous, so the shifted coordinate process is too.
      exact hasAlmostSurelyContinuousPaths_shiftedBrownianPathCoordinateProcess μ x
  · intro hShift
    refine
      { start := ?_
        indepIncrements := ?_
        stationaryIncrements := ?_
        gaussian_marginal := ?_
        continuous_paths := ?_ }
    · -- The same event rewrite recovers the original starting point `x`.
      simpa [brownianPathCoordinateShift_start_preimage (x := x)] using hShift.start
    · -- Remove the deterministic shift from the increment family.
      exact (hasIndepIncrements_sub_const_iff μ W x).2 hShift.indepIncrements
    · -- Remove the deterministic shift from the stationary-increment law.
      exact (hasStationaryIncrements_sub_const_iff μ W x).2 hShift.stationaryIncrements
    · intro t ht
      -- Add back the starting point to transport the centered Gaussian marginal to mean `x`.
      simpa [sub_eq_add_neg, add_assoc] using
        ProbabilityTheory.gaussianReal_add_const (hShift.gaussian_marginal ht) x
    · -- The unshifted coordinate process also has continuous paths under every law on path space.
      exact hasAlmostSurelyContinuousPaths_brownianPathCoordinateProcess μ

end ProbabilityTheory
