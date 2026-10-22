/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Process.Filtration

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory

universe u

namespace MeasureTheory

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

namespace Filtration

/-- Definition 21.22: A filtration on `ℝ≥0` satisfies the usual conditions if it is right
continuous in the canonical mathlib sense `Filtration.IsRightContinuous` and if every `μ`-null
set is already measurable in the initial `σ`-algebra `ℱ 0`. -/
class UsualConditions (ℱ : Filtration NNReal mΩ) (μ : Measure Ω) : Prop extends
    ℱ.IsRightContinuous where
  complete_timeZero : ∀ s : Set Ω, μ s = 0 → MeasurableSet[ℱ 0] s

/-- Helper for Definition 21.22: `UsualConditions` induces completeness of the initial trimmed
measure because every set of trimmed measure zero is ambient `μ`-null, hence already measurable in
`ℱ 0`. -/
instance instIsCompleteTrimTimeZero
    (ℱ : Filtration NNReal mΩ) (μ : Measure Ω) [h : UsualConditions ℱ μ] :
    Measure.IsComplete (μ.trim (ℱ.le 0)) :=
  Measure.IsComplete.mk fun s hs ↦
    h.complete_timeZero s (measure_eq_zero_of_trim_eq_zero (ℱ.le 0) hs)

/-- Helper for Definition 21.22: `UsualConditions` carries the canonical completeness projection
for the initial trimmed measure. -/
theorem usualConditions_initialTrim_isComplete
    (ℱ : Filtration NNReal mΩ) (μ : Measure Ω) [UsualConditions ℱ μ] :
    Measure.IsComplete (μ.trim (ℱ.le 0)) := by
  -- This theorem only re-exposes the completeness instance built from time-zero completeness.
  infer_instance

/-- Helper for Definition 21.22: `UsualConditions` directly exposes that ambient `μ`-null sets are
measurable in the initial `σ`-algebra `ℱ 0`. -/
theorem usualConditions_timeZeroComplete
    (ℱ : Filtration NNReal mΩ) (μ : Measure Ω) [UsualConditions ℱ μ] :
    ∀ s : Set Ω, μ s = 0 → MeasurableSet[ℱ 0] s := by
  -- This is exactly the `complete_timeZero` field carried by `UsualConditions`.
  intro s hs
  exact (inferInstance : UsualConditions ℱ μ).complete_timeZero s hs

/-- Helper for Definition 21.22: if ambient `μ`-null sets are already measurable at time `0`,
then filtration monotonicity makes them measurable at every later time. -/
theorem initialAmbientNullMeasurable_mono
    (ℱ : Filtration NNReal mΩ) (μ : Measure Ω)
    (h0 : ∀ s : Set Ω, μ s = 0 → MeasurableSet[ℱ 0] s)
    (t : NNReal) {s : Set Ω} (hs : μ s = 0) :
    MeasurableSet[ℱ t] s := by
  -- First record measurability at time zero from the assumed completeness bridge.
  have hs0 : MeasurableSet[ℱ 0] s := h0 s hs
  -- Then enlarge the measurable space along filtration monotonicity from `0 ≤ t`.
  exact (ℱ.mono (show (0 : NNReal) ≤ t from bot_le)) s hs0

/-- Helper for Definition 21.22: sets that are null for the initial trimmed measure are measurable
for every later `σ`-algebra in the filtration. -/
theorem measurableSet_of_initialTrimNull
    (ℱ : Filtration NNReal mΩ) (μ : Measure Ω) [UsualConditions ℱ μ] (t : NNReal) {s : Set Ω}
    (hs : (μ.trim (ℱ.le 0)) s = 0) :
    MeasurableSet[ℱ t] s := by
  -- First turn trimmed nullity into ambient nullity using the trim comparison map.
  have hsμ : μ s = 0 := measure_eq_zero_of_trim_eq_zero (ℱ.le 0) hs
  -- Then propagate time-zero measurability forward along the filtration.
  exact initialAmbientNullMeasurable_mono ℱ μ (usualConditions_timeZeroComplete ℱ μ) t hsμ

end Filtration

end MeasureTheory
