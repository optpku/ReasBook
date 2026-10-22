/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Set Function
open scoped Topology NNReal

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [TopologicalSpace E]
variable {Ω : Type v}

/-- A process indexed by nonnegative time has right-continuous paths if each sample path is right
continuous at every time. -/
def HasRightContinuousPaths (X : ℝ≥0 → Ω → E) : Prop :=
  ∀ ω : Ω, ∀ t : ℝ≥0, ContinuousWithinAt (fun s : ℝ≥0 ↦ X s ω) (Set.Ici t) t

/-- Unfolding `HasRightContinuousPaths` gives the pointwise right-continuity condition. -/
theorem hasRightContinuousPaths_iff (X : ℝ≥0 → Ω → E) :
    HasRightContinuousPaths X ↔
      ∀ ω : Ω, ∀ t : ℝ≥0, ContinuousWithinAt (fun s : ℝ≥0 ↦ X s ω) (Set.Ici t) t :=
  Iff.rfl

/-- Definition 21.21: a path `f : ℝ≥0 → E` is RCLL, or càdlàg, if it is right continuous at every
time and has a strict left limit at every positive time. -/
class IsCadlag (f : ℝ≥0 → E) : Prop where
  /-- The path is right continuous at every time. -/
  right_continuous : ∀ t : ℝ≥0, ContinuousWithinAt f (Set.Ici t) t
  /-- The path has a strict left limit at every positive time. -/
  left_limit : ∀ t : Set.Ioi (0 : ℝ≥0),
    Tendsto f (nhdsWithin (t : ℝ≥0) (Set.Iio (t : ℝ≥0)))
      (𝓝 (Function.leftLim f (t : ℝ≥0)))

/-- A càdlàg path is right continuous. -/
theorem IsCadlag.hasRightContinuous {f : ℝ≥0 → E} (hf : IsCadlag f) :
    ∀ t : ℝ≥0, ContinuousWithinAt f (Set.Ici t) t :=
  hf.right_continuous

/-- A process indexed by nonnegative time has càdlàg paths if each sample path is càdlàg. -/
def HasCadlagPaths (X : ℝ≥0 → Ω → E) : Prop :=
  ∀ ω : Ω, IsCadlag (fun t ↦ X t ω)

/-- Unfolding `HasCadlagPaths` gives the pointwise càdlàg path condition. -/
theorem hasCadlagPaths_iff (X : ℝ≥0 → Ω → E) :
    HasCadlagPaths X ↔ ∀ ω : Ω, IsCadlag (fun t ↦ X t ω) :=
  Iff.rfl

/-- A process with càdlàg paths has right-continuous paths. -/
theorem HasCadlagPaths.hasRightContinuousPaths {X : ℝ≥0 → Ω → E}
    (hX : HasCadlagPaths X) : HasRightContinuousPaths X :=
  fun ω t ↦ (hX ω).hasRightContinuous t

/-- Constant paths are càdlàg. -/
instance instIsCadlag_const (c : E) : IsCadlag (fun _ ↦ c) := by
  refine ⟨fun _ ↦ continuousWithinAt_const, ?_⟩
  intro t
  simpa using
    (show Tendsto (fun _ : ℝ≥0 ↦ c) (nhdsWithin (t : ℝ≥0) (Set.Iio (t : ℝ≥0)))
      (𝓝 (Function.leftLim (fun _ : ℝ≥0 ↦ c) (t : ℝ≥0))) from
      tendsto_leftLim_of_tendsto ⟨c, tendsto_const_nhds⟩)

end ProbabilityTheory
