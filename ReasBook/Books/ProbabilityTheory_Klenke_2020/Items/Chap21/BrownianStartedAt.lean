/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Brownian motion under `μ` started from `x`: the process has measurable deterministic-time
coordinates, starts at `x` almost surely, has independent stationary increments, each
positive-time marginal is Gaussian with mean `x` and variance `t`, and its sample paths are
almost surely continuous. -/
class IsBrownianMotionStartedAt (μ : Measure Ω) (B : NNReal → Ω → ℝ) (x : ℝ) : Prop where
  /-- Every deterministic-time coordinate of the Brownian process is strongly measurable. -/
  stronglyMeasurable : ∀ t, StronglyMeasurable (B t)
  /-- The process starts from the state `x` almost surely. -/
  start : μ (B 0 ⁻¹' {x}) = 1
  /-- Brownian motion has independent increments. -/
  indepIncrements : HasIndepIncrements B μ
  /-- Brownian motion has stationary increments. -/
  stationaryIncrements :
    ∀ r s t : NNReal,
      IdentDistrib
        (fun ω ↦ B ((s + t) + r) ω - B (t + r) ω)
        (fun ω ↦ B (s + r) ω - B r ω)
        μ μ
  /-- For every positive time, the time-`t` marginal is Gaussian with mean `x` and variance `t`. -/
  gaussian_marginal : ∀ ⦃t : NNReal⦄, 0 < t → HasLaw (B t) (gaussianReal x t) μ
  /-- Brownian motion has almost surely continuous sample paths. -/
  continuous_paths : HasAlmostSurelyContinuousPaths μ B

namespace IsBrownianMotionStartedAt

/-- Helper for Brownian motion started at a point: the Brownian path map into `NNReal → ℝ` is
measurable. -/
theorem measurable_processPath
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} {x : ℝ}
    (hB : IsBrownianMotionStartedAt μ B x) :
    Measurable (processPath B) := by
  exact measurable_pi_lambda _ fun t ↦ (hB.stronglyMeasurable t).measurable

/-- A Brownian motion started at `x` is carried by a probability measure. -/
theorem isProbabilityMeasure
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} {x : ℝ}
    (hB : IsBrownianMotionStartedAt μ B x) :
    IsProbabilityMeasure μ := by
  let h₁ : HasLaw (B 1) (gaussianReal x 1) μ := hB.gaussian_marginal (by positivity)
  have hgauss : IsProbabilityMeasure (gaussianReal x 1) := inferInstance
  exact h₁.isProbabilityMeasure_iff.mpr hgauss

end IsBrownianMotionStartedAt

-- Proof sketch: if `B` is standard Brownian motion, then `B 0 = 0` pointwise, so the starting
-- law at time `0` is the Dirac mass at `0`; the remaining Brownian fields are exactly the
-- corresponding fields already stored in `IsBrownianMotion`.
/-- A standard Brownian motion is Brownian motion started from `0`. -/
instance {μ : Measure Ω} {B : NNReal → Ω → ℝ} [IsBrownianMotion μ B] :
    IsBrownianMotionStartedAt μ B 0 := by
  have hprob : IsProbabilityMeasure μ :=
    IsBrownianMotion.isProbabilityMeasure ‹IsBrownianMotion μ B›
  -- The standard Brownian owner fields already match the started-at-zero data.
  refine
    { stronglyMeasurable := ‹IsBrownianMotion μ B›.stronglyMeasurable
      start := ?_
      indepIncrements := ‹IsBrownianMotion μ B›.indepIncrements
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ‹IsBrownianMotion μ B›.continuous_paths }
  · -- The pointwise initial condition turns the time-zero law into the Dirac mass at `0`.
    have hpreimage : B 0 ⁻¹' ({0} : Set ℝ) = Set.univ := by
      ext ω
      simp [‹IsBrownianMotion μ B›.zero]
    rw [hpreimage]
    simp
  · -- The started-at-zero stationary-increment field is exactly the Brownian one.
    intro r s t
    exact ‹IsBrownianMotion μ B›.stationaryIncrements r s t
  · -- The positive-time Gaussian marginals agree verbatim with the Brownian owner field.
    intro t ht
    simpa using ‹IsBrownianMotion μ B›.gaussian_marginal ht

/-- Helper for Brownian motion started at a point: the time-zero coordinate equals the starting
point almost surely, provided the time-zero coordinate is measurable. -/
lemma brownianStart_ae_eq_const_of_measurable
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} {x : ℝ}
    (hmeas0 : Measurable (B 0))
    (hB : IsBrownianMotionStartedAt μ B x) :
    B 0 =ᵐ[μ] fun _ ↦ x := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hstartMeas : Measurable (fun ω ↦ B 0 ω = x) := hmeas0.eq measurable_const
  -- Convert the starting-law axiom into the corresponding almost-sure equality.
  change ∀ᵐ ω ∂μ, B 0 ω = x
  rw [ae_iff_prob_eq_one]
  · simpa using hB.start
  · exact hstartMeas

end ProbabilityTheory
