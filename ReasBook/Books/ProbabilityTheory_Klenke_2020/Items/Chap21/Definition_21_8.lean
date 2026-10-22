/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Definition 21.8: a real-valued process on `[0,∞)` is a Brownian motion under `μ` if it starts
from `0`, has independent stationary increments, each positive-time marginal is the centered
Gaussian law with variance `t`, and its sample paths are almost surely continuous. -/
class IsBrownianMotion (μ : Measure Ω) (B : NNReal → Ω → ℝ) : Prop where
  /-- A Brownian motion starts at the constant value `0`. -/
  zero : B 0 = 0
  /-- Brownian motion has independent increments. -/
  indepIncrements : HasIndepIncrements B μ
  /-- Brownian motion has stationary increments. -/
  stationaryIncrements : HasStationaryIncrements B μ
  /-- For every positive time, the marginal law is centered Gaussian with variance `t`. -/
  gaussian_marginal : ∀ ⦃t : NNReal⦄, 0 < t → HasLaw (B t) (gaussianReal 0 t) μ
  /-- Brownian motion has almost surely continuous sample paths. -/
  continuous_paths : HasAlmostSurelyContinuousPaths μ B

namespace IsBrownianMotion

/-- Helper for Definition 21.8: every deterministic-time marginal of a Brownian motion is almost
everywhere measurable. -/
theorem aemeasurable
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (t : NNReal) :
    AEMeasurable (B t) μ := by
  -- Route correction: the Brownian fields give a law statement and almost-sure path continuity,
  -- which support AE measurability of each time marginal, not pointwise measurability.
  by_cases ht : t = 0
  · -- At time `0`, the process is the constant-zero function.
    subst t
    have hzeroFun : B 0 = (0 : Ω → ℝ) := by
      simpa using hB.zero
    rw [hzeroFun]
    refine ⟨0, measurable_zero, ?_⟩
    exact ae_eq_refl (0 : Ω → ℝ)
  · -- For positive times, AE measurability comes directly from the Gaussian law field.
    exact (hB.gaussian_marginal (pos_iff_ne_zero.mpr ht)).aemeasurable

/-- Helper for Definition 21.8: every deterministic-time marginal of a Brownian motion is almost
everywhere strongly measurable. -/
theorem aestronglyMeasurable
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (t : NNReal) :
    AEStronglyMeasurable (B t) μ := by
  -- Upgrade the AE measurability bridge to the standard AE strong measurability companion.
  exact (hB.aemeasurable t).aestronglyMeasurable

/-- Helper for Definition 21.8: every deterministic-time marginal of a Brownian motion is strongly
measurable. -/
theorem stronglyMeasurable
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (t : NNReal) :
    StronglyMeasurable (B t) := by
  -- Route correction: downstream Brownian filtrations and path-map owners still need the original
  -- pointwise measurability theorem, so the unresolved task is to upgrade the AE Gaussian-law
  -- measurability data to an actual deterministic-time measurable version.
  -- TODO: rebuild the measurable continuous-version bridge promised by the Chapter 21 Brownian
  -- owner API, then replace this placeholder by the restored pointwise proof.
  sorry

/-- A Brownian motion is carried by a probability measure. -/
theorem isProbabilityMeasure
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    IsProbabilityMeasure μ := by
  let h₁ : HasLaw (B 1) (gaussianReal 0 1) μ := hB.gaussian_marginal (by positivity)
  have hgauss : IsProbabilityMeasure (gaussianReal 0 1) := inferInstance
  exact h₁.isProbabilityMeasure_iff.mpr hgauss

end IsBrownianMotion

end ProbabilityTheory
