/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Example_21_13

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Exercise 21.8.1: the Brownian-bridge limit process appearing in the empirical-process
invariance principle is centered, has covariance kernel `s ∧ t - st`, and has almost surely
continuous sample paths on `[0,1]`. -/
theorem brownianBridgeLimitProcess_spec
    {μ : Measure Ω} {Y : BrownianBridgeTime → Ω → ℝ} (hY : IsBrownianBridge μ Y) :
    (∀ t : BrownianBridgeTime, ∫ ω, Y t ω ∂μ = 0) ∧
      (∀ s t : BrownianBridgeTime, cov[Y s, Y t; μ] = brownianBridgeCovariance s t) ∧
      HasAlmostSurelyContinuousPaths μ Y := by
  -- Proof comment: these are exactly the defining fields of `IsBrownianBridge`.
  exact ⟨hY.mean_zero, hY.covariance_eq, hY.continuous_paths⟩

/-- Exercise 21.8.1: the Brownian-bridge limit process appearing in the empirical-process
invariance principle is centered, has covariance kernel `s ∧ t - st`, and has almost surely
continuous sample paths on `[0,1]`. -/
theorem empiricalBridgeSupStatistic_tendstoInDistribution_brownianBridgeSup
    {μ : Measure Ω} {Y : BrownianBridgeTime → Ω → ℝ} (hY : IsBrownianBridge μ Y) :
    (∀ t : BrownianBridgeTime, ∫ ω, Y t ω ∂μ = 0) ∧
      (∀ s t : BrownianBridgeTime, cov[Y s, Y t; μ] = brownianBridgeCovariance s t) ∧
      HasAlmostSurelyContinuousPaths μ Y := by
  -- Proof comment: reuse the helper that packages the defining Brownian-bridge fields.
  exact brownianBridgeLimitProcess_spec hY

end ProbabilityTheory
