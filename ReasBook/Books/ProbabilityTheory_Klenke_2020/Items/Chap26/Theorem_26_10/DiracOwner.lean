/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_10.OneDimensional
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_18

open MeasureTheory ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- Shared support API for Theorem 26.10: the chapter's generalized-diffusion owner needs
finite-horizon time admissibility for the drift and diffusion rows, uniformly after deterministic
time shifts. -/
def OneDimensionalGeneralizedDiffusionAdmissible
    (b σ : NNReal → ℝ → ℝ) : Prop :=
  (∀ s : NNReal, ∀ x : ℝ, ∀ T : NNReal,
    IntegrableOn
      (fun u : ℝ ↦ |b (s + u.toNNReal) x|)
      (Set.Icc (0 : ℝ) (T : ℝ))) ∧
    ∀ s : NNReal, ∀ x : ℝ, ∀ T : NNReal,
      IntegrableOn
        (fun u : ℝ ↦ (σ (s + u.toNNReal) x) ^ 2)
        (Set.Icc (0 : ℝ) (T : ℝ))

/-- Shared support API for Theorem 26.10: clause `(1)` should expose one deterministic-start
unique-strong-solution owner theorem that downstream wrappers can import without recreating the
local alias cycle in the target file. -/
theorem diracStrongOwnerCore_ofYamadaWatanabeRegularity
    {b σ : NNReal → ℝ → ℝ} {K α : ℝ}
    (hα_lower : (1 / 2 : ℝ) ≤ α)
    (hα_upper : α ≤ 1)
    (h_time_measurable :
      SDETimeMeasurable (oneDimensionalDrift b) (oneDimensionalDiffusion σ))
    (h_admissible : OneDimensionalGeneralizedDiffusionAdmissible b σ)
    (hb_lipschitz :
      ∀ t : NNReal, ∀ x x' : ℝ, |b t x - b t x'| ≤ K * |x - x'|)
    (hσ_holder :
      ∀ t : NNReal, ∀ x x' : ℝ, |σ t x - σ t x'| ≤ Real.rpow (|x - x'|) α)
    (x0 : ℝ) :
    HasUniqueStrongSolution
      GeneralizedSDEBrownianMotion
      (SolvesStrongGeneralizedSDE (oneDimensionalDiffusion σ) (oneDimensionalDrift b))
      (Measure.dirac (oneDimensionalState x0)) := by
  -- Route correction: the deterministic-start owner now lives in a support module so the target
  -- file can import one stable frontier instead of rebuilding the same local alias cycle.
  -- TODO: reconnect this support theorem to the intended dependency-closed Yamada--Watanabe owner
  -- input for deterministic Dirac starts.
  sorry

end ProbabilityTheory
