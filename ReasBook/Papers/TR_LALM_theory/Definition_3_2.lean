/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Definition_3_2.Stochastic

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace KKT.Stochastic

universe u

variable {n m : ℕ} {Ω : Type u} [MeasurableSpace Ω]

/- Definition 3.2 (1): a random point is stochastic `ε`-KKT when it has a random
multiplier on the same probability space satisfying the two mean-square bounds. -/

/- Definition 3.2 (2): a specified random point-multiplier pair is stochastic
`ε`-KKT when its stationarity and feasibility mean squares are at most `ε ^ 2`. -/

/-- Definition 3.2 (3): one bound on the expected squared aggregate residual
certifies a stochastic `ε`-KKT pair. -/
theorem IsApproximatePair.of_residualMeanSquare_le
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {ε : ℝ≥0}
    {x : Ω → EuclideanSpace ℝ (Fin n)}
    {multiplier : Ω → EuclideanSpace ℝ (Fin m)}
    (aemeasurable_point : AEMeasurable x ℙ)
    (aemeasurable_multiplier : AEMeasurable multiplier ℙ)
    (residualMeanSquare_le :
      residualMeanSquare ℙ f c x multiplier ≤ ε ^ 2) :
    IsApproximatePair ℙ f c ε x multiplier := by
  -- Compare each component integrand with their aggregate residual integrand.
  refine IsApproximatePair.ofBounds aemeasurable_point aemeasurable_multiplier ?_ ?_
  · calc
      stationarityMeanSquare ℙ f c x multiplier =
          ∫⁻ ω, ‖KKT.stationarity f c (x ω) (multiplier ω)‖ₑ ^ 2 ∂ℙ :=
        stationarityMeanSquare_def ℙ f c x multiplier
      _ ≤ ∫⁻ ω, ENNReal.ofReal
          (KKT.residual f c (x ω) (multiplier ω) ^ 2) ∂ℙ := by
        refine lintegral_mono (fun ω ↦ ?_)
        rw [ofReal_residual_sq]
        exact le_add_of_nonneg_right zero_le
      _ = residualMeanSquare ℙ f c x multiplier :=
        (residualMeanSquare_def ℙ f c x multiplier).symm
      _ ≤ ε ^ 2 := residualMeanSquare_le
  · calc
      feasibilityMeanSquare ℙ c x = ∫⁻ ω, ‖c (x ω)‖ₑ ^ 2 ∂ℙ :=
        feasibilityMeanSquare_def ℙ c x
      _ ≤ ∫⁻ ω, ENNReal.ofReal
          (KKT.residual f c (x ω) (multiplier ω) ^ 2) ∂ℙ := by
        refine lintegral_mono (fun ω ↦ ?_)
        rw [ofReal_residual_sq]
        exact le_add_of_nonneg_left zero_le
      _ = residualMeanSquare ℙ f c x multiplier :=
        (residualMeanSquare_def ℙ f c x multiplier).symm
      _ ≤ ε ^ 2 := residualMeanSquare_le

end KKT.Stochastic

end
