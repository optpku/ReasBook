/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Probability.ConditionalProbability
public import TR_LALM_theory.Theorem_3_6.UniformOutput
public import TR_LALM_theory.Theorem_3_7.Localization

public section

open MeasureTheory
open scoped ENNReal

namespace LALM.StochasticRun.UniformOutput

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : LALM.Parameters h x₀ multiplier₀} {Q B b : ℕ+}

/-- The squared KKT residual mean of the independent uniform output, conditioned
on survival of the underlying run through iteration `K`. -/
@[expose] noncomputable def conditionalResidualMeanSquare
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (hK : 2 ≤ K) (X : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  KKT.Stochastic.residualMeanSquare
    (ProbabilityTheory.cond (measure K hK ℙ)
      (Set.univ ×ˢ Localization.survivalEvent run X K)) f c
    (point run) (multiplier run)

/-- The conditional output residual uses the product law conditioned on the lifted
survival event. -/
theorem conditionalResidualMeanSquare_def
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (hK : 2 ≤ K) (X : Set (EuclideanSpace ℝ (Fin n))) :
    conditionalResidualMeanSquare run K hK X =
      KKT.Stochastic.residualMeanSquare
        (ProbabilityTheory.cond (measure K hK ℙ)
          (Set.univ ×ˢ Localization.survivalEvent run X K)) f c
        (point run) (multiplier run) := rfl

/-- Conditioning the product output law on survival is division of the
survival-restricted residual integral by the survival probability. -/
theorem conditionalResidualMeanSquare_eq_inv_mul_setLIntegral
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (hK : 2 ≤ K) (X : Set (EuclideanSpace ℝ (Fin n))) :
    conditionalResidualMeanSquare run K hK X =
      (ℙ (Localization.survivalEvent run X K))⁻¹ *
        ∫⁻ output in
            Set.univ ×ˢ Localization.survivalEvent run X K,
          ENNReal.ofReal
            (KKT.residual f c (point run output) (multiplier run output) ^ 2)
          ∂measure K hK ℙ := by
  rw [conditionalResidualMeanSquare_def,
    KKT.Stochastic.residualMeanSquare_def, ProbabilityTheory.cond,
    lintegral_smul_measure, smul_eq_mul]
  congr 1
  rw [measure_def, Measure.prod_prod, measure_univ, one_mul]

end LALM.StochasticRun.UniformOutput

end

open LALM.StochasticRun
