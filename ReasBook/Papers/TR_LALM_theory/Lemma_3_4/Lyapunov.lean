/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Assumption_2_5.Region
public import TR_LALM_theory.Lemma_3_3.Iteration
public import TR_LALM_theory.Lemma_3_4.Multiplier
public import TR_LALM_theory.Theorem_2_9.Lyapunov

public section

open MeasureTheory
open scoped LALM

namespace LALM.StochasticRun

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

/-- The pathwise stochastic NR-LALM Lyapunov value at an iteration. -/
@[expose] noncomputable def lyapunov
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) : ℝ :=
  ℒ[f, c; params.rho](run.point k ω, run.multiplier k ω) +
    (multiplierPrimalConstant h params.delta params.beta params.rho
      params.multiplierBound / params.rho) * ‖run.step (k - 1) ω‖ ^ 2

/-- The stochastic Lyapunov value is the augmented Lagrangian plus the scaled
preceding-step correction. -/
theorem lyapunov_def
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    run.lyapunov k ω =
      ℒ[f, c; params.rho](run.point k ω, run.multiplier k ω) +
        (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖run.step (k - 1) ω‖ ^ 2 := rfl

/-- The coefficient controlling the two consecutive stochastic gradient-error
terms in Lyapunov descent. -/
@[expose] noncomputable def lyapunovErrorConstant (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀) : ℝ :=
  2 / params.beta + LALM.multiplierErrorConstant h / params.rho

/-- The Lyapunov error coefficient has the source formula `C_eˢ = 2 / β + C_λ,e / ρ`. -/
theorem lyapunovErrorConstant_def (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀) :
    lyapunovErrorConstant h params =
      2 / params.beta + LALM.multiplierErrorConstant h / params.rho := rfl

/-- The initial allowance for the accumulated stochastic primal-step bound. -/
@[expose] noncomputable def initialStepBound (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀) : ℝ :=
  params.delta ^ 2 +
    4 * (LALM.initialPotentialBound h params - LALM.lyapunovLowerBound h params) /
      params.beta

/-- The initial step allowance has the source formula for `D₀`. -/
theorem initialStepBound_def (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀) :
    initialStepBound h params =
      params.delta ^ 2 +
        4 * (LALM.initialPotentialBound h params - LALM.lyapunovLowerBound h params) /
          params.beta := rfl

/-- The coefficient transferring accumulated gradient error to accumulated
primal-step size. -/
@[expose] noncomputable def errorStepConstant (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀) : ℝ :=
  8 * lyapunovErrorConstant h params / params.beta

/-- The accumulated error-step coefficient has the source formula for `D₁`. -/
theorem errorStepConstant_def (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀) :
    errorStepConstant h params =
      8 * lyapunovErrorConstant h params / params.beta := rfl

end LALM.StochasticRun

end
