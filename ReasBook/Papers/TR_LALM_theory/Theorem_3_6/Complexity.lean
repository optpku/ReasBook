/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Algebra.Order.Floor.Ring
public import TR_LALM_theory.Lemma_3_4.Lyapunov
public import TR_LALM_theory.Lemma_3_5.Residual

public section

open MeasureTheory
open scoped NNReal

namespace LALM.StochasticRun

universe u

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- The stochastic average-gradient-error constant
`Aₑ = 2 * σ_f ^ 2 + D₀ / D₁`. -/
@[expose] noncomputable def errorAverageConstant
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) : ℝ :=
  2 * oracle.noiseLevel ^ 2 + initialStepBound h params / errorStepConstant h params

/-- The average-gradient-error constant has the source's explicit formula. -/
theorem errorAverageConstant_def
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) :
    errorAverageConstant h oracle params =
      2 * oracle.noiseLevel ^ 2 +
        initialStepBound h params / errorStepConstant h params := rfl

/-- The stochastic average-primal-step constant
`Aₚ = 2 * D₁ * σ_f ^ 2 + 2 * D₀`. -/
@[expose] noncomputable def stepAverageConstant
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) : ℝ :=
  2 * errorStepConstant h params * oracle.noiseLevel ^ 2 +
    2 * initialStepBound h params

/-- The average-primal-step constant has the source's explicit formula. -/
theorem stepAverageConstant_def
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) :
    stepAverageConstant h oracle params =
      2 * errorStepConstant h params * oracle.noiseLevel ^ 2 +
        2 * initialStepBound h params := rfl

/-- The direct stochastic residual-complexity constant
`C_st = 2 * C_R_st * (Aₚ + Aₑ)`. -/
@[expose] noncomputable def complexityConstant
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) : ℝ :=
  2 * LALM.stochasticResidualConstant h params.delta params.beta params.rho
      params.multiplierBound *
    (stepAverageConstant h oracle params + errorAverageConstant h oracle params)

/-- The direct stochastic complexity constant has the source's explicit formula. -/
theorem complexityConstant_def
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) :
    complexityConstant h oracle params =
      2 * LALM.stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (stepAverageConstant h oracle params + errorAverageConstant h oracle params) := rfl

/-- The canonical stochastic iteration budget at tolerance `ε`, including two
initial iterations so that the uniform output range is nonempty. -/
@[expose] noncomputable def iterationBudget
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (ε : ℝ≥0) : ℕ :=
  Nat.ceil (complexityConstant h oracle params * (ε : ℝ)⁻¹ ^ 2) + 2

/-- The stochastic iteration budget is the ceiling of the exact residual
threshold, followed by two iterations ensuring a nonempty output range. -/
theorem iterationBudget_def
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (ε : ℝ≥0) :
    iterationBudget h oracle params ε =
      Nat.ceil (complexityConstant h oracle params * (ε : ℝ)⁻¹ ^ 2) + 2 := rfl

/-- The canonical budget is at least two and meets the exact stochastic
residual threshold. -/
theorem iterationBudget_spec
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (ε : ℝ≥0) :
    2 ≤ iterationBudget h oracle params ε ∧
      complexityConstant h oracle params * (ε : ℝ)⁻¹ ^ 2 ≤
        (iterationBudget h oracle params ε : ℝ) - 1 := by
  constructor
  · rw [iterationBudget_def]
    omega
  · rw [iterationBudget_def]
    have hceil := Nat.le_ceil
      (complexityConstant h oracle params * (ε : ℝ)⁻¹ ^ 2)
    push_cast
    linarith

end LALM.StochasticRun

end
