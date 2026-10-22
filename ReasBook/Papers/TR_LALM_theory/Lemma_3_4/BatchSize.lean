/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Lemma_3_4.Lyapunov

public section

open MeasureTheory

namespace SPIDER

universe u

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- An inner SPIDER batch size is sufficient for the stochastic NR-LALM bounds
when it absorbs the accumulated gradient-error contribution. -/
def IsSufficientInnerBatchSize (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q b : ℕ+) : Prop :=
  (b : ℝ) ≥ 2 * LALM.StochasticRun.errorStepConstant h params * Q *
    oracle.meanSquareLipschitz ^ 2

/-- Sufficient inner batch size is exactly the batch inequality used in the
stochastic NR-LALM mean-square estimates. -/
theorem isSufficientInnerBatchSize_iff
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q b : ℕ+) :
    IsSufficientInnerBatchSize h oracle params Q b ↔
      (b : ℝ) ≥ 2 * LALM.StochasticRun.errorStepConstant h params * Q *
        oracle.meanSquareLipschitz ^ 2 := Iff.rfl

end SPIDER

end
