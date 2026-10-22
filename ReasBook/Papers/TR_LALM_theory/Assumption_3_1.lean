/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Assumption_2_1.Regularity
public import TR_LALM_theory.Assumption_3_1.Oracle

public section

open MeasureTheory

universe u

variable {n m : ℕ} {Ω : Type u} [MeasurableSpace Ω]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/- Assumption 3.1: On the region from `EqualityConstrained.Regularity f c`, a
stochastic first-order oracle supplies a sampled objective, jointly measurable
sample gradients, expectation and unbiased-gradient identities, and uniform
noise and mean-square Lipschitz bounds. -/

/- The companion specification exposes all conditions bundled by the oracle. -/

end
