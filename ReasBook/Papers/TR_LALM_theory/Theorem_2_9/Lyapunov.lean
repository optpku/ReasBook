/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Assumption_2_3.Parameters

public section

open scoped LALM

namespace LALM

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- The uniform lower bound for the fixed-penalty NR-LALM Lyapunov sequence. -/
@[expose] noncomputable def lyapunovLowerBound (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀) : ℝ :=
  h.objectiveLower - params.multiplierBound ^ 2 / (2 * params.rho)

/-- The Lyapunov lower bound is the objective lower bound minus the maximal
multiplier correction. -/
theorem lyapunovLowerBound_def (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀) :
    lyapunovLowerBound h params =
      h.objectiveLower - params.multiplierBound ^ 2 / (2 * params.rho) := rfl

namespace Run

/-- The fixed-penalty NR-LALM Lyapunov sequence associated with a run. -/
@[expose] noncomputable def lyapunov (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) (k : ℕ) : ℝ :=
  ℒ[f, c; params.rho](run.point k, run.multiplier k) +
    (multiplierPrimalConstant h params.delta params.beta params.rho
      params.multiplierBound / params.rho) * ‖run.step (k - 1)‖ ^ 2

/-- The Lyapunov value is the augmented Lagrangian plus the scaled preceding-step
correction. -/
theorem lyapunov_def (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) (k : ℕ) :
    run.lyapunov h params k =
      ℒ[f, c; params.rho](run.point k, run.multiplier k) +
        (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖run.step (k - 1)‖ ^ 2 := rfl

end Run

end LALM

end
