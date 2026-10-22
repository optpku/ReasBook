/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Lemma_3_4.Multiplier

public section

namespace LALM

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- The stochastic KKT-residual constant determined by the primal, multiplier,
and gradient-error comparison coefficients. -/
@[expose]
noncomputable def stochasticResidualConstant (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : ℝ) : ℝ :=
  max
    (2 * primalComparisonConstant h delta beta rho multiplierBound ^ 2 +
      multiplierPrimalConstant h delta beta rho multiplierBound / rho ^ 2)
    (2 + multiplierErrorConstant h / rho ^ 2)

/-- The stochastic residual constant has its defining maximum formula. -/
theorem stochasticResidualConstant_def (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : ℝ) :
    stochasticResidualConstant h delta beta rho multiplierBound =
      max
        (2 * primalComparisonConstant h delta beta rho multiplierBound ^ 2 +
          multiplierPrimalConstant h delta beta rho multiplierBound / rho ^ 2)
        (2 + multiplierErrorConstant h / rho ^ 2) := rfl

end LALM

end
