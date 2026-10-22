/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Assumption_2_3.Parameters

public section

namespace LALM

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

namespace Residual

/-- The scalar aggregation turning primal and multiplier--primal comparison
constants into a squared KKT-residual comparison constant. -/
@[expose] noncomputable def comparisonConstant
    (primalComparison multiplierPrimal penalty : ℝ) : ℝ :=
  primalComparison ^ 2 + multiplierPrimal / penalty ^ 2

/-- The residual comparison aggregation has its defining explicit formula. -/
theorem comparisonConstant_def
    (primalComparison multiplierPrimal penalty : ℝ) :
    comparisonConstant primalComparison multiplierPrimal penalty =
      primalComparison ^ 2 + multiplierPrimal / penalty ^ 2 := rfl

end Residual

/-- The residual comparison constant combines the squared primal comparison
constant with the penalty-scaled multiplier-primal comparison constant. -/
@[expose] noncomputable def residualComparisonConstant (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : ℝ) : ℝ :=
  Residual.comparisonConstant
    (primalComparisonConstant h delta beta rho multiplierBound)
    (multiplierPrimalConstant h delta beta rho multiplierBound) rho

/-- The residual comparison constant has its defining explicit formula. -/
theorem residualComparisonConstant_def (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : ℝ) :
    residualComparisonConstant h delta beta rho multiplierBound =
      primalComparisonConstant h delta beta rho multiplierBound ^ 2 +
        multiplierPrimalConstant h delta beta rho multiplierBound / rho ^ 2 := rfl

end LALM

end
