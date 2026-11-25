/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.PairedShift
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.DiagonalChebyshevContext

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

/-- The integer Chebyshev transform is tied to the actual diagonal quotient
and the same fixed margin used by the public lower-certificate claim. -/
theorem diagonalCheb_source_eval (x : ℝ) :
    (realPolynomial Division.startDiagonalQuotient).eval x -
      (ADMM.RefinedEndpoint.Data.kappa : ℝ) =
      evaluate (IntegerCoefficients.toRational Data.diagonalChebPolynomial) x /
        Leaves.diagonalDenominator := by
  rw [realPolynomial_perm Data.diagonalPaired_perm, Data.diagonalPaired]
  exact paired_shift_eval Data.chebyshevTree.get 256 Data.chebyshevCache_valid
    256 (by rfl) (Data.diagonalQuotientIntegers.get 256) Leaves.diagonalDenominator
    (fun i ↦ Data.diagonalQuotientIntegers.get (i.val + 257))
    (fun i ↦ Data.diagonalQuotientIntegers.get (255 - i.val))
    (fun i ↦ Data.diagonalChebWeights.get i) ADMM.RefinedEndpoint.Data.kappa
    Data.diagonalChebWeights_zero Data.diagonalChebWeights_pair x

end ADMM.UnitCircle.LowerCertificate
