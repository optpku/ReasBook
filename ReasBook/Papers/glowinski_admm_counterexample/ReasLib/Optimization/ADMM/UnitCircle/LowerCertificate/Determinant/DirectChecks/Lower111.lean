/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectCoefficients

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Determinant

set_option maxRecDepth 16384 in
-- A bounded pure-kernel check of the exact source convolution coefficients.
theorem lowerCheck111 : ∀ i : Fin 8,
    (lowerDeterminantNumerators.getD (888 + i.val) 0 ==
      directDeterminantCoefficient diagonalCoefficient lowerSecondCoefficient lowerCrossCoefficient
        (888 + i.val)) = true := by
  decide +kernel

end ADMM.UnitCircle.LowerCertificate.Determinant
