/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.Data

@[expose] public section

set_option maxRecDepth 16384

namespace ADMM.UnitCircle.LowerCertificate.Determinant

theorem diagonal_representation :
    rationalLaurent (-256) quotientDenominator diagonalNumerators =
      Division.startDiagonalQuotient := by decide +kernel

theorem diagonal_star_representation :
    rationalLaurent (-256) quotientDenominator diagonalNumerators.reverse =
      laurentStar Division.startDiagonalQuotient.reverse := by decide +kernel

theorem diagonal_length : diagonalNumerators.length = 513 := by decide +kernel

theorem startSecond_representation :
    rationalLaurent (-256) quotientDenominator startSecondNumerators =
      Division.startSecondQuotient := by decide +kernel

theorem startSecond_star_representation :
    rationalLaurent (-256) quotientDenominator startSecondNumerators.reverse =
      laurentStar Division.startSecondQuotient.reverse := by decide +kernel

theorem startSecond_length : startSecondNumerators.length = 513 := by decide +kernel

theorem startCross_representation :
    rationalLaurent (-256) quotientDenominator startCrossNumerators =
      Division.startCrossQuotient := by decide +kernel

theorem startCross_star_representation :
    rationalLaurent (-256) quotientDenominator startCrossNumerators.reverse =
      laurentStar Division.startCrossQuotient.reverse := by decide +kernel

theorem startCross_length : startCrossNumerators.length = 513 := by decide +kernel

theorem lowerSecond_representation :
    rationalLaurent (-256) quotientDenominator lowerSecondNumerators =
      Division.lowerSecondQuotient := by decide +kernel

theorem lowerSecond_star_representation :
    rationalLaurent (-256) quotientDenominator lowerSecondNumerators.reverse =
      laurentStar Division.lowerSecondQuotient.reverse := by decide +kernel

theorem lowerSecond_length : lowerSecondNumerators.length = 513 := by decide +kernel

theorem lowerCross_representation :
    rationalLaurent (-256) quotientDenominator lowerCrossNumerators =
      Division.lowerCrossQuotient := by decide +kernel

theorem lowerCross_star_representation :
    rationalLaurent (-256) quotientDenominator lowerCrossNumerators.reverse =
      laurentStar Division.lowerCrossQuotient.reverse := by decide +kernel

theorem lowerCross_length : lowerCrossNumerators.length = 513 := by decide +kernel

theorem diagonal_symmetric : diagonalNumerators.reverse = diagonalNumerators := by decide +kernel

theorem startSecond_symmetric : startSecondNumerators.reverse = startSecondNumerators := by decide +kernel

theorem lowerSecond_symmetric : lowerSecondNumerators.reverse = lowerSecondNumerators := by decide +kernel

end ADMM.UnitCircle.LowerCertificate.Determinant
