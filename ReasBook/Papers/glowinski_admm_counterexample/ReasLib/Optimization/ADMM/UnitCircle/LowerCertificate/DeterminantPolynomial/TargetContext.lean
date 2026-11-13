/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.EvalBridge
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.IntegerPolynomials.StartDeterminant
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.IntegerPolynomials.LowerDeterminant

@[expose] public section

set_option maxRecDepth 8192
set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial

def startScale : ℤ := 2

theorem startScale_pos : 0 < startScale := by decide +kernel

theorem startScale_denominator :
    startScale * Data.IntegerPolynomials.StartDeterminant.denominator = Determinant.determinantDenominator := by
  decide +kernel

def startLeftCoefficient (j : ℕ) : ℤ :=
  directChebCoefficient FirstKind512.tree.get 512
    startChebWeight j

def startRightCoefficient (j : ℕ) : ℤ :=
  startScale * Data.IntegerPolynomials.StartDeterminant.coefficients.get j

def lowerScale : ℤ := 2

theorem lowerScale_pos : 0 < lowerScale := by decide +kernel

theorem lowerScale_denominator :
    lowerScale * Data.IntegerPolynomials.LowerDeterminant.denominator = Determinant.determinantDenominator := by
  decide +kernel

def lowerLeftCoefficient (j : ℕ) : ℤ :=
  directChebCoefficient FirstKind512.tree.get 512
    lowerChebWeight j

def lowerRightCoefficient (j : ℕ) : ℤ :=
  lowerScale * Data.IntegerPolynomials.LowerDeterminant.coefficients.get j

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial
