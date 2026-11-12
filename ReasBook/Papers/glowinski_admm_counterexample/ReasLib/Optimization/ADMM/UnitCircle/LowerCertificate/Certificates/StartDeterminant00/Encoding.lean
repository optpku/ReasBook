/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.StartDeterminant00.Data
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.IntegerEncodingBounds

@[expose] public section

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate.Certificates.StartDeterminant00

open IntegerEncoding

-- Python proposes these magnitudes; every needed inequality is kernel checked.
def encodingInputBound : ℤ := 2 ^ 1032
def encodingBernsteinBound : ℤ := 2 ^ 2153
def encodingRadius : ℤ := 8
def encodingBase : ℤ := 2 ^ 4805

theorem encoding_input_bound : ∀ k : Fin 513,
    |Data.IntegerPolynomials.StartDeterminant.coefficients.get k| ≤ encodingInputBound := by
  decide +kernel

theorem encoding_bernstein_bound : ∀ k : Fin 513,
    |bernsteinTree.get k| ≤ encodingBernsteinBound := by
  decide +kernel

theorem encoding_base_large :
    2 * commonBound 512 encodingInputBound encodingBernsteinBound encodingRadius
      (8) bernsteinDenominator < encodingBase := by
  decide +kernel

def encodingLeft : ℤ := bernsteinDenominator *
  homogeneousHorner ((-8) + (1 : ℤ) * encodingBase) (8)
    (List.ofFn (fun k : Fin 513 ↦ Data.IntegerPolynomials.StartDeterminant.coefficients.get k))

def encodingRight : ℤ := scaleFactor *
  homogeneousHorner encodingBase (1 - encodingBase)
    (List.ofFn (fun k : Fin 513 ↦ bernsteinTree.get k * (Data.choose 512 k : ℤ)))

-- One exact computation covers the entire polynomial, including every coefficient.
theorem encoding_homogeneous_identity : encodingLeft = encodingRight := by
  decide +kernel

/-- This is the exact coefficient-list identity consumed by the original
Bernstein positivity proof, derived from a bounded injective encoding. -/
theorem encoded_semantic_identity :
    IntegerCoefficients.scale bernsteinDenominator
      (IntegerCoefficients.affine 512 (fun k ↦ Data.IntegerPolynomials.StartDeterminant.coefficients.get k) (-8) 1 8) =
    IntegerCoefficients.scale ((8 : ℤ) ^ 512)
      (IntegerCoefficients.directExpansion Data.choose Data.signPower
        512 (fun k ↦ bernsteinTree.get k)) := by
  apply scaled_identity_of_homogeneous_eq Data.choose Data.signPower
    Data.choose_correct Data.signPower_correct 512
    (fun k ↦ Data.IntegerPolynomials.StartDeterminant.coefficients.get k) (fun k ↦ bernsteinTree.get k)
    (P := encodingInputBound) (C := encodingBernsteinBound) (R := encodingRadius)
    (b := encodingBase)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact encoding_input_bound
  · exact encoding_bernstein_bound
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact encoding_base_large
  · simpa only [encodingLeft, encodingRight, scaleFactor_correct] using
      encoding_homogeneous_identity

end ADMM.UnitCircle.LowerCertificate.Certificates.StartDeterminant00
