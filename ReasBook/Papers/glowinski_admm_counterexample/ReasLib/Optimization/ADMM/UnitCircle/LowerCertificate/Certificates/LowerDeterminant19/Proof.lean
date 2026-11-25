/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant19.Encoding

@[expose] public section

set_option maxRecDepth 8192
set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant19

theorem semantic_identity :
    IntegerCoefficients.scale bernsteinDenominator
      (IntegerCoefficients.affine 512 (fun k ↦ Data.IntegerPolynomials.LowerDeterminant.coefficients.get k) (183) 1 256) =
    IntegerCoefficients.scale ((256 : ℤ) ^ 512)
      (IntegerCoefficients.directExpansion Data.choose Data.signPower
        512 (fun k ↦ bernsteinTree.get k)) :=
  encoded_semantic_identity

theorem positive_unit (t : unitInterval) :
    0 < evaluate (List.ofFn (fun k : Fin 513 ↦ (Data.IntegerPolynomials.LowerDeterminant.coefficients.get k : ℚ)))
      ((((183 : ℤ) : ℚ) / (256 : ℤ) : ℚ) +
        ((((1 : ℤ) : ℚ) / (256 : ℤ) : ℚ) : ℝ) * (t : ℝ)) := by
  exact IntegerCoefficients.positive_affine_direct Data.choose Data.signPower
    Data.choose_correct Data.signPower_correct 512 (fun k ↦ Data.IntegerPolynomials.LowerDeterminant.coefficients.get k)
    (fun k ↦ bernsteinTree.get k) (183) 1 256 bernsteinDenominator
    (by decide +kernel) bernsteinDenominator_pos coefficients_pos semantic_identity t

theorem positive {x : ℝ} (hx : x ∈ Set.Icc ((183 / 256) : ℝ) ((23 / 32) : ℝ)) :
    0 < evaluate Data.LowerDeterminant x := by
  let t : unitInterval := ⟨(256 : ℝ) * x - (183), by
    constructor <;> norm_num at * <;> linarith [hx.1, hx.2]⟩
  have h := positive_unit t
  have ht : ((((183 : ℤ) : ℚ) / (256 : ℤ) : ℚ) : ℝ) +
      ((((1 : ℤ) : ℚ) / (256 : ℤ) : ℚ) : ℝ) * (t : ℝ) = x := by
    dsimp [t]
    norm_num
    ring
  rw [ht] at h
  rw [Data.IntegerPolynomials.LowerDeterminant.roundtrip, evaluate_scale]
  apply mul_pos _ h
  have hd : (0 : ℤ) < Data.IntegerPolynomials.LowerDeterminant.denominator := by decide +kernel
  have hdq : (0 : ℚ) < Data.IntegerPolynomials.LowerDeterminant.denominator := by exact_mod_cast hd
  exact Rat.cast_pos.mpr (one_div_pos.mpr hdq)

end ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant19
