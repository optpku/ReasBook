/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.Data

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Determinant

/-- Subtract the fixed margin from the central Laurent coefficient. -/
def shiftedNumerators (p : List ℤ) : List ℤ :=
  Integer.add p (Integer.monomial 256 (-kappaNumerator))

/-- The shifted determinant is formed entirely by exact integer convolution. -/
def determinantVector (A B C : List ℤ) : List ℤ :=
  Integer.subtract (Integer.multiply (shiftedNumerators A) (shiftedNumerators B))
    (Integer.multiply C C.reverse)

/-- Dense rational Laurent expression for the start endpoint determinant. -/
def startDeterminantLaurent : Laurent :=
  rationalLaurent (-512) determinantDenominator startDeterminantNumerators

/-- Dense rational Laurent expression for the lower endpoint determinant. -/
def lowerDeterminantLaurent : Laurent :=
  rationalLaurent (-512) determinantDenominator lowerDeterminantNumerators

/-- The fixed integer margin divided by the common denominator equals κ. -/
lemma kappa_ratio_complex : (kappaNumerator : ℂ) / (quotientDenominator : ℂ) =
    (ADMM.RefinedEndpoint.Data.kappa : ℂ) := by
  have h := congrArg (fun x : ℚ ↦ (x : ℂ)) kappa_ratio
  simpa only [Rat.cast_div, Rat.cast_intCast] using h

/-- A central coefficient shift subtracts exactly the fixed scalar margin. -/
theorem evaluate_shiftedNumerators (p : List ℤ) {z : ℂ} (hz : z ≠ 0) :
    evaluateLaurent (rationalLaurent (-256) quotientDenominator (shiftedNumerators p)) z =
      evaluateLaurent (rationalLaurent (-256) quotientDenominator p) z -
        (ADMM.RefinedEndpoint.Data.kappa : ℂ) := by
  rw [shiftedNumerators, evaluate_rationalLaurent_add _ _ _ _ hz]
  have h := evaluate_rationalLaurent_monomial 256 quotientDenominator (-kappaNumerator) hz
  norm_num only [Nat.cast_ofNat] at h
  rw [h, Int.cast_neg, neg_div, kappa_ratio_complex]
  ring

/-- Dense integer convolution retains the actual shifted quotient determinant. -/
theorem evaluate_determinantVector (A B C : List ℤ) {z : ℂ} (hz : z ≠ 0) :
    evaluateLaurent (rationalLaurent (-512) determinantDenominator (determinantVector A B C)) z =
      (evaluateLaurent (rationalLaurent (-256) quotientDenominator A) z -
        (ADMM.RefinedEndpoint.Data.kappa : ℂ)) *
      (evaluateLaurent (rationalLaurent (-256) quotientDenominator B) z -
        (ADMM.RefinedEndpoint.Data.kappa : ℂ)) -
      evaluateLaurent (rationalLaurent (-256) quotientDenominator C) z *
        evaluateLaurent (rationalLaurent (-256) quotientDenominator C.reverse) z := by
  rw [determinantVector, Integer.subtract, evaluate_rationalLaurent_add _ _ _ _ hz,
    evaluate_rationalLaurent_scale _ _ _ _ hz]
  have hm (p q : List ℤ) := evaluate_rationalLaurent_multiply (-256) (-256)
    quotientDenominator quotientDenominator p q hz
  norm_num only [Int.reduceAdd] at hm
  rw [show determinantDenominator = quotientDenominator * quotientDenominator from rfl]
  rw [hm, hm, evaluate_shiftedNumerators _ hz, evaluate_shiftedNumerators _ hz]
  norm_num
  ring

end ADMM.UnitCircle.LowerCertificate.Determinant
