/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Division.ActualDiagonal
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Division.Checks.StartSecond
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Division.Checks.StartCross
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Division.Checks.LowerSecond
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Division.Checks.LowerCross

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Division

theorem start_second_entry_division {z : ℂ} (hz : ‖z‖ = 1) :
    supplySymbol paperWeights 1 ((377 / 200 : ℚ) : ℝ) z 1 1 =
      (Complex.normSq (delaySymbol 1 z) : ℂ) * evaluateLaurent startSecondQuotient z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [← evaluate_fastSecond (377 / 200) normalizedLag0 hz (evaluate_normalizedLag0 z),
    evaluate_eq_of_normalForm divisionStartSecond z,
    evaluateLaurent_multiply _ _ hz0, evaluate_delayNorm_normSq hz]

theorem start_cross_entry_division {z : ℂ} (hz : ‖z‖ = 1) :
    supplySymbol paperWeights 1 ((377 / 200 : ℚ) : ℝ) z 0 1 =
      (Complex.normSq (delaySymbol 1 z) : ℂ) * evaluateLaurent startCrossQuotient z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [← evaluate_fastCross (377 / 200) normalizedLag0 normalizedLag1 hz
    (evaluate_normalizedLag0 z) (evaluate_normalizedLag1 z),
    evaluate_eq_of_normalForm divisionStartCross z,
    evaluateLaurent_multiply _ _ hz0, evaluate_delayNorm_normSq hz]

theorem lower_second_entry_division {z : ℂ} (hz : ‖z‖ = 1) :
    supplySymbol paperWeights 1 ((75475298801 / 40000000000 : ℚ) : ℝ) z 1 1 =
      (Complex.normSq (delaySymbol 1 z) : ℂ) * evaluateLaurent lowerSecondQuotient z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [← evaluate_fastSecond (75475298801 / 40000000000) normalizedLag0 hz
    (evaluate_normalizedLag0 z), evaluate_eq_of_normalForm divisionLowerSecond z,
    evaluateLaurent_multiply _ _ hz0, evaluate_delayNorm_normSq hz]

theorem lower_cross_entry_division {z : ℂ} (hz : ‖z‖ = 1) :
    supplySymbol paperWeights 1 ((75475298801 / 40000000000 : ℚ) : ℝ) z 0 1 =
      (Complex.normSq (delaySymbol 1 z) : ℂ) * evaluateLaurent lowerCrossQuotient z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [← evaluate_fastCross (75475298801 / 40000000000) normalizedLag0 normalizedLag1 hz
    (evaluate_normalizedLag0 z) (evaluate_normalizedLag1 z),
    evaluate_eq_of_normalForm divisionLowerCross z,
    evaluateLaurent_multiply _ _ hz0, evaluate_delayNorm_normSq hz]

end ADMM.UnitCircle.LowerCertificate.Division
