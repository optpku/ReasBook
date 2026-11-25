/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Division.Arithmetic

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Division

open ADMM.RefinedEndpoint.Data

def delayNorm : Laurent := [(-1, -1), (0, 2), (1, -1)]

def realPartLaurent (p : Laurent) : Laurent := laurentScale (1 / 2) (p ++ laurentStar p)

def fastDiagonal (p : Laurent) : Laurent :=
  realPartLaurent (laurentMultiply [(0, 1), (1, -1)] p)

def fastSecond (γ : ℚ) (p : Laurent) : Laurent :=
  realPartLaurent (laurentMultiply [(0, 2 - γ), (1, γ - 1), (-1, -1)] p) ++
    laurentScale (-epsilon) delayNorm

def fastCross (γ : ℚ) (p q : Laurent) : Laurent :=
  laurentScale (1 / 2) (laurentMultiply delayNorm p ++
    laurentMultiply [(0, 1), (-1, γ - 1)] (laurentStar p ++ laurentScale (-1) (laurentStar q)))

/-- Normalization by short Laurent factors exposes only adjacent source
coefficients, avoiding repeated expansion of the full normal/point expression. -/
theorem coefficient_fastDiagonal (p : Laurent) (j : ℤ) :
    laurentCoefficient (fastDiagonal p) j =
      (laurentCoefficient p j - laurentCoefficient p (j - 1) +
        laurentCoefficient p (-j) - laurentCoefficient p (-j - 1)) / 2 := by
  simp only [fastDiagonal, realPartLaurent, coefficient_scale, coefficient_append,
    coefficient_star, coefficient_multiply_cons, coefficient_multiply_nil]
  simp only [Int.sub_zero, one_mul, neg_one_mul, add_zero]
  ring

theorem coefficient_fastSecond (γ : ℚ) (p : Laurent) (j : ℤ) :
    laurentCoefficient (fastSecond γ p) j =
      ((2 - γ) * (laurentCoefficient p j + laurentCoefficient p (-j)) +
        (γ - 1) * (laurentCoefficient p (j - 1) + laurentCoefficient p (-j - 1)) -
        (laurentCoefficient p (j + 1) + laurentCoefficient p (-j + 1))) / 2 -
      epsilon * laurentCoefficient delayNorm j := by
  simp only [fastSecond, realPartLaurent, coefficient_scale, coefficient_append,
    coefficient_star, coefficient_multiply_cons, coefficient_multiply_nil]
  simp only [Int.sub_zero, sub_neg_eq_add, one_mul, neg_one_mul, add_zero]
  ring

theorem coefficient_fastCross (γ : ℚ) (p q : Laurent) (j : ℤ) :
    laurentCoefficient (fastCross γ p q) j =
      (2 * laurentCoefficient p j - laurentCoefficient p (j - 1) -
        laurentCoefficient p (j + 1) + laurentCoefficient p (-j) - laurentCoefficient q (-j) +
        (γ - 1) * (laurentCoefficient p (-j - 1) - laurentCoefficient q (-j - 1))) / 2 := by
  simp only [fastCross, delayNorm, coefficient_scale, coefficient_append,
    coefficient_star, coefficient_multiply_cons, coefficient_multiply_nil]
  simp only [Int.sub_zero, sub_neg_eq_add, neg_sub, neg_neg, one_mul, neg_one_mul, add_zero]
  have hj : -(j + 1) = -j - 1 := by omega
  simp only [hj]
  ring

lemma evaluate_delayNorm {z : ℂ} (hz : ‖z‖ = 1) :
    evaluateLaurent delayNorm z = delaySymbol 1 z * star (delaySymbol 1 z) := by
  have hzinv : z⁻¹ = star z := by
    simpa only [Complex.star_def] using Complex.inv_eq_conj hz
  simp only [delayNorm, evaluateLaurent_cons, evaluateLaurent_nil, Rat.cast_neg,
    Rat.cast_one, Rat.cast_ofNat, zpow_neg_one, zpow_zero, zpow_one, mul_one, add_zero,
    delaySymbol, Complex.ofReal_one, one_mul, star_sub, star_one]
  have hstar : star z⁻¹ = z := by rw [hzinv, star_star]
  rw [hstar]
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  field_simp [hz0]
  ring

lemma evaluate_realPartLaurent (p : Laurent) {z : ℂ} (hz : ‖z‖ = 1) :
    evaluateLaurent (realPartLaurent p) z =
      (1 / 2 : ℂ) * (evaluateLaurent p z + star (evaluateLaurent p z)) := by
  simp only [realPartLaurent, evaluateLaurent_scale, evaluateLaurent_append,
    evaluateLaurent_star _ hz, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]

/-- The short coefficient formulas retain the exact actual supply entry. -/
theorem evaluate_fastDiagonal (p : Laurent) {z : ℂ} (hz : ‖z‖ = 1)
    (hp : evaluateLaurent p z = lagMultiplier paperWeights 1 z 0) (γ : ℚ) :
    evaluateLaurent (fastDiagonal p) z = supplySymbol paperWeights 1 γ z 0 0 := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hzinv : z⁻¹ = star z := by
    simpa only [Complex.star_def] using Complex.inv_eq_conj hz
  simp only [fastDiagonal, evaluate_realPartLaurent _ hz,
    evaluateLaurent_multiply _ _ hz0, hp]
  simp [supplySymbol, hermitianPart, rawSupplySymbol, normalRow, pointRow,
    Fin.sum_univ_two, residualCoordinateMatrix, delaySymbol, hzinv]
  ring


lemma evaluate_secondFactor (γ : ℚ) {z : ℂ} (hz : ‖z‖ = 1) :
    evaluateLaurent [(0, 2 - γ), (1, γ - 1), (-1, -1)] z =
      star (multiplierSymbol 1 γ z) * delaySymbol 1 z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hzinv : z⁻¹ = star z := by
    simpa only [Complex.star_def] using Complex.inv_eq_conj hz
  have hstar : star z⁻¹ = z := by rw [hzinv, star_star]
  simp only [evaluateLaurent_cons, evaluateLaurent_nil, Rat.cast_sub, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_neg, zpow_zero, zpow_one, zpow_neg_one, mul_one, add_zero,
    multiplierSymbol, delaySymbol, Complex.ofReal_one, one_mul, star_add, star_mul,
    star_sub, star_one, hstar]
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_ratCast, map_ratCast]
  field_simp [hz0]
  ring

theorem evaluate_fastSecond (γ : ℚ) (p : Laurent) {z : ℂ} (hz : ‖z‖ = 1)
    (hp : evaluateLaurent p z = lagMultiplier paperWeights 1 z 0) :
    evaluateLaurent (fastSecond γ p) z = supplySymbol paperWeights 1 γ z 1 1 := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hnorm : delaySymbol 1 z * star (delaySymbol 1 z) =
      (Complex.normSq (delaySymbol 1 z) : ℂ) := by
    simpa only [Complex.star_def] using Complex.mul_conj (delaySymbol 1 z)
  simp only [fastSecond, evaluateLaurent_append, evaluate_realPartLaurent _ hz,
    evaluateLaurent_multiply _ _ hz0, evaluate_secondFactor _ hz, hp,
    evaluateLaurent_scale, evaluate_delayNorm hz, Rat.cast_neg, hnorm]
  simp [supplySymbol, hermitianPart, rawSupplySymbol, normalRow, pointRow,
    Fin.sum_univ_two, residualCoordinateMatrix, paperWeights]
  ring

theorem evaluate_fastCross (γ : ℚ) (p q : Laurent) {z : ℂ} (hz : ‖z‖ = 1)
    (hp : evaluateLaurent p z = lagMultiplier paperWeights 1 z 0)
    (hq : evaluateLaurent q z = lagMultiplier paperWeights 1 z 1) :
    evaluateLaurent (fastCross γ p q) z = supplySymbol paperWeights 1 γ z 0 1 := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hfactor : evaluateLaurent [(0, 1), (-1, γ - 1)] z = multiplierSymbol 1 γ z :=
    evaluate_multiplierLaurent γ z
  simp only [fastCross, evaluateLaurent_scale, evaluateLaurent_append,
    evaluateLaurent_multiply _ _ hz0, evaluateLaurent_star _ hz, evaluate_delayNorm hz,
    hfactor, hp, hq, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_neg,
    neg_one_mul]
  simp [supplySymbol, hermitianPart, rawSupplySymbol, normalRow, pointRow,
    Fin.sum_univ_two, residualCoordinateMatrix]
  ring

end ADMM.UnitCircle.LowerCertificate.Division
