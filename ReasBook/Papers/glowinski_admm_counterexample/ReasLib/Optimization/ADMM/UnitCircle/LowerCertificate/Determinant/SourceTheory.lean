/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.Convolution
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.QuotientSemantics
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Determinant

open ADMM.RefinedEndpoint.Data

noncomputable def startExpression (z : ℂ) : ℂ :=
  (evaluateLaurent Division.startDiagonalQuotient z - (kappa : ℂ)) *
    (evaluateLaurent Division.startSecondQuotient z - (kappa : ℂ)) -
    evaluateLaurent Division.startCrossQuotient z * star (evaluateLaurent Division.startCrossQuotient z)

noncomputable def lowerExpression (z : ℂ) : ℂ :=
  (evaluateLaurent Division.startDiagonalQuotient z - (kappa : ℂ)) *
    (evaluateLaurent Division.lowerSecondQuotient z - (kappa : ℂ)) -
    evaluateLaurent Division.lowerCrossQuotient z * star (evaluateLaurent Division.lowerCrossQuotient z)

/-- The computed start determinant vector retains its exact source quotients. -/
theorem start_vector_eval {z : ℂ} (hz : ‖z‖ = 1) :
    evaluateLaurent (rationalLaurent (-512) determinantDenominator
      (determinantVector diagonalNumerators startSecondNumerators startCrossNumerators)) z =
      startExpression z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [evaluate_determinantVector _ _ _ hz0, diagonal_representation,
    startSecond_representation, startCross_representation, startCross_reverse_eval hz]
  rfl

/-- The computed lower-endpoint determinant vector retains the same source. -/
theorem lower_vector_eval {z : ℂ} (hz : ‖z‖ = 1) :
    evaluateLaurent (rationalLaurent (-512) determinantDenominator
      (determinantVector diagonalNumerators lowerSecondNumerators lowerCrossNumerators)) z =
      lowerExpression z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [evaluate_determinantVector _ _ _ hz0, diagonal_representation,
    lowerSecond_representation, lowerCross_representation, lowerCross_reverse_eval hz]
  rfl

/-- All imaginary cross terms are accounted for in the actual scalar
principal-minor test; both diagonal quotients are real by checked symmetry. -/
theorem startExpression_re {z : ℂ} (hz : ‖z‖ = 1) :
    (startExpression z).re =
      ((evaluateLaurent Division.startDiagonalQuotient z).re - (kappa : ℝ)) *
      ((evaluateLaurent Division.startSecondQuotient z).re - (kappa : ℝ)) -
        Complex.normSq (evaluateLaurent Division.startCrossQuotient z) := by
  unfold startExpression
  rw [diagonal_eq_real hz, startSecond_eq_real hz]
  have hc : evaluateLaurent Division.startCrossQuotient z *
      star (evaluateLaurent Division.startCrossQuotient z) =
      (Complex.normSq (evaluateLaurent Division.startCrossQuotient z) : ℂ) := by
    simpa only [Complex.star_def] using Complex.mul_conj
      (evaluateLaurent Division.startCrossQuotient z)
  rw [hc]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.ratCast_re, Complex.ratCast_im, sub_zero, mul_zero, zero_mul, zero_sub]

theorem lowerExpression_re {z : ℂ} (hz : ‖z‖ = 1) :
    (lowerExpression z).re =
      ((evaluateLaurent Division.startDiagonalQuotient z).re - (kappa : ℝ)) *
      ((evaluateLaurent Division.lowerSecondQuotient z).re - (kappa : ℝ)) -
        Complex.normSq (evaluateLaurent Division.lowerCrossQuotient z) := by
  unfold lowerExpression
  rw [diagonal_eq_real hz, lowerSecond_eq_real hz]
  have hc : evaluateLaurent Division.lowerCrossQuotient z *
      star (evaluateLaurent Division.lowerCrossQuotient z) =
      (Complex.normSq (evaluateLaurent Division.lowerCrossQuotient z) : ℂ) := by
    simpa only [Complex.star_def] using Complex.mul_conj
      (evaluateLaurent Division.lowerCrossQuotient z)
  rw [hc]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.ratCast_re, Complex.ratCast_im, sub_zero, mul_zero, zero_mul, zero_sub]

/-- Exact shifted determinant factorization from the three Hermitian entries. -/
theorem shifted_determinant_factor {Q : Matrix (Fin 2) (Fin 2) ℂ}
    (hQ : Q.IsHermitian) (d κ : ℝ) (A B C : ℂ)
    (h00 : Q 0 0 = (d : ℂ) * A) (h11 : Q 1 1 = (d : ℂ) * B)
    (h01 : Q 0 1 = (d : ℂ) * C) :
    Matrix.det (Q - ((d * κ : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      (d : ℂ) ^ 2 * ((A - (κ : ℂ)) * (B - (κ : ℂ)) - C * star C) := by
  have h10 : Q 1 0 = star (Q 0 1) := (hQ.apply 1 0).symm
  simp [Matrix.det_fin_two, h00, h11, h01, h10, Complex.star_def]
  ring

/-- The polynomial determinant is the shifted determinant of the actual
supply, including the zero frequency where the delay factor vanishes. -/
theorem start_shifted_supply_determinant {z : ℂ} (hz : ‖z‖ = 1) :
    Matrix.det (supplySymbol paperWeights 1 ((377 / 200 : ℚ) : ℝ) z -
      ((Complex.normSq (delaySymbol 1 z) * (kappa : ℝ) : ℝ) : ℂ) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      (Complex.normSq (delaySymbol 1 z) : ℂ) ^ 2 * startExpression z := by
  have h := shifted_determinant_factor
    (supplySymbol_isHermitian paperWeights 1 ((377 / 200 : ℚ) : ℝ) z)
    (Complex.normSq (delaySymbol 1 z)) (kappa : ℝ)
    (evaluateLaurent Division.startDiagonalQuotient z)
    (evaluateLaurent Division.startSecondQuotient z)
    (evaluateLaurent Division.startCrossQuotient z)
    (Division.diagonal_entry_division (377 / 200) hz)
    (Division.start_second_entry_division hz) (Division.start_cross_entry_division hz)
  simpa only [startExpression, Complex.ofReal_ratCast] using h

theorem lower_shifted_supply_determinant {z : ℂ} (hz : ‖z‖ = 1) :
    Matrix.det (supplySymbol paperWeights 1 ((75475298801 / 40000000000 : ℚ) : ℝ) z -
      ((Complex.normSq (delaySymbol 1 z) * (kappa : ℝ) : ℝ) : ℂ) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      (Complex.normSq (delaySymbol 1 z) : ℂ) ^ 2 * lowerExpression z := by
  have h := shifted_determinant_factor
    (supplySymbol_isHermitian paperWeights 1 ((75475298801 / 40000000000 : ℚ) : ℝ) z)
    (Complex.normSq (delaySymbol 1 z)) (kappa : ℝ)
    (evaluateLaurent Division.startDiagonalQuotient z)
    (evaluateLaurent Division.lowerSecondQuotient z)
    (evaluateLaurent Division.lowerCrossQuotient z)
    (Division.diagonal_entry_division (75475298801 / 40000000000) hz)
    (Division.lower_second_entry_division hz) (Division.lower_cross_entry_division hz)
  simpa only [lowerExpression, Complex.ofReal_ratCast] using h

end ADMM.UnitCircle.LowerCertificate.Determinant
