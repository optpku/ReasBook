/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.QuotientChecks

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Determinant

/-- The checked reversed coefficient vector evaluates to the conjugate of
its exact source quotient at every unit-circle point. -/
theorem evaluate_reversed_quotient {p : List ℤ} {q : Laurent}
    (hstar : rationalLaurent (-256) quotientDenominator p.reverse = laurentStar q.reverse)
    {z : ℂ} (hz : ‖z‖ = 1) :
    evaluateLaurent (rationalLaurent (-256) quotientDenominator p.reverse) z =
      star (evaluateLaurent q z) := by
  rw [hstar, evaluateLaurent_star _ hz, evaluateLaurent_reverse]

/-- Symmetric real Laurent coefficients prove real-valuedness also at zero
frequency; no division by the vanishing delay factor is used. -/
theorem quotient_eq_real_of_symmetric {p : List ℤ} {q : Laurent}
    (hrep : rationalLaurent (-256) quotientDenominator p = q)
    (hstar : rationalLaurent (-256) quotientDenominator p.reverse = laurentStar q.reverse)
    (hsym : p.reverse = p) {z : ℂ} (hz : ‖z‖ = 1) :
    evaluateLaurent q z = ((evaluateLaurent q z).re : ℂ) := by
  have h := evaluate_reversed_quotient hstar hz
  rw [hsym, hrep] at h
  have hc : star (evaluateLaurent q z) = evaluateLaurent q z := h.symm
  exact (Complex.conj_eq_iff_re.mp (by simpa only [Complex.star_def] using hc)).symm

theorem diagonal_eq_real {z : ℂ} (hz : ‖z‖ = 1) :
    evaluateLaurent Division.startDiagonalQuotient z =
      ((evaluateLaurent Division.startDiagonalQuotient z).re : ℂ) :=
  quotient_eq_real_of_symmetric diagonal_representation diagonal_star_representation
    diagonal_symmetric hz

theorem startSecond_eq_real {z : ℂ} (hz : ‖z‖ = 1) :
    evaluateLaurent Division.startSecondQuotient z =
      ((evaluateLaurent Division.startSecondQuotient z).re : ℂ) :=
  quotient_eq_real_of_symmetric startSecond_representation startSecond_star_representation
    startSecond_symmetric hz

theorem lowerSecond_eq_real {z : ℂ} (hz : ‖z‖ = 1) :
    evaluateLaurent Division.lowerSecondQuotient z =
      ((evaluateLaurent Division.lowerSecondQuotient z).re : ℂ) :=
  quotient_eq_real_of_symmetric lowerSecond_representation lowerSecond_star_representation
    lowerSecond_symmetric hz

theorem startCross_reverse_eval {z : ℂ} (hz : ‖z‖ = 1) :
    evaluateLaurent (rationalLaurent (-256) quotientDenominator startCrossNumerators.reverse) z =
      star (evaluateLaurent Division.startCrossQuotient z) :=
  evaluate_reversed_quotient startCross_star_representation hz

theorem lowerCross_reverse_eval {z : ℂ} (hz : ‖z‖ = 1) :
    evaluateLaurent (rationalLaurent (-256) quotientDenominator lowerCrossNumerators.reverse) z =
      star (evaluateLaurent Division.lowerCrossQuotient z) :=
  evaluate_reversed_quotient lowerCross_star_representation hz

end ADMM.UnitCircle.LowerCertificate.Determinant
