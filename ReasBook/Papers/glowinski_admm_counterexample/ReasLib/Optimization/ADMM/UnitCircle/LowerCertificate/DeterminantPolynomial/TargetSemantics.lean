/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.TargetContext

@[expose] public section

set_option maxRecDepth 8192

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial

open scoped BigOperators

/-- A checked coefficient identity transports the exact Laurent source to the
rational polynomial used by the interval certificate. -/
theorem start_realPolynomial_eq_of_coefficients
    (h : ∀ i : Fin 513, startLeftCoefficient i = startRightCoefficient i)
    (x : ℝ) :
    (realPolynomial startLaurent).eval x = evaluate Data.StartDeterminant x := by
  rw [startLaurent_direct_eval, startDirectPolynomial, directChebExpansion]
  have hi : List.ofFn (fun j : Fin 513 ↦
      directChebCoefficient FirstKind512.tree.get 512 startChebWeight j) =
      List.ofFn (fun j : Fin 513 ↦ startScale *
        Data.IntegerPolynomials.StartDeterminant.coefficients.get j) := by
    congr 1
    funext j
    exact h j
  rw [hi, Data.IntegerPolynomials.StartDeterminant.roundtrip, evaluate_scale]
  simp only [IntegerCoefficients.toRational, List.map_ofFn, Function.comp_def]
  rw [evaluate_ofFn, evaluate_ofFn]
  simp only [Rat.cast_mul, Rat.cast_intCast, Rat.cast_div, Rat.cast_one, Int.cast_mul]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [← startScale_denominator, Int.cast_mul]
  norm_num [startScale]
  ring

theorem lower_realPolynomial_eq_of_coefficients
    (h : ∀ i : Fin 513, lowerLeftCoefficient i = lowerRightCoefficient i)
    (x : ℝ) :
    (realPolynomial lowerLaurent).eval x = evaluate Data.LowerDeterminant x := by
  rw [lowerLaurent_direct_eval, lowerDirectPolynomial, directChebExpansion]
  have hi : List.ofFn (fun j : Fin 513 ↦
      directChebCoefficient FirstKind512.tree.get 512 lowerChebWeight j) =
      List.ofFn (fun j : Fin 513 ↦ lowerScale *
        Data.IntegerPolynomials.LowerDeterminant.coefficients.get j) := by
    congr 1
    funext j
    exact h j
  rw [hi, Data.IntegerPolynomials.LowerDeterminant.roundtrip, evaluate_scale]
  simp only [IntegerCoefficients.toRational, List.map_ofFn, Function.comp_def]
  rw [evaluate_ofFn, evaluate_ofFn]
  simp only [Rat.cast_mul, Rat.cast_intCast, Rat.cast_div, Rat.cast_one, Int.cast_mul]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [← lowerScale_denominator, Int.cast_mul]
  norm_num [lowerScale]
  ring

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial
