/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.LookupContext
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.DirectTransform
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.PairedShift

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial

theorem startLaurent_real_eval (x : ℝ) :
    (realPolynomial startLaurent).eval x =
      evaluate (IntegerCoefficients.toRational startChebPolynomial) x /
        Determinant.determinantDenominator := by
  rw [realPolynomial_perm startLaurent_perm_paired, startPaired]
  have h := paired_shift_eval FirstKind512.tree.get 512 FirstKind512.cache_valid
    512 (by rfl) (startCoefficient 512) Determinant.determinantDenominator
    (fun i ↦ startCoefficient (i.val + 513))
    (fun i ↦ startCoefficient (511 - i.val)) startChebWeight 0
    (by simp only [startChebWeight, Fin.cases_zero, sub_zero])
    (by intro i; rfl) x
  simpa only [Rat.cast_zero, sub_zero, startChebPolynomial] using h

theorem lowerLaurent_real_eval (x : ℝ) :
    (realPolynomial lowerLaurent).eval x =
      evaluate (IntegerCoefficients.toRational lowerChebPolynomial) x /
        Determinant.determinantDenominator := by
  rw [realPolynomial_perm lowerLaurent_perm_paired, lowerPaired]
  have h := paired_shift_eval FirstKind512.tree.get 512 FirstKind512.cache_valid
    512 (by rfl) (lowerCoefficient 512) Determinant.determinantDenominator
    (fun i ↦ lowerCoefficient (i.val + 513))
    (fun i ↦ lowerCoefficient (511 - i.val)) lowerChebWeight 0
    (by simp only [lowerChebWeight, Fin.cases_zero, sub_zero])
    (by intro i; rfl) x
  simpa only [Rat.cast_zero, sub_zero, lowerChebPolynomial] using h

def startDirectPolynomial : List ℤ :=
  directChebExpansion FirstKind512.tree.get 512 startChebWeight

def lowerDirectPolynomial : List ℤ :=
  directChebExpansion FirstKind512.tree.get 512 lowerChebWeight

theorem startLaurent_direct_eval (x : ℝ) :
    (realPolynomial startLaurent).eval x =
      evaluate (IntegerCoefficients.toRational startDirectPolynomial) x /
        Determinant.determinantDenominator := by
  rw [startLaurent_real_eval, startDirectPolynomial,
    directChebExpansion_eval_eq FirstKind512.tree.get 512 FirstKind512.cache_valid
      512 (by rfl)]
  rfl

theorem lowerLaurent_direct_eval (x : ℝ) :
    (realPolynomial lowerLaurent).eval x =
      evaluate (IntegerCoefficients.toRational lowerDirectPolynomial) x /
        Determinant.determinantDenominator := by
  rw [lowerLaurent_real_eval, lowerDirectPolynomial,
    directChebExpansion_eval_eq FirstKind512.tree.get 512 FirstKind512.cache_valid
      512 (by rfl)]
  rfl

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial
