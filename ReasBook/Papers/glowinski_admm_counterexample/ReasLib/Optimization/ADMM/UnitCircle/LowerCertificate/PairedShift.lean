/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.ChebyshevTransform

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

open scoped BigOperators
open Polynomial

theorem paired_shift_eval (T : ℕ → List ℤ) (N : ℕ)
    (hT : ChebyshevCacheValid T N) (n : ℕ) (hn : n ≤ N)
    (c₀ D : ℤ) (cp cm : Fin n → ℤ) (g : Fin (n + 1) → ℤ) (κ : ℚ)
    (hzero : (g 0 : ℚ) / D = (c₀ : ℚ) / D - κ)
    (hpair : ∀ i : Fin n, g i.succ = cp i + cm i) (x : ℝ) :
    (realPolynomial (pairedLaurent n ((c₀ : ℚ) / D)
      (fun i ↦ (cp i : ℚ) / D) (fun i ↦ (cm i : ℚ) / D))).eval x - κ =
      evaluate (IntegerCoefficients.toRational
        (IntegerCoefficients.chebyshevTransform T n g)) x / D := by
  rw [pairedLaurent_realPolynomial, IntegerCoefficients.evaluate_chebyshevTransform
    T N hT n hn, Fin.sum_univ_succ]
  simp only [eval_add, eval_C, eval_finsetSum, eval_mul, Fin.val_zero,
    Int.natCast_zero, Chebyshev.T_zero, eval_one, mul_one, Fin.val_succ,
    Int.natCast_add, Int.natCast_one]
  rw [add_div, Finset.sum_div]
  have hz : (g 0 : ℝ) / D = (c₀ : ℝ) / D - κ := by exact_mod_cast hzero
  rw [hz]
  have hs : (∑ i : Fin n,
      ((((cp i : ℚ) / D + (cm i : ℚ) / D : ℚ) : ℝ) *
        (Chebyshev.T ℝ (i.val + 1 : ℤ)).eval x)) =
      ∑ i : Fin n, (g i.succ : ℝ) * (Chebyshev.T ℝ (i.val + 1 : ℤ)).eval x / D := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hpair i]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  rw [hs]
  push_cast
  ring

end ADMM.UnitCircle.LowerCertificate
