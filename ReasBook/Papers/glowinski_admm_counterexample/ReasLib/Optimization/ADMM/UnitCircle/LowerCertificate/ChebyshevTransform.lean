/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.ChebyshevCache

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

open scoped BigOperators
open Polynomial

/-- Pair the positive and negative frequencies, retaining the exact coefficients. -/
def pairedLaurent (n : ℕ) (c₀ : ℚ) (cp cm : Fin n → ℚ) : Laurent :=
  (0, c₀) :: (List.ofFn (fun i : Fin n ↦
    [((i.val + 1 : ℤ), cp i), (-(i.val + 1 : ℤ), cm i)])).flatten

theorem realPolynomial_perm {p q : Laurent} (h : p.Perm q) :
    realPolynomial p = realPolynomial q := by
  exact (h.map (fun e ↦ C (e.2 : ℝ) * Chebyshev.T ℝ e.1)).sum_eq

theorem pairedLaurent_realPolynomial (n : ℕ) (c₀ : ℚ) (cp cm : Fin n → ℚ) :
    realPolynomial (pairedLaurent n c₀ cp cm) =
      C (c₀ : ℝ) + ∑ i : Fin n,
        C ((cp i + cm i : ℚ) : ℝ) * Chebyshev.T ℝ (i.val + 1 : ℤ) := by
  simp only [pairedLaurent, realPolynomial, List.map_cons, List.sum_cons,
    Chebyshev.T_zero, mul_one, List.map_flatten, List.sum_flatten,
    List.map_ofFn, Function.comp_def, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, Chebyshev.T_neg, List.sum_ofFn]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Rat.cast_add, map_add]
  ring

namespace IntegerCoefficients

def chebyshevTransform (T : ℕ → List ℤ) (n : ℕ) (c : Fin (n + 1) → ℤ) : List ℤ :=
  sum (List.ofFn (fun k : Fin (n + 1) ↦ scale (c k) (T k)))

theorem evaluate_chebyshevTransform (T : ℕ → List ℤ) (N : ℕ)
    (hT : ChebyshevCacheValid T N) (n : ℕ) (hn : n ≤ N)
    (c : Fin (n + 1) → ℤ) (x : ℝ) :
    evaluate (toRational (chebyshevTransform T n c)) x =
      ∑ k : Fin (n + 1), (c k : ℝ) * (Chebyshev.T ℝ (k : ℤ)).eval x := by
  rw [chebyshevTransform, cast_sum, List.map_ofFn, evaluate_sum,
    List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  change evaluate (toRational (scale (c k) (T k))) x = _
  rw [cast_scale, evaluate_scale, chebyshevCache_sound hT (by have hk := k.isLt; omega)]
  simp only [Rat.cast_intCast]

end IntegerCoefficients

end ADMM.UnitCircle.LowerCertificate
