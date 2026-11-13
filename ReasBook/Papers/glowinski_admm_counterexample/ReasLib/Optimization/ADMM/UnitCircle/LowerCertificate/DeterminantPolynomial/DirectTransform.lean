/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.ChebyshevTransform

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial

open scoped BigOperators
open Polynomial

theorem integer_add_length (p q : List ℤ) :
    (IntegerCoefficients.add p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [IntegerCoefficients.add]
  | cons a p ih =>
    cases q with
    | nil => simp [IntegerCoefficients.add]
    | cons b q => simp [IntegerCoefficients.add, ih, Nat.succ_max_succ]

theorem integer_scale_length (a : ℤ) (p : List ℤ) :
    (IntegerCoefficients.scale a p).length = p.length := by
  simp only [IntegerCoefficients.scale, List.length_map]

theorem chebyshevCache_length {T : ℕ → List ℤ} {N : ℕ}
    (hT : ChebyshevCacheValid T N) {m : ℕ} (hm : m ≤ N) :
    (T m).length = m + 1 := by
  induction m using Nat.twoStepInduction with
  | zero => simp [hT.1]
  | one => simp [hT.2.1]
  | more m ih0 ih1 =>
    rw [hT.2.2 ⟨m, by omega⟩, integer_add_length, List.length_cons,
      integer_scale_length, integer_scale_length, ih1 (by omega), ih0 (by omega)]
    omega

theorem evaluate_integer_lookup (n : ℕ) (p : List ℤ) (hp : p.length ≤ n) (x : ℝ) :
    evaluate (List.ofFn (fun i : Fin n ↦ (p.getD i 0 : ℚ))) x =
      evaluate (IntegerCoefficients.toRational p) x := by
  induction n generalizing p with
  | zero =>
    have hp0 : p = [] := List.length_eq_zero_iff.mp (by omega)
    simp [hp0, IntegerCoefficients.toRational]
  | succ n ih =>
    cases p with
    | nil =>
      simp [IntegerCoefficients.toRational, List.ofFn_const, evaluate_zeroes]
    | cons a p =>
      rw [List.ofFn_succ, evaluate_cons]
      change (a : ℝ) + x * evaluate (List.ofFn
        (fun i : Fin n ↦ (p.getD i 0 : ℚ))) x = _
      rw [ih p (by simpa using hp)]
      rfl

def directChebCoefficient (T : ℕ → List ℤ) (n : ℕ)
    (c : Fin (n + 1) → ℤ) (j : ℕ) : ℤ :=
  ∑ k : Fin (n + 1), c k * (T k).getD j 0

def directChebExpansion (T : ℕ → List ℤ) (n : ℕ)
    (c : Fin (n + 1) → ℤ) : List ℤ :=
  List.ofFn (fun j : Fin (n + 1) ↦ directChebCoefficient T n c j)

/-- A direct coefficient transform avoids constructing and then extracting
hundreds of intermediate shifted coefficient lists. -/
theorem evaluate_directChebExpansion (T : ℕ → List ℤ) (N : ℕ)
    (hT : ChebyshevCacheValid T N) (n : ℕ) (hn : n ≤ N)
    (c : Fin (n + 1) → ℤ) (x : ℝ) :
    evaluate (IntegerCoefficients.toRational (directChebExpansion T n c)) x =
      ∑ k : Fin (n + 1), (c k : ℝ) * (Chebyshev.T ℝ (k : ℤ)).eval x := by
  simp only [IntegerCoefficients.toRational, directChebExpansion,
    List.map_ofFn, Function.comp_def]
  rw [evaluate_ofFn]
  simp only [Rat.cast_intCast]
  simp only [directChebCoefficient, Int.cast_sum, Int.cast_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hk : (k : ℕ) ≤ N := (by have h := k.isLt; omega : (k : ℕ) ≤ n).trans hn
  have hlen : (T k).length ≤ n + 1 := by
    rw [chebyshevCache_length hT hk]
    have h := k.isLt
    omega
  calc
    (∑ j : Fin (n + 1), ((c k : ℝ) * ((T k).getD j 0 : ℝ)) * x ^ (j : ℕ)) =
        (c k : ℝ) * ∑ j : Fin (n + 1), ((T k).getD j 0 : ℝ) * x ^ (j : ℕ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = (c k : ℝ) * evaluate (IntegerCoefficients.toRational (T k)) x := by
      congr 1
      rw [← evaluate_integer_lookup (n + 1) (T k) hlen x, evaluate_ofFn]
      simp only [Rat.cast_intCast]
    _ = _ := by rw [chebyshevCache_sound hT hk]

theorem directChebExpansion_eval_eq (T : ℕ → List ℤ) (N : ℕ)
    (hT : ChebyshevCacheValid T N) (n : ℕ) (hn : n ≤ N)
    (c : Fin (n + 1) → ℤ) (x : ℝ) :
    evaluate (IntegerCoefficients.toRational (directChebExpansion T n c)) x =
      evaluate (IntegerCoefficients.toRational
        (IntegerCoefficients.chebyshevTransform T n c)) x := by
  rw [evaluate_directChebExpansion T N hT n hn,
    IntegerCoefficients.evaluate_chebyshevTransform T N hT n hn]

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial
