/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.DirectTransform
public import Mathlib.Data.List.GetD

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial

open scoped BigOperators

theorem integer_add_getD (p q : List ℤ) (j : ℕ) :
    (IntegerCoefficients.add p q).getD j 0 = p.getD j 0 + q.getD j 0 := by
  induction p generalizing q j with
  | nil => simp [IntegerCoefficients.add]
  | cons a p ih =>
    cases q with
    | nil => simp [IntegerCoefficients.add]
    | cons b q =>
      cases j with
      | zero => rfl
      | succ j => simpa only [IntegerCoefficients.add, List.getD_cons_succ] using ih q j

theorem integer_scale_getD (a : ℤ) (p : List ℤ) (j : ℕ) :
    (IntegerCoefficients.scale a p).getD j 0 = a * p.getD j 0 := by
  induction p generalizing j with
  | nil => simp [IntegerCoefficients.scale]
  | cons b p ih =>
    cases j with
    | zero => rfl
    | succ j => simpa only [IntegerCoefficients.scale, List.map_cons,
        List.getD_cons_succ] using ih j

/-- First-kind Chebyshev rows contain only coefficients of the same parity
as the row index. This follows from the checked recurrence, for every cache. -/
theorem chebyshevCache_getD_parity {T : ℕ → List ℤ} {N : ℕ}
    (hT : ChebyshevCacheValid T N) {m : ℕ} (hm : m ≤ N)
    (j : ℕ) (hpar : m % 2 ≠ j % 2) : (T m).getD j 0 = 0 := by
  induction m using Nat.twoStepInduction generalizing j with
  | zero =>
    rw [hT.1]
    cases j with
    | zero => simp at hpar
    | succ j => simp
  | one =>
    rw [hT.2.1]
    cases j with
    | zero => rfl
    | succ j =>
      cases j with
      | zero => simp at hpar
      | succ j => simp
  | more m ih0 ih1 =>
    rw [hT.2.2 ⟨m, by omega⟩, integer_add_getD]
    cases j with
    | zero =>
      rw [List.getD_cons_zero, integer_scale_getD]
      have h0 : (T m).getD 0 0 = 0 := by apply ih0 <;> omega
      rw [h0]
      ring
    | succ j =>
      rw [List.getD_cons_succ, integer_scale_getD, integer_scale_getD]
      have h0 : (T m).getD (j + 1) 0 = 0 := by apply ih0 <;> omega
      have h1 : (T (m + 1)).getD j 0 = 0 := by apply ih1 <;> omega
      rw [h0, h1]
      ring

def sparseChebCoefficient (T : ℕ → List ℤ) (n : ℕ)
    (c : Fin (n + 1) → ℤ) (j : ℕ) : ℤ :=
  ∑ k : Fin (n + 1), if j ≤ (k : ℕ) ∧ (k : ℕ) % 2 = j % 2 then
    c k * (T k).getD j 0 else 0

/-- Degree and parity guards skip only coefficients proved to be zero. -/
theorem sparseChebCoefficient_eq (T : ℕ → List ℤ) (N : ℕ)
    (hT : ChebyshevCacheValid T N) (n : ℕ) (hn : n ≤ N)
    (c : Fin (n + 1) → ℤ) (j : ℕ) :
    sparseChebCoefficient T n c j = directChebCoefficient T n c j := by
  apply Finset.sum_congr rfl
  intro k _
  have hk : (k : ℕ) ≤ N := (by have h := k.isLt; omega : (k : ℕ) ≤ n).trans hn
  split_ifs with h
  · rfl
  · by_cases hj : j ≤ (k : ℕ)
    · have hp : (k : ℕ) % 2 ≠ j % 2 := by tauto
      rw [chebyshevCache_getD_parity hT hk j hp, mul_zero]
    · have hlen : (T k).length ≤ j := by
        rw [chebyshevCache_length hT hk]
        omega
      rw [List.getD_eq_default _ 0 hlen, mul_zero]

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial
