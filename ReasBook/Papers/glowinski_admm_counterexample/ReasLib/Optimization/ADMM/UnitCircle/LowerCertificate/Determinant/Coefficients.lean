/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.IntegerLaurent

@[expose] public section

open scoped BigOperators

namespace ADMM.UnitCircle.LowerCertificate.Determinant.Integer

theorem coefficient_add (p q : List ℤ) (k : ℕ) :
    (add p q).getD k 0 = p.getD k 0 + q.getD k 0 := by
  induction k generalizing p q with
  | zero => cases p <;> cases q <;> simp [add]
  | succ k ih =>
    cases p with
    | nil => simp [add]
    | cons a p =>
      cases q with
      | nil => simp [add]
      | cons b q =>
        change (add p q).getD k 0 = p.getD k 0 + q.getD k 0
        exact ih p q

theorem coefficient_scale (a : ℤ) (p : List ℤ) (k : ℕ) :
    (scale a p).getD k 0 = a * p.getD k 0 := by
  induction k generalizing p with
  | zero => cases p <;> simp [scale]
  | succ k ih =>
    cases p with
    | nil => simp [scale]
    | cons b p =>
      change (scale a p).getD k 0 = a * p.getD k 0
      exact ih p

/-- A coefficient of Horner convolution is a finite exact sum of source
products. This permits bounded kernel batches without expanding all output
coefficients in a dependent equality proof. -/
theorem coefficient_multiply (p q : List ℤ) (k : ℕ) :
    (multiply p q).getD k 0 =
      ∑ i ∈ Finset.range p.length,
        if i ≤ k then p.getD i 0 * q.getD (k - i) 0 else 0 := by
  induction p generalizing q k with
  | nil => simp [multiply]
  | cons a p ih =>
    cases q with
    | nil => simp [multiply]
    | cons b q =>
      change (add (scale a (b :: q)) (0 :: multiply p (b :: q))).getD k 0 = _
      rw [coefficient_add, coefficient_scale]
      cases k with
      | zero =>
        simp only [List.getD_cons_zero, List.length_cons]
        rw [Finset.sum_range_succ']
        simp
      | succ k =>
        simp only [List.getD_cons_succ]
        rw [ih]
        simp only [List.length_cons]
        rw [Finset.sum_range_succ']
        simp only [List.getD_cons_zero, Nat.sub_zero, zero_le, if_true,
          List.getD_cons_succ, Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub]
        ring


theorem length_add (p q : List ℤ) : (add p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q =>
      change (add p q).length + 1 = max (p.length + 1) (q.length + 1)
      rw [ih]
      omega

theorem length_scale (a : ℤ) (p : List ℤ) : (scale a p).length = p.length := by
  simp only [scale, List.length_map]

theorem length_multiply {p q : List ℤ} (hp : p ≠ []) (hq : q ≠ []) :
    (multiply p q).length = p.length + q.length - 1 := by
  induction p generalizing q with
  | nil => exact False.elim (hp rfl)
  | cons a p ih =>
    cases q with
    | nil => exact False.elim (hq rfl)
    | cons b q =>
      change (add (scale a (b :: q)) (0 :: multiply p (b :: q))).length = _
      rw [length_add, length_scale, List.length_cons, List.length_cons]
      by_cases hpn : p = []
      · subst p
        simp only [multiply, List.length_nil, List.length_cons]
        omega
      · rw [ih hpn (by simp)]
        simp only [List.length_cons]
        omega

theorem coefficient_subtract (p q : List ℤ) (k : ℕ) :
    (subtract p q).getD k 0 = p.getD k 0 - q.getD k 0 := by
  rw [subtract, coefficient_add, coefficient_scale]
  ring

theorem coefficient_monomial (n : ℕ) (a : ℤ) (k : ℕ) :
    (monomial n a).getD k 0 = if k = n then a else 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [monomial]
    | succ k => simp [monomial]
  | succ n ih =>
    cases k with
    | zero => simp [monomial]
    | succ k =>
      change (monomial n a).getD k 0 = _
      simpa only [Nat.succ.injEq] using ih k

end ADMM.UnitCircle.LowerCertificate.Determinant.Integer
