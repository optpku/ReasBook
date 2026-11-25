/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.Lookups
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.Coefficients
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.Convolution

@[expose] public section

open scoped BigOperators

namespace ADMM.UnitCircle.LowerCertificate.Determinant

def shiftCoefficient (f : ℕ → ℤ) (k : ℕ) : ℤ :=
  f k - if k = 256 then kappaNumerator else 0

def reverseCoefficient (f : ℕ → ℤ) (k : ℕ) : ℤ :=
  if k < 513 then f (512 - k) else 0

/-- The finite direct coefficient formula uses logarithmic source lookups. -/
def directDeterminantCoefficient (A B C : ℕ → ℤ) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range 513, if i ≤ k then
    shiftCoefficient A i * shiftCoefficient B (k - i) -
      C i * reverseCoefficient C (k - i)
    else 0

theorem shiftCoefficient_eq {p : List ℤ} {f : ℕ → ℤ}
    (hf : ∀ k, f k = p.getD k 0) (k : ℕ) :
    shiftCoefficient f k = (shiftedNumerators p).getD k 0 := by
  rw [shiftCoefficient, hf, shiftedNumerators, Integer.coefficient_add, Integer.coefficient_monomial]
  split_ifs <;> ring

theorem reverseCoefficient_eq {p : List ℤ} (hp : p.length = 513) {f : ℕ → ℤ}
    (hf : ∀ k, f k = p.getD k 0) (k : ℕ) :
    reverseCoefficient f k = p.reverse.getD k 0 := by
  by_cases hk : k < 513
  · rw [reverseCoefficient, if_pos hk, hf]
    rw [List.getD_reverse k (by rw [hp]; exact hk), hp]
  · rw [reverseCoefficient, if_neg hk, List.getD_eq_default _ _
      (by rw [List.length_reverse, hp]; omega)]

theorem shiftedNumerators_length {p : List ℤ} (hp : p.length = 513) :
    (shiftedNumerators p).length = 513 := by
  simp only [shiftedNumerators, Integer.length_add, hp, Integer.monomial,
    List.length_append, List.length_replicate, List.length_singleton]
  norm_num

/-- The direct finite-sum checker computes precisely a coefficient of the
proved integer Horner convolution, rather than a separate numerical oracle. -/
theorem directDeterminantCoefficient_eq {a b c : List ℤ}
    (ha : a.length = 513) (hb : b.length = 513) (hc : c.length = 513)
    {A B C : ℕ → ℤ} (hA : ∀ k, A k = a.getD k 0)
    (hB : ∀ k, B k = b.getD k 0) (hC : ∀ k, C k = c.getD k 0) (k : ℕ) :
    directDeterminantCoefficient A B C k = (determinantVector a b c).getD k 0 := by
  rw [determinantVector, Integer.coefficient_subtract,
    Integer.coefficient_multiply, Integer.coefficient_multiply,
    shiftedNumerators_length ha, hc, ← Finset.sum_sub_distrib]
  unfold directDeterminantCoefficient
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ≤ k
  · simp only [if_pos hi, ← shiftCoefficient_eq hA, ← shiftCoefficient_eq hB,
      ← reverseCoefficient_eq hc hC, ← hC]
  · simp only [if_neg hi, sub_self]

theorem determinantVector_length {a b c : List ℤ}
    (ha : a.length = 513) (hb : b.length = 513) (hc : c.length = 513) :
    (determinantVector a b c).length = 1025 := by
  have hsa := shiftedNumerators_length ha
  have hsb := shiftedNumerators_length hb
  have hcr : c.reverse.length = 513 := by rw [List.length_reverse, hc]
  have hna : shiftedNumerators a ≠ [] := by intro h; rw [h] at hsa; cases hsa
  have hnb : shiftedNumerators b ≠ [] := by intro h; rw [h] at hsb; cases hsb
  have hnc : c ≠ [] := by intro h; rw [h] at hc; cases hc
  have hncr : c.reverse ≠ [] := by intro h; rw [h] at hcr; cases hcr
  rw [determinantVector, Integer.subtract, Integer.length_add, Integer.length_scale,
    Integer.length_multiply hna hnb, Integer.length_multiply hnc hncr, hsa, hsb, hc, hcr]
  norm_num

end ADMM.UnitCircle.LowerCertificate.Determinant
