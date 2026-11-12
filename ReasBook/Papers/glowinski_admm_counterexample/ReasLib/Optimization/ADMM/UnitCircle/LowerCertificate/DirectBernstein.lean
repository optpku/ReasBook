/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.CachedPowers
public import Mathlib.Algebra.Polynomial.Coeff

@[expose] public section

set_option maxRecDepth 8192

namespace ADMM.UnitCircle.LowerCertificate

open scoped BigOperators
open Polynomial

theorem coeff_one_sub_X_pow (n j : ℕ) :
    ((1 - X : ℝ[X]) ^ n).coeff j = (n.choose j : ℝ) * (-1) ^ j := by
  have hb : (1 - X : ℝ[X]) ^ n = ∑ i ∈ Finset.range (n + 1),
      C ((n.choose i : ℝ) * (-1) ^ i) * X ^ i := by
    rw [sub_eq_add_neg, add_comm (1 : ℝ[X]), add_pow]
    apply Finset.sum_congr rfl
    intro i _
    simp only [one_pow, mul_one, map_mul, map_natCast, map_pow]
    rw [show (-X : ℝ[X]) = C (-1) * X by simp, mul_pow]
    ring
  rw [hb, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    simp [Ne.symm hbj]
  · intro hj
    have hnj : n < j := by simpa using hj
    simp [Nat.choose_eq_zero_of_lt hnj]

theorem bernsteinPolynomial_coefficient (n k j : ℕ) :
    (bernsteinPolynomial ℝ n k).coeff j =
      if k ≤ j then (n.choose k : ℝ) * (Nat.choose (n - k) (j - k) : ℝ) *
        (-1) ^ (j - k) else 0 := by
  rw [bernsteinPolynomial, mul_assoc, ← C_eq_natCast, coeff_C_mul,
    coeff_X_pow_mul', coeff_one_sub_X_pow]
  split_ifs <;> simp_all [mul_assoc]

noncomputable def powerPolynomial (n : ℕ) (p : Fin (n + 1) → ℝ) : ℝ[X] :=
  ∑ i : Fin (n + 1), C (p i) * X ^ (i : ℕ)

theorem powerPolynomial_coefficient (n : ℕ) (p : Fin (n + 1) → ℝ) (j : ℕ) :
    (powerPolynomial n p).coeff j = if h : j < n + 1 then p ⟨j, h⟩ else 0 := by
  rw [powerPolynomial, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  split_ifs with hj
  · rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro b _ hb
      have hne : j ≠ (b : ℕ) := by intro he; apply hb; exact Fin.ext he.symm
      simp [hne]
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    have hne : j ≠ (i : ℕ) := by have hi := i.isLt; omega
    simp [hne]

namespace IntegerCoefficients

def affineCoefficient (choose : ℕ → ℕ → ℕ) (pa pb ps : ℕ → ℤ)
    (n : ℕ) (p : Fin (n + 1) → ℤ) (j : ℕ) : ℤ :=
  ∑ k : Fin (n + 1), if j ≤ (k : ℕ) then
    p k * (choose k j : ℤ) * pa ((k : ℕ) - j) * pb j * ps (n - k)
    else 0

/-- Power coefficients of a Bernstein expansion, computed directly without
materializing and adding `n+1` shifted coefficient lists. -/
def directCoefficient (choose : ℕ → ℕ → ℕ) (sign : ℕ → ℤ)
    (n : ℕ) (c : Fin (n + 1) → ℤ) (j : ℕ) : ℤ :=
  ∑ k : Fin (n + 1), if (k : ℕ) ≤ j then
    c k * (choose n k : ℤ) * choose (n - k) (j - k) * sign (j - k)
    else 0

def directExpansion (choose : ℕ → ℕ → ℕ) (sign : ℕ → ℤ)
    (n : ℕ) (c : Fin (n + 1) → ℤ) : List ℤ :=
  List.ofFn (fun j : Fin (n + 1) ↦ directCoefficient choose sign n c j)

theorem evaluate_directExpansion (choose : ℕ → ℕ → ℕ) (sign : ℕ → ℤ)
    (hchoose : ∀ n k, choose n k = Nat.fast_choose n k)
    (hsign : ∀ m, sign m = (-1) ^ m) (n : ℕ) (c : Fin (n + 1) → ℤ)
    (t : unitInterval) :
    evaluate (toRational (directExpansion choose sign n c)) t =
      ∑ k : Fin (n + 1), (c k : ℝ) * bernstein n k t := by
  have hp : powerPolynomial n (fun j ↦
        (directCoefficient choose sign n c j : ℝ)) =
      ∑ k : Fin (n + 1), C (c k : ℝ) * bernsteinPolynomial ℝ n k := by
    ext j
    rw [powerPolynomial_coefficient, finsetSum_coeff]
    simp only [coeff_C_mul, bernsteinPolynomial_coefficient]
    by_cases hj : j < n + 1
    · rw [dif_pos hj]
      simp only [directCoefficient, Int.cast_sum, apply_ite, Int.cast_mul,
        Int.cast_natCast, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_zero,
        hchoose, hsign, ← Nat.choose_eq_fast_choose]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp_all [mul_assoc]
    · rw [dif_neg hj]
      symm
      apply Finset.sum_eq_zero
      intro k _
      have hk := k.isLt
      have hkj : (k : ℕ) ≤ j := by omega
      have hlt : n - (k : ℕ) < j - (k : ℕ) := by omega
      simp [hkj, Nat.choose_eq_zero_of_lt hlt]
  have h := congrArg (fun p : ℝ[X] ↦ p.eval (t : ℝ)) hp
  simp only [powerPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X] at h
  simp only [toRational, directExpansion, List.map_ofFn, Function.comp_def]
  rw [evaluate_ofFn]
  simpa only [Rat.cast_intCast, bernstein, Polynomial.toContinuousMapOn,
    Polynomial.toContinuousMap, ContinuousMap.restrict_apply, ContinuousMap.coe_mk] using h

theorem positive_affine_direct (choose : ℕ → ℕ → ℕ) (sign : ℕ → ℤ)
    (hchoose : ∀ n k, choose n k = Nat.fast_choose n k)
    (hsign : ∀ m, sign m = (-1) ^ m) (n : ℕ)
    (p c : Fin (n + 1) → ℤ) (A B S E : ℤ)
    (hS : 0 < S) (hE : 0 < E) (hc : ∀ k, 0 < c k)
    (heq : scale E (affine n p A B S) =
      scale (S ^ n) (directExpansion choose sign n c)) (t : unitInterval) :
    0 < evaluate (List.ofFn (fun k ↦ (p k : ℚ)))
      (((A : ℚ) / S : ℚ) + ((B : ℚ) / S : ℚ) * (t : ℝ)) := by
  have hs : (1 : ℝ) ≤ evaluate (toRational (directExpansion choose sign n c)) t := by
    rw [evaluate_directExpansion choose sign hchoose hsign]
    calc
      (1 : ℝ) = ∑ k : Fin (n + 1), (1 : ℝ) * bernstein n k t := by
        simp only [one_mul, bernstein.probability]
      _ ≤ ∑ k : Fin (n + 1), (c k : ℝ) * bernstein n k t := by
        apply Finset.sum_le_sum
        intro k _
        have hk : (1 : ℤ) ≤ c k := hc k
        have hk' : (1 : ℝ) ≤ (c k : ℝ) := by exact_mod_cast hk
        exact mul_le_mul_of_nonneg_right hk' bernstein_nonneg
  have h := congrArg (fun q ↦ evaluate (toRational q) (t : ℝ)) heq
  rw [cast_scale, cast_affine n p A B S (ne_of_gt hS), evaluate_scale,
    evaluate_scale, evaluate_affineCoefficients, cast_scale, evaluate_scale] at h
  have hSp : (0 : ℝ) < ((S : ℚ) : ℝ) ^ n := by
    apply pow_pos
    exact_mod_cast hS
  have hEp : (0 : ℝ) < ((E : ℚ) : ℝ) := by exact_mod_cast hE
  have hright : 0 < (((S ^ n : ℤ) : ℚ) : ℝ) *
      evaluate (toRational (directExpansion choose sign n c)) t := by
    push_cast
    exact mul_pos hSp (lt_of_lt_of_le zero_lt_one hs)
  rw [← h] at hright
  simp only [Rat.cast_pow] at hright
  exact (mul_pos_iff_of_pos_left hSp).1 ((mul_pos_iff_of_pos_left hEp).1 hright)

theorem identity_of_direct_coefficients
    (choose : ℕ → ℕ → ℕ) (sign pa pb ps : ℕ → ℤ)
    (hchoose : ∀ n k, choose n k = Nat.fast_choose n k)
    (A B S E : ℤ) (hpa : ∀ m, pa m = A ^ m) (hpb : ∀ m, pb m = B ^ m)
    (hps : ∀ m, ps m = S ^ m) (n : ℕ) (p c : Fin (n + 1) → ℤ)
    (h : ∀ j : Fin (n + 1),
      E * affineCoefficient choose pa pb ps n p j =
        S ^ n * directCoefficient choose sign n c j) :
    scale E (affine n p A B S) = scale (S ^ n) (directExpansion choose sign n c) := by
  rw [← fastAffine_sound choose pa pb ps A B S hchoose hpa hpb hps]
  simp only [scale, fastAffine, directExpansion, List.map_ofFn, Function.comp_def]
  congr 1
  funext j
  exact h j

end IntegerCoefficients

end ADMM.UnitCircle.LowerCertificate
