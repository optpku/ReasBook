/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.IntegerEncoding
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.HomogeneousHorner
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DirectBernstein

@[expose] public section

/-!
# Integer encodings of affine and Bernstein transformations

These are identities at arbitrary integer bases. The unrestricted Bernstein
identity is obtained from an identity of polynomials, so no unit-interval
assumption is imposed on the encoding base.
-/

namespace ADMM.UnitCircle.LowerCertificate.IntegerEncoding

open scoped BigOperators
open Polynomial IntegerCoefficients

theorem encoded_ofFn (b : ℤ) (n : ℕ) (p : Fin (n + 1) → ℤ) :
    encoded b (List.ofFn p) = ∑ k : Fin (n + 1), p k * b ^ (k : ℕ) := by
  induction n with
  | zero => simp [encoded]
  | succ n ih =>
    rw [List.ofFn_succ, encoded_cons, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    simp only [Fin.val_succ, pow_succ]
    ring

/-- The direct affine coefficient formula is a homogeneous substitution
when evaluated at any integer encoding base. This includes `S = 0`. -/
theorem encoded_affine (b : ℤ) (n : ℕ) (p : Fin (n + 1) → ℤ) (A B S : ℤ) :
    encoded b (affine n p A B S) =
      ∑ k : Fin (n + 1), p k * (A + B * b) ^ (k : ℕ) * S ^ (n - k) := by
  unfold affine
  rw [encoded_ofFn]
  simp only [← Nat.choose_eq_fast_choose]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hsub : (Finset.range (n + 1)).filter (fun j ↦ j ≤ (k : ℕ)) =
      Finset.range ((k : ℕ) + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hfin := Fin.sum_univ_eq_sum_range
    (fun j : ℕ ↦ (if j ≤ (k : ℕ) then
      p k * (Nat.choose k j : ℤ) * A ^ ((k : ℕ) - j) * B ^ j * S ^ (n - k)
      else 0) * b ^ j) (n + 1)
  calc
    (∑ j : Fin (n + 1),
      (if (j : ℕ) ≤ (k : ℕ) then
        p k * (Nat.choose k j : ℤ) * A ^ ((k : ℕ) - j) * B ^ (j : ℕ) *
          S ^ (n - k) else 0) * b ^ (j : ℕ)) =
        ∑ j ∈ Finset.range (n + 1), if j ≤ (k : ℕ) then
          p k * (Nat.choose k j : ℤ) * A ^ ((k : ℕ) - j) * B ^ j *
            S ^ (n - k) * b ^ j else 0 := by
      simpa only [ite_mul, zero_mul] using hfin
    _ = ∑ j ∈ Finset.range ((k : ℕ) + 1),
        p k * (Nat.choose k j : ℤ) * A ^ ((k : ℕ) - j) * B ^ j *
          S ^ (n - k) * b ^ j := by
      rw [← Finset.sum_filter, hsub]
    _ = p k * (B * b + A) ^ (k : ℕ) * S ^ (n - k) := by
      rw [add_pow, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_pow]
      ring
    _ = _ := by rw [add_comm (B * b)]

/-- The algebraic identity underlying direct Bernstein expansion. It is
valid as a polynomial identity, independently of the evaluation argument. -/
theorem directExpansion_polynomial_identity (choose : ℕ → ℕ → ℕ)
    (sign : ℕ → ℤ) (hchoose : ∀ n k, choose n k = Nat.fast_choose n k)
    (hsign : ∀ m, sign m = (-1) ^ m) (n : ℕ) (c : Fin (n + 1) → ℤ) :
    powerPolynomial n (fun j ↦ (directCoefficient choose sign n c j : ℝ)) =
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

/-- Unlike the positivity-oriented interface, this identity allows every
real argument, including bases lying outside `[0, 1]`. -/
theorem evaluate_directExpansion_unrestricted (choose : ℕ → ℕ → ℕ)
    (sign : ℕ → ℤ) (hchoose : ∀ n k, choose n k = Nat.fast_choose n k)
    (hsign : ∀ m, sign m = (-1) ^ m) (n : ℕ) (c : Fin (n + 1) → ℤ) (x : ℝ) :
    evaluate (toRational (directExpansion choose sign n c)) x =
      ∑ k : Fin (n + 1), (c k : ℝ) * (choose n k : ℝ) *
        x ^ (k : ℕ) * (1 - x) ^ (n - k) := by
  have h := congrArg (fun p : ℝ[X] ↦ p.eval x)
    (directExpansion_polynomial_identity choose sign hchoose hsign n c)
  simp only [powerPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    bernsteinPolynomial, eval_natCast, eval_sub, eval_one] at h
  simp only [toRational, directExpansion, List.map_ofFn, Function.comp_def]
  rw [evaluate_ofFn]
  simpa only [Rat.cast_intCast, hchoose, ← Nat.choose_eq_fast_choose, mul_assoc] using h

/-- Evaluating the direct Bernstein coefficient list at an integer base is
the corresponding homogeneous sum, with no frequency or interval condition. -/
theorem encoded_directExpansion (choose : ℕ → ℕ → ℕ) (sign : ℕ → ℤ)
    (hchoose : ∀ n k, choose n k = Nat.fast_choose n k)
    (hsign : ∀ m, sign m = (-1) ^ m) (b : ℤ) (n : ℕ)
    (c : Fin (n + 1) → ℤ) :
    encoded b (directExpansion choose sign n c) =
      ∑ k : Fin (n + 1), (c k * (choose n k : ℤ)) * b ^ (k : ℕ) *
        (1 - b) ^ (n - k) := by
  have h := evaluate_directExpansion_unrestricted choose sign hchoose hsign n c (b : ℝ)
  rw [evaluate_toRational, ← cast_encoded] at h
  exact_mod_cast h

/-- The affine encoding can be computed by a linear number of integer ring
operations, without constructing the transformed coefficient list. -/
theorem encoded_affine_homogeneous (b : ℤ) (n : ℕ)
    (p : Fin (n + 1) → ℤ) (A B S : ℤ) :
    encoded b (affine n p A B S) =
      homogeneousHorner (A + B * b) S (List.ofFn p) := by
  rw [encoded_affine, homogeneousHorner_ofFn_degree]

/-- The unrestricted Bernstein encoding also has a linear Horner evaluator. -/
theorem encoded_directExpansion_homogeneous (choose : ℕ → ℕ → ℕ)
    (sign : ℕ → ℤ) (hchoose : ∀ n k, choose n k = Nat.fast_choose n k)
    (hsign : ∀ m, sign m = (-1) ^ m) (b : ℤ) (n : ℕ)
    (c : Fin (n + 1) → ℤ) :
    encoded b (directExpansion choose sign n c) =
      homogeneousHorner b (1 - b)
        (List.ofFn (fun k : Fin (n + 1) ↦ c k * (choose n k : ℤ))) := by
  rw [encoded_directExpansion choose sign hchoose hsign, homogeneousHorner_ofFn_degree]

end ADMM.UnitCircle.LowerCertificate.IntegerEncoding
