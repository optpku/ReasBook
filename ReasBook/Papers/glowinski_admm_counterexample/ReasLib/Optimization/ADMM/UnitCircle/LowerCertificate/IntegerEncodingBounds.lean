/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.IntegerEncoding
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DirectBernstein
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.IntegerEncodingSemantics
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Tactic.GCongr

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.IntegerEncoding

open scoped BigOperators

def affineBound (n : ℕ) (P R : ℤ) : ℤ :=
  ((n + 1 : ℕ) : ℤ) * P * 2 ^ n * R ^ n

def directBound (n : ℕ) (C : ℤ) : ℤ :=
  ((n + 1 : ℕ) : ℤ) * C * 4 ^ n

theorem affineBound_nonneg (n : ℕ) {P R : ℤ} (hP : 0 ≤ P) (hR : 1 ≤ R) :
    0 ≤ affineBound n P R := by
  unfold affineBound
  positivity

theorem directBound_nonneg (n : ℕ) {C : ℤ} (hC : 0 ≤ C) :
    0 ≤ directBound n C := by
  unfold directBound
  positivity

theorem choose_abs_le_two_pow (choose : ℕ → ℕ → ℕ)
    (hchoose : ∀ n k, choose n k = Nat.fast_choose n k) (a j n : ℕ) (ha : a ≤ n) :
    |(choose a j : ℤ)| ≤ (2 : ℤ) ^ n := by
  rw [abs_of_nonneg (Int.natCast_nonneg _)]
  have hc : (choose a j : ℤ) ≤ (2 : ℤ) ^ a := by
    have h := Nat.choose_le_two_pow a j
    rw [Nat.choose_eq_fast_choose] at h
    rw [hchoose]
    exact_mod_cast h
  exact hc.trans (pow_le_pow_right₀ (by norm_num) ha)

/-- The affine coefficient estimate uses only input bounds, not a numerical
evaluation of any transformed coefficient. It holds at every natural index. -/
theorem affine_coefficient_abs_bound (n : ℕ) (p : Fin (n + 1) → ℤ)
    {P R A B S : ℤ} (hP : 0 ≤ P) (hR : 1 ≤ R)
    (hp : ∀ k, |p k| ≤ P) (hA : |A| ≤ R) (hB : |B| ≤ R) (hS : |S| ≤ R)
    (j : ℕ) :
    |IntegerCoefficients.affineCoefficient Nat.fast_choose
      (fun m ↦ A ^ m) (fun m ↦ B ^ m) (fun m ↦ S ^ m) n p j| ≤
      affineBound n P R := by
  let f : Fin (n + 1) → ℤ := fun k ↦ if j ≤ (k : ℕ) then
    p k * (Nat.fast_choose k j : ℤ) * A ^ ((k : ℕ) - j) * B ^ j * S ^ (n - k)
    else 0
  have hterm (k : Fin (n + 1)) : |f k| ≤ P * 2 ^ n * R ^ n := by
    by_cases hj : j ≤ (k : ℕ)
    · have hk : (k : ℕ) ≤ n := by omega
      have hc := choose_abs_le_two_pow Nat.fast_choose (fun _ _ ↦ rfl) k j n hk
      rw [abs_of_nonneg (Int.natCast_nonneg _)] at hc
      have hw : |A| ^ ((k : ℕ) - j) * |B| ^ j * |S| ^ (n - k) ≤ R ^ n := by
        calc
          _ ≤ R ^ ((k : ℕ) - j) * R ^ j * R ^ (n - k) := by gcongr
          _ = R ^ n := by
            rw [← pow_add, ← pow_add]
            congr 1
            omega
      have hpc : |p k| * (Nat.fast_choose k j : ℤ) ≤ P * 2 ^ n :=
        mul_le_mul (hp k) hc (Int.natCast_nonneg _) hP
      calc
        |f k| = (|p k| * (Nat.fast_choose k j : ℤ)) *
            (|A| ^ ((k : ℕ) - j) * |B| ^ j * |S| ^ (n - k)) := by
          simp only [f, if_pos hj, abs_mul, abs_pow,
            abs_of_nonneg (Int.natCast_nonneg _)]
          ring
        _ ≤ _ := mul_le_mul hpc hw (by positivity) (by positivity)
    · simp only [f, if_neg hj, abs_zero]
      positivity
  calc
    _ = |∑ k, f k| := rfl
    _ ≤ ∑ k, |f k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin (n + 1), P * 2 ^ n * R ^ n :=
      Finset.sum_le_sum (fun k _ ↦ hterm k)
    _ = affineBound n P R := by simp [affineBound, mul_assoc]

/-- A coarse uniform bound for every Bernstein-to-power coefficient. The
estimate is also valid outside the polynomial's degree range. -/
theorem direct_coefficient_abs_bound (choose : ℕ → ℕ → ℕ) (sign : ℕ → ℤ)
    (hchoose : ∀ n k, choose n k = Nat.fast_choose n k)
    (hsign : ∀ m, sign m = (-1) ^ m) (n : ℕ) (c : Fin (n + 1) → ℤ)
    {C : ℤ} (hC : 0 ≤ C) (hc : ∀ k, |c k| ≤ C) (j : ℕ) :
    |IntegerCoefficients.directCoefficient choose sign n c j| ≤ directBound n C := by
  let f : Fin (n + 1) → ℤ := fun k ↦ if (k : ℕ) ≤ j then
    c k * (choose n k : ℤ) * choose (n - k) (j - k) * sign (j - k) else 0
  have hterm (k : Fin (n + 1)) : |f k| ≤ C * 4 ^ n := by
    by_cases hk : (k : ℕ) ≤ j
    · have hcn := choose_abs_le_two_pow choose hchoose n k n le_rfl
      have hck := choose_abs_le_two_pow choose hchoose (n - k) (j - k) n
        (Nat.sub_le _ _)
      have hs : |sign (j - k)| = 1 := by simp [hsign, abs_pow]
      have hfirst : |c k| * |(choose n k : ℤ)| ≤ C * 2 ^ n :=
        mul_le_mul (hc k) hcn (abs_nonneg _) hC
      calc
        |f k| = |c k| * |(choose n k : ℤ)| *
            |(choose (n - k) (j - k) : ℤ)| := by
          simp only [f, if_pos hk, abs_mul, hs, mul_one]
        _ ≤ C * 2 ^ n * 2 ^ n :=
          mul_le_mul hfirst hck (abs_nonneg _) (by positivity)
        _ = C * 4 ^ n := by rw [mul_assoc, ← mul_pow]; norm_num
    · simp only [f, if_neg hk, abs_zero]
      positivity
  calc
    _ = |∑ k, f k| := rfl
    _ ≤ ∑ k, |f k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin (n + 1), C * 4 ^ n :=
      Finset.sum_le_sum (fun k _ ↦ hterm k)
    _ = directBound n C := by simp [directBound, mul_assoc]

theorem bounded_affine (n : ℕ) (p : Fin (n + 1) → ℤ)
    {P R A B S : ℤ} (hP : 0 ≤ P) (hR : 1 ≤ R) (hp : ∀ k, |p k| ≤ P)
    (hA : |A| ≤ R) (hB : |B| ≤ R) (hS : |S| ≤ R) :
    Bounded (IntegerCoefficients.affine n p A B S) (affineBound n P R) := by
  intro a ha
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
  exact affine_coefficient_abs_bound n p hP hR hp hA hB hS j

theorem bounded_directExpansion (choose : ℕ → ℕ → ℕ) (sign : ℕ → ℤ)
    (hchoose : ∀ n k, choose n k = Nat.fast_choose n k)
    (hsign : ∀ m, sign m = (-1) ^ m) (n : ℕ) (c : Fin (n + 1) → ℤ)
    {C : ℤ} (hC : 0 ≤ C) (hc : ∀ k, |c k| ≤ C) :
    Bounded (IntegerCoefficients.directExpansion choose sign n c) (directBound n C) := by
  intro a ha
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
  exact direct_coefficient_abs_bound choose sign hchoose hsign n c hC hc j

theorem Bounded.scale {p : List ℤ} {M : ℤ} (hp : Bounded p M) (a : ℤ) :
    Bounded (IntegerCoefficients.scale a p) (|a| * M) := by
  intro b hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hp x hx) (abs_nonneg a)

theorem Bounded.mono {p : List ℤ} {M N : ℤ} (hp : Bounded p M) (hMN : M ≤ N) :
    Bounded p N := fun a ha ↦ (hp a ha).trans hMN

def commonBound (n : ℕ) (P C R S E : ℤ) : ℤ :=
  max (|E| * affineBound n P R) (|S| ^ n * directBound n C)

theorem commonBound_nonneg (n : ℕ) {P C R S E : ℤ}
    (hP : 0 ≤ P) (_hC : 0 ≤ C) (hR : 1 ≤ R) :
    0 ≤ commonBound n P C R S E :=
  (mul_nonneg (abs_nonneg E) (affineBound_nonneg n hP hR)).trans (le_max_left _ _)

/-- One encoded equality implies precisely the coefficient-list identity
already consumed by the Bernstein positivity certificate. -/
theorem scaled_identity_of_encoded_eq (choose : ℕ → ℕ → ℕ) (sign : ℕ → ℤ)
    (hchoose : ∀ n k, choose n k = Nat.fast_choose n k)
    (hsign : ∀ m, sign m = (-1) ^ m) (n : ℕ) (p c : Fin (n + 1) → ℤ)
    {P C R A B S E b : ℤ} (hP : 0 ≤ P) (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hp : ∀ k, |p k| ≤ P) (hc : ∀ k, |c k| ≤ C)
    (hA : |A| ≤ R) (hB : |B| ≤ R) (hS : |S| ≤ R)
    (hb : 2 * commonBound n P C R S E < b)
    (heq : encoded b (IntegerCoefficients.scale E (IntegerCoefficients.affine n p A B S)) =
      encoded b (IntegerCoefficients.scale (S ^ n)
        (IntegerCoefficients.directExpansion choose sign n c))) :
    IntegerCoefficients.scale E (IntegerCoefficients.affine n p A B S) =
      IntegerCoefficients.scale (S ^ n) (IntegerCoefficients.directExpansion choose sign n c) := by
  apply eq_of_encoded_eq (commonBound_nonneg n hP hC hR) hb
  · simp only [IntegerCoefficients.scale, List.length_map, IntegerCoefficients.affine,
      IntegerCoefficients.directExpansion, List.length_ofFn]
  · exact ((bounded_affine n p hP hR hp hA hB hS).scale E).mono (le_max_left _ _)
  · have h := (bounded_directExpansion choose sign hchoose hsign n c hC hc).scale (S ^ n)
    rw [abs_pow] at h
    exact h.mono (le_max_right _ _)
  · exact heq

/-- The complete replacement for the quadratic coefficient-check family:
two linear homogeneous evaluations and a certified coarse bound suffice. -/
theorem scaled_identity_of_homogeneous_eq (choose : ℕ → ℕ → ℕ) (sign : ℕ → ℤ)
    (hchoose : ∀ n k, choose n k = Nat.fast_choose n k)
    (hsign : ∀ m, sign m = (-1) ^ m) (n : ℕ) (p c : Fin (n + 1) → ℤ)
    {P C R A B S E b : ℤ} (hP : 0 ≤ P) (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hp : ∀ k, |p k| ≤ P) (hc : ∀ k, |c k| ≤ C)
    (hA : |A| ≤ R) (hB : |B| ≤ R) (hS : |S| ≤ R)
    (hb : 2 * commonBound n P C R S E < b)
    (heq : E * homogeneousHorner (A + B * b) S (List.ofFn p) =
      S ^ n * homogeneousHorner b (1 - b)
        (List.ofFn (fun k ↦ c k * (choose n k : ℤ)))) :
    IntegerCoefficients.scale E (IntegerCoefficients.affine n p A B S) =
      IntegerCoefficients.scale (S ^ n) (IntegerCoefficients.directExpansion choose sign n c) := by
  apply scaled_identity_of_encoded_eq choose sign hchoose hsign n p c
    hP hC hR hp hc hA hB hS hb
  rw [encoded_scale, encoded_scale, encoded_affine_homogeneous,
    encoded_directExpansion_homogeneous choose sign hchoose hsign]
  exact heq

end ADMM.UnitCircle.LowerCertificate.IntegerEncoding
