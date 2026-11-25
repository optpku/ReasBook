/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.AffineCoefficients

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

open scoped BigOperators

-- Integer arithmetic retains one common denominator throughout a certificate.
namespace IntegerCoefficients

def toRational (p : List ℤ) : Coefficients := p.map (fun a : ℤ ↦ (a : ℚ))

def add : List ℤ → List ℤ → List ℤ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def scale (a : ℤ) (p : List ℤ) : List ℤ := p.map (a * ·)

def sum (ps : List (List ℤ)) : List ℤ := ps.foldr add []

def basis (n k : ℕ) : List ℤ :=
  List.replicate k 0 ++ List.ofFn (fun j : Fin (n - k + 1) ↦
    (Nat.fast_choose n k : ℤ) * Nat.fast_choose (n - k) j * (-1) ^ (j : ℕ))

def expansion (n : ℕ) (c : Fin (n + 1) → ℤ) : List ℤ :=
  sum (List.ofFn (fun k : Fin (n + 1) ↦ scale (c k) (basis n k)))

theorem cast_add (p q : List ℤ) : toRational (add p q) = LowerCertificate.add (toRational p) (toRational q) := by
  induction p generalizing q with
  | nil => rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q =>
      change (((a + b : ℤ) : ℚ) :: toRational (add p q)) = _
      rw [Int.cast_add, ih]
      rfl

theorem cast_scale (a : ℤ) (p : List ℤ) :
    toRational (scale a p) = LowerCertificate.scale (a : ℚ) (toRational p) := by
  simp only [toRational, scale, LowerCertificate.scale, List.map_map, Function.comp_def, Int.cast_mul]

theorem cast_sum (ps : List (List ℤ)) :
    toRational (sum ps) = LowerCertificate.sum (ps.map toRational) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change toRational (add p (sum ps)) = LowerCertificate.add (toRational p) _
    rw [cast_add, ih]
    rfl

theorem cast_basis (n k : ℕ) : toRational (basis n k) = fastBasis n k := by
  simp only [toRational, basis, fastBasis, List.map_append, List.map_replicate,
    List.map_ofFn, Function.comp_def, Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_zero]

theorem cast_expansion (n : ℕ) (c : Fin (n + 1) → ℤ) :
    toRational (expansion n c) = fastExpansion n (fun k ↦ (c k : ℚ)) := by
  simp only [expansion, cast_sum, List.map_ofFn, Function.comp_def,
    cast_scale, cast_basis, fastExpansion]

/-- The affine transform has denominator `S^n`, fixed across every coefficient. -/
def affine (n : ℕ) (p : Fin (n + 1) → ℤ) (A B S : ℤ) : List ℤ :=
  List.ofFn (fun j : Fin (n + 1) ↦ ∑ k : Fin (n + 1),
    if (j : ℕ) ≤ (k : ℕ) then
      p k * (Nat.fast_choose k j : ℤ) * A ^ ((k : ℕ) - j) * B ^ (j : ℕ) *
        S ^ (n - k)
    else 0)

theorem cast_affine (n : ℕ) (p : Fin (n + 1) → ℤ) (A B S : ℤ) (hS : S ≠ 0) :
    toRational (affine n p A B S) =
      LowerCertificate.scale ((S : ℚ) ^ n)
        (affineCoefficients n (fun k ↦ (p k : ℚ)) ((A : ℚ) / S) ((B : ℚ) / S)) := by
  simp only [toRational, affine, affineCoefficients, LowerCertificate.scale,
    List.map_ofFn, Function.comp_def]
  congr 1
  funext j
  simp only [Int.cast_sum, apply_ite, Int.cast_mul, Int.cast_natCast,
    Int.cast_pow, Int.cast_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hj
  · have hk : (k : ℕ) ≤ n := by omega
    have hSq : (S : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hS
    have he : n = (n - (k : ℕ)) + ((k : ℕ) - (j : ℕ)) + (j : ℕ) := by omega
    have hpow := congrArg (fun m : ℕ ↦ (S : ℚ) ^ m) he
    rw [pow_add, pow_add] at hpow
    rw [hpow, div_pow, div_pow]
    field_simp
  · simp

/-- Positive integer Bernstein coefficients and one checked integer identity
prove positivity, with no rational reduction inside the large identity. -/
theorem positive_affine (n : ℕ) (p c : Fin (n + 1) → ℤ) (A B S E : ℤ)
    (hS : 0 < S) (hE : 0 < E) (hc : ∀ k, 0 < c k)
    (heq : scale E (affine n p A B S) = scale (S ^ n) (expansion n c))
    (t : unitInterval) :
    0 < evaluate (List.ofFn (fun k ↦ (p k : ℚ)))
      (((A : ℚ) / S : ℚ) + ((B : ℚ) / S : ℚ) * (t : ℝ)) := by
  have hs : (1 : ℝ) ≤ evaluate (fastExpansion n (fun k ↦ (c k : ℚ))) t := by
    rw [evaluate_fastExpansion]
    calc
      (1 : ℝ) = ∑ k : Fin (n + 1), (1 : ℝ) * bernstein n k t := by
        simp only [one_mul, bernstein.probability]
      _ ≤ ∑ k : Fin (n + 1), ((c k : ℚ) : ℝ) * bernstein n k t := by
        apply Finset.sum_le_sum
        intro k _
        have hk : (1 : ℤ) ≤ c k := hc k
        have hk' : (1 : ℝ) ≤ ((c k : ℚ) : ℝ) := by exact_mod_cast hk
        exact mul_le_mul_of_nonneg_right hk' bernstein_nonneg
  have h := congrArg (fun q ↦ evaluate (toRational q) (t : ℝ)) heq
  rw [cast_scale, cast_affine n p A B S (ne_of_gt hS), evaluate_scale,
    evaluate_scale, evaluate_affineCoefficients, cast_scale, cast_expansion,
    evaluate_scale] at h
  have hSp : (0 : ℝ) < ((S : ℚ) : ℝ) ^ n := by
    apply pow_pos
    exact_mod_cast hS
  have hEp : (0 : ℝ) < ((E : ℚ) : ℝ) := by exact_mod_cast hE
  have hright : 0 < (((S ^ n : ℤ) : ℚ) : ℝ) *
      evaluate (fastExpansion n (fun k ↦ (c k : ℚ))) t := by
    push_cast
    exact mul_pos hSp (lt_of_lt_of_le zero_lt_one hs)
  rw [← h] at hright
  simp only [Rat.cast_pow] at hright
  exact (mul_pos_iff_of_pos_left hSp).1 ((mul_pos_iff_of_pos_left hEp).1 hright)

end IntegerCoefficients

end ADMM.UnitCircle.LowerCertificate
