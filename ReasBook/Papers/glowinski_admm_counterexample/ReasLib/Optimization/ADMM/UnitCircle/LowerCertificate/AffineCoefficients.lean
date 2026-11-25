/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FastBernstein

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

open scoped BigOperators

/-- Direct coefficient formula for an affine substitution. Unlike recursive
Horner composition, this finite triangular formula does not duplicate recursive
tail computations during kernel reduction. -/
def affineCoefficients (n : ℕ) (p : Fin (n + 1) → ℚ) (a b : ℚ) : Coefficients :=
  List.ofFn (fun j : Fin (n + 1) ↦ ∑ k : Fin (n + 1),
    if (j : ℕ) ≤ (k : ℕ) then
      p k * (Nat.fast_choose k j : ℚ) * a ^ ((k : ℕ) - j) * b ^ (j : ℕ)
    else 0)

theorem evaluate_affineCoefficients (n : ℕ) (p : Fin (n + 1) → ℚ) (a b : ℚ) (x : ℝ) :
    evaluate (affineCoefficients n p a b) x =
      evaluate (List.ofFn p) ((a : ℝ) + b * x) := by
  unfold affineCoefficients
  rw [evaluate_ofFn, evaluate_ofFn]
  simp only [Rat.cast_sum, apply_ite, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_zero, ← Nat.choose_eq_fast_choose]
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
      (p k : ℝ) * (Nat.choose k j : ℝ) * (a : ℝ) ^ ((k : ℕ) - j) *
        (b : ℝ) ^ j else 0) * x ^ j) (n + 1)
  calc
    (∑ j : Fin (n + 1),
      (if (j : ℕ) ≤ (k : ℕ) then
        (p k : ℝ) * (Nat.choose k j : ℝ) * (a : ℝ) ^ ((k : ℕ) - j) *
          (b : ℝ) ^ (j : ℕ) else 0) * x ^ (j : ℕ)) =
      ∑ j ∈ Finset.range (n + 1), if j ≤ (k : ℕ) then
        (p k : ℝ) * (Nat.choose k j : ℝ) * (a : ℝ) ^ ((k : ℕ) - j) *
          (b : ℝ) ^ j * x ^ j else 0 := by
        simpa only [ite_mul, zero_mul] using hfin
    _ = ∑ j ∈ Finset.range ((k : ℕ) + 1),
        (p k : ℝ) * (Nat.choose k j : ℝ) * (a : ℝ) ^ ((k : ℕ) - j) *
          (b : ℝ) ^ j * x ^ j := by
        rw [← Finset.sum_filter, hsub]
    _ = (p k : ℝ) * ((b : ℝ) * x + a) ^ (k : ℕ) := by
      rw [add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_pow]
      ring
    _ = _ := by rw [add_comm ((b : ℝ) * x)]

/-- Directly checked affine coefficients are enough for an interval certificate. -/
theorem positive_on_interval_affine (n : ℕ) (p : Fin (n + 1) → ℚ)
    (a b : ℚ) (hab : a < b) (c : Fin (n + 1) → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (hc : ∀ k, δ ≤ c k)
    (heq : affineCoefficients n p a (b - a) = fastExpansion n c)
    {x : ℝ} (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    0 < evaluate (List.ofFn p) x := by
  have hba : 0 < (b : ℝ) - a := by exact_mod_cast sub_pos.mpr hab
  let t : unitInterval := ⟨(x - a) / (b - a), by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hba.le
    · exact (div_le_one hba).mpr (sub_le_sub_right hx.2 a)⟩
  have ht : (a : ℝ) + ((b - a : ℚ) : ℝ) * (t : ℝ) = x := by
    rw [Rat.cast_sub]
    dsimp [t]
    rw [mul_div_cancel₀ _ (ne_of_gt hba)]
    ring
  have hs : (δ : ℝ) ≤ evaluate (fastExpansion n c) t := by
    rw [evaluate_fastExpansion]
    calc
      (δ : ℝ) = ∑ k : Fin (n + 1), (δ : ℝ) * bernstein n k t := by
        rw [← Finset.mul_sum, bernstein.probability, mul_one]
      _ ≤ ∑ k : Fin (n + 1), (c k : ℝ) * bernstein n k t := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (Rat.cast_le.mpr (hc k)) bernstein_nonneg
  have h := congrArg (fun q ↦ evaluate q (t : ℝ)) heq
  rw [evaluate_affineCoefficients, ht] at h
  exact (Rat.cast_pos.mpr hδ).trans_le (h ▸ hs)

end ADMM.UnitCircle.LowerCertificate
