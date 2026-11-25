/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Coefficients

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

open scoped BigOperators

theorem evaluate_append (p q : Coefficients) (x : ℝ) :
    evaluate (p ++ q) x = evaluate p x + x ^ p.length * evaluate q x := by
  induction p with
  | nil => simp [evaluate]
  | cons a p ih => simp [evaluate, ih, pow_succ]; ring

theorem evaluate_zeroes (n : ℕ) (x : ℝ) : evaluate (List.replicate n 0) x = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem evaluate_ofFn (n : ℕ) (c : Fin (n + 1) → ℚ) (x : ℝ) :
    evaluate (List.ofFn c) x = ∑ k : Fin (n + 1), (c k : ℝ) * x ^ (k : ℕ) := by
  induction n with
  | zero => simp [evaluate]
  | succ n ih =>
    rw [List.ofFn_succ, evaluate_cons, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    simp only [Fin.val_succ, pow_succ]
    ring

/-- Binomial coefficients are computed by descending factorials, avoiding
the exponentially recursive definitional equations of `Nat.choose`. -/
def fastBasis (n k : ℕ) : Coefficients :=
  List.replicate k 0 ++ List.ofFn (fun j : Fin (n - k + 1) ↦
    (Nat.fast_choose n k : ℚ) * Nat.fast_choose (n - k) j * (-1) ^ (j : ℕ))

theorem evaluate_fastBasis (n k : ℕ) (x : unitInterval) :
    evaluate (fastBasis n k) x = bernstein n k x := by
  rw [fastBasis, evaluate_append, evaluate_zeroes, zero_add,
    List.length_replicate, evaluate_ofFn]
  simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow, Rat.cast_neg, Rat.cast_one]
  simp only [← Nat.choose_eq_fast_choose]
  rw [bernstein_apply]
  have hbin : (∑ j : Fin (n - k + 1),
      (Nat.choose (n - k) j : ℝ) * (-1) ^ (j : ℕ) * (x : ℝ) ^ (j : ℕ)) =
      (1 - (x : ℝ)) ^ (n - k) := by
    calc
      _ = ∑ j ∈ Finset.range (n - k + 1),
          (-(x : ℝ)) ^ j * (1 : ℝ) ^ (n - k - j) * (n - k).choose j := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro j _
        conv_rhs => rw [neg_pow]
        simp only [one_pow, mul_one]
        ring
      _ = _ := by rw [← add_pow]; congr 1 <;> ring
  calc
    (x : ℝ) ^ k * (∑ j : Fin (n - k + 1),
        (n.choose k : ℝ) * (Nat.choose (n - k) j : ℝ) *
          (-1) ^ (j : ℕ) * (x : ℝ) ^ (j : ℕ)) =
      (n.choose k : ℝ) * (x : ℝ) ^ k * (∑ j : Fin (n - k + 1),
        (Nat.choose (n - k) j : ℝ) * (-1) ^ (j : ℕ) * (x : ℝ) ^ (j : ℕ)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = _ := by rw [hbin]

def fastExpansion (n : ℕ) (c : Fin (n + 1) → ℚ) : Coefficients :=
  sum (List.ofFn (fun k : Fin (n + 1) ↦ scale (c k) (fastBasis n k)))

theorem evaluate_fastExpansion (n : ℕ) (c : Fin (n + 1) → ℚ) (x : unitInterval) :
    evaluate (fastExpansion n c) x =
      ∑ k : Fin (n + 1), (c k : ℝ) * bernstein n k x := by
  unfold fastExpansion
  rw [evaluate_sum, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  change evaluate (scale (c k) (fastBasis n k)) (x : ℝ) = _
  rw [evaluate_scale, evaluate_fastBasis]

theorem positive_on_interval_fast (p : Coefficients) (a b : ℚ) (hab : a < b)
    (n : ℕ) (c : Fin (n + 1) → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (hc : ∀ k, δ ≤ c k)
    (heq : compose p [a, b - a] = fastExpansion n c)
    {x : ℝ} (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) : 0 < evaluate p x := by
  have hba : 0 < (b : ℝ) - a := by exact_mod_cast sub_pos.mpr hab
  let t : unitInterval := ⟨(x - a) / (b - a), by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hba.le
    · exact (div_le_one hba).mpr (sub_le_sub_right hx.2 a)⟩
  have ht : evaluate [a, b - a] (t : ℝ) = x := by
    simp only [evaluate_cons, evaluate_nil, mul_zero, add_zero, Rat.cast_sub]
    dsimp [t]
    rw [mul_comm ((x - a) / (b - a)), mul_div_cancel₀ _ (ne_of_gt hba)]
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
  rw [evaluate_compose, ht] at h
  exact (Rat.cast_pos.mpr hδ).trans_le (h ▸ hs)

end ADMM.UnitCircle.LowerCertificate
