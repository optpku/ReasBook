/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Supply.Bilateral
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Fourier.Transform

@[expose] public section

open scoped BigOperators ComplexConjugate
open ADMM.ConvergenceProof

namespace ADMM.UnitCircle.Supply

/-- Pairings supported at nonnegative times have the same bilateral and
one-sided totals. -/
theorem tsum_bilateral_eq_nat {F : ℤ → ℂ} (hF : Summable F)
    (hneg : ∀ k : ℕ, F (-(k + 1 : ℤ)) = 0) :
    (∑' k : ℤ, F k) = ∑' k : ℕ, F k := by
  rw [← tsum_nat_add_neg_add_one hF]
  apply tsum_congr
  intro k
  rw [hneg, add_zero]

lemma complexSequence_delay_nat {m : ℕ} (α : ℝ) (x : ℕ → Fin m → ℝ)
    (a : Fin m) (j k : ℕ) :
    complexSequence α x a ((k : ℤ) - j) =
      if j ≤ k then ((α ^ (k - j) * x (k - j) a : ℝ) : ℂ) else 0 := by
  exact extendZero_delay _ j k

/-- Exact cancellation of the time weights in a delayed point pairing. -/
lemma weighted_delay_pair_term {m : ℕ} (α : ℝ) (x g : ℕ → Fin m → ℝ)
    (a : Fin m) (j k : ℕ) :
    ((timeWeight α k * g k a * zeroDelay x j k a : ℝ) : ℂ) =
      (α ^ j : ℂ) * (conj (complexSequence α g a k) *
        complexSequence α x a ((k : ℤ) - j)) := by
  rw [complexSequence_nat, complexSequence_delay_nat]
  by_cases hj : j ≤ k
  · simp only [if_pos hj, zeroDelay, if_pos hj, Complex.conj_ofReal]
    have hp : α ^ j * α ^ (k - j) = α ^ k := by
      rw [← pow_add, Nat.add_sub_of_le hj]
    have heq : timeWeight α k * g k a * x (k - j) a =
        α ^ j * ((α ^ k * g k a) * (α ^ (k - j) * x (k - j) a)) := by
      dsimp only [timeWeight]
      rw [show 2 * k = k + k by omega, pow_add]
      nlinarith [congrArg (fun r : ℝ ↦ α ^ k * g k a * x (k - j) a * r) hp]
    exact_mod_cast heq
  · simp only [if_neg hj, zeroDelay, if_neg hj, Pi.zero_apply, mul_zero, Complex.ofReal_zero]

/-- Exact cancellation of the time weights when the normal is delayed. -/
lemma weighted_reverse_pair_term {m : ℕ} (α : ℝ) (x g : ℕ → Fin m → ℝ)
    (a : Fin m) (j k : ℕ) :
    ((timeWeight α k * zeroDelay g j k a * x k a : ℝ) : ℂ) =
      (α ^ j : ℂ) * (conj (complexSequence α g a ((k : ℤ) - j)) *
        complexSequence α x a k) := by
  rw [complexSequence_nat, complexSequence_delay_nat]
  by_cases hj : j ≤ k
  · simp only [if_pos hj, zeroDelay, if_pos hj, Complex.conj_ofReal]
    have hp : α ^ j * α ^ (k - j) = α ^ k := by
      rw [← pow_add, Nat.add_sub_of_le hj]
    have heq : timeWeight α k * g (k - j) a * x k a =
        α ^ j * ((α ^ (k - j) * g (k - j) a) * (α ^ k * x k a)) := by
      dsimp only [timeWeight]
      rw [show 2 * k = k + k by omega, pow_add]
      nlinarith [congrArg (fun r : ℝ ↦ α ^ k * g (k - j) a * x k a * r) hp]
    exact_mod_cast heq
  · simp only [if_neg hj, zeroDelay, if_neg hj, Pi.zero_apply, mul_zero,
      map_zero, zero_mul, Complex.ofReal_zero]

/-- Summability of the genuine complex delayed pairing follows from ℓ₂. -/
theorem summable_complex_pair {m : ℕ} (α : ℝ) (x g : ℕ → Fin m → ℝ)
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k)))
    (a : Fin m) (j : ℤ) :
    Summable (fun k : ℤ ↦ conj (complexSequence α g a k) *
      complexSequence α x a (k - j)) := by
  simpa only [RCLike.inner_apply', Fourier.delay_apply, complexLp_apply] using
    (lp.summable_inner (𝕜 := ℂ) (complexLp α g hg a)
      (Fourier.delay j (complexLp α x hx a)))

/-- The one-sided weighted backward comparison is the actual bilateral delay
pairing, multiplied by the exact power of the discount. -/
theorem weighted_delay_pairing {m : ℕ} (α : ℝ) (x g : ℕ → Fin m → ℝ)
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k)))
    (a : Fin m) (j : ℕ) :
    ((∑' k, timeWeight α k * g k a * zeroDelay x j k a : ℝ) : ℂ) =
      (α ^ j : ℂ) * ∑' k : ℤ, conj (complexSequence α g a k) *
        complexSequence α x a (k - j) := by
  rw [tsum_bilateral_eq_nat (summable_complex_pair α x g hx hg a j)]
  · rw [Complex.ofReal_tsum, ← tsum_mul_left]
    exact tsum_congr (fun k ↦ weighted_delay_pair_term α x g a j k)
  · intro k
    simp only [complexSequence_negSucc, map_zero, zero_mul, Complex.ofReal_zero]

/-- The same origin pairing is recovered by taking the zero lag. -/
theorem weighted_origin_pairing {m : ℕ} (α : ℝ) (x g : ℕ → Fin m → ℝ)
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k)))
    (a : Fin m) :
    ((∑' k, timeWeight α k * g k a * x k a : ℝ) : ℂ) =
      ∑' k : ℤ, conj (complexSequence α g a k) * complexSequence α x a k := by
  simpa only [zeroDelay, Nat.zero_le, if_true, Nat.sub_zero, pow_zero, one_mul,
    Int.natCast_zero, sub_zero] using weighted_delay_pairing α x g hx hg a 0


/-- Summability when the normal, rather than the point, carries the delay. -/
theorem summable_complex_reverse_pair {m : ℕ} (α : ℝ) (x g : ℕ → Fin m → ℝ)
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k)))
    (a : Fin m) (j : ℤ) :
    Summable (fun k : ℤ ↦ conj (complexSequence α g a (k - j)) *
      complexSequence α x a k) := by
  simpa only [RCLike.inner_apply', Fourier.delay_apply, complexLp_apply] using
    (lp.summable_inner (𝕜 := ℂ) (Fourier.delay j (complexLp α g hg a))
      (complexLp α x hx a))

/-- The reverse comparison is the true bilateral delay in the normal slot. -/
theorem weighted_reverse_pairing {m : ℕ} (α : ℝ) (x g : ℕ → Fin m → ℝ)
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k)))
    (a : Fin m) (j : ℕ) :
    ((∑' k, timeWeight α k * zeroDelay g j k a * x k a : ℝ) : ℂ) =
      (α ^ j : ℂ) * ∑' k : ℤ, conj (complexSequence α g a (k - j)) *
        complexSequence α x a k := by
  rw [tsum_bilateral_eq_nat (summable_complex_reverse_pair α x g hx hg a j)]
  · rw [Complex.ofReal_tsum, ← tsum_mul_left]
    exact tsum_congr (fun k ↦ weighted_reverse_pair_term α x g a j k)
  · intro k
    simp only [complexSequence_negSucc, mul_zero]

/-- Each scalar coordinate pairing is absolutely summable. -/
theorem summable_weighted_coordinate_pair {m : ℕ} {α : ℝ}
    {x g : ℕ → Fin m → ℝ}
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k)))
    (a : Fin m) : Summable (fun k ↦ timeWeight α k * g k a * x k a) := by
  apply Summable.of_norm_bounded
    (((summable_weighted_coordinate hg a).add (summable_weighted_coordinate hx a)).div_const 2)
  intro k
  have h : |g k a * x k a| ≤ ((g k a) ^ 2 + (x k a) ^ 2) / 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (g k a + x k a), sq_nonneg (g k a - x k a)]
  rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg (timeWeight_nonneg α k)]
  have hp := mul_le_mul_of_nonneg_left h (timeWeight_nonneg α k)
  nlinarith

/-- Delaying both sides of a pairing contributes the squared lag discount. -/
theorem weighted_both_delayed_pairing {m : ℕ} (α : ℝ) (x g : ℕ → Fin m → ℝ)
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k)))
    (a : Fin m) (j : ℕ) :
    (∑' k, timeWeight α k * zeroDelay g j k a * zeroDelay x j k a) =
      timeWeight α j * (∑' k, timeWeight α k * g k a * x k a) := by
  have hpair : Summable (fun k ↦ timeWeight α k * (g k a * x k a)) := by
    simpa only [mul_assoc] using summable_weighted_coordinate_pair hx hg a
  have hv := weighted_zeroDelay (x := fun k ↦ g k a * x k a) (α := α) hpair j
  have heq : (fun k ↦ timeWeight α k * zeroDelay g j k a * zeroDelay x j k a) =
      (fun k ↦ timeWeight α k * zeroDelay (fun n ↦ g n a * x n a) j k) := by
    funext k
    by_cases hj : j ≤ k <;> simp [zeroDelay, hj, mul_assoc]
  rw [heq]
  simpa only [mul_assoc] using hv.2

end ADMM.UnitCircle.Supply
