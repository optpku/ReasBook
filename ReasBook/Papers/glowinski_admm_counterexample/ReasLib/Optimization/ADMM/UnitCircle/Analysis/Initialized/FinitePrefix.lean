/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Supply.Total
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.DiscountRemoval

@[expose] public section

namespace ADMM.UnitCircle.Initialized

open Supply
open scoped BigOperators

/-- Changing only the initial graph point affects only the first `ℓ+1` supplies. -/
theorem blockSupply_eq_after_prefix {m ℓ : ℕ} (c : LagWeights ℓ) (b : Fin 2)
    (x g xBar gBar : ℕ → Fin m → ℝ)
    (hx : ∀ k, 0 < k → xBar k = x k) (hg : ∀ k, 0 < k → gBar k = g k)
    (k : ℕ) (hk : ℓ + 1 ≤ k) : blockSupply c b xBar gBar k = blockSupply c b x g k := by
  have hk0 : 0 < k := by omega
  unfold blockSupply
  rw [hx k hk0, hg k hk0]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.val + 1 ≤ k := by have := i.isLt; omega
  have hprev : 0 < k - (i.val + 1) := by have := i.isLt; omega
  simp only [lagSupply, zeroDelay, if_pos hi, hx _ hk0, hg _ hk0,
    hx _ hprev, hg _ hprev]

/-- A finite support supply error has an absolute total bound independent of the discount. -/
theorem weighted_tsum_prefix_error_le {a b : ℕ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (L : ℕ)
    (htail : ∀ k, L ≤ k → a k = b k) :
    |∑' k, α ^ (2 * k) * (a k - b k)| ≤
      ∑ k ∈ Finset.range L, |a k - b k| := by
  have heq : (∑' k, α ^ (2 * k) * (a k - b k)) =
      ∑ k ∈ Finset.range L, α ^ (2 * k) * (a k - b k) := by
    apply tsum_eq_sum
    intro k hk
    have hkL : L ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    rw [htail k hkL, sub_self, mul_zero]
  rw [heq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul, abs_of_nonneg (pow_nonneg hα0 _)]
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hα0 hα1)

/-- Two summable supplies differing on a fixed prefix have the same uniform error bound. -/
theorem weighted_totals_prefix_error_le {a b : ℕ → ℝ} {α : ℝ}
    (ha : Summable (fun k ↦ α ^ (2 * k) * a k))
    (hb : Summable (fun k ↦ α ^ (2 * k) * b k))
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (L : ℕ)
    (htail : ∀ k, L ≤ k → a k = b k) :
    |(∑' k, α ^ (2 * k) * a k) - (∑' k, α ^ (2 * k) * b k)| ≤
      ∑ k ∈ Finset.range L, |a k - b k| := by
  rw [← ha.tsum_sub hb]
  simpa only [mul_sub] using weighted_tsum_prefix_error_le hα0 hα1 L htail

/-- A uniform finite initialization error transports a nonpositive auxiliary
supply estimate to a bound for the actual nonnegative residual dissipation. -/
theorem residual_bound_of_prefix_corrections
    {actualSupply auxSupply residual auxResidual : ℕ → ℝ} {α ε : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hs : Summable (fun k ↦ α ^ (2 * k) * actualSupply k))
    (hbs : Summable (fun k ↦ α ^ (2 * k) * auxSupply k))
    (hr : Summable (fun k ↦ α ^ (2 * k) * residual k))
    (hbr : Summable (fun k ↦ α ^ (2 * k) * auxResidual k))
    (hε : 0 ≤ ε) (hSupply : 0 ≤ ∑' k, α ^ (2 * k) * actualSupply k)
    (hAux : (∑' k, α ^ (2 * k) * auxSupply k) +
      ε * (∑' k, α ^ (2 * k) * auxResidual k) ≤ 0)
    (L : ℕ) (hSupplyTail : ∀ k, L ≤ k → auxSupply k = actualSupply k)
    (hResidualTail : ∀ k, 1 ≤ k → auxResidual k = residual k) :
    ε * (∑' k, α ^ (2 * k) * residual k) ≤
      (∑ k ∈ Finset.range L, |auxSupply k - actualSupply k|) +
        ε * |auxResidual 0 - residual 0| := by
  have hS := weighted_totals_prefix_error_le hbs hs hα0 hα1 L hSupplyTail
  have hR := weighted_totals_prefix_error_le hbr hr hα0 hα1 1 hResidualTail
  simp only [Finset.sum_range_one] at hR
  have hR' := mul_le_mul_of_nonneg_left (abs_le.mp hR).1 hε
  have hS' := (abs_le.mp hS).1
  linarith

end ADMM.UnitCircle.Initialized
