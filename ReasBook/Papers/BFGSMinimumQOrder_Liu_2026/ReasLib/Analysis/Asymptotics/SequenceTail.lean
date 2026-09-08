module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Normed.Group.Completeness
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Quantitative tails of convergent sequences

This file collects the telescoping and norm estimates that turn control of
successive differences into control of the distance to a sequence's limit.
The results apply to sequences in an arbitrary complete normed additive group.
-/

public section

open Filter
open scoped Asymptotics BigOperators Topology

universe u

namespace SequenceTail

variable {E : Type u} [NormedAddCommGroup E]

/-- The sum of the forward-difference tail of a convergent sequence is its
remaining displacement. -/
theorem tsum_forwardDiff {a : ℕ → E} {aLim : E}
    (hDiff : Summable fun n ↦ a (n + 1) - a n)
    (ha : Tendsto a atTop (𝓝 aLim)) (n : ℕ) :
    ∑' k : ℕ, (a (n + k + 1) - a (n + k)) = aLim - a n := by
  have hPartial :
      Tendsto (fun m ↦ ∑ i ∈ Finset.range m, (a (i + 1) - a i)) atTop
        (𝓝 (aLim - a 0)) := by
    simpa only [Finset.sum_range_sub] using ha.sub tendsto_const_nhds
  have hFull : HasSum (fun i ↦ a (i + 1) - a i) (aLim - a 0) :=
    (hDiff.hasSum_iff_tendsto_nat).mpr hPartial
  have hTail := (hasSum_nat_add_iff' n).mpr hFull
  have hTailValue :
      (aLim - a 0) - ∑ i ∈ Finset.range n, (a (i + 1) - a i) = aLim - a n := by
    rw [Finset.sum_range_sub]
    abel
  rw [hTailValue] at hTail
  have hReindex (k : ℕ) :
      a (n + k + 1) - a (n + k) = a (k + n + 1) - a (k + n) := by
    rw [Nat.add_comm k n]
  exact (hTail.congr_fun hReindex).tsum_eq

variable [CompleteSpace E]

/-- The distance from a convergent sequence to its limit is bounded by the
sum of the norms of its remaining forward differences. -/
theorem norm_sub_limit_le_tsum {a : ℕ → E} {aLim : E}
    (hDiffNorm : Summable fun n ↦ ‖a (n + 1) - a n‖)
    (ha : Tendsto a atTop (𝓝 aLim)) (n : ℕ) :
    ‖a n - aLim‖ ≤ ∑' k : ℕ, ‖a (n + k + 1) - a (n + k)‖ := by
  have hDiff : Summable (fun m ↦ a (m + 1) - a m) :=
    Summable.of_norm hDiffNorm
  have hShift : Summable (fun k ↦ ‖a (n + k + 1) - a (n + k)‖) := by
    have h := (summable_nat_add_iff n).mpr hDiffNorm
    refine h.congr ?_
    intro k
    rw [Nat.add_comm k n]
  rw [norm_sub_rev, ← tsum_forwardDiff hDiff ha n]
  exact norm_tsum_le_tsum_norm hShift

/-- A pointwise comparison for forward differences and a summable comparison
tail give a pointwise bound on the distance to the limit. -/
theorem norm_sub_limit_le {a : ℕ → E} {aLim : E} {u v : ℕ → ℝ} {K C : ℝ}
    (hK : 0 ≤ K)
    (hDiffNorm : Summable fun n ↦ ‖a (n + 1) - a n‖)
    (ha : Tendsto a atTop (𝓝 aLim))
    (hDiffBound : ∀ n, ‖a (n + 1) - a n‖ ≤ K * u n)
    (hTail : ∀ n, Summable (fun k ↦ u (n + k)) ∧
      (∑' k : ℕ, u (n + k)) ≤ C * v n) (n : ℕ) :
    ‖a n - aLim‖ ≤ K * C * v n := by
  have hNormShift : Summable (fun k ↦ ‖a (n + k + 1) - a (n + k)‖) := by
    have h := (summable_nat_add_iff n).mpr hDiffNorm
    refine h.congr ?_
    intro k
    rw [Nat.add_comm k n]
  calc
    ‖a n - aLim‖ ≤ ∑' k : ℕ, ‖a (n + k + 1) - a (n + k)‖ :=
      norm_sub_limit_le_tsum hDiffNorm ha n
    _ ≤ ∑' k : ℕ, K * u (n + k) :=
      hNormShift.tsum_le_tsum (fun k ↦ hDiffBound (n + k)) ((hTail n).1.mul_left K)
    _ = K * (∑' k : ℕ, u (n + k)) := by
      rw [(hTail n).1.tsum_mul_left]
    _ ≤ K * (C * v n) := mul_le_mul_of_nonneg_left (hTail n).2 hK
    _ = K * C * v n := by ring

/-- An eventual comparison for forward differences and a uniformly summable
comparison tail give the corresponding big-O bound for the distance to the
limit. -/
theorem norm_sub_limit_isBigO {a : ℕ → E} {aLim : E} {u v : ℕ → ℝ} {K C : ℝ}
    (hK : 0 ≤ K) (hv : ∀ n, 0 ≤ v n)
    (hDiffNorm : Summable fun n ↦ ‖a (n + 1) - a n‖)
    (ha : Tendsto a atTop (𝓝 aLim))
    (hDiffBound : ∀ᶠ n in atTop, ‖a (n + 1) - a n‖ ≤ K * u n)
    (hTail : ∀ n, Summable (fun k ↦ u (n + k)) ∧
      (∑' k : ℕ, u (n + k)) ≤ C * v n) :
    (fun n ↦ ‖a n - aLim‖) =O[atTop] v := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hDiffBound
  apply Asymptotics.IsBigO.of_bound (K * C)
  refine eventually_atTop.mpr ⟨N, ?_⟩
  intro n hn
  have hShiftBound (k : ℕ) :
      ‖a (n + k + 1) - a (n + k)‖ ≤ K * u (n + k) :=
    hN (n + k) (hn.trans (Nat.le_add_right n k))
  have hNormShift : Summable (fun k ↦ ‖a (n + k + 1) - a (n + k)‖) := by
    have h := (summable_nat_add_iff n).mpr hDiffNorm
    refine h.congr ?_
    intro k
    rw [Nat.add_comm k n]
  have hRaw : ‖a n - aLim‖ ≤ K * C * v n := by
    calc
      ‖a n - aLim‖ ≤ ∑' k : ℕ, ‖a (n + k + 1) - a (n + k)‖ :=
        norm_sub_limit_le_tsum hDiffNorm ha n
      _ ≤ ∑' k : ℕ, K * u (n + k) :=
        hNormShift.tsum_le_tsum hShiftBound ((hTail n).1.mul_left K)
      _ = K * (∑' k : ℕ, u (n + k)) := by
        rw [(hTail n).1.tsum_mul_left]
      _ ≤ K * (C * v n) := mul_le_mul_of_nonneg_left (hTail n).2 hK
      _ = K * C * v n := by ring
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (hv n)] using hRaw

end SequenceTail
