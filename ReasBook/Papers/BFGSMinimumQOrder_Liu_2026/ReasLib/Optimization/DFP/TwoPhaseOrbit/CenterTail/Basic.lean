module

public import Mathlib.Analysis.Normed.Group.Completeness
public import Mathlib.Analysis.Normed.Group.InfiniteSum

public section

noncomputable section

open Filter
open scoped BigOperators Topology

universe u

namespace DFP.TwoPhaseOrbit

/-!
# Generic center-tail adapters

The orbit-specific center files provide estimates for individual increments and
for scalar comparison tails.  The lemmas below isolate the normed-series step:
they convert those inputs into bounds for a vector tail without exposing any
orbit construction.
-/

/-- A summable nonnegative majorant bounds the norm of every shifted vector tail. -/
theorem norm_tsum_nat_add_le_of_majorant
    {E : Type u} [NormedAddCommGroup E] {d : ℕ → E} {m : ℕ → ℝ}
    (hdNorm : Summable (fun j : ℕ ↦ ‖d j‖)) (hm : Summable m)
    (hbound : ∀ j : ℕ, ‖d j‖ ≤ m j) (n : ℕ) :
    ‖∑' k : ℕ, d (n + k)‖ ≤ ∑' k : ℕ, m (n + k) := by
  have hdn : Summable (fun k : ℕ ↦ ‖d (n + k)‖) := by
    have hshift := (summable_nat_add_iff n).mpr hdNorm
    have hcomm : ∀ k : ℕ, ‖d (k + n)‖ = ‖d (n + k)‖ := by
      intro k
      rw [Nat.add_comm k n]
    exact hshift.congr hcomm
  have hmn : Summable (fun k : ℕ ↦ m (n + k)) := by
    have hshift := (summable_nat_add_iff n).mpr hm
    have hcomm : ∀ k : ℕ, m (k + n) = m (n + k) := by
      intro k
      rw [Nat.add_comm k n]
    exact hshift.congr hcomm
  have hshiftBound : ∀ k : ℕ, ‖d (n + k)‖ ≤ m (n + k) := by
    intro k
    exact hbound (n + k)
  calc
    ‖∑' k : ℕ, d (n + k)‖ ≤ ∑' k : ℕ, ‖d (n + k)‖ :=
      norm_tsum_le_tsum_norm hdn
    _ ≤ ∑' k : ℕ, m (n + k) :=
      hdn.tsum_le_tsum hshiftBound hmn

/-- A scalar factor and a summable comparison sequence give a scaled vector-tail
bound. -/
theorem norm_tsum_nat_add_le_of_scaled_majorant
    {E : Type u} [NormedAddCommGroup E] {d : ℕ → E} {u : ℕ → ℝ} {K : ℝ}
    (hdNorm : Summable (fun j : ℕ ↦ ‖d j‖)) (hu : Summable u)
    (hbound : ∀ j : ℕ, ‖d j‖ ≤ K * u j) (n : ℕ) :
    ‖∑' k : ℕ, d (n + k)‖ ≤ K * (∑' k : ℕ, u (n + k)) := by
  have hmajorant : Summable (fun j : ℕ ↦ K * u j) := hu.mul_left K
  have hbase := norm_tsum_nat_add_le_of_majorant hdNorm hmajorant hbound n
  have hun : Summable (fun k : ℕ ↦ u (n + k)) := by
    have hshift := (summable_nat_add_iff n).mpr hu
    have hcomm : ∀ k : ℕ, u (k + n) = u (n + k) := by
      intro k
      rw [Nat.add_comm k n]
    exact hshift.congr hcomm
  calc
    ‖∑' k : ℕ, d (n + k)‖ ≤ ∑' k : ℕ, K * u (n + k) := hbase
    _ = K * (∑' k : ℕ, u (n + k)) := by rw [hun.tsum_mul_left]

/-- A pointwise power estimate gives the corresponding vector-tail bound, with
the exponent kept abstract for reuse by different decay regimes. -/
theorem norm_tsum_nat_add_le_of_power_bound
    {E : Type u} [NormedAddCommGroup E] {d : ℕ → E} {ε : ℕ → ℝ}
    {K : ℝ} (p : ℕ) (hdNorm : Summable (fun j : ℕ ↦ ‖d j‖))
    (hε : Summable (fun j : ℕ ↦ ε j ^ p))
    (hbound : ∀ j : ℕ, ‖d j‖ ≤ K * ε j ^ p) (n : ℕ) :
    ‖∑' k : ℕ, d (n + k)‖ ≤ K * (∑' k : ℕ, ε (n + k) ^ p) := by
  exact norm_tsum_nat_add_le_of_scaled_majorant hdNorm hε hbound n

/-- If a summable series tail is the displacement from a sequence value to its
limit, its norm is bounded by the tail of the increment norms. -/
theorem norm_sub_limit_le_of_tsum_tail_eq
    {E : Type u} [NormedAddCommGroup E] {d : ℕ → E} {x : ℕ → E} {xLim : E}
    (hdNorm : Summable (fun j : ℕ ↦ ‖d j‖))
    (htail : ∀ n : ℕ, (∑' k : ℕ, d (n + k)) = xLim - x n)
    (n : ℕ) :
    ‖x n - xLim‖ ≤ ∑' k : ℕ, ‖d (n + k)‖ := by
  have hdn : Summable (fun k : ℕ ↦ ‖d (n + k)‖) := by
    have hshift := (summable_nat_add_iff n).mpr hdNorm
    have hcomm : ∀ k : ℕ, ‖d (k + n)‖ = ‖d (n + k)‖ := by
      intro k
      rw [Nat.add_comm k n]
    exact hshift.congr hcomm
  rw [norm_sub_rev, ← htail n]
  exact norm_tsum_le_tsum_norm hdn

/-- A convergent sequence with summable forward differences has its remaining
displacement bounded by the norm sum of those differences. -/
theorem norm_sub_limit_le_of_summable_forward_difference
    {E : Type u} [NormedAddCommGroup E] [CompleteSpace E]
    {x : ℕ → E} {xLim : E}
    (hDiffNorm : Summable (fun n : ℕ ↦ ‖x (n + 1) - x n‖))
    (hx : Tendsto x atTop (𝓝 xLim)) (n : ℕ) :
    ‖x n - xLim‖ ≤ ∑' k : ℕ, ‖x (n + k + 1) - x (n + k)‖ := by
  have hTailEq : ∀ n : ℕ,
      (∑' k : ℕ, (x (n + k + 1) - x (n + k))) = xLim - x n := by
    intro j
    have hPartial :
        Tendsto (fun r ↦ ∑ i ∈ Finset.range r, (x (i + 1) - x i)) atTop
          (𝓝 (xLim - x 0)) := by
      simpa only [Finset.sum_range_sub] using hx.sub tendsto_const_nhds
    have hDiff : Summable (fun i : ℕ ↦ x (i + 1) - x i) :=
      Summable.of_norm hDiffNorm
    have hFull : HasSum (fun i : ℕ ↦ x (i + 1) - x i) (xLim - x 0) :=
      (hDiff.hasSum_iff_tendsto_nat).mpr hPartial
    have hTail := (hasSum_nat_add_iff' j).mpr hFull
    have hTailValue :
        (xLim - x 0) - ∑ i ∈ Finset.range j, (x (i + 1) - x i) = xLim - x j := by
      rw [Finset.sum_range_sub]
      abel
    rw [hTailValue] at hTail
    have hReindex (k : ℕ) :
        x (j + k + 1) - x (j + k) = x (k + j + 1) - x (k + j) := by
      rw [Nat.add_comm k j]
    exact (hTail.congr_fun hReindex).tsum_eq
  exact norm_sub_limit_le_of_tsum_tail_eq hDiffNorm hTailEq n

end DFP.TwoPhaseOrbit
