module

public import Mathlib.Topology.Algebra.InfiniteSum.Real

public section

open Filter
open scoped BigOperators Topology

namespace ParabolicRecurrence

/-- A finite sum of consecutive decrements of a shifted real sequence telescopes. -/
theorem sum_range_shift_sub (u : ℕ → ℝ) (j n : ℕ) :
    ∑ k ∈ Finset.range n, (u (j + k) - u (j + k + 1)) = u j - u (j + n) := by
  simpa only [Nat.add_zero, Nat.add_assoc] using
    (Finset.sum_range_sub' (fun k ↦ u (j + k)) n)

/-- A positive family whose decrement dominates `c * ε i j ^ (p + 1)` has uniformly
summable shifted `q`-power tails whenever `p + 1 ≤ q`, with the telescoping bound
`∑' k, ε i (j + k) ^ q ≤ c⁻¹ * ε i j ^ (q - p)`. -/
theorem summable_tail_pow_and_tsum_le_of_decrement {ι : Type*} {ε : ι → ℕ → ℝ}
    {p q : ℕ} {c : ℝ} (hc : 0 < c) (hpq : p + 1 ≤ q)
    (hpositive : ∀ i j, 0 < ε i j)
    (hdecrement : ∀ i j, c * ε i j ^ (p + 1) ≤ ε i j - ε i (j + 1))
    (i : ι) (j : ℕ) :
    Summable (fun k : ℕ ↦ ε i (j + k) ^ q) ∧
      (∑' k : ℕ, ε i (j + k) ^ q) ≤ c⁻¹ * ε i j ^ (q - p) := by
  have hstep (n : ℕ) : ε i (n + 1) ≤ ε i n := by
    have hnonneg : 0 ≤ c * ε i n ^ (p + 1) :=
      mul_nonneg hc.le (pow_nonneg (hpositive i n).le _)
    exact sub_nonneg.mp (hnonneg.trans (hdecrement i n))
  have hantitone : Antitone (ε i) := antitone_nat_of_succ_le hstep
  let r : ℕ := q - (p + 1)
  have hpowerMono (k : ℕ) : ε i (j + k) ^ r ≤ ε i j ^ r := by
    have hindex : j ≤ j + k := Nat.le_add_right j k
    exact pow_le_pow_left₀ (hpositive i (j + k)).le (hantitone hindex) r
  have hpowerDecrement (k : ℕ) :
      ε i (j + k) ^ (p + 1) ≤
        c⁻¹ * (ε i (j + k) - ε i (j + k + 1)) := by
    exact (le_inv_mul_iff₀ hc).2 (hdecrement i (j + k))
  have hterm (k : ℕ) :
      ε i (j + k) ^ q ≤
        (c⁻¹ * ε i j ^ r) * (ε i (j + k) - ε i (j + k + 1)) := by
    rw [← Nat.sub_add_cancel hpq, pow_add]
    calc
      ε i (j + k) ^ r * ε i (j + k) ^ (p + 1) ≤
          ε i j ^ r * ε i (j + k) ^ (p + 1) :=
        mul_le_mul_of_nonneg_right (hpowerMono k)
          (pow_nonneg (hpositive i (j + k)).le _)
      _ ≤ ε i j ^ r *
          (c⁻¹ * (ε i (j + k) - ε i (j + k + 1))) :=
        mul_le_mul_of_nonneg_left (hpowerDecrement k)
          (pow_nonneg (hpositive i j).le _)
      _ = (c⁻¹ * ε i j ^ r) *
          (ε i (j + k) - ε i (j + k + 1)) := by ring
  have hfactorNonneg : 0 ≤ c⁻¹ * ε i j ^ r :=
    mul_nonneg (inv_nonneg.mpr hc.le) (pow_nonneg (hpositive i j).le _)
  have hfinite (n : ℕ) :
      ∑ k ∈ Finset.range n, ε i (j + k) ^ q ≤ c⁻¹ * ε i j ^ (q - p) := by
    calc
      ∑ k ∈ Finset.range n, ε i (j + k) ^ q ≤
          ∑ k ∈ Finset.range n,
            (c⁻¹ * ε i j ^ r) * (ε i (j + k) - ε i (j + k + 1)) :=
        Finset.sum_le_sum fun k _ ↦ hterm k
      _ = (c⁻¹ * ε i j ^ r) *
          ∑ k ∈ Finset.range n, (ε i (j + k) - ε i (j + k + 1)) := by
        rw [Finset.mul_sum]
      _ = (c⁻¹ * ε i j ^ r) * (ε i j - ε i (j + n)) := by
        rw [sum_range_shift_sub]
      _ ≤ (c⁻¹ * ε i j ^ r) * ε i j := by
        apply mul_le_mul_of_nonneg_left
        · exact sub_le_self _ (hpositive i (j + n)).le
        · exact hfactorNonneg
      _ = c⁻¹ * ε i j ^ (q - p) := by
        have hexponent : r + 1 = q - p := by
          dsimp [r]
          omega
        rw [mul_assoc, ← pow_succ, hexponent]
  have htermNonneg (k : ℕ) : 0 ≤ ε i (j + k) ^ q :=
    pow_nonneg (hpositive i (j + k)).le _
  have hsummable : Summable (fun k : ℕ ↦ ε i (j + k) ^ q) :=
    summable_of_sum_range_le htermNonneg hfinite
  have htsum :
      (∑' k : ℕ, ε i (j + k) ^ q) ≤ c⁻¹ * ε i j ^ (q - p) :=
    Real.tsum_le_of_sum_range_le htermNonneg hfinite
  exact ⟨hsummable, htsum⟩

/-- Two-sided order-`p + 1` decrement bounds give the sharp interval for the
corresponding power tail when every sequence tends to zero. -/
theorem tsum_tail_pow_interval_of_two_sided_decrement {ι : Type*} {ε : ι → ℕ → ℝ}
    {p : ℕ} {a δ : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ) (hδa : δ < a)
    (hpositive : ∀ i j, 0 < ε i j)
    (hzero : ∀ i, Tendsto (ε i) atTop (𝓝 0))
    (hlower : ∀ i j,
      (a - δ) * ε i j ^ (p + 1) ≤ ε i j - ε i (j + 1))
    (hupper : ∀ i j,
      ε i j - ε i (j + 1) ≤ (a + δ) * ε i j ^ (p + 1))
    (i : ι) (j : ℕ) :
    ε i j / (a + δ) ≤ ∑' k : ℕ, ε i (j + k) ^ (p + 1) ∧
      (∑' k : ℕ, ε i (j + k) ^ (p + 1)) ≤ ε i j / (a - δ) := by
  have hminus : 0 < a - δ := sub_pos.mpr hδa
  have hplus : 0 < a + δ := add_pos_of_pos_of_nonneg ha hδ
  have hpacket := summable_tail_pow_and_tsum_le_of_decrement
    (c := a - δ) (q := p + 1) hminus le_rfl hpositive hlower i j
  have hsummable : Summable (fun k : ℕ ↦ ε i (j + k) ^ (p + 1)) := hpacket.1
  have htailUpper :
      (∑' k : ℕ, ε i (j + k) ^ (p + 1)) ≤ ε i j / (a - δ) := by
    calc
      (∑' k : ℕ, ε i (j + k) ^ (p + 1)) ≤
          (a - δ)⁻¹ * ε i j ^ (p + 1 - p) := hpacket.2
      _ = ε i j / (a - δ) := by
        have hexponent : p + 1 - p = 1 := by omega
        rw [hexponent, pow_one, div_eq_mul_inv, mul_comm]
  have htermLower (k : ℕ) :
      (a + δ)⁻¹ * (ε i (j + k) - ε i (j + k + 1)) ≤
        ε i (j + k) ^ (p + 1) := by
    exact (inv_mul_le_iff₀ hplus).2 (hupper i (j + k))
  have hfiniteLower (n : ℕ) :
      (a + δ)⁻¹ * (ε i j - ε i (j + n)) ≤
        ∑ k ∈ Finset.range n, ε i (j + k) ^ (p + 1) := by
    calc
      (a + δ)⁻¹ * (ε i j - ε i (j + n)) =
          (a + δ)⁻¹ *
            ∑ k ∈ Finset.range n, (ε i (j + k) - ε i (j + k + 1)) := by
        rw [sum_range_shift_sub]
      _ = ∑ k ∈ Finset.range n,
          (a + δ)⁻¹ * (ε i (j + k) - ε i (j + k + 1)) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.range n, ε i (j + k) ^ (p + 1) :=
        Finset.sum_le_sum fun k _ ↦ htermLower k
  have hshiftZero : Tendsto (fun n ↦ ε i (j + n)) atTop (𝓝 0) := by
    have hcomp := (hzero i).comp (tendsto_add_atTop_nat j)
    refine hcomp.congr' (Eventually.of_forall ?_)
    intro n
    simp only [Function.comp_apply]
    rw [Nat.add_comm]
  have hdiffTendsto :
      Tendsto (fun n ↦ ε i j - ε i (j + n)) atTop (𝓝 (ε i j)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hshiftZero
  have hleftTendsto :
      Tendsto (fun n ↦ (a + δ)⁻¹ * (ε i j - ε i (j + n))) atTop
        (𝓝 ((a + δ)⁻¹ * ε i j)) := by
    exact tendsto_const_nhds.mul hdiffTendsto
  have hpartialTendsto :
      Tendsto (fun n ↦ ∑ k ∈ Finset.range n, ε i (j + k) ^ (p + 1)) atTop
        (𝓝 (∑' k : ℕ, ε i (j + k) ^ (p + 1))) :=
    hsummable.hasSum.tendsto_sum_nat
  have htailLowerInv :
      (a + δ)⁻¹ * ε i j ≤ ∑' k : ℕ, ε i (j + k) ^ (p + 1) :=
    le_of_tendsto_of_tendsto' hleftTendsto hpartialTendsto hfiniteLower
  have htailLower :
      ε i j / (a + δ) ≤ ∑' k : ℕ, ε i (j + k) ^ (p + 1) := by
    simpa only [div_eq_mul_inv, mul_comm] using htailLowerInv
  exact ⟨htailLower, htailUpper⟩

end ParabolicRecurrence
