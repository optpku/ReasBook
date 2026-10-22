/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Definition_6_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Remark_6_5
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.Decomposition.Exhaustion
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Order.Zorn

open Filter MeasureTheory
open scoped ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Helper for Corollary 6.15: on a finite measure space, the local Cauchy hypothesis makes every
geometric deviation threshold eventually uniformly small. -/
private lemma eventuallyPairwiseDeviation_le_geometric
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {fSeq : ℕ → Ω → E}
    (h_cauchy :
      ∀ ε : ℝ, 0 < ε →
        Tendsto
          (fun p : ℕ × ℕ ↦ μ {ω | ε < dist (fSeq p.1 ω) (fSeq p.2 ω)})
          (atTop ×ˢ atTop) (𝓝 0)) :
    ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
        μ {ω | ((1 / 2 : ℝ) ^ (k + 1)) < dist (fSeq n ω) (fSeq m ω)}
          ≤ ((2⁻¹ : ℝ≥0∞) ^ (k + 1)) := by
  intro k
  have hk_pos : 0 < ((1 / 2 : ℝ) ^ (k + 1)) := by positivity
  have hk_tendsto :=
    h_cauchy ((1 / 2 : ℝ) ^ (k + 1)) hk_pos
  have h_small :
      ∀ᶠ p : ℕ × ℕ in atTop,
        μ {ω | ((1 / 2 : ℝ) ^ (k + 1)) < dist (fSeq p.1 ω) (fSeq p.2 ω)} <
          ((2⁻¹ : ℝ≥0∞) ^ (k + 1)) := by
    rw [Filter.prod_atTop_atTop_eq] at hk_tendsto
    exact hk_tendsto (Iio_mem_nhds (ENNReal.pow_pos (by simp) _))
  obtain ⟨N, hN⟩ := eventually_atTop_prod_self'.1 h_small
  exact ⟨N, fun n hn m hm ↦ (hN n hn m hm).le⟩

/-- Helper for Corollary 6.15: extract a strict subsequence whose successive deviation events
already satisfy the geometric bounds from the source proof. -/
private lemma existsStrictMono_subsequence_with_geometricStepBounds
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {fSeq : ℕ → Ω → E}
    (h_cauchy :
      ∀ ε : ℝ, 0 < ε →
        Tendsto
          (fun p : ℕ × ℕ ↦ μ {ω | ε < dist (fSeq p.1 ω) (fSeq p.2 ω)})
          (atTop ×ˢ atTop) (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ k,
        μ {ω | ((1 / 2 : ℝ) ^ (k + 1)) < dist (fSeq (ns k) ω) (fSeq (ns (k + 1)) ω)}
          ≤ ((2⁻¹ : ℝ≥0∞) ^ (k + 1)) := by
  classical
  have hgeom := eventuallyPairwiseDeviation_le_geometric μ h_cauchy
  choose N hN using hgeom
  let ns : ℕ → ℕ := Nat.rec (N 0) fun k m ↦ max (m + 1) (N (k + 1))
  have hns_zero : ns 0 = N 0 := by
    simp [ns]
  have hns_succ : ∀ k, ns (k + 1) = max (ns k + 1) (N (k + 1)) := by
    intro k
    simp [ns]
  have hns_strict : StrictMono ns := by
    refine strictMono_nat_of_lt_succ ?_
    intro k
    rw [hns_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
  have hN_le : ∀ k, N k ≤ ns k := by
    intro k
    cases k with
    | zero =>
        simp [hns_zero]
    | succ k =>
        rw [hns_succ]
        exact Nat.le_max_right _ _
  let bad : ℕ → Set Ω := fun k ↦
    {ω | ((1 / 2 : ℝ) ^ (k + 1)) < dist (fSeq (ns k) ω) (fSeq (ns (k + 1)) ω)}
  have hbad : ∀ k, μ (bad k) ≤ ((2⁻¹ : ℝ≥0∞) ^ (k + 1)) := by
    intro k
    have hnsk_ge : ns k ≥ N k := hN_le k
    have hnsksucc_ge : ns (k + 1) ≥ N k := by
      exact le_trans (hN_le k) (Nat.le_of_lt (hns_strict (Nat.lt_succ_self k)))
    simpa [bad] using hN k (ns k) hnsk_ge (ns (k + 1)) hnsksucc_ge
  exact ⟨ns, hns_strict, by simpa [bad] using hbad⟩

/-- Helper for Corollary 6.15: extract a strict subsequence whose `k`th anchor controls every
later term by the geometric deviation bound from the source proof. -/
private lemma existsStrictMono_subsequence_with_geometricAnchorBounds
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {fSeq : ℕ → Ω → E}
    (h_cauchy :
      ∀ ε : ℝ, 0 < ε →
        Tendsto
          (fun p : ℕ × ℕ ↦ μ {ω | ε < dist (fSeq p.1 ω) (fSeq p.2 ω)})
          (atTop ×ˢ atTop) (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ k, ∀ n ≥ ns k,
        μ {ω | ((1 / 2 : ℝ) ^ (k + 1)) < dist (fSeq n ω) (fSeq (ns k) ω)}
          ≤ ((2⁻¹ : ℝ≥0∞) ^ (k + 1)) := by
  classical
  have hgeom := eventuallyPairwiseDeviation_le_geometric μ h_cauchy
  choose N hN using hgeom
  let ns : ℕ → ℕ := Nat.rec (N 0) fun k m ↦ max (m + 1) (N (k + 1))
  have hns_zero : ns 0 = N 0 := by
    simp [ns]
  have hns_succ : ∀ k, ns (k + 1) = max (ns k + 1) (N (k + 1)) := by
    intro k
    simp [ns]
  have hns_strict : StrictMono ns := by
    refine strictMono_nat_of_lt_succ ?_
    intro k
    rw [hns_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
  have hN_le : ∀ k, N k ≤ ns k := by
    intro k
    cases k with
    | zero =>
        simp [hns_zero]
    | succ k =>
        rw [hns_succ]
        exact Nat.le_max_right _ _
  refine ⟨ns, hns_strict, ?_⟩
  intro k n hn
  -- Proof comment: the recursive choice ensures that the `k`th anchor is already beyond the
  -- Cauchy threshold `N k`, so every later term satisfies the same geometric deviation bound.
  exact hN k n (le_trans (hN_le k) hn) (ns k) (hN_le k)

/-- Helper for Corollary 6.15: geometric step bounds give a geometric estimate for every tail
union of bad sets. -/
private lemma tailUnionMeasure_le_geometricOfStepBounds
    (μ : Measure Ω) {bad : ℕ → Set Ω}
    (hbad : ∀ k, μ (bad k) ≤ ((2⁻¹ : ℝ≥0∞) ^ (k + 1))) :
    ∀ K, μ (⋃ j, bad (K + j)) ≤ ((2⁻¹ : ℝ≥0∞) ^ K) := by
  intro K
  have htail :
      ∑' j : ℕ, ((2⁻¹ : ℝ≥0∞) ^ (j + 1)) = 1 := by
    calc
      ∑' j : ℕ, ((2⁻¹ : ℝ≥0∞) ^ (j + 1))
          = (2⁻¹ : ℝ≥0∞) * (1 - (2⁻¹ : ℝ≥0∞))⁻¹ := ENNReal.tsum_geometric_add_one _
      _ = 1 := by
        simpa using ENNReal.inv_mul_cancel (Ne.symm (NeZero.ne' 2))
          (by simp : (2 : ℝ≥0∞) ≠ ∞)
  -- Proof comment: subadditivity reduces the tail union to the geometric series with the
  -- already chosen `2⁻¹` ratio.
  calc
    μ (⋃ j, bad (K + j)) ≤ ∑' j : ℕ, μ (bad (K + j)) := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ((2⁻¹ : ℝ≥0∞) ^ (K + j + 1)) := ENNReal.tsum_le_tsum fun j ↦ hbad (K + j)
    _ = ∑' j : ℕ, ((2⁻¹ : ℝ≥0∞) ^ K) * ((2⁻¹ : ℝ≥0∞) ^ (j + 1)) := by
      congr with j
      rw [Nat.add_assoc, pow_add]
    _ = ((2⁻¹ : ℝ≥0∞) ^ K) * ∑' j : ℕ, ((2⁻¹ : ℝ≥0∞) ^ (j + 1)) := by
      rw [ENNReal.tsum_mul_left]
    _ = ((2⁻¹ : ℝ≥0∞) ^ K) := by
      rw [htail, mul_one]

/-- Helper for Corollary 6.15: on a finite measure space, the geometric fast subsequence should
be turned into a pointwise limit outside a limsup-null set, then upgraded to full convergence in
measure by comparison with a fixed anchor term. -/
private lemma existsLimitInMeasureOfFiniteCauchy
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    (h_cauchy :
      ∀ ε : ℝ, 0 < ε →
        Tendsto
          (fun p : ℕ × ℕ ↦ μ {ω | ε < dist (fSeq p.1 ω) (fSeq p.2 ω)})
          (atTop ×ˢ atTop) (𝓝 0)) :
    ∃ f : Ω → E, TendstoInMeasure μ fSeq atTop f := by
  classical
  obtain ⟨ns, hns, hanchor⟩ :=
    existsStrictMono_subsequence_with_geometricAnchorBounds μ h_cauchy
  let bad : ℕ → Set Ω := fun k ↦
    {ω | ((1 / 2 : ℝ) ^ (k + 1)) < dist (fSeq (ns k) ω) (fSeq (ns (k + 1)) ω)}
  have hbad : ∀ k, μ (bad k) ≤ ((2⁻¹ : ℝ≥0∞) ^ (k + 1)) := by
    intro k
    simpa [bad, dist_comm] using hanchor k (ns (k + 1)) (Nat.le_of_lt (hns (Nat.lt_succ_self k)))
  have hbad_ne_top : (∑' k, μ (bad k)) ≠ ∞ := by
    have hgeom_ne_top : (∑' k, ((2⁻¹ : ℝ≥0∞) ^ (k + 1))) ≠ ∞ := by
      rw [ENNReal.tsum_geometric_add_one]
      simp
    exact ne_top_of_le_ne_top hgeom_ne_top (ENNReal.tsum_le_tsum hbad)
  have h_bad_limsup : μ (limsup bad atTop) = 0 :=
    measure_limsup_atTop_eq_zero hbad_ne_top
  have h_exists_limit :
      ∀ ω ∈ (limsup bad atTop)ᶜ, ∃ l : E, Tendsto (fun k ↦ fSeq (ns k) ω) atTop (𝓝 l) := by
    intro ω hω
    have h_eventually_not : ∀ᶠ k in atTop, ω ∉ bad k := by
      rw [Set.mem_compl_iff, mem_limsup_iff_frequently_mem, not_frequently] at hω
      exact hω
    obtain ⟨N, hN⟩ := eventually_atTop.1 h_eventually_not
    let tail : ℕ → E := fun k ↦ fSeq (ns (k + N)) ω
    have htail :
        ∀ k, dist (tail k) (tail (k + 1)) ≤ ((1 / 2 : ℝ) ^ (N + k + 1)) := by
      intro k
      have hnot_mem : ω ∉ bad (N + k) := hN (N + k) (Nat.le_add_right N k)
      exact le_of_not_gt <| by
        simpa [bad, tail, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnot_mem
    have htail_sum : Summable (fun k : ℕ ↦ ((1 / 2 : ℝ) ^ (N + k + 1))) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (_root_.summable_nat_add_iff (N + 1)).2
          summable_geometric_two
    have htail_cauchy : CauchySeq tail :=
      cauchySeq_of_dist_le_of_summable _ htail htail_sum
    obtain ⟨l, htail_tendsto⟩ := cauchySeq_tendsto_of_complete htail_cauchy
    refine ⟨l, ?_⟩
    -- Proof comment: once the shifted tail converges, the whole fast subsequence has the same
    -- limit because discarding finitely many initial terms does not affect `atTop` convergence.
    exact (tendsto_add_atTop_iff_nat N).1 <| by
      simpa [tail, Function.comp, Nat.add_assoc] using htail_tendsto
  let f : Ω → E := fun ω ↦
    if hω : ω ∉ limsup bad atTop then
      Classical.choose (h_exists_limit ω (by simpa [Set.mem_compl_iff] using hω))
    else
      fSeq (ns 0) ω
  have hf_limit :
      ∀ ω (hω : ω ∈ (limsup bad atTop)ᶜ),
        Tendsto (fun k ↦ fSeq (ns k) ω) atTop (𝓝 (f ω)) := by
    intro ω hω
    have hω' : ω ∉ limsup bad atTop := by
      simpa [Set.mem_compl_iff] using hω
    simpa [f, hω', Set.mem_compl_iff] using Classical.choose_spec (h_exists_limit ω hω)
  have hf_dist_tail :
      ∀ {ω n}, ω ∉ ⋃ j, bad (n + j) → dist (fSeq (ns n) ω) (f ω) ≤ ((1 / 2 : ℝ) ^ n) := by
    intro ω n hω_tail
    have hω_compl : ω ∈ (limsup bad atTop)ᶜ := by
      rw [Set.mem_compl_iff, mem_limsup_iff_frequently_mem, not_frequently]
      refine eventually_atTop.2 ⟨n, ?_⟩
      intro m hm
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
      exact fun hmem ↦ hω_tail (Set.mem_iUnion.2 ⟨j, hmem⟩)
    let tail : ℕ → E := fun k ↦ fSeq (ns (n + k)) ω
    have htail :
        ∀ k, dist (tail k) (tail (k + 1)) ≤ ((1 / 2 : ℝ) ^ (n + 1)) * ((1 / 2 : ℝ) ^ k) := by
      intro k
      have hnot_mem : ω ∉ bad (n + k) := by
        intro hmem
        exact hω_tail (Set.mem_iUnion.2 ⟨k, hmem⟩)
      have hle :
          dist (fSeq (ns (n + k)) ω) (fSeq (ns (n + k + 1)) ω) ≤ ((1 / 2 : ℝ) ^ (n + k + 1)) := by
        exact le_of_not_gt <| by
          simpa [bad, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnot_mem
      simpa [tail, pow_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, mul_comm, mul_left_comm,
        mul_assoc] using hle
    have htail_tendsto : Tendsto tail atTop (𝓝 (f ω)) := by
      simpa [tail, Function.comp, Nat.add_assoc, Nat.add_comm] using
        (tendsto_add_atTop_iff_nat n).2 (hf_limit ω hω_compl)
    have hdist0 :
        dist (tail 0) (f ω) ≤ ((1 / 2 : ℝ) ^ (n + 1)) / (1 - (1 / 2 : ℝ)) := by
      simpa using
        (dist_le_of_le_geometric_of_tendsto
          (1 / 2 : ℝ) ((1 / 2 : ℝ) ^ (n + 1)) (by norm_num) htail htail_tendsto 0)
    have hratio : ((1 / 2 : ℝ) ^ (n + 1)) / (1 - (1 / 2 : ℝ)) = ((1 / 2 : ℝ) ^ n) := by
      rw [show (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) by norm_num, div_eq_mul_inv]
      rw [show ((1 / 2 : ℝ))⁻¹ = (2 : ℝ) by norm_num]
      rw [pow_succ]
      ring
    have hdist : dist (tail 0) (f ω) ≤ ((1 / 2 : ℝ) ^ n) := by
      calc
        dist (tail 0) (f ω) ≤ ((1 / 2 : ℝ) ^ (n + 1)) / (1 - (1 / 2 : ℝ)) := hdist0
        _ = ((1 / 2 : ℝ) ^ n) := hratio
    simpa [tail] using hdist
  have hpow_real : Tendsto (fun k : ℕ ↦ ((1 / 2 : ℝ) ^ k)) atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hpow_enn : Tendsto (fun k : ℕ ↦ ((2⁻¹ : ℝ≥0∞) ^ k)) atTop (𝓝 0) := by
    exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by simp)
  have h_subseq : TendstoInMeasure μ (fun k ↦ fSeq (ns k)) atTop f := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    rw [ENNReal.tendsto_atTop_zero]
    intro δ hδ
    obtain ⟨K₁, hK₁⟩ := (Metric.tendsto_atTop.1 hpow_real) ε hε
    obtain ⟨K₂, hK₂⟩ := (ENNReal.tendsto_atTop_zero.1 hpow_enn) δ hδ
    refine ⟨max K₁ K₂, fun n hn ↦ ?_⟩
    have hpow_small : ((1 / 2 : ℝ) ^ n) < ε := by
      simpa [Real.dist_eq, abs_of_nonneg (by positivity : 0 ≤ ((1 / 2 : ℝ) ^ n))] using
        hK₁ n (le_trans (le_max_left _ _) hn)
    have hmeas_small : ((2⁻¹ : ℝ≥0∞) ^ n) ≤ δ :=
      hK₂ n (le_trans (le_max_right _ _) hn)
    have h_subset :
        {ω | ε ≤ dist (fSeq (ns n) ω) (f ω)} ⊆ limsup bad atTop ∪ ⋃ j, bad (n + j) := by
      intro ω hω
      by_cases hlim : ω ∈ limsup bad atTop
      · exact Or.inl hlim
      · by_cases htail : ω ∈ ⋃ j, bad (n + j)
        · exact Or.inr htail
        · exfalso
          have hdist_small := lt_of_le_of_lt (hf_dist_tail htail) hpow_small
          exact (not_le_of_gt hdist_small) hω
    have htail_measure :=
      tailUnionMeasure_le_geometricOfStepBounds μ hbad n
    have hmeasure_le :
        μ {ω | ε ≤ dist (fSeq (ns n) ω) (f ω)} ≤ ((2⁻¹ : ℝ≥0∞) ^ n) := by
      calc
        μ {ω | ε ≤ dist (fSeq (ns n) ω) (f ω)}
            ≤ μ (limsup bad atTop ∪ ⋃ j, bad (n + j)) := measure_mono h_subset
        _ ≤ μ (limsup bad atTop) + μ (⋃ j, bad (n + j)) := measure_union_le _ _
        _ = 0 + μ (⋃ j, bad (n + j)) := by simp [h_bad_limsup]
        _ ≤ 0 + ((2⁻¹ : ℝ≥0∞) ^ n) := by gcongr
        _ = ((2⁻¹ : ℝ≥0∞) ^ n) := by simp
    exact hmeasure_le.trans hmeas_small
  refine ⟨f, ?_⟩
  rw [tendstoInMeasure_iff_dist] at h_subseq ⊢
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  by_cases hδ_top : δ = ∞
  · refine ⟨0, fun n _hn ↦ ?_⟩
    simp [hδ_top]
  have hδ_half_pos : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  have hpow_real_shift : Tendsto (fun k : ℕ ↦ ((1 / 2 : ℝ) ^ (k + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_add_atTop_iff_nat 1).2 hpow_real
  have hpow_enn_shift : Tendsto (fun k : ℕ ↦ ((2⁻¹ : ℝ≥0∞) ^ (k + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_add_atTop_iff_nat 1).2 hpow_enn
  have h_subseq_half := h_subseq (ε / 2) (by linarith)
  obtain ⟨K₁, hK₁⟩ := (Metric.tendsto_atTop.1 hpow_real_shift) (ε / 2) (by linarith)
  obtain ⟨K₂, hK₂⟩ := (ENNReal.tendsto_atTop_zero.1 hpow_enn_shift) (δ / 2) hδ_half_pos
  obtain ⟨K₃, hK₃⟩ := (ENNReal.tendsto_atTop_zero.1 h_subseq_half) (δ / 2) hδ_half_pos
  let K := max (max K₁ K₂) K₃
  refine ⟨ns K, fun n hn ↦ ?_⟩
  let dev : Set Ω := {ω | ε ≤ dist (fSeq n ω) (f ω)}
  let anchorDev : Set Ω := {ω | ε / 2 < dist (fSeq n ω) (fSeq (ns K) ω)}
  let limitDev : Set Ω := {ω | ε / 2 ≤ dist (fSeq (ns K) ω) (f ω)}
  have hK₁_le : K₁ ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hK₂_le : K₂ ≤ K := le_trans (le_max_right K₁ K₂) (le_max_left (max K₁ K₂) K₃)
  have hK₃_le : K₃ ≤ K := le_max_right (max K₁ K₂) K₃
  have hpow_small : ((1 / 2 : ℝ) ^ (K + 1)) < ε / 2 := by
    simpa [Real.dist_eq, abs_of_nonneg (by positivity : 0 ≤ ((1 / 2 : ℝ) ^ (K + 1)))] using
      hK₁ K hK₁_le
  have h_anchor_subset :
      anchorDev ⊆ {ω | ((1 / 2 : ℝ) ^ (K + 1)) < dist (fSeq n ω) (fSeq (ns K) ω)} := by
    intro ω hω
    exact lt_trans hpow_small hω
  have h_anchor_small :
      μ anchorDev ≤ δ / 2 := by
    have hbound :
        μ {ω | ((1 / 2 : ℝ) ^ (K + 1)) < dist (fSeq n ω) (fSeq (ns K) ω)}
          ≤ ((2⁻¹ : ℝ≥0∞) ^ (K + 1)) := hanchor K n hn
    calc
      μ anchorDev
          ≤ μ {ω | ((1 / 2 : ℝ) ^ (K + 1)) < dist (fSeq n ω) (fSeq (ns K) ω)} :=
            measure_mono h_anchor_subset
      _ ≤ ((2⁻¹ : ℝ≥0∞) ^ (K + 1)) := hbound
      _ ≤ δ / 2 := hK₂ K hK₂_le
  have h_limit_small : μ limitDev ≤ δ / 2 := by
    simpa [limitDev] using hK₃ K hK₃_le
  have h_subset : dev ⊆ anchorDev ∪ limitDev := by
    intro ω hω
    by_cases hanchorω : ε / 2 < dist (fSeq n ω) (fSeq (ns K) ω)
    · exact Or.inl hanchorω
    · by_cases hlimitω : ε / 2 ≤ dist (fSeq (ns K) ω) (f ω)
      · exact Or.inr hlimitω
      · exfalso
        have hanchor_le : dist (fSeq n ω) (fSeq (ns K) ω) ≤ ε / 2 := le_of_not_gt hanchorω
        have hlimit_lt : dist (fSeq (ns K) ω) (f ω) < ε / 2 := lt_of_not_ge hlimitω
        have hdist_lt : dist (fSeq n ω) (f ω) < ε := by
          calc
            dist (fSeq n ω) (f ω)
                ≤ dist (fSeq n ω) (fSeq (ns K) ω) + dist (fSeq (ns K) ω) (f ω) :=
                  dist_triangle _ _ _
            _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hanchor_le hlimit_lt
            _ = ε := by ring
        exact (not_le_of_gt hdist_lt) hω
  calc
    μ dev ≤ μ anchorDev + μ limitDev := by
      exact (measure_mono h_subset).trans (measure_union_le _ _)
    _ ≤ δ / 2 + δ / 2 := add_le_add h_anchor_small h_limit_small
    _ = δ := by rw [ENNReal.add_halves]

/-- Helper for Corollary 6.15: on a finite measure space, a local Cauchy sequence with
measurable terms admits a measurable limit representative. -/
private lemma existsMeasurableLimitInMeasureOfFiniteCauchy
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    (h_meas : ∀ n, Measurable (fSeq n))
    (h_cauchy :
      ∀ ε : ℝ, 0 < ε →
        Tendsto
          (fun p : ℕ × ℕ ↦ μ {ω | ε < dist (fSeq p.1 ω) (fSeq p.2 ω)})
          (atTop ×ˢ atTop) (𝓝 0)) :
    ∃ f : Ω → E, Measurable f ∧ TendstoInMeasure μ fSeq atTop f := by
  obtain ⟨g, hg_tendsto⟩ := existsLimitInMeasureOfFiniteCauchy (μ := μ) h_cauchy
  have hg_aemeas : AEMeasurable g μ :=
    TendstoInMeasure.aemeasurable (μ := μ) (fun n ↦ (h_meas n).aemeasurable) hg_tendsto
  refine ⟨AEMeasurable.mk g hg_aemeas, hg_aemeas.measurable_mk, ?_⟩
  -- Proof comment: replacing the abstract limit by its measurable `mk` representative preserves
  -- convergence in measure because the two functions agree almost everywhere.
  exact TendstoInMeasure.congr_right hg_aemeas.ae_eq_mk hg_tendsto

/-- Helper for Corollary 6.15: every measurable finite restriction of a locally Cauchy sequence
already has a local limit on that restricted finite measure space. -/
private lemma existsLimitOnFiniteRestriction
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq)
    {A : Set Ω} (_hA : MeasurableSet A) (hA_fin : μ A < ∞) :
    ∃ fA : Ω → E, TendstoInMeasureOnFiniteMeasureSets (μ.restrict A) fSeq fA := by
  haveI : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 hA_fin.ne
  obtain ⟨fA, hfA⟩ :=
    existsLimitInMeasureOfFiniteCauchy (μ.restrict A) <|
      by
        intro ε hε
        simpa [Measure.restrict_univ] using h_cauchy A hA_fin ε hε
  exact ⟨fA, (tendstoInMeasureOnFiniteMeasureSets_iff_mathlib_tendstoInMeasure
    (μ.restrict A)).2 hfA⟩

/-- Helper for Corollary 6.15: on a finite restriction, the local limit can be chosen measurable
once the original sequence is measurable. -/
private lemma existsMeasuredLimitOnFiniteRestriction
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    (h_meas : ∀ n, Measurable (fSeq n))
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq)
    {A : Set Ω} (hA_fin : μ A < ∞) :
    ∃ fA : Ω → E, Measurable fA ∧
      TendstoInMeasureOnFiniteMeasureSets (μ.restrict A) fSeq fA := by
  haveI : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 hA_fin.ne
  obtain ⟨fA, hfA_meas, hfA_tendsto⟩ :=
    existsMeasurableLimitInMeasureOfFiniteCauchy (μ := μ.restrict A)
      (h_meas := h_meas) <| by
        intro ε hε
        simpa [Measure.restrict_univ] using h_cauchy A hA_fin ε hε
  exact ⟨fA, hfA_meas,
    (tendstoInMeasureOnFiniteMeasureSets_iff_mathlib_tendstoInMeasure
      (μ.restrict A)).2 hfA_tendsto⟩

/-- Helper for Corollary 6.15: finite-restriction limits agree almost everywhere on the overlap,
because both restrictions converge in measure to the same sequence on `A ∩ B`. -/
private lemma localLimit_aeEq_on_finiteInter
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E} {A B : Set Ω} {fA fB : Ω → E}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA_fin : μ A < ∞) (hB_fin : μ B < ∞)
    (hA_lim : TendstoInMeasureOnFiniteMeasureSets (μ.restrict A) fSeq fA)
    (hB_lim : TendstoInMeasureOnFiniteMeasureSets (μ.restrict B) fSeq fB) :
    fA =ᵐ[μ.restrict (A ∩ B)] fB := by
  have hInter_fin : μ (A ∩ B) < ∞ := lt_of_le_of_lt (measure_mono Set.inter_subset_left) hA_fin
  haveI : IsFiniteMeasure (μ.restrict (A ∩ B)) := isFiniteMeasure_restrict.2 hInter_fin.ne
  have hA_on_inter :
      TendstoInMeasure (μ.restrict (A ∩ B)) fSeq atTop fA := by
    have hAB_fin : (μ.restrict A) B < ∞ := lt_of_le_of_lt (Measure.restrict_apply_le A B) hB_fin
    simpa [Measure.restrict_restrict hB, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
      hA_lim B hAB_fin
  have hB_on_inter :
      TendstoInMeasure (μ.restrict (A ∩ B)) fSeq atTop fB := by
    have hBA_fin : (μ.restrict B) A < ∞ := lt_of_le_of_lt (Measure.restrict_apply_le B A) hA_fin
    simpa [Measure.restrict_restrict hA, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
      hB_lim A hBA_fin
  -- Proof comment: uniqueness of limits in measure on a finite measure space closes the overlap.
  exact tendstoInMeasure_ae_unique hA_on_inter hB_on_inter

/-- Helper for Corollary 6.15: any chosen family of finite-restriction limits is automatically
compatible on pairwise overlaps. -/
private lemma chosenFiniteRestrictionLimits_compatible
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    {ι : Type*} {s : ι → Set Ω} {g : ι → Ω → E}
    (hs : ∀ i, MeasurableSet (s i))
    (hs_fin : ∀ i, μ (s i) < ∞)
    (hg : ∀ i, TendstoInMeasureOnFiniteMeasureSets (μ.restrict (s i)) fSeq (g i)) :
    ∀ i j, g i =ᵐ[μ.restrict (s i ∩ s j)] g j := by
  intro i j
  -- Proof comment: both chosen witnesses come from the same sequence on the finite overlap, so
  -- the finite-measure uniqueness lemma identifies them there.
  exact localLimit_aeEq_on_finiteInter μ (hs i) (hs j) (hs_fin i) (hs_fin j) (hg i) (hg j)

/-- Helper for Corollary 6.15: a countable family of measurable local witnesses that agree almost
everywhere on pairwise overlaps can be glued to one ambient representative. -/
private lemma glueCountableCompatibleFiniteRestrictions
    (μ : Measure Ω)
    {s : ℕ → Set Ω} {g : ℕ → Ω → E}
    (hs : ∀ n, MeasurableSet (s n))
    (hcompat : ∀ i j, g i =ᵐ[μ.restrict (s i ∩ s j)] g j) :
    ∃ f : Ω → E, ∀ n, f =ᵐ[μ.restrict (s n)] g n := by
  classical
  let trimmed : ℕ → Set Ω := fun n ↦ s n \ ⋃ m ∈ Finset.range n, s m
  have htrimmed_meas : ∀ n, MeasurableSet (trimmed n) := by
    intro n
    refine (hs n).diff ?_
    exact MeasurableSet.iUnion fun m ↦ MeasurableSet.iUnion fun _ ↦ hs m
  have htrimmed_cover : ∀ n, s n = ⋃ m ∈ Finset.range (n + 1), s n ∩ trimmed m := by
    intro n
    ext x
    constructor
    · intro hx
      let p : ℕ → Prop := fun m ↦ m ≤ n ∧ x ∈ s m
      have hp : ∃ m, p m := ⟨n, le_rfl, hx⟩
      let m := Nat.find hp
      have hm_le : m ≤ n := (Nat.find_spec hp).1
      have hxm : x ∈ s m := (Nat.find_spec hp).2
      have hmin : ∀ k, k < m → x ∉ s k := by
        intro k hk hkx
        exact Nat.not_lt_of_ge (Nat.find_min' hp ⟨le_trans (Nat.le_of_lt hk) hm_le, hkx⟩) hk
      have hxm_trimmed : x ∈ trimmed m := by
        refine ⟨hxm, ?_⟩
        intro hx_union
        rcases Set.mem_iUnion.1 hx_union with ⟨k, hx_union⟩
        rcases Set.mem_iUnion.1 hx_union with ⟨hk, hkx⟩
        exact hmin k (Finset.mem_range.1 hk) hkx
      exact Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨Finset.mem_range.2 (Nat.lt_succ_iff.2 hm_le),
        ⟨hx, hxm_trimmed⟩⟩⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨m, hx⟩
      rcases Set.mem_iUnion.1 hx with ⟨_hm, hx⟩
      exact hx.1
  let f : Ω → E := fun x ↦
    if hx : ∃ n, x ∈ trimmed n then
      g (Nat.find hx) x
    else
      g 0 x
  have hf_on_trimmed : ∀ n, Set.EqOn f (g n) (trimmed n) := by
    intro n x hx
    have hx_exists : ∃ m, x ∈ trimmed m := ⟨n, hx⟩
    have hfind_le : Nat.find hx_exists ≤ n := Nat.find_min' hx_exists hx
    have hfind_ge : n ≤ Nat.find hx_exists := by
      by_contra hlt
      have hlt' : Nat.find hx_exists < n := Nat.lt_of_not_ge hlt
      have hfind_mem : x ∈ trimmed (Nat.find hx_exists) := Nat.find_spec hx_exists
      exact hx.2 <| Set.mem_iUnion.2 ⟨Nat.find hx_exists, Set.mem_iUnion.2
        ⟨Finset.mem_range.2 hlt', hfind_mem.1⟩⟩
    have hfind_eq : Nat.find hx_exists = n := le_antisymm hfind_le hfind_ge
    simp [f, hx_exists, hfind_eq]
  refine ⟨f, ?_⟩
  intro n
  -- Proof comment: on the `n`th piece, only the finitely many minimal-index strata `trimmed m`
  -- with `m ≤ n` matter, so the pairwise overlap exceptions stay finite.
  have hpiece :
      ∀ m ∈ Finset.range (n + 1), f =ᵐ[μ.restrict (s n ∩ trimmed m)] g n := by
    intro m hm
    have hm_le : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hm)
    have h_exact : f =ᵐ[μ.restrict (s n ∩ trimmed m)] g m := by
      have hEqOn : Set.EqOn f (g m) (s n ∩ trimmed m) := fun x hx ↦ hf_on_trimmed m hx.2
      exact hEqOn.aeEq_restrict ((hs n).inter (htrimmed_meas m))
    have h_overlap : g m =ᵐ[μ.restrict (s n ∩ trimmed m)] g n := by
      refine ae_restrict_of_ae_restrict_of_subset ?_ (hcompat m n)
      intro x hx
      exact ⟨hx.2.1, hx.1⟩
    exact h_exact.trans h_overlap
  have hglued :
      f =ᵐ[μ.restrict (⋃ m ∈ Finset.range (n + 1), s n ∩ trimmed m)] g n := by
    rw [ae_eq_restrict_biUnion_finset_iff]
    intro m hm
    exact hpiece m hm
  have hrestrict :
      μ.restrict (s n) =
        μ.restrict (⋃ m ∈ Finset.range (n + 1), s n ∩ trimmed m) := by
    simpa using congrArg (fun t : Set Ω ↦ μ.restrict t) (htrimmed_cover n)
  simpa [hrestrict] using hglued

/-- Helper for Corollary 6.15: if one already has local convergence in measure on every canonical
sigma-finite spanning set, then the tail outside a large spanning set is negligible on every
finite-measure test set, so the local limits assemble to a global local limit. -/
private lemma tendstoInMeasureOnFiniteMeasureSets_of_spanningSetLocalLimits
    (μ : Measure Ω) [SigmaFinite μ]
    {fSeq : ℕ → Ω → E} {f : Ω → E}
    (h_local :
      ∀ n, TendstoInMeasureOnFiniteMeasureSets (μ.restrict (spanningSets μ n)) fSeq f) :
    TendstoInMeasureOnFiniteMeasureSets μ fSeq f := by
  intro A hA_fin
  let B := toMeasurable μ A
  have hB : MeasurableSet B := measurableSet_toMeasurable μ A
  have hB_fin : μ B < ∞ := by
    simpa [B, measure_toMeasurable] using hA_fin
  -- Proof comment: replace the test set by its measurable hull so that all later restriction
  -- rewrites and the continuity-from-above step can use the measurable `spanningSets μ n`.
  rw [show μ.restrict A = μ.restrict B by
    simpa [B] using (Measure.restrict_toMeasurable μ hA_fin.ne).symm]
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  by_cases hδ_top : δ = ∞
  · refine ⟨0, fun n hn ↦ ?_⟩
    simp [hδ_top]
  have hδ_half_pos : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  let tail : ℕ → Set Ω := fun n ↦ (spanningSets μ n)ᶜ
  have htail_meas : ∀ n, NullMeasurableSet (tail n) (μ.restrict B) := by
    intro n
    exact ((measurableSet_spanningSets μ n).compl).nullMeasurableSet
  have htail_anti : Antitone tail := by
    intro m n hmn
    exact Set.compl_subset_compl.2 (monotone_spanningSets μ hmn)
  have htail_empty : (⋂ n, tail n) = ∅ := by
    ext x
    constructor
    · intro hx
      have hx_mem : x ∈ ⋃ n, spanningSets μ n := by
        simpa [iUnion_spanningSets μ] using (Set.mem_univ x)
      rcases Set.mem_iUnion.1 hx_mem with ⟨n, hn⟩
      exact ((Set.mem_iInter.1 hx) n) hn
    · intro hx
      simp at hx
  have htail_tendsto :
      Tendsto (fun n ↦ (μ.restrict B) (tail n)) atTop (𝓝 0) := by
    have htail_tendsto' :
        Tendsto (fun n ↦ (μ.restrict B) (tail n)) atTop
          (𝓝 ((μ.restrict B) (⋂ n, tail n))) := by
      refine tendsto_measure_iInter_atTop htail_meas htail_anti ?_
      refine ⟨0, ?_⟩
      refine ne_top_of_le_ne_top hB_fin.ne ?_
      calc
        (μ.restrict B) (tail 0) ≤ (μ.restrict B) Set.univ := by
          exact measure_mono (by intro ω hω; simp)
        _ = μ B := by simpa using (Measure.restrict_apply_univ B)
    simpa [htail_empty] using htail_tendsto'
  obtain ⟨K₁, hK₁⟩ := (ENNReal.tendsto_atTop_zero.1 htail_tendsto) (δ / 2) hδ_half_pos
  have h_restrict :
      TendstoInMeasure (μ.restrict (B ∩ spanningSets μ K₁)) fSeq atTop f := by
    have hBK_fin : (μ.restrict (spanningSets μ K₁)) B < ∞ := by
      exact lt_of_le_of_lt (Measure.restrict_apply_le (spanningSets μ K₁) B) hB_fin
    -- Proof comment: local convergence on the `K₁`-st spanning set gives convergence on the
    -- finite restriction `B ∩ spanningSets μ K₁` after one restriction rewrite.
    simpa [Measure.restrict_restrict hB, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc]
      using h_local K₁ B hBK_fin
  have h_restrict_small := (tendstoInMeasure_iff_dist.1 h_restrict) ε hε
  obtain ⟨K₂, hK₂⟩ := (ENNReal.tendsto_atTop_zero.1 h_restrict_small) (δ / 2) hδ_half_pos
  refine ⟨max K₁ K₂, fun n hn ↦ ?_⟩
  let S := spanningSets μ K₁
  let dev : Set Ω := {ω | ε ≤ dist (fSeq n ω) (f ω)}
  have hS : MeasurableSet S := measurableSet_spanningSets μ K₁
  have h_local_small :
      (μ.restrict (B ∩ S)) dev ≤ δ / 2 := by
    exact hK₂ n (le_trans (le_max_right _ _) hn)
  have h_tail_small :
      (μ.restrict B) (Sᶜ) ≤ δ / 2 := by
    simpa [tail, S] using hK₁ K₁ le_rfl
  have hsplit :
      (μ.restrict B) dev ≤ (μ.restrict (B ∩ S)) dev + (μ.restrict B) (Sᶜ) := by
    have h_subset : dev ⊆ (dev ∩ S) ∪ Sᶜ := by
      intro ω hdev
      by_cases hSω : ω ∈ S
      · exact Or.inl ⟨hdev, hSω⟩
      · exact Or.inr hSω
    calc
      (μ.restrict B) dev ≤ (μ.restrict B) ((dev ∩ S) ∪ Sᶜ) := measure_mono h_subset
      _ ≤ (μ.restrict B) (dev ∩ S) + (μ.restrict B) (Sᶜ) := measure_union_le _ _
      _ = (μ.restrict (B ∩ S)) dev + (μ.restrict B) (Sᶜ) := by
        congr 1
        calc
          (μ.restrict B) (dev ∩ S) = ((μ.restrict B).restrict S) dev := by
            have h_restrict_apply :
                ((μ.restrict B).restrict S) dev = (μ.restrict B) (dev ∩ S) :=
              Measure.restrict_apply' hS
            simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
              h_restrict_apply.symm
          _ = (μ.restrict (B ∩ S)) dev := by
            have h_restrict_restrict :
                ((μ.restrict B).restrict S) = μ.restrict (S ∩ B) :=
              Measure.restrict_restrict hS
            congr 1
            simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
              h_restrict_restrict
  calc
    (μ.restrict B) dev ≤ (μ.restrict (B ∩ S)) dev + (μ.restrict B) (Sᶜ) := hsplit
    _ ≤ δ / 2 + δ / 2 := add_le_add h_local_small h_tail_small
    _ = δ := by rw [ENNReal.add_halves]

/-- Helper for Corollary 6.15: on a sigma-finite measure space, the finite-restriction limits on
the canonical spanning sets are compatible and can therefore be glued into one global local limit.
-/
private lemma existsLimitOnSigmaFiniteMeasure
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E] [SigmaFinite μ]
    {fSeq : ℕ → Ω → E}
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq) :
    ∃ f : Ω → E, TendstoInMeasureOnFiniteMeasureSets μ fSeq f := by
  let s : ℕ → Set Ω := spanningSets μ
  have hs : ∀ n, MeasurableSet (s n) := by
    intro n
    simpa [s] using measurableSet_spanningSets μ n
  have hs_fin : ∀ n, μ (s n) < ∞ := by
    intro n
    simpa [s] using measure_spanningSets_lt_top μ n
  have h_exists :
      ∀ n, ∃ g : Ω → E, TendstoInMeasureOnFiniteMeasureSets (μ.restrict (s n)) fSeq g := by
    intro n
    exact existsLimitOnFiniteRestriction μ h_cauchy (hs n) (hs_fin n)
  choose g hg using h_exists
  have hcompat : ∀ i j, g i =ᵐ[μ.restrict (s i ∩ s j)] g j := by
    intro i j
    -- Proof comment: both local witnesses come from the same sequence on the finite overlap, so
    -- the finite-measure uniqueness lemma forces a.e. agreement there.
    exact localLimit_aeEq_on_finiteInter μ (hs i) (hs j) (hs_fin i) (hs_fin j)
      (hg i) (hg j)
  obtain ⟨f, hf_eq⟩ :=
    glueCountableCompatibleFiniteRestrictions μ hs hcompat
  have h_local :
      ∀ n, TendstoInMeasureOnFiniteMeasureSets (μ.restrict (s n)) fSeq f := by
    intro n A hA_fin
    have h_tendsto :
        TendstoInMeasure ((μ.restrict (s n)).restrict A) fSeq atTop (g n) := hg n A hA_fin
    have h_eq_restrict : g n =ᵐ[((μ.restrict (s n)).restrict A)] f := by
      exact ae_restrict_of_ae (hf_eq n).symm
    exact TendstoInMeasure.congr_right h_eq_restrict h_tendsto
  -- Proof comment: once the glued representative agrees with each finite-piece witness on every
  -- spanning set, the previous lemma promotes those local convergences to all finite test sets.
  exact ⟨f,
    tendstoInMeasureOnFiniteMeasureSets_of_spanningSetLocalLimits μ h_local⟩

/-- Helper for Corollary 6.15: on a finite test set, measurable sigma-finite subsets can
approximate the maximal restricted mass up to the geometric error `1 / (n + 1)`. -/
private lemma existsSigmaFiniteApproxOnFiniteSet
    (μ : Measure Ω) {A : Set Ω} (hA_fin : μ A < ∞) (n : ℕ) :
    ∃ S : Set Ω, MeasurableSet S ∧ SigmaFinite (μ.restrict S) ∧
      (⨆ s, ⨆ (_ : MeasurableSet s), ⨆ (_ : SigmaFinite (μ.restrict s)), (μ.restrict A) s) -
          1 / (((n + 1 : ℕ) : ℝ≥0∞)) ≤
        (μ.restrict A) S := by
  haveI : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 hA_fin.ne
  -- Proof comment: this is the finite-measure exhaustion theorem specialized to the ambient
  -- measure `μ` and the finite control `μ.restrict A`.
  simpa using exists_isSigmaFiniteSet_measure_ge μ (μ.restrict A) (n + 1)

/-- Helper for Corollary 6.15: the near-optimal sigma-finite approximant for a measurable finite
test set can be chosen inside the test set itself. -/
private lemma existsSigmaFiniteApproxWithinFiniteSet
    (μ : Measure Ω) {A : Set Ω} (hA : MeasurableSet A) (hA_fin : μ A < ∞) (n : ℕ) :
    ∃ S : Set Ω, S ⊆ A ∧ MeasurableSet S ∧ SigmaFinite (μ.restrict S) ∧
      (⨆ s, ⨆ (_ : MeasurableSet s), ⨆ (_ : SigmaFinite (μ.restrict s)), (μ.restrict A) s) -
          1 / (((n + 1 : ℕ) : ℝ≥0∞)) ≤
        (μ.restrict A) S := by
  obtain ⟨T, hT_meas, hT_sigma, hT_bound⟩ := existsSigmaFiniteApproxOnFiniteSet μ hA_fin n
  let S := T ∩ A
  have hS_meas : MeasurableSet S := hT_meas.inter hA
  have hS_subset : S ⊆ A := Set.inter_subset_right
  have hS_sigma : SigmaFinite (μ.restrict S) := by
    letI : SigmaFinite (μ.restrict T) := hT_sigma
    -- Proof comment: intersecting a sigma-finite carrier with the measurable finite slice keeps
    -- the restriction sigma-finite.
    simpa [S, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
      (inferInstance : SigmaFinite (μ.restrict (T ∩ A)))
  have hS_measure : (μ.restrict A) S = (μ.restrict A) T := by
    -- Proof comment: after restricting to `A`, intersecting once more with `A` does not change
    -- the measured set.
    calc
      (μ.restrict A) S = μ (S ∩ A) := Measure.restrict_apply' hA
      _ = μ (T ∩ A) := by
            congr 1
            ext x
            simp [S]
      _ = (μ.restrict A) T := by
            simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
              (Measure.restrict_apply' hA).symm
  exact ⟨S, hS_subset, hS_meas, hS_sigma, hS_measure ▸ hT_bound⟩

/-- Helper for Corollary 6.15: if `μ ≪ ν` and `ν` is finite, then every `μ`-finite test set is
already `μ`-almost everywhere contained in the sigma-finite carrier `μ.sigmaFiniteSetWRT ν`. -/
private lemma ae_restrict_mem_sigmaFiniteCarrier_of_finite
    (μ ν : Measure Ω) [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {A : Set Ω} (hA_fin : μ A < ∞) :
    ∀ᵐ ω ∂ μ.restrict A, ω ∈ μ.sigmaFiniteSetWRT ν := by
  let S := μ.sigmaFiniteSetWRT ν
  have hS : MeasurableSet S := measurableSet_sigmaFiniteSetWRT
  rw [ae_iff]
  change μ.restrict A Sᶜ = 0
  by_contra h_nonzero
  have hμ_nonzero : μ (A ∩ Sᶜ) ≠ 0 := by
    intro h_zero
    apply h_nonzero
    calc
      (μ.restrict A) Sᶜ = μ (Sᶜ ∩ A) := Measure.restrict_apply hS.compl
      _ = μ (A ∩ Sᶜ) := by simp [Set.inter_comm]
      _ = 0 := h_zero
  have hν_nonzero : ν (A ∩ Sᶜ) ≠ 0 := by
    intro h_zero
    exact hμ_nonzero (hμν h_zero)
  have h_top : μ (A ∩ Sᶜ) = ∞ :=
    measure_eq_top_of_subset_compl_sigmaFiniteSetWRT
      Set.inter_subset_right hν_nonzero
  have h_le : μ (A ∩ Sᶜ) ≤ μ A := measure_mono Set.inter_subset_left
  have hA_top : μ A = ∞ := top_unique <| h_top ▸ h_le
  exact hA_fin.ne hA_top

/-- Helper for Corollary 6.15: local Cauchy convergence in measure is stable under measurable
restriction of the ambient measure. -/
private lemma cauchyInMeasureOnFiniteMeasureSets_restrict
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E}
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq)
    {s : Set Ω} (hs : MeasurableSet s) :
    CauchyInMeasureOnFiniteMeasureSets (μ.restrict s) fSeq := by
  intro A hA_fin ε hε
  -- Proof comment: rewrite the nested restriction to a single restriction on `A ∩ s`, then
  -- reuse the original local Cauchy hypothesis on that finite-measure test set.
  simpa [Measure.restrict_restrict' hs, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
    h_cauchy (A ∩ s) (by
      calc
        μ (A ∩ s) = (μ.restrict s) A := by
          simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
            (Measure.restrict_apply' hs).symm
        _ < ∞ := hA_fin) ε hε

/-- Helper for Corollary 6.15: local convergence in measure survives measurable restriction by
rewriting the nested restriction to one restriction on the intersection. -/
private lemma tendstoInMeasureOnFiniteMeasureSets_restrict
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E} {f : Ω → E}
    (h_tendsto : TendstoInMeasureOnFiniteMeasureSets μ fSeq f)
    {s : Set Ω} (hs : MeasurableSet s) :
    TendstoInMeasureOnFiniteMeasureSets (μ.restrict s) fSeq f := by
  intro A hA_fin
  -- Proof comment: the restricted measure only sees `A ∩ s`, so the original local convergence
  -- hypothesis applies after one restriction rewrite.
  simpa [Measure.restrict_restrict' hs, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
    h_tendsto (A ∩ s) (by
      calc
        μ (A ∩ s) = (μ.restrict s) A := by
          simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
            (Measure.restrict_apply' hs).symm
        _ < ∞ := hA_fin)

/-- Helper for Corollary 6.15: local convergence in measure is invariant under an almost-
everywhere replacement of the target function. -/
private lemma tendstoInMeasureOnFiniteMeasureSets_congr_ae
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E} {f g : Ω → E}
    (hfg : f =ᵐ[μ] g)
    (hf : TendstoInMeasureOnFiniteMeasureSets μ fSeq f) :
    TendstoInMeasureOnFiniteMeasureSets μ fSeq g := by
  intro A hA_fin
  -- Proof comment: after restricting to a finite test set, the target functions are still a.e.
  -- equal, so convergence in measure transports across `TendstoInMeasure.congr_right`.
  exact TendstoInMeasure.congr_right (ae_restrict_of_ae hfg) (hf A hA_fin)

/-- Helper for Corollary 6.15: a finite-measure test set is almost everywhere contained in the
canonical sigma-finite carrier `μ.sigmaFiniteSetWRT (μ.restrict A)` built from its own
restriction. -/
private lemma ae_mem_sigmaFiniteCarrier_of_selfRestrictFinite
    (μ : Measure Ω) {A : Set Ω} (hA_fin : μ A < ∞) :
    ∀ᵐ ω ∂ μ.restrict A, ω ∈ μ.sigmaFiniteSetWRT (μ.restrict A) := by
  let C := μ.sigmaFiniteSetWRT (μ.restrict A)
  have hC : MeasurableSet C := measurableSet_sigmaFiniteSetWRT
  rw [ae_iff]
  change μ.restrict A Cᶜ = 0
  by_contra h_nonzero
  letI : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 hA_fin.ne
  have hμ_nonzero : μ (A ∩ Cᶜ) ≠ 0 := by
    simpa [Measure.restrict_apply, hC.compl, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
      using h_nonzero
  have hν_nonzero : (μ.restrict A) (A ∩ Cᶜ) ≠ 0 := by
    simpa [Measure.restrict_eq_self μ Set.inter_subset_left] using
      hμ_nonzero
  have h_top :
      μ (A ∩ Cᶜ) = ∞ :=
    measure_eq_top_of_subset_compl_sigmaFiniteSetWRT
      Set.inter_subset_right hν_nonzero
  have h_le : μ (A ∩ Cᶜ) ≤ μ A := measure_mono Set.inter_subset_left
  exact hA_fin.ne <| top_unique <| h_top ▸ h_le

/-- Helper for Corollary 6.15: if an `s`-finite control measure is enlarged by the finite
restriction `μ.restrict A`, then the resulting canonical carrier already covers `A`
`μ.restrict A`-almost everywhere. -/
private lemma ae_mem_sigmaFiniteCarrier_of_add_restrictFinite
    (μ ν : Measure Ω) [SFinite ν] {A : Set Ω} (hA_fin : μ A < ∞) :
    ∀ᵐ ω ∂ μ.restrict A, ω ∈ μ.sigmaFiniteSetWRT (ν + μ.restrict A) := by
  letI : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 hA_fin.ne
  let C := μ.sigmaFiniteSetWRT (ν + μ.restrict A)
  have hC : MeasurableSet C := measurableSet_sigmaFiniteSetWRT
  rw [ae_iff]
  change μ.restrict A Cᶜ = 0
  by_contra h_nonzero
  have h_nonzero_raw : μ (A ∩ Cᶜ) ≠ 0 := by
    simpa [Measure.restrict_apply, hC.compl, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
      using h_nonzero
  have hrestrict_eval : (μ.restrict A) (A ∩ Cᶜ) = μ (A ∩ Cᶜ) := by
    simpa using
      (Measure.restrict_eq_self μ (Set.inter_subset_left : A ∩ Cᶜ ⊆ A))
  have hrestrict_nonzero : (μ.restrict A) (A ∩ Cᶜ) ≠ 0 := by
    rwa [hrestrict_eval]
  have hcontrol_nonzero : (ν + μ.restrict A) (A ∩ Cᶜ) ≠ 0 := by
    intro h_zero
    apply hrestrict_nonzero
    have hle :
        (μ.restrict A) (A ∩ Cᶜ) ≤ (ν + μ.restrict A) (A ∩ Cᶜ) := by
      rw [Measure.add_apply]
      exact le_add_of_nonneg_left (zero_le _)
    exact le_antisymm (hle.trans (by simpa [h_zero])) (zero_le _)
  have h_top :
      μ (A ∩ Cᶜ) = ∞ :=
    measure_eq_top_of_subset_compl_sigmaFiniteSetWRT
      Set.inter_subset_right hcontrol_nonzero
  have h_le : μ (A ∩ Cᶜ) ≤ μ A := measure_mono Set.inter_subset_left
  -- Proof comment: any positive leftover mass on `A \ C` would force infinite `μ`-mass there by
  -- the defining extremal property of `sigmaFiniteSetWRT`, contradicting `μ A < ∞`.
  exact hA_fin.ne <| top_unique <| h_top ▸ h_le

/-- Helper for Corollary 6.15: if a finite control measure `ν` is enlarged by the finite
restriction `μ.restrict A`, then the resulting canonical carrier for `ν` itself is
`ν`-almost everywhere full. -/
private lemma ae_mem_sigmaFiniteCarrier_of_finiteControl_add_restrictFinite
    (μ ν : Measure Ω) [IsFiniteMeasure ν] {A : Set Ω}
    [SFinite (ν + μ.restrict A)] (_hA_fin : μ A < ∞) :
    ∀ᵐ ω ∂ ν, ω ∈ ν.sigmaFiniteSetWRT (ν + μ.restrict A) := by
  have hν_abs :
      ν ≪ (ν + μ.restrict A) :=
    Measure.absolutelyContinuous_of_le <| by
      intro s
      rw [Measure.add_apply]
      exact le_add_of_nonneg_right (zero_le _)
  -- Proof comment: apply the generic complement-null theorem with first measure `ν`; finite
  -- measures are sigma-finite, so the new carrier is `ν`-almost everywhere full.
  rw [ae_iff]
  exact hν_abs <|
    measure_compl_sigmaFiniteSetWRT (μ := ν) (ν := ν + μ.restrict A) hν_abs

/-- Helper for Corollary 6.15: if a measurable finite test set is almost everywhere contained in
the carrier of a local limit, then that same witness already gives convergence in measure on the
test set itself. -/
private lemma tendstoInMeasure_of_ae_mem_carrier
    (μ : Measure Ω)
    {S A : Set Ω} (hS : MeasurableSet S) (hA : MeasurableSet A)
    {fSeq : ℕ → Ω → E} {f : Ω → E}
    (h_tendsto : TendstoInMeasureOnFiniteMeasureSets (μ.restrict S) fSeq f)
    (hA_fin : μ A < ∞)
    (h_cover : ∀ᵐ ω ∂μ.restrict A, ω ∈ S) :
    TendstoInMeasure (μ.restrict A) fSeq atTop f := by
  have h_local_meas :=
    (tendstoInMeasureOnFiniteMeasureSets_iff_forall_measurable (μ.restrict S)).1 h_tendsto
  have hrestrict_eq : ((μ.restrict S).restrict A) = μ.restrict A := by
    calc
      ((μ.restrict S).restrict A) = ((μ.restrict A).restrict S) := by
        rw [Measure.restrict_restrict hA, Measure.restrict_restrict hS]
        simp [Set.inter_comm]
      _ = μ.restrict A := Measure.restrict_eq_self_of_ae_mem h_cover
  have hA_fin_on_S : (μ.restrict S) A < ∞ := by
    calc
      (μ.restrict S) A = ((μ.restrict S).restrict A) Set.univ := by
        simp
      _ = (μ.restrict A) Set.univ := by rw [hrestrict_eq]
      _ = μ A := by simpa [Measure.restrict_apply_univ] using (Measure.restrict_apply_univ A)
      _ < ∞ := hA_fin
  have hA_tendsto : TendstoInMeasure ((μ.restrict S).restrict A) fSeq atTop f :=
    h_local_meas A hA hA_fin_on_S
  -- Proof comment: once the two restricted measures are identified, the carrier-local limit can
  -- be read directly as convergence on `A`.
  simpa [hrestrict_eq] using hA_tendsto

/-- Helper for Corollary 6.15: if a measurable carrier admits a measure-dense family of finite
subsets on which the same witness is already a local limit, then the witness is a local limit on
the whole carrier. -/
private lemma tendstoInMeasureOnFiniteMeasureSets_ofMeasureDenseFamily
    (μ : Measure Ω)
    {S : Set Ω} (hS : MeasurableSet S)
    {fSeq : ℕ → Ω → E} {f : Ω → E}
    {𝒜 : Set (Set Ω)}
    (hDense : (μ.restrict S).MeasureDense 𝒜)
    (hsubset : ∀ t ∈ 𝒜, t ⊆ S)
    (hfinite : ∀ t ∈ 𝒜, μ t < ∞)
    (htendsto : ∀ t ∈ 𝒜, TendstoInMeasureOnFiniteMeasureSets (μ.restrict t) fSeq f) :
    TendstoInMeasureOnFiniteMeasureSets (μ.restrict S) fSeq f := by
  rw [tendstoInMeasureOnFiniteMeasureSets_iff_forall_measurable]
  intro A hA hA_fin
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  by_cases hδ_top : δ = ∞
  · refine ⟨0, fun n _hn ↦ ?_⟩
    simp [hδ_top]
  have hδ_half_pos : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  have hδ_half_ne_top : δ / 2 ≠ ∞ := by
    simp [ENNReal.div_eq_top, hδ_top]
  have hδ_half_toReal_pos : 0 < (δ / 2).toReal :=
    ENNReal.toReal_pos hδ_half_pos.ne' hδ_half_ne_top
  obtain ⟨t, ht_mem, ht_close⟩ :=
    hDense.approx A hA hA_fin.ne ((δ / 2).toReal) hδ_half_toReal_pos
  have ht_meas : MeasurableSet t := hDense.measurable t ht_mem
  have ht_subset : t ⊆ S := hsubset t ht_mem
  have ht_fin : μ t < ∞ := hfinite t ht_mem
  haveI : IsFiniteMeasure (μ.restrict t) := isFiniteMeasure_restrict.2 ht_fin.ne
  have ht_tendsto :
      TendstoInMeasure (μ.restrict t) fSeq atTop f :=
    (tendstoInMeasureOnFiniteMeasureSets_iff_mathlib_tendstoInMeasure (μ.restrict t)).1
      (htendsto t ht_mem)
  have ht_small := (tendstoInMeasure_iff_dist.1 ht_tendsto) ε hε
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.1 ht_small) (δ / 2) hδ_half_pos
  refine ⟨N, fun n hn ↦ ?_⟩
  let dev : Set Ω := {ω | ε ≤ dist (fSeq n ω) (f ω)}
  have h_diff_subset : A \ t ⊆ symmDiff A t := by
    simpa [Set.symmDiff_def] using
      (subset_union_left : A \ t ⊆ (A \ t) ∪ (t \ A))
  have hsplit :
      ((μ.restrict S).restrict A) dev ≤ (μ.restrict t) dev + (μ.restrict S) (A \ t) := by
    calc
      ((μ.restrict S).restrict A) dev = (μ.restrict S) (dev ∩ A) := by
        rw [Measure.restrict_apply' hA]
      _ ≤ (μ.restrict S) ((dev ∩ t) ∪ (A \ t)) := by
        apply measure_mono
        intro x hx
        rcases hx with ⟨hxDev, hxA⟩
        by_cases hxt : x ∈ t
        · exact Or.inl ⟨hxDev, hxt⟩
        · exact Or.inr ⟨hxA, hxt⟩
      _ ≤ (μ.restrict S) (dev ∩ t) + (μ.restrict S) (A \ t) := measure_union_le _ _
      _ = ((μ.restrict S).restrict t) dev + (μ.restrict S) (A \ t) := by
        congr 1
        symm
        exact Measure.restrict_apply' ht_meas
      _ = (μ.restrict t) dev + (μ.restrict S) (A \ t) := by
        rw [Measure.restrict_restrict_of_subset ht_subset]
  have hlocal_small : (μ.restrict t) dev ≤ δ / 2 := hN n hn
  have hresidual_small : (μ.restrict S) (A \ t) ≤ δ / 2 := by
    calc
      (μ.restrict S) (A \ t) ≤ (μ.restrict S) (symmDiff A t) := measure_mono h_diff_subset
      _ ≤ ENNReal.ofReal ((δ / 2).toReal) := ht_close.le
      _ = δ / 2 := by rw [ENNReal.ofReal_toReal hδ_half_ne_top]
  -- Proof comment: approximate the finite test set by one good dense-family member, control the
  -- deviation on that member by its local limit, and absorb the leftover symmetric-difference
  -- mass into the residual error.
  calc
    ((μ.restrict S).restrict A) dev ≤ (μ.restrict t) dev + (μ.restrict S) (A \ t) := hsplit
    _ ≤ δ / 2 + δ / 2 := add_le_add hlocal_small hresidual_small
    _ = δ := by rw [ENNReal.add_halves]

/-- Helper for Corollary 6.15: a measurable countable family of finite slices can be globalized
with the already compiled countable glue theorem. -/
private lemma existsGlobalLimitOnCountableControlFamily
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E} {s : ℕ → Set Ω}
    (hs : ∀ n, MeasurableSet (s n))
    (hs_fin : ∀ n, μ (s n) < ∞)
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq) :
    ∃ f : Ω → E, ∀ n, TendstoInMeasureOnFiniteMeasureSets (μ.restrict (s n)) fSeq f := by
  have h_exists :
      ∀ n, ∃ g : Ω → E, TendstoInMeasureOnFiniteMeasureSets (μ.restrict (s n)) fSeq g := by
    intro n
    exact existsLimitOnFiniteRestriction μ h_cauchy (hs n) (hs_fin n)
  choose g hg using h_exists
  have hcompat : ∀ i j, g i =ᵐ[μ.restrict (s i ∩ s j)] g j := by
    -- Proof comment: the local witnesses all come from the same original sequence, so the finite
    -- overlap uniqueness lemma forces pairwise a.e. compatibility.
    exact chosenFiniteRestrictionLimits_compatible μ hs hs_fin hg
  obtain ⟨f, hf⟩ := glueCountableCompatibleFiniteRestrictions μ hs hcompat
  refine ⟨f, ?_⟩
  intro n
  -- Proof comment: on each control slice, the glued witness differs from the chosen local limit
  -- only by restricted almost-everywhere equality, so convergence in measure transports directly.
  exact tendstoInMeasureOnFiniteMeasureSets_congr_ae (μ := μ.restrict (s n)) (hf n).symm (hg n)

/-- Helper for Corollary 6.15: if one fixed countable family is measure-dense after intersecting
with every finite test set, then local limits on that family already imply the full theorem. -/
private lemma existsGlobalLimitFromCountableControlFamily
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E} {f : Ω → E} {s : ℕ → Set Ω}
    (hs : ∀ n, MeasurableSet (s n))
    (hDense :
      ∀ A, MeasurableSet A → μ A < ∞ →
        (μ.restrict A).MeasureDense (Set.range fun n : ℕ ↦ A ∩ s n))
    (hlocal : ∀ n, TendstoInMeasureOnFiniteMeasureSets (μ.restrict (s n)) fSeq f) :
    TendstoInMeasureOnFiniteMeasureSets μ fSeq f := by
  rw [tendstoInMeasureOnFiniteMeasureSets_iff_forall_measurable]
  intro A hA hA_fin
  haveI : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 hA_fin.ne
  have hlocalInter :
      ∀ t ∈ Set.range (fun n : ℕ ↦ A ∩ s n),
        TendstoInMeasureOnFiniteMeasureSets (μ.restrict t) fSeq f := by
    rintro t ⟨n, rfl⟩
    -- Proof comment: restricting the `n`th local control-slice convergence to the finite test
    -- set `A` gives the required convergence on the intersection `A ∩ s n`.
    simpa [Measure.restrict_restrict hA, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
      using
        (tendstoInMeasureOnFiniteMeasureSets_restrict
          (μ := μ.restrict (s n)) (h_tendsto := hlocal n) hA)
  exact
    (tendstoInMeasureOnFiniteMeasureSets_iff_mathlib_tendstoInMeasure (μ.restrict A)).1 <|
      tendstoInMeasureOnFiniteMeasureSets_ofMeasureDenseFamily (μ := μ) (S := A) hA
        (hDense A hA hA_fin)
        (by
          rintro t ⟨n, rfl⟩ x hx
          exact hx.1)
        (by
          rintro t ⟨n, rfl⟩
          exact lt_of_le_of_lt (measure_mono Set.inter_subset_left) hA_fin)
        hlocalInter

/-- Helper for Corollary 6.15: a partial local limit records a measurable carrier together with a
representative that already realizes the local convergence on that carrier. -/
private structure PartialLocalLimit (μ : Measure Ω) (fSeq : ℕ → Ω → E) where
  carrier : Set Ω
  carrier_meas : MeasurableSet carrier
  witness : Ω → E
  tendsto : TendstoInMeasureOnFiniteMeasureSets (μ.restrict carrier) fSeq witness

/-- Helper for Corollary 6.15: on the empty carrier, every witness is vacuously a local limit. -/
private lemma tendstoInMeasureOnFiniteMeasureSets_empty
    (μ : Measure Ω) {fSeq : ℕ → Ω → E} {f : Ω → E} :
    TendstoInMeasureOnFiniteMeasureSets (μ.restrict ∅) fSeq f := by
  intro A hA_fin
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  simp [Measure.restrict_empty]

/-- Helper for Corollary 6.15: exact extension means enlarging the carrier while keeping the old
witness pointwise unchanged on the old carrier. -/
private def PartialLocalLimit.ExactExtension
    {μ : Measure Ω} {fSeq : ℕ → Ω → E}
    (p q : PartialLocalLimit μ fSeq) : Prop :=
  p.carrier ⊆ q.carrier ∧ Set.EqOn q.witness p.witness p.carrier

private instance instLEPartialLocalLimit
    {μ : Measure Ω} {fSeq : ℕ → Ω → E} : LE (PartialLocalLimit μ fSeq) where
  le := PartialLocalLimit.ExactExtension

/-- Helper for Corollary 6.15: the exact-extension order is reflexive and transitive, so Zorn can
later be applied once chain upper bounds are available. -/
private instance instPreorderPartialLocalLimit
    {μ : Measure Ω} {fSeq : ℕ → Ω → E} : Preorder (PartialLocalLimit μ fSeq) where
  le := (· ≤ ·)
  le_refl p := ⟨subset_rfl, fun _ _ ↦ rfl⟩
  le_trans p q r hpq hqr := by
    refine ⟨hpq.1.trans hqr.1, ?_⟩
    intro x hx
    exact (hqr.2 (hpq.1 hx)).trans (hpq.2 hx)

/-- Helper for Corollary 6.15: the empty carrier with witness `fSeq 0` is the canonical starting
point for the exact-extension Zorn argument. -/
private def emptyPartialLocalLimit
    (μ : Measure Ω) (fSeq : ℕ → Ω → E) : PartialLocalLimit μ fSeq :=
  { carrier := ∅
    carrier_meas := MeasurableSet.empty
    witness := fSeq 0
    tendsto := tendstoInMeasureOnFiniteMeasureSets_empty μ }

/-- Helper for Corollary 6.15: a supported partial local limit strengthens
`PartialLocalLimit` by one countable family of measurable finite-measure support pieces whose
union already covers every finite measurable slice of the carrier almost everywhere. -/
private structure SupportedPartialLocalLimit (μ : Measure Ω) (fSeq : ℕ → Ω → E)
    extends PartialLocalLimit μ fSeq where
  support : ℕ → Set Ω
  support_subset : ∀ n, support n ⊆ carrier
  support_meas : ∀ n, MeasurableSet (support n)
  support_finite : ∀ n, μ (support n) < ∞
  ae_mem_iUnion_support :
    ∀ ⦃A : Set Ω⦄, MeasurableSet A → μ A < ∞ → A ⊆ carrier →
      ∀ᵐ x ∂ μ.restrict A, x ∈ ⋃ n, support n

/-- Helper for Corollary 6.15: the repaired globalization shell records an arbitrary measurable
finite-measure cover family, rather than one global countable support sequence for the whole
carrier. -/
private structure LocallyCoveredPartialLocalLimit (μ : Measure Ω) (fSeq : ℕ → Ω → E)
    extends PartialLocalLimit μ fSeq where
  cover : Set (Set Ω)
  cover_subset : ∀ s ∈ cover, s ⊆ carrier
  cover_meas : ∀ s ∈ cover, MeasurableSet s
  cover_finite : ∀ s ∈ cover, μ s < ∞
  ae_mem_sUnion_cover :
    ∀ ⦃A : Set Ω⦄, MeasurableSet A → μ A < ∞ → A ⊆ carrier →
      ∀ᵐ x ∂ μ.restrict A, x ∈ ⋃₀ cover

/-- Helper for Corollary 6.15: the empty carrier also satisfies the locally-covered-shell
invariant, because every finite measurable slice of `∅` is empty. -/
private def emptyLocallyCoveredPartialLocalLimit
    (μ : Measure Ω) (fSeq : ℕ → Ω → E) : LocallyCoveredPartialLocalLimit μ fSeq :=
  { emptyPartialLocalLimit μ fSeq with
    cover := ∅
    cover_subset := by
      intro s hs x hx
      exact False.elim hs
    cover_meas := by
      intro s hs
      exact False.elim hs
    cover_finite := by
      intro s hs
      exact False.elim hs
    ae_mem_sUnion_cover := by
      intro A hA hA_fin hA_subset
      have hA_empty : A = ∅ := by
        ext x
        constructor
        · intro hx
          exact (hA_subset hx).elim
        · intro hx
          simp at hx
      simpa [hA_empty, Measure.restrict_empty] }

/-- Helper for Corollary 6.15: the locally-covered shell uses the same exact carrier extension
order as `PartialLocalLimit`; the cover family is auxiliary data for proving upper bounds. -/
private def LocallyCoveredPartialLocalLimit.ExactExtension
    {μ : Measure Ω} {fSeq : ℕ → Ω → E}
    (p q : LocallyCoveredPartialLocalLimit μ fSeq) : Prop :=
  p.carrier ⊆ q.carrier ∧ Set.EqOn q.witness p.witness p.carrier

private instance instLELocallyCoveredPartialLocalLimit
    {μ : Measure Ω} {fSeq : ℕ → Ω → E} : LE (LocallyCoveredPartialLocalLimit μ fSeq) where
  le := LocallyCoveredPartialLocalLimit.ExactExtension

/-- Helper for Corollary 6.15: the locally-covered exact-extension relation is reflexive and
transitive, so Zorn can run on the repaired globalization shell. -/
private instance instPreorderLocallyCoveredPartialLocalLimit
    {μ : Measure Ω} {fSeq : ℕ → Ω → E} : Preorder (LocallyCoveredPartialLocalLimit μ fSeq) where
  le := (· ≤ ·)
  le_refl p := ⟨subset_rfl, fun _ _ ↦ rfl⟩
  le_trans p q r hpq hqr := by
    refine ⟨hpq.1.trans hqr.1, ?_⟩
    -- Proof comment: exact extension composes by restricting the later witness equality from
    -- `q.carrier` back to `p.carrier`.
    intro x hx
    exact (hqr.2 (hpq.1 hx)).trans (hpq.2 hx)

/-- Helper for Corollary 6.15: the empty carrier also satisfies the supported-shell invariant,
because every finite measurable slice of `∅` is itself empty. -/
private def emptySupportedPartialLocalLimit
    (μ : Measure Ω) (fSeq : ℕ → Ω → E) : SupportedPartialLocalLimit μ fSeq :=
  { emptyPartialLocalLimit μ fSeq with
    support := fun _ ↦ ∅
    support_subset := by
      intro n x hx
      simp at hx
    support_meas := by
      intro n
      exact MeasurableSet.empty
    support_finite := by
      intro n
      simp
    ae_mem_iUnion_support := by
      intro A hA hA_fin hA_subset
      have hA_empty : A = ∅ := by
        ext x
        constructor
        · intro hx
          exact (hA_subset hx).elim
        · intro hx
          simp at hx
      simpa [hA_empty, Measure.restrict_empty] }

/-- Helper for Corollary 6.15: the supported-shell order only preserves the old witness up to
`μ.restrict p.carrier`-almost-everywhere equality, which removes the false null-slice pointwise
invariant from the obsolete finite-slice shell. -/
private def SupportedPartialLocalLimit.AeExtension
    {μ : Measure Ω} {fSeq : ℕ → Ω → E}
    (p q : SupportedPartialLocalLimit μ fSeq) : Prop :=
  p.carrier ⊆ q.carrier ∧ p.witness =ᵐ[μ.restrict p.carrier] q.witness

private instance instLESupportedPartialLocalLimit
    {μ : Measure Ω} {fSeq : ℕ → Ω → E} : LE (SupportedPartialLocalLimit μ fSeq) where
  le := SupportedPartialLocalLimit.AeExtension

/-- Helper for Corollary 6.15: the supported-shell a.e.-extension relation is reflexive and
transitive, so it can support the replacement Zorn argument once the chain upper bound is proved.
-/
private instance instPreorderSupportedPartialLocalLimit
    {μ : Measure Ω} {fSeq : ℕ → Ω → E} : Preorder (SupportedPartialLocalLimit μ fSeq) where
  le := (· ≤ ·)
  le_refl p := ⟨subset_rfl, Filter.EventuallyEq.rfl⟩
  le_trans p q r hpq hqr := by
    refine ⟨hpq.1.trans hqr.1, ?_⟩
    -- Proof comment: the second a.e.-equality only needs to be restricted from `q.carrier` down
    -- to `p.carrier`, because `p ≤ q` already records the carrier inclusion.
    exact hpq.2.trans <| ae_restrict_of_ae_restrict_of_subset hpq.1 hqr.2

/-- Helper for Corollary 6.15: the raw union of the carriers in a chain is the natural support of
the eventual upper-bound witness. -/
private def chainCarrier
    {μ : Measure Ω} {fSeq : ℕ → Ω → E}
    (c : Set (PartialLocalLimit μ fSeq)) : Set Ω :=
  ⋃ p ∈ c, p.carrier

/-- Helper for Corollary 6.15: on the raw chain union, read the value from any chain member
containing the point; outside the union, fall back to a fixed base witness. -/
private noncomputable def chainWitness
    {μ : Measure Ω} {fSeq : ℕ → Ω → E}
    (c : Set (PartialLocalLimit μ fSeq)) (base : Ω → E) : Ω → E :=
  by
    classical
    exact fun x ↦
      if hx : x ∈ chainCarrier c then
        let p := Classical.choose (Set.mem_iUnion₂.mp hx)
        p.witness x
      else
        base x

/-- Helper for Corollary 6.15: on every member of an exact-extension chain, the canonical
`chainWitness` agrees pointwise with that member's witness. -/
private lemma chainWitness_eqOn_member
    {μ : Measure Ω} {fSeq : ℕ → Ω → E}
    {c : Set (PartialLocalLimit μ fSeq)}
    (hc : IsChain (fun p q : PartialLocalLimit μ fSeq ↦ p ≤ q) c)
    {base : Ω → E} {p : PartialLocalLimit μ fSeq}
    (hp : p ∈ c) :
    Set.EqOn (chainWitness c base) p.witness p.carrier := by
  classical
  intro x hx
  have hx_chain : x ∈ chainCarrier c := Set.mem_iUnion₂.2 ⟨p, hp, hx⟩
  let q : PartialLocalLimit μ fSeq := Classical.choose (Set.mem_iUnion₂.mp hx_chain)
  have hq : q ∈ c := (Classical.choose_spec (Set.mem_iUnion₂.mp hx_chain)).1
  have hxq : x ∈ q.carrier := (Classical.choose_spec (Set.mem_iUnion₂.mp hx_chain)).2
  have hq_eq : q.witness x = p.witness x := by
    rcases hc.total hp hq with hpq | hqp
    · exact hpq.2 hx
    · exact (hqp.2 hxq).symm
  -- Proof comment: the chosen chain witness may come from a different chain member, but chain
  -- comparability plus exact-extension compatibility makes its value agree on the overlap.
  simpa [chainWitness, hx_chain, q] using hq_eq

/-- Helper for Corollary 6.15: any countable family inside an exact-extension chain can be
replaced by a monotone sequence in the same chain that dominates it termwise. -/
private lemma existsMonotoneChainSequence_dominating
    {μ : Measure Ω} {fSeq : ℕ → Ω → E}
    {c : Set (PartialLocalLimit μ fSeq)}
    (hc : IsChain (fun p q : PartialLocalLimit μ fSeq ↦ p ≤ q) c)
    {u : ℕ → PartialLocalLimit μ fSeq}
    (hu : ∀ n, u n ∈ c) :
    ∃ s : ℕ → PartialLocalLimit μ fSeq,
      (∀ n, s n ∈ c) ∧
      Monotone s ∧
      ∀ n, u n ≤ s n := by
  classical
  let s : ℕ → PartialLocalLimit μ fSeq :=
    Nat.rec (u 0) fun n (prev : PartialLocalLimit μ fSeq) ↦
      if h : u (n + 1) ≤ prev then prev else u (n + 1)
  have hs_zero : s 0 = u 0 := by
    simp [s]
  have hs_mem : ∀ n, s n ∈ c := by
    intro n
    induction n with
    | zero =>
        simpa [hs_zero] using hu 0
    | succ n ihn =>
        simp [s]
        split_ifs with h
        · exact ihn
        · exact hu (n + 1)
  have hs_step : ∀ n, s n ≤ s (n + 1) := by
    intro n
    simp [s]
    split_ifs with h
    · exact le_rfl
    · rcases hc.total (hu (n + 1)) (hs_mem n) with hcmp | hcmp
      · exact False.elim (h hcmp)
      · exact hcmp
  have hs_mono : Monotone s := monotone_nat_of_le_succ hs_step
  refine ⟨s, hs_mem, hs_mono, ?_⟩
  intro n
  cases n with
  | zero =>
      simpa [hs_zero]
  | succ n =>
      simp [s]
      split_ifs with h
      · exact h
      · exact le_rfl

/-- Helper for Corollary 6.15: on a finite test set, every exact-extension chain admits a
monotone countable subchain whose union already dominates each chain carrier almost everywhere. -/
private lemma existsMonotoneChainSequence_aeDominatingOnFiniteSet
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E}
    {c : Set (PartialLocalLimit μ fSeq)}
    (hc : IsChain (fun p q : PartialLocalLimit μ fSeq ↦ p ≤ q) c)
    {y : PartialLocalLimit μ fSeq} (hy : y ∈ c)
    {A : Set Ω} (hA_fin : μ A < ∞) :
    ∃ s : ℕ → PartialLocalLimit μ fSeq,
      (∀ n, s n ∈ c) ∧
      Monotone (fun n => (s n).carrier) ∧
      ∀ z ∈ c, z.carrier ≤ᵐ[μ.restrict A] ⋃ n, (s n).carrier := by
  classical
  haveI : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 hA_fin.ne
  let C : Set (Set Ω) := {S | ∃ z ∈ c, z.carrier = S}
  have hC_meas : ∀ s ∈ C, MeasurableSet s := by
    intro s hs
    rcases hs with ⟨z, -, rfl⟩
    exact z.carrier_meas
  obtain ⟨D, hDC, hD_count, hD_cover⟩ :=
    Measure.exists_ae_subset_biUnion_countable (μ := μ.restrict A) hC_meas
  obtain ⟨g, hgD⟩ := Set.countable_iff_exists_subset_range.mp hD_count
  let u : ℕ → PartialLocalLimit μ fSeq := fun n ↦
    if hgn : g n ∈ C then Classical.choose hgn else y
  have hu_mem : ∀ n, u n ∈ c := by
    intro n
    by_cases hgn : g n ∈ C
    · simpa [u, hgn] using (Classical.choose_spec hgn).1
    · simpa [u, hgn] using hy
  obtain ⟨s, hs_mem, hs_mono, hus⟩ :=
    existsMonotoneChainSequence_dominating hc hu_mem
  have hs_carrier_mono : Monotone (fun n => (s n).carrier) := by
    intro i j hij
    exact (hs_mono hij).1
  refine ⟨s, hs_mem, hs_carrier_mono, ?_⟩
  have hD_subset_uUnion : ⋃₀ D ⊆ ⋃ n, (u n).carrier := by
    intro x hx
    rcases Set.mem_sUnion.1 hx with ⟨d, hdD, hxd⟩
    rcases hgD hdD with ⟨n, rfl⟩
    have hgn : g n ∈ C := hDC hdD
    have hxu : x ∈ (u n).carrier := by
      -- Proof comment: when the enumerated carrier really comes from the chain, the chosen
      -- representative has exactly that carrier, so points of the counted union lie in `u n`.
      have hcarrier : (Classical.choose hgn).carrier = g n := (Classical.choose_spec hgn).2
      have hxchoose : x ∈ (Classical.choose hgn).carrier := by
        simpa [hcarrier] using hxd
      simpa [u, hgn] using hxchoose
    exact Set.mem_iUnion.2 ⟨n, hxu⟩
  have huUnion_subset_sUnion : (⋃ n, (u n).carrier) ⊆ ⋃ n, (s n).carrier := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨n, hxn⟩
    exact Set.mem_iUnion.2 ⟨n, (hus n).1 hxn⟩
  intro z hz
  have hz_cover : z.carrier ≤ᵐ[μ.restrict A] ⋃₀ D := hD_cover z.carrier ⟨z, hz, rfl⟩
  -- Proof comment: the countable measurable-union theorem first compresses the whole chain
  -- carrier family to one countable subfamily, and the monotone domination step then upgrades
  -- that family to an increasing sequence inside the same chain.
  exact hz_cover.trans <| Filter.Eventually.of_forall fun x hx ↦
    huUnion_subset_sUnion (hD_subset_uUnion hx)

/-- Helper for Corollary 6.15: on a finite test set, the chain carriers admit members whose
restricted measures approach the supremum from below with an explicit geometric error. -/
private lemma existsChainCarrier_nearSupOnFiniteSet
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E}
    {c : Set (PartialLocalLimit μ fSeq)}
    {y : PartialLocalLimit μ fSeq} (hy : y ∈ c)
    {A : Set Ω} (hA_fin : μ A < ∞) :
    ∀ n, ∃ p ∈ c,
      ((⨆ q : c, (μ.restrict A) q.1.carrier) - ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) ≤
        (μ.restrict A) p.carrier := by
  classical
  intro n
  let M : ℝ≥0∞ := ⨆ q : c, (μ.restrict A) q.1.carrier
  have hM_le : M ≤ μ A := by
    refine iSup_le fun q ↦ ?_
    calc
      (μ.restrict A) q.1.carrier ≤ (μ.restrict A) Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = μ A := by simp
  have hM_ne_top : M ≠ ∞ := ne_top_of_le_ne_top hA_fin.ne hM_le
  let η : ℝ≥0∞ := ((n + 1 : ℕ) : ℝ≥0∞)⁻¹
  by_cases hηM : η < M
  · have hsub_lt : M - η < M := ENNReal.sub_lt_self hM_ne_top hηM.ne_bot (by simp [η])
    obtain ⟨q, hq⟩ := exists_lt_of_lt_ciSup' hsub_lt
    exact ⟨q.1, q.2, le_of_lt hq⟩
  · refine ⟨y, hy, ?_⟩
    have hzero : M - η = 0 := tsub_eq_zero_of_le (not_lt.mp hηM)
    rw [hzero]
    exact zero_le _

/-- Helper for Corollary 6.15: the near-sup chain members on a finite test set can be
monotonized without losing the quantitative carrier-measure approximation. -/
private lemma existsChainCarrierApproxOnFiniteSet
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E}
    {c : Set (PartialLocalLimit μ fSeq)}
    (hc : IsChain (fun p q : PartialLocalLimit μ fSeq ↦ p ≤ q) c)
    {y : PartialLocalLimit μ fSeq} (hy : y ∈ c)
    {A : Set Ω} (hA_fin : μ A < ∞) :
    ∃ s : ℕ → PartialLocalLimit μ fSeq,
      (∀ n, s n ∈ c) ∧
      Monotone s ∧
      ∀ n,
        ((⨆ q : c, (μ.restrict A) q.1.carrier) - ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) ≤
          (μ.restrict A) (s n).carrier := by
  classical
  have hnear := existsChainCarrier_nearSupOnFiniteSet μ hy hA_fin
  choose u hu_mem hu_bound using hnear
  obtain ⟨s, hs_mem, hs_mono, hus⟩ :=
    existsMonotoneChainSequence_dominating hc hu_mem
  refine ⟨s, hs_mem, hs_mono, ?_⟩
  intro n
  exact (hu_bound n).trans <| measure_mono (hus n).1

/-- Helper for Corollary 6.15: on a finite restricted measure, a measurable set of full
restricted mass holds almost everywhere. -/
private lemma ae_mem_of_restrict_eq_full
    (μ : Measure Ω)
    {A U : Set Ω}
    (hU : MeasurableSet U)
    (hA_fin : μ A < ∞)
    (hfull : (μ.restrict A) U = μ A) :
    ∀ᵐ x ∂ μ.restrict A, x ∈ U := by
  have hU_fin : (μ.restrict A) U ≠ ∞ :=
    ne_top_of_le_ne_top hA_fin.ne <| by
      calc
        (μ.restrict A) U ≤ (μ.restrict A) Set.univ := measure_mono (Set.subset_univ U)
        _ = μ A := by simp
  rw [ae_iff]
  change (μ.restrict A) Uᶜ = 0
  -- Proof comment: on the finite restricted measure `μ.restrict A`, full mass of `U` is
  -- equivalent to null mass of the measurable complement.
  calc
    (μ.restrict A) Uᶜ = (μ.restrict A) Set.univ - (μ.restrict A) U := by
      simpa using (measure_compl (μ := μ.restrict A) hU hU_fin)
    _ = μ A - μ A := by simp [hfull]
    _ = 0 := by simp

/-- Helper for Corollary 6.15: if a finite measurable slice lies inside the measurable hull of
the raw chain carrier, then that measurable hull has full restricted mass on the slice. -/
private lemma measurableHullChainCarrier_fullOnFiniteSlice
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E}
    {c : Set (PartialLocalLimit μ fSeq)}
    {A : Set Ω}
    (hA : MeasurableSet A) (hA_fin : μ A < ∞)
    (hA_subset : A ⊆ toMeasurable μ (chainCarrier c)) :
    (μ.restrict A) (toMeasurable μ (chainCarrier c)) = μ A := by
  -- Proof comment: on the finite slice `A`, the measurable hull already contains every point of
  -- `A`, so restricting to that hull does not change the slice measure.
  calc
    (μ.restrict A) (toMeasurable μ (chainCarrier c)) =
        μ (toMeasurable μ (chainCarrier c) ∩ A) := by
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
        (Measure.restrict_apply' hA :
          (μ.restrict A) (toMeasurable μ (chainCarrier c)) =
            μ (toMeasurable μ (chainCarrier c) ∩ A))
    _ = μ A := by
      congr 1
      ext x
      constructor
      · intro hx
        exact hx.2
      · intro hx
        exact ⟨hA_subset hx, hx⟩

/-- Helper for Corollary 6.15: the monotone carrier approximation extracted from a chain realizes
the chain-measure supremum on the chosen finite slice as one concrete countable union. -/
private lemma iUnionChainCarrierApprox_apply
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E}
    {c : Set (PartialLocalLimit μ fSeq)}
    {A : Set Ω}
    (hA_fin : μ A < ∞)
    {s : ℕ → PartialLocalLimit μ fSeq}
    (hs_mem : ∀ n, s n ∈ c)
    (hs_mono : Monotone fun n => (s n).carrier)
    (hs_approx :
      ∀ n,
        ((⨆ q : c, (μ.restrict A) q.1.carrier) - ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) ≤
          (μ.restrict A) (s n).carrier) :
    (μ.restrict A) (⋃ n, (s n).carrier) = ⨆ q : c, (μ.restrict A) q.1.carrier := by
  let M : ℝ≥0∞ := ⨆ q : c, (μ.restrict A) q.1.carrier
  have hM_le : M ≤ μ A := by
    refine iSup_le ?_
    intro q
    calc
      (μ.restrict A) q.1.carrier ≤ (μ.restrict A) Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = μ A := by simp
  have hseq_le : (⨆ n, (μ.restrict A) (s n).carrier) ≤ M := by
    refine iSup_le ?_
    intro n
    exact le_iSup_of_le ⟨s n, hs_mem n⟩ le_rfl
  have hM_le_seq : M ≤ ⨆ n, (μ.restrict A) (s n).carrier := by
    refine ENNReal.le_of_forall_pos_le_add ?_
    intro ε hε hseq_ne_top
    obtain ⟨N, hN⟩ := ENNReal.exists_inv_nat_lt
      (show ((ε : NNReal) : ℝ≥0∞) ≠ 0 from by exact_mod_cast (ne_of_gt hε))
    have hinv_lt : (((N + 1 : ℕ) : ℝ≥0∞)⁻¹) < ε := by
      exact lt_of_le_of_lt
        (ENNReal.inv_le_inv.2 <| Nat.cast_le.2 N.le_succ) hN
    have hstep : M ≤ (μ.restrict A) (s N).carrier + (((N + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
      exact tsub_le_iff_right.mp (hs_approx N)
    -- Proof comment: the explicit geometric lower bounds on the approximating subchain force the
    -- supremum over the sequence to recover the full chain supremum.
    exact hstep.trans <| add_le_add (le_iSup (fun n => (μ.restrict A) (s n).carrier) N) hinv_lt.le
  -- Proof comment: continuity from below rewrites the countable union measure as the supremum of
  -- the increasing carrier measures, and the approximation bounds identify that supremum.
  calc
    (μ.restrict A) (⋃ n, (s n).carrier) = ⨆ n, (μ.restrict A) (s n).carrier := by
      rw [hs_mono.measure_iUnion]
    _ = M := le_antisymm hseq_le hM_le_seq
    _ = ⨆ q : c, (μ.restrict A) q.1.carrier := rfl

/-- Helper for Corollary 6.15: once an approximating monotone subchain already attains the full
restricted mass on a finite slice `A`, its raw carrier union covers `A` almost everywhere. -/
private lemma ae_mem_iUnion_chainCarrierApprox_of_iSup_eq_full
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E}
    {c : Set (PartialLocalLimit μ fSeq)}
    {A : Set Ω}
    (hA_fin : μ A < ∞)
    {s : ℕ → PartialLocalLimit μ fSeq}
    (hs_mem : ∀ n, s n ∈ c)
    (hs_mono : Monotone s)
    (hs_approx :
      ∀ n,
        ((⨆ q : c, (μ.restrict A) q.1.carrier) - ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) ≤
          (μ.restrict A) (s n).carrier)
    (hfull : (⨆ q : c, (μ.restrict A) q.1.carrier) = μ A) :
    ∀ᵐ x ∂ μ.restrict A, x ∈ ⋃ n, (s n).carrier := by
  let U : Set Ω := ⋃ n, (s n).carrier
  have hU_meas : MeasurableSet U := MeasurableSet.iUnion fun n ↦ (s n).carrier_meas
  have hU_full : (μ.restrict A) U = μ A := by
    calc
      (μ.restrict A) U = ⨆ q : c, (μ.restrict A) q.1.carrier :=
        iUnionChainCarrierApprox_apply μ hA_fin hs_mem (fun i j hij ↦ (hs_mono hij).1) hs_approx
      _ = μ A := hfull
  -- Proof comment: once the explicit countable subchain recovers the full restricted mass on
  -- `A`, the complement of its carrier union is null for `μ.restrict A`.
  exact ae_mem_of_restrict_eq_full μ hU_meas hA_fin hU_full

/-- Helper for Corollary 6.15: after the restricted carrier-mass supremum is known to equal the
full mass of a finite slice, the existing approximation lemmas produce the required monotone
countable carrier cover inside the same chain. -/
private lemma existsMonotoneCarrierCoverOnFiniteSlice_of_iSup_eq_full
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E}
    {c : Set (PartialLocalLimit μ fSeq)}
    (hc : IsChain (fun p q : PartialLocalLimit μ fSeq ↦ p ≤ q) c)
    {y : PartialLocalLimit μ fSeq} (hy : y ∈ c)
    {A : Set Ω} (hA_fin : μ A < ∞)
    (hfull : (⨆ q : c, (μ.restrict A) q.1.carrier) = μ A) :
    ∃ s : ℕ → PartialLocalLimit μ fSeq,
      (∀ n, s n ∈ c) ∧
      Monotone (fun n => (s n).carrier) ∧
      ∀ᵐ x ∂ μ.restrict A, x ∈ ⋃ n, (s n).carrier := by
  obtain ⟨s, hs_mem, hs_mono, hs_approx⟩ :=
    existsChainCarrierApproxOnFiniteSet μ hc hy hA_fin
  refine ⟨s, hs_mem, ?_, ?_⟩
  · -- Proof comment: the carrier monotonicity is the only part of the approximating sequence
    -- needed later when the chain witness is assembled on the finite slice.
    intro i j hij
    exact (hs_mono hij).1
  · -- Proof comment: the full-mass hypothesis is exactly the input needed by the previously
    -- isolated almost-everywhere carrier-cover lemma.
    exact
      ae_mem_iUnion_chainCarrierApprox_of_iSup_eq_full
        μ hA_fin hs_mem hs_mono hs_approx hfull

/-- Helper for Corollary 6.15: if two local limits agree almost everywhere on the overlap of two
measurable carriers, then the piecewise exact extension is a local limit on the union carrier. -/
private lemma tendstoInMeasureOnFiniteMeasureSets_union_piecewise
    (μ : Measure Ω)
    {S C : Set Ω} (hS : MeasurableSet S) (hC : MeasurableSet C)
    [DecidablePred fun x ↦ x ∈ S]
    {fSeq : ℕ → Ω → E} {f g : Ω → E}
    (hf : TendstoInMeasureOnFiniteMeasureSets (μ.restrict S) fSeq f)
    (hg : TendstoInMeasureOnFiniteMeasureSets (μ.restrict C) fSeq g)
    (hfg : f =ᵐ[μ.restrict (S ∩ C)] g) :
    TendstoInMeasureOnFiniteMeasureSets (μ.restrict (S ∪ C)) fSeq (S.piecewise f g) := by
  rw [tendstoInMeasureOnFiniteMeasureSets_iff_forall_measurable]
  intro A hA hA_fin
  let k : Ω → E := S.piecewise f g
  have hA_S_fin : (μ.restrict S) A < ∞ := by
    calc
      (μ.restrict S) A = μ (A ∩ S) := by
        simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
          (Measure.restrict_apply' hS)
      _ ≤ μ (A ∩ (S ∪ C)) := measure_mono fun _ hx ↦ ⟨hx.1, Or.inl hx.2⟩
      _ = (μ.restrict (S ∪ C)) A := by
        simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
          (Measure.restrict_apply' (hS.union hC)).symm
      _ < ∞ := hA_fin
  have hA_C_fin : (μ.restrict C) A < ∞ := by
    calc
      (μ.restrict C) A = μ (A ∩ C) := by
        simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
          (Measure.restrict_apply' hC)
      _ ≤ μ (A ∩ (S ∪ C)) := measure_mono fun _ hx ↦ ⟨hx.1, Or.inr hx.2⟩
      _ = (μ.restrict (S ∪ C)) A := by
        simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
          (Measure.restrict_apply' (hS.union hC)).symm
      _ < ∞ := hA_fin
  have hkS : k =ᵐ[((μ.restrict S).restrict A)] f := by
    exact (piecewise_ae_eq_restrict hS).restrict
  have hkC_base : k =ᵐ[μ.restrict C] g := by
    have hfg_global : ∀ᵐ x ∂μ, x ∈ S ∩ C → f x = g x :=
      (ae_restrict_iff' (hS.inter hC)).1 hfg
    have hkC_global : ∀ᵐ x ∂μ, x ∈ C → k x = g x := by
      filter_upwards [hfg_global] with x hx hxC
      by_cases hxS : x ∈ S
      · simpa [k, hxS, hx ⟨hxS, hxC⟩]
      · simpa [k, hxS]
    exact (ae_restrict_iff' hC).2 hkC_global
  have hkC : k =ᵐ[((μ.restrict C).restrict A)] g := hkC_base.restrict
  have hS_tendsto :
      TendstoInMeasure ((μ.restrict S).restrict A) fSeq atTop k :=
    TendstoInMeasure.congr_right hkS.symm (hf A hA_S_fin)
  have hC_tendsto :
      TendstoInMeasure ((μ.restrict C).restrict A) fSeq atTop k :=
    TendstoInMeasure.congr_right hkC.symm (hg A hA_C_fin)
  rw [tendstoInMeasure_iff_dist] at hS_tendsto hC_tendsto ⊢
  intro ε hε
  have hS_small := hS_tendsto ε hε
  have hC_small := hC_tendsto ε hε
  let dev : ℕ → Set Ω := fun n ↦ {ω | ε ≤ dist (fSeq n ω) (k ω)}
  have h_union_bound :
      ∀ n,
        ((μ.restrict (S ∪ C)).restrict A) (dev n) ≤
          ((μ.restrict S).restrict A) (dev n) + ((μ.restrict C).restrict A) (dev n) := by
    intro n
    have h_subset :
        (dev n ∩ A ∩ (S ∪ C)) ⊆ (dev n ∩ A ∩ S) ∪ (dev n ∩ A ∩ C) := by
      intro x hx
      rcases hx with ⟨hxDevA, hxUnion⟩
      rcases hxDevA with ⟨hxDev, hxA⟩
      have hxUnion' : x ∈ S ∨ x ∈ C := by
        simpa [Set.mem_union] using hxUnion
      rcases hxUnion' with hxS | hxC
      · exact Or.inl ⟨⟨hxDev, hxA⟩, hxS⟩
      · exact Or.inr ⟨⟨hxDev, hxA⟩, hxC⟩
    calc
      ((μ.restrict (S ∪ C)).restrict A) (dev n)
          = μ (dev n ∩ A ∩ (S ∪ C)) := by
              rw [Measure.restrict_apply' hA]
              have h_union_apply :
                  (μ.restrict (S ∪ C)) (dev n ∩ A) = μ ((dev n ∩ A) ∩ (S ∪ C)) :=
                Measure.restrict_apply' (hS.union hC)
              simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
                h_union_apply
      _ ≤ μ ((dev n ∩ A ∩ S) ∪ (dev n ∩ A ∩ C)) := measure_mono h_subset
      _ ≤ μ (dev n ∩ A ∩ S) + μ (dev n ∩ A ∩ C) := measure_union_le _ _
      _ = ((μ.restrict S).restrict A) (dev n) + ((μ.restrict C).restrict A) (dev n) := by
            rw [Measure.restrict_apply' hA]
            rw [Measure.restrict_apply' hA]
            congr 1
            · simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
                (Measure.restrict_apply' hS).symm
            · simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
                (Measure.restrict_apply' hC).symm
  have h_sum_tendsto :
      Tendsto
        (fun n ↦ ((μ.restrict S).restrict A) (dev n) + ((μ.restrict C).restrict A) (dev n))
        atTop (𝓝 0) := by
    simpa using hS_small.add hC_small
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_sum_tendsto
    (fun _ ↦ zero_le _) ?_
  intro n
  exact h_union_bound n

/-- Helper for Corollary 6.15: a partial local limit can be extended exactly across the canonical
sigma-finite carrier attached to any finite-measure test set. -/
private lemma existsExactExtensionByFiniteCarrier
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq)
    (p : PartialLocalLimit μ fSeq)
    {A : Set Ω} (hA_fin : μ A < ∞) :
    ∃ q : PartialLocalLimit μ fSeq,
      p.carrier ⊆ q.carrier ∧
      Set.EqOn q.witness p.witness p.carrier ∧
      ∀ᵐ ω ∂ μ.restrict A, ω ∈ q.carrier := by
  classical
  let C := μ.sigmaFiniteSetWRT (μ.restrict A)
  have hC : MeasurableSet C := measurableSet_sigmaFiniteSetWRT
  letI : SigmaFinite (μ.restrict C) := inferInstance
  have h_cauchy_on_C :
      CauchyInMeasureOnFiniteMeasureSets (μ.restrict C) fSeq :=
        cauchyInMeasureOnFiniteMeasureSets_restrict μ h_cauchy hC
  obtain ⟨g, hg⟩ := existsLimitOnSigmaFiniteMeasure (μ.restrict C) h_cauchy_on_C
  have hp_overlap :
      TendstoInMeasureOnFiniteMeasureSets (μ.restrict (p.carrier ∩ C)) fSeq p.witness := by
    -- Proof comment: the old local limit restricts to the overlap carrier without changing its
    -- witness.
    have hp_overlap' :
        TendstoInMeasureOnFiniteMeasureSets ((μ.restrict p.carrier).restrict C) fSeq p.witness :=
      tendstoInMeasureOnFiniteMeasureSets_restrict (μ.restrict p.carrier) p.tendsto hC
    have hp_overlap_measure :
        ((μ.restrict p.carrier).restrict C) = μ.restrict (C ∩ p.carrier) := by
      simpa using
        (Measure.restrict_restrict' p.carrier_meas)
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
      (show TendstoInMeasureOnFiniteMeasureSets (μ.restrict (C ∩ p.carrier)) fSeq p.witness by
        exact hp_overlap_measure ▸ hp_overlap')
  have hg_overlap :
      TendstoInMeasureOnFiniteMeasureSets (μ.restrict (p.carrier ∩ C)) fSeq g := by
    -- Proof comment: the new sigma-finite witness restricts to the same overlap carrier.
    simpa [Measure.restrict_restrict p.carrier_meas, Set.inter_assoc, Set.inter_left_comm,
      Set.inter_comm] using
      tendstoInMeasureOnFiniteMeasureSets_restrict (μ.restrict C) hg p.carrier_meas
  haveI : SigmaFinite (μ.restrict (p.carrier ∩ C)) := by
    letI : SigmaFinite ((μ.restrict C).restrict p.carrier) := inferInstance
    simpa [Measure.restrict_restrict p.carrier_meas, Set.inter_assoc, Set.inter_left_comm,
      Set.inter_comm]
  have h_overlap_ae : p.witness =ᵐ[μ.restrict (p.carrier ∩ C)] g :=
    ae_eq_of_tendstoInMeasureOnFiniteMeasureSets
      (μ.restrict (p.carrier ∩ C)) hp_overlap hg_overlap
  let q : PartialLocalLimit μ fSeq :=
    { carrier := p.carrier ∪ C
      carrier_meas := p.carrier_meas.union hC
      witness := p.carrier.piecewise p.witness g
      tendsto :=
        tendstoInMeasureOnFiniteMeasureSets_union_piecewise
          μ p.carrier_meas hC p.tendsto hg h_overlap_ae }
  refine ⟨q, ?_, ?_, ?_⟩
  · intro x hx
    exact Or.inl hx
  · intro x hx
    simp [q, hx]
  · -- Proof comment: every finite-measure test set is almost everywhere contained in the new
    -- sigma-finite carrier, hence also in the enlarged carrier.
    filter_upwards [ae_mem_sigmaFiniteCarrier_of_selfRestrictFinite μ hA_fin] with x hx
    exact Or.inr hx

/-- Helper for Corollary 6.15: the exact finite-carrier extension step upgrades to the supported
shell by adjoining the canonical sigma-finite spanning pieces on the new carrier. -/
private lemma existsExactExtensionByFiniteCarrier_supported
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq)
    (p : SupportedPartialLocalLimit μ fSeq)
    {A : Set Ω} (hA_fin : μ A < ∞) :
    ∃ q : SupportedPartialLocalLimit μ fSeq,
      p.carrier ⊆ q.carrier ∧
      Set.EqOn q.witness p.witness p.carrier ∧
      ∀ᵐ ω ∂ μ.restrict A, ω ∈ q.carrier := by
  classical
  let C := μ.sigmaFiniteSetWRT (μ.restrict A)
  have hC : MeasurableSet C := measurableSet_sigmaFiniteSetWRT
  letI : SigmaFinite (μ.restrict C) := inferInstance
  have h_cauchy_on_C :
      CauchyInMeasureOnFiniteMeasureSets (μ.restrict C) fSeq :=
    cauchyInMeasureOnFiniteMeasureSets_restrict μ h_cauchy hC
  obtain ⟨g, hg⟩ := existsLimitOnSigmaFiniteMeasure (μ.restrict C) h_cauchy_on_C
  have hp_overlap :
      TendstoInMeasureOnFiniteMeasureSets (μ.restrict (p.carrier ∩ C)) fSeq p.witness := by
    -- Proof comment: the old supported witness restricts to the overlap carrier without changing
    -- its values.
    have hp_overlap' :
        TendstoInMeasureOnFiniteMeasureSets ((μ.restrict p.carrier).restrict C) fSeq p.witness :=
      tendstoInMeasureOnFiniteMeasureSets_restrict (μ.restrict p.carrier) p.tendsto hC
    have hp_overlap_measure :
        ((μ.restrict p.carrier).restrict C) = μ.restrict (C ∩ p.carrier) := by
      simpa using
        (Measure.restrict_restrict' p.carrier_meas)
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
      (show TendstoInMeasureOnFiniteMeasureSets (μ.restrict (C ∩ p.carrier)) fSeq p.witness by
        exact hp_overlap_measure ▸ hp_overlap')
  have hg_overlap :
      TendstoInMeasureOnFiniteMeasureSets (μ.restrict (p.carrier ∩ C)) fSeq g := by
    -- Proof comment: the sigma-finite witness on `C` restricts to the same overlap carrier.
    simpa [Measure.restrict_restrict p.carrier_meas, Set.inter_assoc, Set.inter_left_comm,
      Set.inter_comm] using
      tendstoInMeasureOnFiniteMeasureSets_restrict (μ.restrict C) hg p.carrier_meas
  haveI : SigmaFinite (μ.restrict (p.carrier ∩ C)) := by
    letI : SigmaFinite ((μ.restrict C).restrict p.carrier) := inferInstance
    simpa [Measure.restrict_restrict p.carrier_meas, Set.inter_assoc, Set.inter_left_comm,
      Set.inter_comm]
  have h_overlap_ae : p.witness =ᵐ[μ.restrict (p.carrier ∩ C)] g :=
    ae_eq_of_tendstoInMeasureOnFiniteMeasureSets
      (μ.restrict (p.carrier ∩ C)) hp_overlap hg_overlap
  let supportUnion : Set Ω :=
    ⋃ n, p.support n ∪ (C ∩ spanningSets (μ.restrict C) n)
  have h_old_support : (⋃ n, p.support n) ⊆ supportUnion := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨n, hxn⟩
    exact Set.mem_iUnion.2 ⟨n, Or.inl hxn⟩
  have h_new_support : C ⊆ supportUnion := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨spanningSetsIndex (μ.restrict C) x, ?_⟩
    exact Or.inr ⟨hx, mem_spanningSetsIndex (μ.restrict C) x⟩
  let q : SupportedPartialLocalLimit μ fSeq :=
    { carrier := p.carrier ∪ C
      carrier_meas := p.carrier_meas.union hC
      witness := p.carrier.piecewise p.witness g
      tendsto :=
        tendstoInMeasureOnFiniteMeasureSets_union_piecewise
          μ p.carrier_meas hC p.tendsto hg h_overlap_ae
      support := fun n ↦ p.support n ∪ (C ∩ spanningSets (μ.restrict C) n)
      support_subset := by
        intro n x hx
        rcases hx with hx | hx
        · exact Or.inl (p.support_subset n hx)
        · exact Or.inr hx.1
      support_meas := by
        intro n
        exact (p.support_meas n).union (hC.inter (measurableSet_spanningSets (μ.restrict C) n))
      support_finite := by
        intro n
        have h_new_piece_finite : μ (C ∩ spanningSets (μ.restrict C) n) < ∞ := by
          calc
            μ (C ∩ spanningSets (μ.restrict C) n)
                = (μ.restrict C) (spanningSets (μ.restrict C) n) := by
                    rw [Measure.restrict_apply' (μ := μ) (s := C)
                      (t := spanningSets (μ.restrict C) n) hC]
                    simp [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
            _ < ∞ := measure_spanningSets_lt_top (μ.restrict C) n
        calc
          μ (p.support n ∪ (C ∩ spanningSets (μ.restrict C) n))
              ≤ μ (p.support n) + μ (C ∩ spanningSets (μ.restrict C) n) :=
                measure_union_le _ _
          _ < ∞ := ENNReal.add_lt_top.2 ⟨p.support_finite n, h_new_piece_finite⟩
      ae_mem_iUnion_support := by
        intro B hB hB_fin hB_subset
        have hB_fin_old : μ (B ∩ p.carrier) < ∞ := by
          exact (measure_mono Set.inter_subset_left).trans_lt hB_fin
        have h_old :
            ∀ᵐ x ∂ μ.restrict (B ∩ p.carrier), x ∈ ⋃ n, p.support n :=
          p.ae_mem_iUnion_support (hB.inter p.carrier_meas) hB_fin_old (by
            intro x hx
            exact hx.2)
        have h_old_global : ∀ᵐ x ∂ μ, x ∈ B ∩ p.carrier → x ∈ supportUnion := by
          have h_old_global_raw : ∀ᵐ x ∂ μ, x ∈ B ∩ p.carrier → x ∈ ⋃ n, p.support n := by
            exact (ae_restrict_iff' (hB.inter p.carrier_meas)).1 h_old
          filter_upwards [h_old_global_raw] with x hx hxBp
          exact h_old_support (hx hxBp)
        have h_cover_global : ∀ᵐ x ∂ μ, x ∈ B → x ∈ supportUnion := by
          filter_upwards [h_old_global] with x hx_old hxB
          rcases hB_subset hxB with hxCarrier | hxC
          · exact hx_old ⟨hxB, hxCarrier⟩
          · exact h_new_support hxC
        -- Proof comment: on the old carrier slice, the existing support family already covers
        -- almost everywhere; on the new sigma-finite carrier, the canonical spanning sets cover
        -- pointwise, so the combined family covers every finite slice of the enlarged carrier.
        exact (ae_restrict_iff' hB).2 h_cover_global }
  refine ⟨q, ?_, ?_, ?_⟩
  · intro x hx
    exact Or.inl hx
  · intro x hx
    simp [q, hx]
  · -- Proof comment: the enlarged carrier still contains the finite test set almost everywhere
    -- because the new sigma-finite component was chosen from `μ.sigmaFiniteSetWRT`.
    filter_upwards [ae_mem_sigmaFiniteCarrier_of_selfRestrictFinite μ hA_fin] with x hx
    exact Or.inr hx

/-- Helper for Corollary 6.15: the repaired local-cover shell is stable under exact extension
across the canonical sigma-finite carrier of a finite test set. -/
private lemma existsAeExtensionByFiniteCarrier_locallyCovered
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq)
    (p : LocallyCoveredPartialLocalLimit μ fSeq)
    {A : Set Ω} (hA_fin : μ A < ∞) :
    ∃ q : LocallyCoveredPartialLocalLimit μ fSeq,
      p.carrier ⊆ q.carrier ∧
      Set.EqOn q.witness p.witness p.carrier ∧
      ∀ᵐ ω ∂ μ.restrict A, ω ∈ q.carrier := by
  classical
  let C := μ.sigmaFiniteSetWRT (μ.restrict A)
  have hC : MeasurableSet C := measurableSet_sigmaFiniteSetWRT
  letI : SigmaFinite (μ.restrict C) := inferInstance
  have h_cauchy_on_C :
      CauchyInMeasureOnFiniteMeasureSets (μ.restrict C) fSeq :=
    cauchyInMeasureOnFiniteMeasureSets_restrict μ h_cauchy hC
  obtain ⟨g, hg⟩ := existsLimitOnSigmaFiniteMeasure (μ.restrict C) h_cauchy_on_C
  have hp_overlap :
      TendstoInMeasureOnFiniteMeasureSets (μ.restrict (p.carrier ∩ C)) fSeq p.witness := by
    -- Proof comment: the old local-cover witness restricts to the overlap carrier without
    -- changing its values.
    have hp_overlap' :
        TendstoInMeasureOnFiniteMeasureSets ((μ.restrict p.carrier).restrict C) fSeq p.witness :=
      tendstoInMeasureOnFiniteMeasureSets_restrict (μ.restrict p.carrier) p.tendsto hC
    have hp_overlap_measure :
        ((μ.restrict p.carrier).restrict C) = μ.restrict (C ∩ p.carrier) := by
      simpa using
        (Measure.restrict_restrict' p.carrier_meas)
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
      (show TendstoInMeasureOnFiniteMeasureSets (μ.restrict (C ∩ p.carrier)) fSeq p.witness by
        exact hp_overlap_measure ▸ hp_overlap')
  have hg_overlap :
      TendstoInMeasureOnFiniteMeasureSets (μ.restrict (p.carrier ∩ C)) fSeq g := by
    -- Proof comment: the sigma-finite witness on `C` restricts to the same overlap carrier.
    simpa [Measure.restrict_restrict p.carrier_meas, Set.inter_assoc, Set.inter_left_comm,
      Set.inter_comm] using
      tendstoInMeasureOnFiniteMeasureSets_restrict (μ.restrict C) hg p.carrier_meas
  haveI : SigmaFinite (μ.restrict (p.carrier ∩ C)) := by
    letI : SigmaFinite ((μ.restrict C).restrict p.carrier) := inferInstance
    simpa [Measure.restrict_restrict p.carrier_meas, Set.inter_assoc, Set.inter_left_comm,
      Set.inter_comm]
  have h_overlap_ae : p.witness =ᵐ[μ.restrict (p.carrier ∩ C)] g :=
    ae_eq_of_tendstoInMeasureOnFiniteMeasureSets
      (μ.restrict (p.carrier ∩ C)) hp_overlap hg_overlap
  let extraCover : Set (Set Ω) := {s | ∃ n, s = C ∩ spanningSets (μ.restrict C) n}
  have h_old_cover :
      (⋃₀ p.cover) ⊆ ⋃₀ (p.cover ∪ extraCover) := by
    intro x hx
    rcases Set.mem_sUnion.1 hx with ⟨s, hs, hxs⟩
    exact Set.mem_sUnion.2 ⟨s, Or.inl hs, hxs⟩
  have h_new_cover : C ⊆ ⋃₀ (p.cover ∪ extraCover) := by
    intro x hx
    refine Set.mem_sUnion.2 ?_
    refine ⟨C ∩ spanningSets (μ.restrict C) (spanningSetsIndex (μ.restrict C) x), ?_, ?_⟩
    · exact Or.inr ⟨spanningSetsIndex (μ.restrict C) x, rfl⟩
    · exact ⟨hx, mem_spanningSetsIndex (μ.restrict C) x⟩
  let q : LocallyCoveredPartialLocalLimit μ fSeq :=
    { carrier := p.carrier ∪ C
      carrier_meas := p.carrier_meas.union hC
      witness := p.carrier.piecewise p.witness g
      tendsto :=
        tendstoInMeasureOnFiniteMeasureSets_union_piecewise
          μ p.carrier_meas hC p.tendsto hg h_overlap_ae
      cover := p.cover ∪ extraCover
      cover_subset := by
        intro s hs x hx
        rcases hs with hs | hs
        · exact Or.inl (p.cover_subset s hs hx)
        · rcases hs with ⟨n, rfl⟩
          exact Or.inr hx.1
      cover_meas := by
        intro s hs
        rcases hs with hs | hs
        · exact p.cover_meas s hs
        · rcases hs with ⟨n, rfl⟩
          exact hC.inter (measurableSet_spanningSets (μ.restrict C) n)
      cover_finite := by
        intro s hs
        rcases hs with hs | hs
        · exact p.cover_finite s hs
        · rcases hs with ⟨n, rfl⟩
          calc
            μ (C ∩ spanningSets (μ.restrict C) n)
                = (μ.restrict C) (spanningSets (μ.restrict C) n) := by
                    rw [Measure.restrict_apply' (μ := μ) (s := C)
                      (t := spanningSets (μ.restrict C) n) hC]
                    simp [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
            _ < ∞ := measure_spanningSets_lt_top (μ.restrict C) n
      ae_mem_sUnion_cover := by
        intro B hB hB_fin hB_subset
        have hB_fin_old : μ (B ∩ p.carrier) < ∞ := by
          exact (measure_mono Set.inter_subset_left).trans_lt hB_fin
        have h_old :
            ∀ᵐ x ∂ μ.restrict (B ∩ p.carrier), x ∈ ⋃₀ p.cover :=
          p.ae_mem_sUnion_cover (hB.inter p.carrier_meas) hB_fin_old (by
            intro x hx
            exact hx.2)
        have h_old_global : ∀ᵐ x ∂ μ, x ∈ B ∩ p.carrier → x ∈ ⋃₀ (p.cover ∪ extraCover) := by
          have h_old_global_raw : ∀ᵐ x ∂ μ, x ∈ B ∩ p.carrier → x ∈ ⋃₀ p.cover := by
            exact (ae_restrict_iff' (hB.inter p.carrier_meas)).1 h_old
          filter_upwards [h_old_global_raw] with x hx hxBp
          exact h_old_cover (hx hxBp)
        have h_cover_global : ∀ᵐ x ∂ μ, x ∈ B → x ∈ ⋃₀ (p.cover ∪ extraCover) := by
          filter_upwards [h_old_global] with x hx_old hxB
          rcases hB_subset hxB with hxCarrier | hxC
          · exact hx_old ⟨hxB, hxCarrier⟩
          · exact h_new_cover hxC
        -- Proof comment: on the old carrier slice, the previous cover family already gives the
        -- a.e. cover; on the new sigma-finite carrier, the canonical spanning sets cover
        -- pointwise, so the enlarged family still covers every finite slice almost everywhere.
        exact (ae_restrict_iff' hB).2 h_cover_global }
  refine ⟨q, ?_, ?_, ?_⟩
  · intro x hx
    exact Or.inl hx
  · intro x hx
    simp [q, hx]
  · -- Proof comment: the new sigma-finite carrier still captures the finite test set almost
    -- everywhere, so the enlarged carrier does as well.
    filter_upwards [ae_mem_sigmaFiniteCarrier_of_selfRestrictFinite μ hA_fin] with x hx
    exact Or.inr hx

/-- Helper for Corollary 6.15: on any finite slice of one chain member, that slice is already
covered almost everywhere by the global cover family obtained from all members of the chain. -/
private lemma ae_mem_globalCover_of_member_onFiniteSlice
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E}
    {c : Set (LocallyCoveredPartialLocalLimit μ fSeq)}
    {p : LocallyCoveredPartialLocalLimit μ fSeq}
    (hp : p ∈ c)
    {A : Set Ω} (hA : MeasurableSet A) (hA_fin : μ A < ∞) :
    ∀ᵐ x ∂ μ.restrict (A ∩ p.carrier),
      x ∈ ⋃₀ {s : Set Ω | ∃ q ∈ c, s ∈ q.cover} := by
  have h_local :
      ∀ᵐ x ∂ μ.restrict (A ∩ p.carrier), x ∈ ⋃₀ p.cover :=
    p.ae_mem_sUnion_cover (hA.inter p.carrier_meas)
      ((measure_mono Set.inter_subset_left).trans_lt hA_fin) (by
        intro x hx
        exact hx.2)
  -- Proof comment: a finite slice of one member is already covered a.e. by that member's own
  -- cover family, so it is certainly covered a.e. by the global cover family of the whole chain.
  filter_upwards [h_local] with x hx
  rcases Set.mem_sUnion.1 hx with ⟨s, hs, hxs⟩
  exact Set.mem_sUnion.2 ⟨s, ⟨p, hp, hs⟩, hxs⟩

/-- Helper for Corollary 6.15: in a chain of locally covered partial local limits, cover pieces
from comparable members carry pointwise-equal witnesses on overlaps. -/
private lemma locallyCoveredWitness_aeEq_onCoverInter
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E}
    {c : Set (LocallyCoveredPartialLocalLimit μ fSeq)}
    (hc : IsChain (fun p q : LocallyCoveredPartialLocalLimit μ fSeq ↦ p ≤ q) c)
    {p q : LocallyCoveredPartialLocalLimit μ fSeq}
    (hp : p ∈ c) (hq : q ∈ c)
    {s t : Set Ω}
    (hs : s ∈ p.cover) (ht : t ∈ q.cover) :
    p.witness =ᵐ[μ.restrict (s ∩ t)] q.witness := by
  rcases hc.total hp hq with hpq | hqp
  · -- Proof comment: if `p ≤ q`, the later witness agrees with the old one on all of
    -- `p.carrier`, hence certainly on every old cover-piece overlap.
    filter_upwards [ae_restrict_mem ((p.cover_meas s hs).inter (q.cover_meas t ht))] with x hx
    exact (hpq.2 <| p.cover_subset s hs hx.1).symm
  · -- Proof comment: the opposite chain comparison gives the same overlap equality after
    -- restricting from `q.carrier`.
    filter_upwards [ae_restrict_mem ((p.cover_meas s hs).inter (q.cover_meas t ht))] with x hx
    exact hqp.2 <| q.cover_subset t ht hx.2

/-- Helper for Corollary 6.15: in a chain of supported partial local limits, any two support
pieces carry almost-everywhere equal witnesses on their overlap. -/
private lemma supportedWitness_aeEq_onSupportInter
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E}
    {c : Set (SupportedPartialLocalLimit μ fSeq)}
    (hc : IsChain (fun p q : SupportedPartialLocalLimit μ fSeq ↦ p ≤ q) c)
    {p q : SupportedPartialLocalLimit μ fSeq}
    (hp : p ∈ c) (hq : q ∈ c)
    (i j : ℕ) :
    p.witness =ᵐ[μ.restrict (p.support i ∩ q.support j)] q.witness := by
  have hpInter_subset : p.support i ∩ q.support j ⊆ p.carrier := by
    intro x hx
    exact p.support_subset i hx.1
  have hqInter_subset : p.support i ∩ q.support j ⊆ q.carrier := by
    intro x hx
    exact q.support_subset j hx.2
  rcases hc.total hp hq with hpq | hqp
  · -- Proof comment: if `p ≤ q`, the chain order already records that the two witnesses agree
    -- almost everywhere on the old carrier of `p`, so we only restrict that equality to the
    -- concrete support-piece overlap.
    exact ae_restrict_of_ae_restrict_of_subset hpInter_subset hpq.2
  · -- Proof comment: the opposite chain comparison gives the same overlap compatibility after
    -- restricting from `q.carrier` and then reversing the equality.
    refine (ae_restrict_of_ae_restrict_of_subset hqInter_subset hqp.2).mono ?_
    intro x hx
    exact hx.symm

/-- Helper for Corollary 6.15: a nonempty exact-extension chain of partial local limits should
admit an upper bound on the measurable hull of the raw carrier union. -/
private lemma chainWitness_tendstoOnFiniteSet_of_countableCover
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E}
    {c : Set (PartialLocalLimit μ fSeq)}
    (hc : IsChain (fun p q : PartialLocalLimit μ fSeq ↦ p ≤ q) c)
    {y : PartialLocalLimit μ fSeq} (hy : y ∈ c)
    {A : Set Ω} (hA : MeasurableSet A) (hA_fin : μ A < ∞)
    {s : ℕ → PartialLocalLimit μ fSeq}
    (hs_mem : ∀ n, s n ∈ c)
    (hs_mono : Monotone fun n => (s n).carrier)
    (hcover : ∀ᵐ x ∂ μ.restrict A, x ∈ ⋃ n, (s n).carrier) :
    TendstoInMeasure (μ.restrict A) fSeq atTop (chainWitness c y.witness) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  have hδ_half_pos : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  have h_residual_tendsto :
      Tendsto (fun n ↦ (μ.restrict A) ((s n).carrierᶜ)) atTop (𝓝 0) := by
    have hcover_zero : (μ.restrict A) ((⋃ n, (s n).carrier)ᶜ) = 0 := by
      have hcover_zero_raw : (μ.restrict A) {a | a ∉ ⋃ n, (s n).carrier} = 0 := ae_iff.1 hcover
      have hcover_eqset : {a | a ∉ ⋃ n, (s n).carrier} = (⋃ n, (s n).carrier)ᶜ := by
        ext x
        simp [Set.mem_compl_iff]
      exact hcover_eqset ▸ hcover_zero_raw
    have h_inter_zero : (μ.restrict A) (⋂ n, (s n).carrierᶜ) = 0 := by
      have h_inter_eq : (⋂ n, (s n).carrierᶜ) = (⋃ n, (s n).carrier)ᶜ := by
        ext x
        simp [Set.mem_iInter, Set.mem_iUnion, Set.mem_compl_iff]
      rw [h_inter_eq]
      exact hcover_zero
    have h_residual_meas : ∀ n, MeasurableSet ((s n).carrierᶜ) := by
      intro n
      exact (s n).carrier_meas.compl
    have h_residual_anti : Antitone fun n => (s n).carrierᶜ := by
      intro i j hij
      exact Set.compl_subset_compl.2 (hs_mono hij)
    have h_residual_fin : ∃ n, (μ.restrict A) ((s n).carrierᶜ) ≠ ∞ := by
      refine ⟨0, ne_top_of_le_ne_top hA_fin.ne ?_⟩
      calc
        (μ.restrict A) ((s 0).carrierᶜ) ≤ (μ.restrict A) Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = μ A := by simp
    simpa [h_inter_zero] using
      tendsto_measure_iInter_atTop (μ := μ.restrict A)
        (fun n ↦ (h_residual_meas n).nullMeasurableSet) h_residual_anti h_residual_fin
  obtain ⟨N, hN⟩ :=
    (ENNReal.tendsto_atTop_zero.1 h_residual_tendsto) (δ / 2) hδ_half_pos
  have h_residual_small : (μ.restrict A) ((s N).carrierᶜ) ≤ δ / 2 :=
    hN N le_rfl
  have h_member_tendsto :
      TendstoInMeasure ((μ.restrict A).restrict (s N).carrier) fSeq atTop
        (chainWitness c y.witness) := by
    have hA_fin_member : (μ.restrict (s N).carrier) A < ∞ := by
      calc
        (μ.restrict (s N).carrier) A = μ (A ∩ (s N).carrier) := by
          simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
            (Measure.restrict_apply' (s N).carrier_meas)
        _ ≤ μ A := measure_mono Set.inter_subset_left
        _ < ∞ := hA_fin
    have h_member_tendsto' :
        TendstoInMeasure (((μ.restrict (s N).carrier).restrict A)) fSeq atTop
          (s N).witness :=
      (s N).tendsto A hA_fin_member
    have h_chainWitness_eq :
        chainWitness c y.witness =ᵐ[((μ.restrict A).restrict (s N).carrier)] (s N).witness := by
      filter_upwards [ae_restrict_mem (s N).carrier_meas] with x hx
      exact chainWitness_eqOn_member hc (hs_mem N) hx
    -- Proof comment: on the chosen chain member, the canonical witness is literally the stored
    -- witness, so the local convergence transports across the exact-extension equality.
    exact TendstoInMeasure.congr_right h_chainWitness_eq.symm <| by
      simpa [Measure.restrict_restrict hA, Measure.restrict_restrict (s N).carrier_meas,
        Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using h_member_tendsto'
  have h_local_tendsto :=
    (tendstoInMeasure_iff_dist.1 h_member_tendsto) ε hε
  obtain ⟨K, hK⟩ :=
    (ENNReal.tendsto_atTop_zero.1 h_local_tendsto) (δ / 2) hδ_half_pos
  refine ⟨K, fun n hn ↦ ?_⟩
  let dev : Set Ω := {x | ε ≤ dist (fSeq n x) (chainWitness c y.witness x)}
  have h_split :
      (μ.restrict A) dev ≤ ((μ.restrict A).restrict (s N).carrier) dev +
        (μ.restrict A) ((s N).carrierᶜ) := by
    have h_subset : dev ⊆ (dev ∩ (s N).carrier) ∪ (s N).carrierᶜ := by
      intro x hx
      by_cases hxN : x ∈ (s N).carrier
      · exact Or.inl ⟨hx, hxN⟩
      · exact Or.inr hxN
    calc
      (μ.restrict A) dev ≤ (μ.restrict A) ((dev ∩ (s N).carrier) ∪ (s N).carrierᶜ) :=
        measure_mono h_subset
      _ ≤ (μ.restrict A) (dev ∩ (s N).carrier) + (μ.restrict A) ((s N).carrierᶜ) :=
        measure_union_le _ _
      _ = ((μ.restrict A).restrict (s N).carrier) dev + (μ.restrict A) ((s N).carrierᶜ) := by
        rw [Measure.restrict_apply' (s N).carrier_meas]
  have h_local_small :
      ((μ.restrict A).restrict (s N).carrier) dev ≤ δ / 2 :=
    hK n hn
  -- Proof comment: split the deviation set into the part already controlled on one chain member
  -- and the residual complement, whose `μ.restrict A`-measure is small by the countable cover.
  calc
    (μ.restrict A) dev ≤ ((μ.restrict A).restrict (s N).carrier) dev +
        (μ.restrict A) ((s N).carrierᶜ) := h_split
    _ ≤ δ / 2 + δ / 2 := add_le_add h_local_small h_residual_small
    _ = δ := by rw [ENNReal.add_halves]

/-- Helper for Corollary 6.15: once every finite measurable slice of `toMeasurable μ
(chainCarrier c)` admits a countable increasing subchain cover, the canonical chain witness
extends to an exact upper bound on the measurable hull of the raw chain carrier. -/
private lemma existsChainUpperBoundLocalOfFiniteCover
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    {c : Set (PartialLocalLimit μ fSeq)}
    (hc : IsChain (fun p q : PartialLocalLimit μ fSeq ↦ p ≤ q) c)
    {y : PartialLocalLimit μ fSeq} (hy : y ∈ c)
    (hcover :
      ∀ ⦃A : Set Ω⦄, MeasurableSet A → μ A < ∞ →
        A ⊆ toMeasurable μ (chainCarrier c) →
        ∃ s : ℕ → PartialLocalLimit μ fSeq,
          (∀ n, s n ∈ c) ∧
          Monotone (fun n => (s n).carrier) ∧
          ∀ᵐ x ∂ μ.restrict A, x ∈ ⋃ n, (s n).carrier) :
    ∃ ub : PartialLocalLimit μ fSeq, ∀ z ∈ c, z ≤ ub := by
  classical
  -- Route correction: the old unconditional chain-upper-bound statement is false because null
  -- carriers can accumulate positive-measure support. The correct reusable statement isolates the
  -- genuinely missing premise: a countable increasing carrier cover on each finite measurable
  -- slice of the measurable hull.
  let carrier := toMeasurable μ (chainCarrier c)
  let ub : PartialLocalLimit μ fSeq :=
    { carrier := carrier
      carrier_meas := measurableSet_toMeasurable _ _
      witness := chainWitness c y.witness
      tendsto := by
        rw [tendstoInMeasureOnFiniteMeasureSets_iff_forall_measurable]
        intro A hA hA_fin
        let B := A ∩ carrier
        have hB : MeasurableSet B := hA.inter (measurableSet_toMeasurable _ _)
        have hB_fin : μ B < ∞ := by
          calc
            μ B = ((μ.restrict carrier) A) := by
              simp [B, carrier, Measure.restrict_apply, hA, measurableSet_toMeasurable,
                Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
            _ < ∞ := hA_fin
        obtain ⟨s, hs_mem, hs_mono, hs_cover⟩ :=
          hcover hB hB_fin (by
            intro x hx
            exact hx.2)
        have hB_tendsto :
            TendstoInMeasure (μ.restrict B) fSeq atTop (chainWitness c y.witness) :=
          chainWitness_tendstoOnFiniteSet_of_countableCover μ hc hy hB hB_fin hs_mem hs_mono
            hs_cover
        have hrestrict :
            ((μ.restrict carrier).restrict A) = μ.restrict B := by
          simpa [B, carrier, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
            (Measure.restrict_restrict hA :
              ((μ.restrict carrier).restrict A) = μ.restrict (A ∩ carrier))
        -- Proof comment: after rewriting the restricted measure to the finite slice `B`, the
        -- countable-cover hypothesis lets the previously proved chain witness lemma close the
        -- local convergence goal.
        simpa [hrestrict] using hB_tendsto }
  refine ⟨ub, ?_⟩
  intro z hz
  refine ⟨?_, ?_⟩
  · intro x hx
    exact subset_toMeasurable μ _ (Set.mem_iUnion₂.2 ⟨z, hz, hx⟩)
  · -- Proof comment: on the old carrier of `z`, the canonical chain witness literally reads the
    -- value of `z.witness`, so exact-extension compatibility is automatic.
    exact chainWitness_eqOn_member hc hz

/-- Helper for Corollary 6.15: the Zorn argument reduces the whole globalization step to showing
that every nonempty exact-extension chain admits an upper bound once the finite-slice countable
cover premise has been verified. -/
private lemma existsChainUpperBoundLocal
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    {c : Set (PartialLocalLimit μ fSeq)}
    (hc : IsChain (fun p q : PartialLocalLimit μ fSeq ↦ p ≤ q) c)
    {y : PartialLocalLimit μ fSeq} (hy : y ∈ c)
    (hcover :
      ∀ ⦃A : Set Ω⦄, MeasurableSet A → μ A < ∞ →
        A ⊆ toMeasurable μ (chainCarrier c) →
        ∃ s : ℕ → PartialLocalLimit μ fSeq,
          (∀ n, s n ∈ c) ∧
          Monotone (fun n => (s n).carrier) ∧
          ∀ᵐ x ∂ μ.restrict A, x ∈ ⋃ n, (s n).carrier) :
    ∃ ub : PartialLocalLimit μ fSeq, ∀ z ∈ c, z ≤ ub := by
  -- Proof comment: this is just the previously isolated finite-slice upper-bound lemma once the
  -- chain-specific countable cover hypothesis has been supplied by the caller.
  exact existsChainUpperBoundLocalOfFiniteCover μ hc hy hcover

/-- Helper for Corollary 6.15: the remaining upper-bound obligation is now isolated entirely in
the canonical `PartialLocalLimit` order, provided the caller can supply the finite-slice
countable-cover premise that the raw carrier shell does not generate by itself. -/
private lemma existsChainUpperBoundPartialLocalLimit
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    {c : Set (PartialLocalLimit μ fSeq)}
    (hc : IsChain (fun p q : PartialLocalLimit μ fSeq ↦ p ≤ q) c)
    {y : PartialLocalLimit μ fSeq} (hy : y ∈ c)
    (hcover :
      ∀ ⦃A : Set Ω⦄, MeasurableSet A → μ A < ∞ →
        A ⊆ toMeasurable μ (chainCarrier c) →
        ∃ s : ℕ → PartialLocalLimit μ fSeq,
          (∀ n, s n ∈ c) ∧
          Monotone (fun n => (s n).carrier) ∧
          ∀ᵐ x ∂ μ.restrict A, x ∈ ⋃ n, (s n).carrier) :
    ∃ ub : PartialLocalLimit μ fSeq, ∀ z ∈ c, z ≤ ub := by
  -- Proof comment: the false unconditional upper-bound statement has been replaced by the
  -- correct conditional form, so this lemma is now just the previously isolated local upper-bound
  -- constructor.
  exact existsChainUpperBoundLocal μ hc hy hcover

/-- Helper for Corollary 6.15: on a finite slice, the full owner-piece family of a locally
covered chain admits one countable measurable union that dominates every individual cover piece
almost everywhere. This is the strongest countable compression supplied by
`Measure.exists_ae_subset_biUnion_countable`; it does not yet say that the finite slice itself is
covered almost everywhere by countably many owner pieces. -/
private lemma existsCountableGlobalCoverPiecesOnFiniteSlice
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E}
    {c : Set (LocallyCoveredPartialLocalLimit μ fSeq)}
    {A : Set Ω} (hA_fin : μ A < ∞) :
    ∃ D : Set (Set Ω),
      D ⊆ {s : Set Ω | ∃ p ∈ c, s ∈ p.cover} ∧
      D.Countable ∧
      ∀ p ∈ c, ∀ s ∈ p.cover, s ≤ᵐ[μ.restrict A] ⋃₀ D := by
  let C : Set (Set Ω) := {s : Set Ω | ∃ p ∈ c, s ∈ p.cover}
  have hC_meas : ∀ s ∈ C, MeasurableSet s := by
    intro s hs
    rcases hs with ⟨p, hp, hs⟩
    exact p.cover_meas s hs
  haveI : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 hA_fin.ne
  obtain ⟨D, hDC, hD_count, hD_cover⟩ :=
    Measure.exists_ae_subset_biUnion_countable (μ := μ.restrict A) hC_meas
  refine ⟨D, hDC, hD_count, ?_⟩
  intro p hp s hs
  -- Proof comment: the measurable-union compression theorem acts on the global family
  -- `{s | ∃ p ∈ c, s ∈ p.cover}` and returns one countable subfamily whose union dominates each
  -- original cover piece almost everywhere on the finite slice.
  exact hD_cover s ⟨p, hp, hs⟩

/-- Helper for Corollary 6.15: once a nonempty countable family of actual cover pieces is known,
it can be enumerated exactly together with one chosen owner from the chain for each enumerated
piece. -/
private lemma enumerateNonemptyCountableCoverPiecesWithOwners
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E}
    {c : Set (LocallyCoveredPartialLocalLimit μ fSeq)}
    {D : Set (Set Ω)}
    (hD_nonempty : D.Nonempty)
    (hD_subset : D ⊆ {s : Set Ω | ∃ p ∈ c, s ∈ p.cover})
    (hD_count : D.Countable) :
    ∃ u : ℕ → Set Ω, ∃ o : ℕ → LocallyCoveredPartialLocalLimit μ fSeq,
      Set.range u = D ∧
      (∀ n, o n ∈ c) ∧
      (∀ n, u n ∈ (o n).cover) := by
  classical
  obtain ⟨u, hu_eq⟩ : ∃ u : ℕ → Set Ω, D = Set.range u :=
    hD_count.exists_eq_range hD_nonempty
  have hu_range : Set.range u = D := hu_eq.symm
  have howner : ∀ n, ∃ p ∈ c, u n ∈ p.cover := by
    intro n
    have hun : u n ∈ D := by
      rw [← hu_range]
      exact Set.mem_range_self n
    exact hD_subset hun
  -- Proof comment: after enumerating the countable set exactly, owner selection is just one
  -- classical choice per enumerated piece.
  choose o ho_mem hu_mem using howner
  exact ⟨u, o, hu_range, ho_mem, hu_mem⟩

/-- Helper for Corollary 6.15: the `toPartial` image of a locally-covered chain is still a chain
for the exact-extension order, because the order forgets only the auxiliary cover data. -/
private lemma toPartialImage_isChain
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E}
    {c : Set (LocallyCoveredPartialLocalLimit μ fSeq)}
    (hc : IsChain (fun p q : LocallyCoveredPartialLocalLimit μ fSeq ↦ p ≤ q) c) :
    IsChain
      (fun p q : PartialLocalLimit μ fSeq ↦ p ≤ q)
      ((fun p : LocallyCoveredPartialLocalLimit μ fSeq ↦
          { carrier := p.carrier
            carrier_meas := p.carrier_meas
            witness := p.witness
            tendsto := p.tendsto }) '' c) := by
  intro p hp q hq hpq
  rcases hp with ⟨p', hp', rfl⟩
  rcases hq with ⟨q', hq', rfl⟩
  by_cases hbase :
      (show PartialLocalLimit μ fSeq from
        { carrier := p'.carrier
          carrier_meas := p'.carrier_meas
          witness := p'.witness
          tendsto := p'.tendsto }) =
      { carrier := q'.carrier
        carrier_meas := q'.carrier_meas
        witness := q'.witness
        tendsto := q'.tendsto }
  · exact Or.inl <| le_of_eq hbase
  · have hp'q' : p' ≠ q' := by
      intro hpq'
      apply hbase
      cases hpq'
      rfl
    rcases hc hp' hq' hp'q' with hp'q' | hq'p'
    · exact Or.inl <| by
        simpa [PartialLocalLimit.ExactExtension,
          LocallyCoveredPartialLocalLimit.ExactExtension] using hp'q'
    · exact Or.inr <| by
        simpa [PartialLocalLimit.ExactExtension,
          LocallyCoveredPartialLocalLimit.ExactExtension] using hq'p'

/-- Helper for Corollary 6.15: passing to the `toPartial` image preserves the raw chain carrier
exactly, so the finite-slice inclusion hypothesis can be transported without changing sets. -/
private lemma toPartialImage_chainCarrier_eq
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E}
    {c : Set (LocallyCoveredPartialLocalLimit μ fSeq)} :
    chainCarrier
        ((fun p : LocallyCoveredPartialLocalLimit μ fSeq ↦
            { carrier := p.carrier
              carrier_meas := p.carrier_meas
              witness := p.witness
              tendsto := p.tendsto }) '' c) =
      ⋃ p ∈ c, p.carrier := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion₂.1 hx with ⟨p, hp, hx⟩
    rcases hp with ⟨q, hq, rfl⟩
    exact Set.mem_iUnion₂.2 ⟨q, hq, hx⟩
  · intro hx
    rcases Set.mem_iUnion₂.1 hx with ⟨p, hp, hx⟩
    exact Set.mem_iUnion₂.2 ⟨
      { carrier := p.carrier
        carrier_meas := p.carrier_meas
        witness := p.witness
        tendsto := p.tendsto },
      ⟨p, hp, rfl⟩,
      hx⟩

/-- Helper for Corollary 6.15: `sequenceGeneratedSpace fSeq` is the smallest measurable structure
making every term of the sequence `fSeq` measurable. -/
private abbrev sequenceGeneratedSpace
    (fSeq : ℕ → Ω → E) : MeasurableSpace Ω :=
  ⨆ n, MeasurableSpace.comap (fSeq n) ‹MeasurableSpace E›

omit [MetricSpace E] [BorelSpace E] in
/-- Helper for Corollary 6.15: the only viable generated-space control measure is the trim of the
ambient outer measure along `sequenceGeneratedSpace fSeq`. -/
private noncomputable abbrev generatedSpaceTrimmedOuterMeasure
    (μ : Measure Ω) {fSeq : ℕ → Ω → E} : OuterMeasure Ω :=
  @OuterMeasure.trim Ω (sequenceGeneratedSpace fSeq) μ.toOuterMeasure

omit [MetricSpace E] [BorelSpace E] in
/-- Helper for Corollary 6.15: if the sequence-generated sigma-algebra is already contained in the
Carathéodory sigma-algebra of the trimmed ambient outer measure, then that trim upgrades to an
actual measure on `sequenceGeneratedSpace fSeq`. -/
private noncomputable def generatedSpaceControlMeasure
    (μ : Measure Ω) {fSeq : ℕ → Ω → E}
    (hcar : sequenceGeneratedSpace fSeq ≤
      (generatedSpaceTrimmedOuterMeasure (μ := μ) (fSeq := fSeq)).caratheodory) :
    @Measure Ω (sequenceGeneratedSpace fSeq) :=
  @OuterMeasure.toMeasure Ω (sequenceGeneratedSpace fSeq)
    (generatedSpaceTrimmedOuterMeasure (μ := μ) (fSeq := fSeq)) hcar

omit [MetricSpace E] [BorelSpace E] in
/-- Helper for Corollary 6.15: under the missing Carathéodory premise, the generated-space control
measure agrees with the ambient measure on every generated-space measurable set. -/
private lemma generatedSpaceControlMeasure_apply
    (μ : Measure Ω) {fSeq : ℕ → Ω → E}
    (hcar : sequenceGeneratedSpace fSeq ≤
      (generatedSpaceTrimmedOuterMeasure (μ := μ) (fSeq := fSeq)).caratheodory)
    {s : Set Ω} (hs : @MeasurableSet Ω (sequenceGeneratedSpace fSeq) s) :
    generatedSpaceControlMeasure (μ := μ) (fSeq := fSeq) hcar s = μ s := by
  have hto :
      @OuterMeasure.toMeasure Ω (sequenceGeneratedSpace fSeq)
          (generatedSpaceTrimmedOuterMeasure (μ := μ) (fSeq := fSeq)) hcar s =
        generatedSpaceTrimmedOuterMeasure (μ := μ) (fSeq := fSeq) s :=
    toMeasure_apply (ms := sequenceGeneratedSpace fSeq)
      (generatedSpaceTrimmedOuterMeasure (μ := μ) (fSeq := fSeq)) hcar hs
  -- Proof comment: once the Carathéodory side condition is available, the only remaining work is
  -- to evaluate the trimmed outer measure on a generated-space measurable set.
  rw [generatedSpaceControlMeasure]
  rw [hto]
  rw [generatedSpaceTrimmedOuterMeasure]
  rw [@OuterMeasure.trim_eq Ω (sequenceGeneratedSpace fSeq) μ.toOuterMeasure s hs]
  exact Measure.toOuterMeasure_apply μ s

omit [MetricSpace E] [BorelSpace E] in
/-- Helper for Corollary 6.15: the same control-measure identification applies on intersections of
generated-space measurable sets, which is the form needed for deviation families later. -/
private lemma generatedSpaceControlMeasure_apply_inter
    (μ : Measure Ω) {fSeq : ℕ → Ω → E}
    (hcar : sequenceGeneratedSpace fSeq ≤
      (generatedSpaceTrimmedOuterMeasure (μ := μ) (fSeq := fSeq)).caratheodory)
    {A B : Set Ω}
    (hA : @MeasurableSet Ω (sequenceGeneratedSpace fSeq) A)
    (hB : @MeasurableSet Ω (sequenceGeneratedSpace fSeq) B) :
    generatedSpaceControlMeasure (μ := μ) (fSeq := fSeq) hcar (A ∩ B) =
      μ (A ∩ B) := by
  -- Proof comment: the intersection case is just the measurable-set evaluation lemma applied to
  -- one more generated-space measurable set.
  exact generatedSpaceControlMeasure_apply (μ := μ) (fSeq := fSeq) hcar (hA.inter hB)

/-- Helper for Corollary 6.15: each term `fSeq n` is measurable for the generated measurable
structure `sequenceGeneratedSpace fSeq`. -/
private lemma measurable_sequenceGeneratedSpace
    {fSeq : ℕ → Ω → E} (n : ℕ) :
    Measurable[sequenceGeneratedSpace fSeq] (fSeq n) := by
  -- Proof comment: the `n`th summand in the supremum defining `sequenceGeneratedSpace fSeq`
  -- already contains exactly the pullback sigma-algebra needed for `fSeq n`.
  refine Measurable.of_comap_le ?_
  exact le_iSup_of_le n le_rfl

/-- Helper for Corollary 6.15: if every `fSeq n` is already measurable for the ambient sigma
algebra, then the sequence-generated sigma-algebra sits inside the ambient measurable space. -/
private lemma sequenceGeneratedSpace_le_ambient_of_measurable
    {fSeq : ℕ → Ω → E} (h_meas : ∀ n, Measurable (fSeq n)) :
    sequenceGeneratedSpace fSeq ≤ ‹MeasurableSpace Ω› := by
  -- Proof comment: each summand in the supremum is contained in the ambient sigma-algebra as
  -- soon as the corresponding sequence term is ambient measurable.
  refine iSup_le fun n ↦ ?_
  exact (h_meas n).comap_le

omit [MetricSpace E] [BorelSpace E] in
/-- Helper for Corollary 6.15: once `sequenceGeneratedSpace fSeq` is contained in the ambient
sigma-algebra, the trimmed outer measure upgrades to a genuine measure on that smaller space. -/
private lemma sequenceGeneratedSpace_le_generatedSpaceTrimmedCaratheodory
    (μ : Measure Ω) {fSeq : ℕ → Ω → E}
    (hm : sequenceGeneratedSpace fSeq ≤ ‹MeasurableSpace Ω›) :
    sequenceGeneratedSpace fSeq ≤
      (generatedSpaceTrimmedOuterMeasure (μ := μ) (fSeq := fSeq)).caratheodory := by
  let _ : MeasurableSpace Ω := sequenceGeneratedSpace fSeq
  let ν : Measure Ω := μ.trim hm
  have hν : sequenceGeneratedSpace fSeq ≤ ν.toOuterMeasure.caratheodory :=
    le_toOuterMeasure_caratheodory ν
  -- Proof comment: `μ.trim hm` is already a measure on the generated sigma-algebra, and its
  -- outer measure is exactly the trimmed ambient outer measure.
  simpa [ν, generatedSpaceTrimmedOuterMeasure,
    toOuterMeasure_trim_eq_trim_toOuterMeasure (μ := μ) hm] using hν

/-- Helper for Corollary 6.15: when `E` has a countably generated Borel structure, the measurable
structure generated by the sequence `fSeq` is itself generated by one countable family of sets. -/
private lemma sequenceGeneratedSpace_isCountablyGenerated
    [MeasurableSpace.CountablyGenerated E] (fSeq : ℕ → Ω → E) :
    ∃ b : Set (Set Ω), b.Countable ∧
      sequenceGeneratedSpace fSeq = MeasurableSpace.generateFrom b := by
  classical
  obtain ⟨b, hb_count, hb_eq⟩ :=
    (MeasurableSpace.CountablyGenerated.isCountablyGenerated (α := E))
  refine ⟨⋃ n, Set.preimage (fSeq n) '' b, ?_, ?_⟩
  · exact Set.countable_iUnion fun n ↦ hb_count.image (Set.preimage (fSeq n))
  · -- Proof comment: each pullback sigma-algebra is generated by preimages of one fixed
    -- countable generating family for `E`, and countable `iSup` becomes one countable
    -- `generateFrom`.
    calc
      sequenceGeneratedSpace fSeq
          = ⨆ n, MeasurableSpace.comap (fSeq n) (MeasurableSpace.generateFrom b) := by
              simp [sequenceGeneratedSpace, hb_eq]
      _ = ⨆ n, MeasurableSpace.generateFrom (Set.preimage (fSeq n) '' b) := by
            simp [MeasurableSpace.comap_generateFrom]
      _ = MeasurableSpace.generateFrom (⋃ n, Set.preimage (fSeq n) '' b) := by
            exact MeasurableSpace.iSup_generateFrom fun n ↦ Set.preimage (fSeq n) '' b

/-- Helper for Corollary 6.15: the sequence-generated sigma-algebra admits one fixed countable
generating algebra, independent of the finite branch measure chosen later. -/
private lemma existsCountableGeneratingAlgebra_sequenceGeneratedSpace
    [TopologicalSpace.SeparableSpace E] {fSeq : ℕ → Ω → E} :
    ∃ 𝒜 : Set (Set Ω), 𝒜.Countable ∧ IsSetAlgebra 𝒜 ∧
      sequenceGeneratedSpace fSeq = MeasurableSpace.generateFrom 𝒜 := by
  rcases sequenceGeneratedSpace_isCountablyGenerated (fSeq := fSeq) with ⟨b, hb_count, hb_eq⟩
  refine ⟨generateSetAlgebra b, countable_generateSetAlgebra hb_count,
    isSetAlgebra_generateSetAlgebra, ?_⟩
  -- Proof comment: passing from a countable generating family to its generated set algebra keeps
  -- countability and does not change the resulting sigma-algebra.
  simpa [hb_eq] using
    (MeasurableSpace.generateFrom_generateSetAlgebra_eq (𝒜 := b)).symm

/-- Helper for Corollary 6.15: every finite measure on a countably generated measurable space
admits one fixed countable generating algebra that is already measure-dense. -/
private lemma existsDenseGeneratingSetAlgebra_countablyGenerated
    {m : MeasurableSpace Ω} [MeasurableSpace.CountablyGenerated Ω]
    (μ : @Measure Ω m) [IsFiniteMeasure μ] :
    ∃ 𝒜 : Set (Set Ω), 𝒜.Countable ∧ IsSetAlgebra 𝒜 ∧
      m = MeasurableSpace.generateFrom 𝒜 ∧ μ.MeasureDense 𝒜 := by
  let 𝒜 : Set (Set Ω) := generateSetAlgebra (MeasurableSpace.countableGeneratingSet Ω)
  have hgen : m = MeasurableSpace.generateFrom 𝒜 := by
    simpa [𝒜] using (MeasurableSpace.generateFrom_countableGeneratingSet (α := Ω)).symm
  refine ⟨𝒜,
    countable_generateSetAlgebra (MeasurableSpace.countable_countableGeneratingSet (α := Ω)),
    isSetAlgebra_generateSetAlgebra, hgen, ?_⟩
  -- Proof comment: on a finite measure, any generating set algebra is automatically
  -- measure-dense, so the generated space comes with one fixed countable approximation family.
  exact Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
    (μ := μ) isSetAlgebra_generateSetAlgebra hgen

/-- Helper for Corollary 6.15: once a finite measure is known to live on a measurable structure
equal to the sequence-generated sigma-algebra, the standard countably generated algebra
approximation theorem applies on that branch. -/
private lemma existsDenseGeneratingSetAlgebra_of_eq_sequenceGeneratedSpace
    [TopologicalSpace.SeparableSpace E]
    {fSeq : ℕ → Ω → E} {m : MeasurableSpace Ω}
    (hm : m = sequenceGeneratedSpace fSeq) (ν : @Measure Ω m)
    [IsFiniteMeasure ν] :
    ∃ 𝒜 : Set (Set Ω), 𝒜.Countable ∧ IsSetAlgebra 𝒜 ∧
      m = MeasurableSpace.generateFrom 𝒜 ∧
      ν.MeasureDense 𝒜 := by
  letI : @MeasurableSpace.CountablyGenerated Ω m := by
    -- Proof comment: the explicit countable generating family for the sequence-generated
    -- sigma-algebra can be reused after transporting the measurable-space equality.
    rcases sequenceGeneratedSpace_isCountablyGenerated (fSeq := fSeq) with ⟨b, hb, hb_eq⟩
    exact ⟨b, hb, by simpa [hm] using hb_eq⟩
  -- Proof comment: with countable generation available on `m`, the generic finite-measure
  -- dense-generating-algebra theorem closes the branch directly.
  simpa [hm] using existsDenseGeneratingSetAlgebra_countablyGenerated (m := m) ν

/-- Helper for Corollary 6.15: on every finite branch measure carried by
`sequenceGeneratedSpace fSeq`, the dense generating algebra can be replaced by a countable family
of sets that still approximates every finite measurable set and whose members themselves all have
finite measure. -/
private lemma existsCountableFiniteMeasureDenseFamily_sequenceGeneratedSpace
    [TopologicalSpace.SeparableSpace E]
    {fSeq : ℕ → Ω → E} {m : MeasurableSpace Ω}
    (hm : m = sequenceGeneratedSpace fSeq) (ν : @Measure Ω m)
    [IsFiniteMeasure ν] :
    ∃ 𝒜 : Set (Set Ω), 𝒜.Countable ∧ ν.MeasureDense 𝒜 ∧ ∀ s ∈ 𝒜, ν s ≠ ∞ := by
  obtain ⟨𝒜, h𝒜_count, -, -, h𝒜_dense⟩ :=
    existsDenseGeneratingSetAlgebra_of_eq_sequenceGeneratedSpace (fSeq := fSeq) hm ν
  let 𝒜fin : Set (Set Ω) := {s | s ∈ 𝒜 ∧ ν s ≠ ∞}
  have h𝒜fin_count : 𝒜fin.Countable := h𝒜_count.mono (by
    intro s hs
    exact hs.1)
  have h𝒜fin_dense : ν.MeasureDense 𝒜fin := h𝒜_dense.fin_meas
  -- Proof comment: the finite-measure refinement from `MeasureDense.fin_meas` preserves both the
  -- approximation property and countability, so the generated-space branch now has one explicit
  -- countable family of finite control sets.
  exact ⟨𝒜fin, h𝒜fin_count, h𝒜fin_dense, fun s hs ↦ hs.2⟩

/-- Helper for Corollary 6.15: the pairwise deviation events of `fSeq` are measurable for the
countably generated measurable structure `sequenceGeneratedSpace fSeq`. -/
private lemma deviationSet_measurable_sequenceGeneratedSpace
    [TopologicalSpace.SeparableSpace E]
    {fSeq : ℕ → Ω → E} (m n : ℕ) (ε : ℝ) :
    let _ : MeasurableSpace Ω := sequenceGeneratedSpace fSeq
    MeasurableSet {ω | ε < dist (fSeq m ω) (fSeq n ω)} := by
  let _ : MeasurableSpace Ω := sequenceGeneratedSpace fSeq
  -- Proof comment: once both sequence terms are measurable in the generated sigma-algebra,
  -- measurability of the distance deviation set is a standard Borel-space consequence.
  exact measurableSet_lt measurable_const
    ((measurable_sequenceGeneratedSpace (fSeq := fSeq) m).dist
      (measurable_sequenceGeneratedSpace (fSeq := fSeq) n))

/-- Helper for Corollary 6.15: restricting to a finite test set and then trimming to a smaller
measurable structure preserves absolute continuity with respect to the ambient trimmed measure. -/
private lemma restrict_trim_absolutelyContinuous
    {m0 : MeasurableSpace Ω} (μ : @Measure Ω m0) {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {A : Set Ω} :
    (μ.restrict A).trim hm ≪ μ.trim hm := by
  -- Proof comment: `μ.restrict A` is dominated by `μ`, and the trim functor preserves absolute
  -- continuity once both measures are viewed on the smaller measurable structure.
  exact
    Measure.AbsolutelyContinuous.trim
      (μ := μ.restrict A) (ν := μ)
      Measure.restrict_le_self.absolutelyContinuous hm

/-- Helper for Corollary 6.15: an almost-everywhere statement proved after trimming a finite
restriction can be transported back to the original restricted measure. -/
private lemma ae_of_ae_restrict_trim
    {m0 : MeasurableSpace Ω} (μ : @Measure Ω m0) {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {A : Set Ω} {p : Ω → Prop}
    (h : ∀ᵐ x ∂(μ.restrict A).trim hm, p x) :
    ∀ᵐ x ∂ μ.restrict A, p x := by
  -- Proof comment: trimming only forgets sets outside the smaller sigma-algebra, so an a.e.
  -- statement on the trim remains a.e. true for the original restricted measure.
  simpa using (ae_of_ae_trim (μ := μ.restrict A) hm h)

/-- Helper for Corollary 6.15: a finite-slice globalizer stores one witness together with the
family of measurable finite slices on which that witness is already known to be a local limit. -/
private structure FiniteSliceGlobalizer (μ : Measure Ω) (fSeq : ℕ → Ω → E) where
  witness : Ω → E
  verified : Set (Set Ω)
  verified_meas : ∀ ⦃A : Set Ω⦄, A ∈ verified → MeasurableSet A
  verified_finite : ∀ ⦃A : Set Ω⦄, A ∈ verified → μ A < ∞
  tendsto_verified :
    ∀ ⦃A : Set Ω⦄, A ∈ verified →
      TendstoInMeasureOnFiniteMeasureSets (μ.restrict A) fSeq witness

/-- Helper for Corollary 6.15: the repaired finite-slice order enlarges the verified family while
preserving the old witness only up to `μ.restrict A`-almost-everywhere equality on each already
verified slice `A`. -/
private def FiniteSliceGlobalizer.AeExtension
    {μ : Measure Ω} {fSeq : ℕ → Ω → E}
    (p q : FiniteSliceGlobalizer μ fSeq) : Prop :=
  p.verified ⊆ q.verified ∧
    ∀ ⦃A : Set Ω⦄, A ∈ p.verified → q.witness =ᵐ[μ.restrict A] p.witness

private instance instLEFiniteSliceGlobalizer
    {μ : Measure Ω} {fSeq : ℕ → Ω → E} : LE (FiniteSliceGlobalizer μ fSeq) where
  le := FiniteSliceGlobalizer.AeExtension

/-- Helper for Corollary 6.15: the repaired finite-slice a.e.-extension relation is reflexive and
transitive, so Zorn can run on verified finite slices rather than on raw carriers. -/
private instance instPreorderFiniteSliceGlobalizer
    {μ : Measure Ω} {fSeq : ℕ → Ω → E} : Preorder (FiniteSliceGlobalizer μ fSeq) where
  le := (· ≤ ·)
  le_refl p := ⟨subset_rfl, fun _ _ ↦ Filter.EventuallyEq.rfl⟩
  le_trans p q r hpq hqr := by
    refine ⟨hpq.1.trans hqr.1, ?_⟩
    intro A hA
    exact (hqr.2 (hpq.1 hA)).trans (hpq.2 hA)

/-- Helper for Corollary 6.15: the empty verified family is the canonical starting point for the
finite-slice Zorn argument. -/
private def emptyFiniteSliceGlobalizer
    (μ : Measure Ω) (fSeq : ℕ → Ω → E) : FiniteSliceGlobalizer μ fSeq :=
  { witness := fSeq 0
    verified := ∅
    verified_meas := by
      intro A hA
      exact False.elim hA
    verified_finite := by
      intro A hA
      exact False.elim hA
    tendsto_verified := by
      intro A hA
      exact False.elim hA }

/-- Helper for Corollary 6.15: two verified finite slices from compatible local witnesses agree
almost everywhere on their overlap because both restrictions converge in measure to the same
sequence there. -/
private lemma finiteSliceWitness_aeEq_onVerifiedInter
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    {p q : FiniteSliceGlobalizer μ fSeq}
    {A B : Set Ω}
    (hA : A ∈ p.verified) (hB : B ∈ q.verified) :
    p.witness =ᵐ[μ.restrict (A ∩ B)] q.witness := by
  -- Proof comment: both verified witnesses come from the same original Cauchy sequence, so the
  -- finite-overlap uniqueness lemma identifies them there.
  exact localLimit_aeEq_on_finiteInter μ
    (p.verified_meas hA) (q.verified_meas hB)
    (p.verified_finite hA) (q.verified_finite hB)
    (p.tendsto_verified hA) (q.tendsto_verified hB)

/-- Helper for Corollary 6.15: adjoining one new measurable finite slice is done by gluing the
old witness with a fresh local limit on that slice; overlap uniqueness preserves every old
verified slice. -/
private lemma existsAeExtensionByFiniteSlice
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq)
    (p : FiniteSliceGlobalizer μ fSeq)
    {A : Set Ω} (hA : MeasurableSet A) (hA_fin : μ A < ∞) :
    ∃ q : FiniteSliceGlobalizer μ fSeq, p ≤ q ∧ A ∈ q.verified := by
  classical
  obtain ⟨g, hg⟩ := existsLimitOnFiniteRestriction μ h_cauchy hA hA_fin
  let qWitness : Ω → E := A.piecewise g p.witness
  have hq_on_A : qWitness =ᵐ[μ.restrict A] g := by
    exact piecewise_ae_eq_restrict hA
  have hq_on_old :
      ∀ ⦃B : Set Ω⦄, B ∈ p.verified → qWitness =ᵐ[μ.restrict B] p.witness := by
    intro B hB
    have hAB :
        g =ᵐ[μ.restrict (A ∩ B)] p.witness :=
      localLimit_aeEq_on_finiteInter μ hA (p.verified_meas hB) hA_fin
        (p.verified_finite hB) hg (p.tendsto_verified hB)
    have hAB_global :
        ∀ᵐ x ∂ μ, x ∈ A ∩ B → g x = p.witness x := by
      exact (ae_restrict_iff' (hA.inter (p.verified_meas hB))).1 hAB
    have hq_global :
        ∀ᵐ x ∂ μ, x ∈ B → qWitness x = p.witness x := by
      filter_upwards [hAB_global] with x hx hxB
      by_cases hxA : x ∈ A
      · simpa [qWitness, hxA] using hx ⟨hxA, hxB⟩
      · simpa [qWitness, hxA]
    exact (ae_restrict_iff' (p.verified_meas hB)).2 hq_global
  let q : FiniteSliceGlobalizer μ fSeq :=
    { witness := qWitness
      verified := insert A p.verified
      verified_meas := by
        intro B hB
        rcases Set.mem_insert_iff.mp hB with rfl | hB
        · exact hA
        · exact p.verified_meas hB
      verified_finite := by
        intro B hB
        rcases Set.mem_insert_iff.mp hB with rfl | hB
        · exact hA_fin
        · exact p.verified_finite hB
      tendsto_verified := by
        intro B hB
        by_cases hBA : B = A
        · subst B
          -- Proof comment: on the new slice, the glued witness is just the fresh local limit.
          simpa using
            (tendstoInMeasureOnFiniteMeasureSets_congr_ae (μ := μ.restrict A)
              hq_on_A.symm hg)
        · have hBold : B ∈ p.verified := by
            exact (Set.mem_insert_iff.mp hB).resolve_left hBA
          -- Proof comment: on every old verified slice, the glued witness differs from the old
          -- witness only on `A`, and there the two local limits already agree almost everywhere.
          exact tendstoInMeasureOnFiniteMeasureSets_congr_ae (μ := μ.restrict B)
            (hq_on_old hBold).symm (p.tendsto_verified hBold) }
  refine ⟨q, ?_, by simp [q]⟩
  refine ⟨?_, ?_⟩
  · intro B hB
    exact Set.mem_insert_iff.mpr (Or.inr hB)
  · intro B hB
    exact hq_on_old hB

/-- Helper for Corollary 6.15: inside one verified slice `A`, the family of all intersections
`A ∩ B` coming from chain members compresses to countably many measurable finite pieces whose
union still covers `A` almost everywhere under `μ.restrict A`. -/
private lemma existsCountableVerifiedInterCoverOnSlice
    (μ : Measure Ω)
    {fSeq : ℕ → Ω → E}
    {c : Set (FiniteSliceGlobalizer μ fSeq)}
    {p : FiniteSliceGlobalizer μ fSeq}
    (hp : p ∈ c)
    {A : Set Ω} (hA : A ∈ p.verified) :
    ∃ t : ℕ → Set Ω,
      (∀ n, ∃ q ∈ c, ∃ B ∈ q.verified, t n = A ∩ B) ∧
      (∀ n, MeasurableSet (t n)) ∧
      (∀ n, μ (t n) < ∞) ∧
      ∀ᵐ x ∂ μ.restrict A, x ∈ ⋃ n, t n := by
  classical
  let C : Set (Set Ω) := {s | ∃ q ∈ c, ∃ B ∈ q.verified, s = A ∩ B}
  have hC_meas : ∀ s ∈ C, MeasurableSet s := by
    intro s hs
    rcases hs with ⟨q, hq, B, hB, rfl⟩
    exact (p.verified_meas hA).inter (q.verified_meas hB)
  haveI : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 (p.verified_finite hA).ne
  obtain ⟨D, hD_subset, hD_count, hD_cover⟩ :=
    Measure.exists_ae_subset_biUnion_countable (μ := μ.restrict A) hC_meas
  have hA_in_C : A ∈ C := by
    refine ⟨p, hp, A, hA, ?_⟩
    ext x
    simp
  have hA_cover : ∀ᵐ x ∂ μ.restrict A, x ∈ ⋃₀ D := by
    filter_upwards [ae_restrict_mem (p.verified_meas hA), hD_cover A hA_in_C] with x hxA hx
    exact hx hxA
  by_cases hD : D.Nonempty
  · obtain ⟨u, hu⟩ : ∃ u : ℕ → Set Ω, D = Set.range u := hD_count.exists_eq_range hD
    refine ⟨u, ?_, ?_, ?_, ?_⟩
    · intro n
      have hun : u n ∈ D := by
        rw [hu]
        exact Set.mem_range_self n
      exact hD_subset hun
    · intro n
      rcases hD_subset (by
        rw [hu]
        exact Set.mem_range_self n) with ⟨q, hq, B, hB, hs⟩
      simpa [hs] using (p.verified_meas hA).inter (q.verified_meas hB)
    · intro n
      rcases hD_subset (by
        rw [hu]
        exact Set.mem_range_self n) with ⟨q, hq, B, hB, hs⟩
      simpa [hs] using
        (lt_of_le_of_lt (measure_mono Set.inter_subset_left) (p.verified_finite hA))
    · simpa [hu] using hA_cover
  · refine ⟨fun _ ↦ A, ?_, ?_, ?_, ?_⟩
    · intro n
      refine ⟨p, hp, A, hA, ?_⟩
      ext x
      simp
    · intro n
      exact p.verified_meas hA
    · intro n
      exact p.verified_finite hA
    · filter_upwards [ae_restrict_mem (p.verified_meas hA)] with x hx
      exact Set.mem_iUnion.2 ⟨0, hx⟩

/-- Helper for Corollary 6.15: if a countable family of overlap pieces covers `A`
`μ.restrict A`-almost everywhere and two functions agree almost everywhere on every piece
`A ∩ t n`, then they already agree almost everywhere on all of `A`. -/
private lemma aeEqOnVerifiedSlice_ofCountableOverlapCover
    (μ : Measure Ω)
    {A : Set Ω}
    {t : ℕ → Set Ω} (ht : ∀ n, MeasurableSet (t n))
    {f g : Ω → E}
    (hfg : ∀ n, f =ᵐ[μ.restrict (A ∩ t n)] g)
    (hcover : ∀ᵐ x ∂μ.restrict A, x ∈ ⋃ n, t n) :
    f =ᵐ[μ.restrict A] g := by
  have hrestrict :
      (μ.restrict A).restrict (⋃ n, t n) = μ.restrict A :=
    Measure.restrict_eq_self_of_ae_mem hcover
  have hUnion :
      f =ᵐ[(μ.restrict A).restrict (⋃ n, t n)] g := by
    -- Proof comment: once the cover is restricted to the countable union, the conclusion reduces
    -- to the standard countable restricted-a.e. equality equivalence on the pieces `A ∩ t n`.
    rw [ae_eq_restrict_iUnion_iff]
    intro n
    simpa [Measure.restrict_restrict (ht n), Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
      using hfg n
  -- Proof comment: the cover is `μ.restrict A`-almost everywhere full, so equality on the
  -- restricted union is already equality on all of `A`.
  simpa [hrestrict] using hUnion

/-- Helper for Corollary 6.15: one verified finite slice already carries a local limit that is
compatible with every chain member witness on overlaps, because all such witnesses come from the
same original Cauchy sequence. -/
private lemma existsVerifiedSliceLocalLimit_ofChain
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq)
    {c : Set (FiniteSliceGlobalizer μ fSeq)}
    {p : FiniteSliceGlobalizer μ fSeq}
    (_hp : p ∈ c)
    {A : Set Ω} (hA : A ∈ p.verified) :
    ∃ gA : Ω → E,
      TendstoInMeasureOnFiniteMeasureSets (μ.restrict A) fSeq gA ∧
      ∀ q ∈ c, ∀ B ∈ q.verified, gA =ᵐ[μ.restrict (A ∩ B)] q.witness := by
  obtain ⟨gA, hgA⟩ :=
    existsLimitOnFiniteRestriction μ h_cauchy (p.verified_meas hA) (p.verified_finite hA)
  refine ⟨gA, hgA, ?_⟩
  intro q hq B hB
  -- Proof comment: the fresh local limit on `A` and the existing chain member witness on `B`
  -- are both limits of the same sequence on the finite overlap `A ∩ B`, so overlap uniqueness
  -- identifies them there.
  exact localLimit_aeEq_on_finiteInter μ
    (p.verified_meas hA) (q.verified_meas hB)
    (p.verified_finite hA) (q.verified_finite hB)
    hgA (q.tendsto_verified hB)

/-- Helper for Corollary 6.15: a nonempty chain of finite-slice globalizers would be closed by
one ambient witness that agrees almost everywhere with every chain member witness on each of that
member's verified slices. -/
private lemma existsUpperBoundWitnessForFiniteSliceChain
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq)
    {c : Set (FiniteSliceGlobalizer μ fSeq)}
    (_hc : IsChain (fun p q : FiniteSliceGlobalizer μ fSeq ↦ p ≤ q) c)
    {y : FiniteSliceGlobalizer μ fSeq} (_hy : y ∈ c) :
    ∃ g : Ω → E,
      ∀ p ∈ c, ∀ A ∈ p.verified,
        g =ᵐ[μ.restrict A] p.witness ∧
          TendstoInMeasureOnFiniteMeasureSets (μ.restrict A) fSeq g := by
  classical
  -- Route correction: the raw-carrier shell has been removed from the live proof. The only
  -- remaining step is to glue the verified-slice local limits into one ambient witness.
  -- TODO: choose one ambient representative from the chain's verified-slice local limits,
  -- use `existsCountableVerifiedInterCoverOnSlice` plus
  -- `aeEqOnVerifiedSlice_ofCountableOverlapCover` to show that representative agrees with each
  -- owner witness on whole verified slices, and transport convergence by
  -- `tendstoInMeasureOnFiniteMeasureSets_congr_ae`.
  sorry

/-- Helper for Corollary 6.15: once the ambient witness for a finite-slice chain is available,
the upper bound is the union of all verified finite slices in the chain. -/
private lemma existsChainUpperBoundFiniteSliceGlobalizer
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq)
    {c : Set (FiniteSliceGlobalizer μ fSeq)}
    (hc : IsChain (fun p q : FiniteSliceGlobalizer μ fSeq ↦ p ≤ q) c)
    {y : FiniteSliceGlobalizer μ fSeq} (hy : y ∈ c) :
    ∃ ub : FiniteSliceGlobalizer μ fSeq, ∀ z ∈ c, z ≤ ub := by
  classical
  obtain ⟨g, hg⟩ := existsUpperBoundWitnessForFiniteSliceChain μ h_cauchy hc hy
  let ub : FiniteSliceGlobalizer μ fSeq :=
    { witness := g
      verified := {A | ∃ p ∈ c, A ∈ p.verified}
      verified_meas := by
        intro A hA
        rcases hA with ⟨p, hp, hA⟩
        exact p.verified_meas hA
      verified_finite := by
        intro A hA
        rcases hA with ⟨p, hp, hA⟩
        exact p.verified_finite hA
      tendsto_verified := by
        intro A hA
        rcases hA with ⟨p, hp, hA⟩
        exact (hg p hp A hA).2 }
  refine ⟨ub, ?_⟩
  intro z hz
  refine ⟨?_, ?_⟩
  · intro A hA
    exact ⟨z, hz, hA⟩
  · intro A hA
    exact (hg z hz A hA).1

/-- Helper for Corollary 6.15: the genuine closing route now runs Zorn on
`FiniteSliceGlobalizer`, where maximality forces every measurable finite slice into the verified
family. -/
private lemma existsGlobalLimitFromMaximalFiniteSliceGlobalizer
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq) :
    ∃ f : Ω → E, TendstoInMeasureOnFiniteMeasureSets μ fSeq f := by
  classical
  let s : Set (FiniteSliceGlobalizer μ fSeq) := Set.univ
  have hs_chain :
      ∀ c ⊆ s,
        IsChain (fun p q : FiniteSliceGlobalizer μ fSeq ↦ p ≤ q) c →
          ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub := by
    intro c _ hc y hy
    obtain ⟨ub, hub⟩ := existsChainUpperBoundFiniteSliceGlobalizer μ h_cauchy hc hy
    exact ⟨ub, by trivial, hub⟩
  obtain ⟨p, _hp0, hpMax⟩ :=
    zorn_le_nonempty₀ s hs_chain (emptyFiniteSliceGlobalizer μ fSeq) (by trivial)
  refine ⟨p.witness, ?_⟩
  rw [tendstoInMeasureOnFiniteMeasureSets_iff_forall_measurable]
  intro A hA hA_fin
  obtain ⟨q, hpq, hA_mem_q⟩ :=
    existsAeExtensionByFiniteSlice μ h_cauchy p hA hA_fin
  have hqp : q ≤ p := hpMax.le_of_ge (by trivial) hpq
  have hA_mem_p : A ∈ p.verified := hqp.1 hA_mem_q
  -- Proof comment: maximality turns the one-slice extension step into actual membership of every
  -- measurable finite test set in `p.verified`, so `p.witness` already closes the public theorem.
  haveI : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 hA_fin.ne
  exact
    (tendstoInMeasureOnFiniteMeasureSets_iff_mathlib_tendstoInMeasure (μ.restrict A)).1
      (p.tendsto_verified hA_mem_p)

/-- Helper for Corollary 6.15: the retired locally-covered shell is now only a wrapper around
the repaired finite-slice globalization route. -/
private lemma existsGlobalLimitFromMaximalLocallyCoveredPartialLocalLimit
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq) :
    ∃ f : Ω → E, TendstoInMeasureOnFiniteMeasureSets μ fSeq f := by
  exact existsGlobalLimitFromMaximalFiniteSliceGlobalizer μ h_cauchy

/-- Helper for Corollary 6.15: the retired `PartialLocalLimit` shell is now only a wrapper around
the repaired finite-slice globalization route. -/
private lemma existsGlobalLimitFromMaximalPartialLocalLimit
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq) :
    ∃ f : Ω → E, TendstoInMeasureOnFiniteMeasureSets μ fSeq f := by
  exact existsGlobalLimitFromMaximalFiniteSliceGlobalizer μ h_cauchy

/-- Helper for Corollary 6.15: the direct finite-restriction wrapper now delegates to the
repaired finite-slice Zorn shell. -/
private lemma existsGlobalLimitFromFiniteRestrictions_direct
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq) :
    ∃ f : Ω → E, TendstoInMeasureOnFiniteMeasureSets μ fSeq f := by
  exact existsGlobalLimitFromMaximalFiniteSliceGlobalizer μ h_cauchy

/-- Helper for Corollary 6.15: the obsolete supported-shell theorem is now only a wrapper around
the repaired finite-slice globalization route. -/
private lemma existsGlobalLimitFromMaximalSupportedPartialLocalLimit
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq) :
    ∃ f : Ω → E, TendstoInMeasureOnFiniteMeasureSets μ fSeq f := by
  exact existsGlobalLimitFromMaximalFiniteSliceGlobalizer μ h_cauchy

/-- Helper for Corollary 6.15: the generated-space trim route is no longer the active
globalization argument; it now delegates to the exact-extension Zorn step. -/
private lemma existsGlobalLimitFromGeneratedSpaceControl
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq) :
    ∃ f : Ω → E, TendstoInMeasureOnFiniteMeasureSets μ fSeq f := by
  -- Route correction: the generated-space trim route is no longer the active closing argument;
  -- the direct finite-restriction globalization is the real remaining route.
  exact existsGlobalLimitFromFiniteRestrictions_direct μ h_cauchy

/-- Corollary 6.15: For maps into a complete separable metric space, every sequence that is
Cauchy in local `μ`-measure converges in local `μ`-measure. -/
theorem cauchyInMeasureOnFiniteMeasureSets_exists_limit
    (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    {fSeq : ℕ → Ω → E}
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq) :
    ∃ f : Ω → E, TendstoInMeasureOnFiniteMeasureSets μ fSeq f := by
  -- Route correction: the public theorem now follows the `FiniteSliceGlobalizer` Zorn route,
  -- with the only remaining blocker isolated in the ambient chain witness-gluing lemma.
  exact existsGlobalLimitFromFiniteRestrictions_direct μ h_cauchy
