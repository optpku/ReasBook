/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_12

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u}

noncomputable section

/-- The `n`th truncation in the strong-law proof, obtained from `X_{n+1}` by cutting it off
outside the event `|X_{n+1}| ≤ n + 1`. -/
def strongLawTruncation (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  Set.indicator {ω | |X (n + 1) ω| ≤ (n + 1 : ℝ)} (X (n + 1))

/-- The strong-law truncation is exactly `X_{n+1}` on the event `|X_{n+1}| ≤ n + 1` and `0`
outside it. -/
@[simp]
theorem strongLawTruncation_apply (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    strongLawTruncation X n ω = if |X (n + 1) ω| ≤ (n + 1 : ℝ) then X (n + 1) ω else 0 := by
  simp [strongLawTruncation, Set.indicator_apply]

/-- The partial sum of the strong-law truncations `Y₁, …, Yₙ`. -/
def strongLawTruncationPartialSum (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range n, strongLawTruncation X i ω

-- Proof sketch: use the first Borel--Cantelli lemma for the events
-- `{ω | |X (n + 1) ω| > n + 1}` together with identical distribution and integrability of `X 1`
-- to show that the original and truncated sequences differ only finitely often almost surely;
-- then the normalized difference of the corresponding partial sums tends to `0`, so the almost
-- sure limit of the truncated averages is also the almost sure limit of the original averages.
variable [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- Helper for Lemma 5.18: the truncation differs from the original summand exactly on the event
`|X (n + 1)| > n + 1`. -/
private theorem strongLawTruncation_ne_iff
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    strongLawTruncation X n ω ≠ X (n + 1) ω ↔ (n + 1 : ℝ) < |X (n + 1) ω| := by
  by_cases h : |X (n + 1) ω| ≤ (n + 1 : ℝ)
  · -- Proof comment: on the truncation event, the indicator keeps the original value.
    simp [strongLawTruncation_apply, h, not_lt_of_ge h]
  · -- Proof comment: off the truncation event, the indicator is zero, and positivity of `n + 1`
    -- forces the original value to be nonzero.
    have hlt : (n + 1 : ℝ) < |X (n + 1) ω| := lt_of_not_ge h
    have hx : X (n + 1) ω ≠ 0 := by
      exact abs_pos.mp (lt_trans (by positivity) hlt)
    simpa [strongLawTruncation_apply, h, hlt, eq_comm] using hx

/-- Helper for Lemma 5.18: the mismatch probabilities between the original and truncated summands
form a summable series. -/
private theorem strongLawTruncation_mismatch_prob_summable
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_integrable : Integrable (X 1) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P) :
    (∑' n : ℕ, P ({ω | strongLawTruncation X n ω ≠ X (n + 1) ω})) < ⊤ := by
  have htop :
      (∑' n : ℕ, P ({ω | |X 1 ω| ∈ Set.Ioi (n : ℝ)})) < ⊤ := by
    letI : MeasureSpace Ω := ⟨P⟩
    let Y : Ω → ℝ := fun ω ↦ |X 1 ω|
    have hY_integrable : Integrable Y := by
      simpa [Y, Real.norm_eq_abs] using hX_integrable.norm
    simpa only [MeasureSpace.volume, Real.norm_eq_abs] using
      (ProbabilityTheory.tsum_prob_mem_Ioi_lt_top hY_integrable fun ω ↦ by
        simp [Y])
  have hle :
      (∑' n : ℕ, P ({ω | strongLawTruncation X n ω ≠ X (n + 1) ω})) ≤
        ∑' n : ℕ, P ({ω | |X 1 ω| ∈ Set.Ioi (n : ℝ)}) := by
    refine ENNReal.tsum_le_tsum fun n ↦ ?_
    calc
      P ({ω | strongLawTruncation X n ω ≠ X (n + 1) ω})
          = P ({ω | |X (n + 1) ω| ∈ Set.Ioi ((n + 1 : ℝ))}) := by
            congr 1
            ext ω
            simpa [Set.mem_Ioi] using (strongLawTruncation_ne_iff X n ω)
      _ = P ({ω | |X 1 ω| ∈ Set.Ioi ((n + 1 : ℝ))}) := by
            exact (hX_ident n).norm.measure_mem_eq measurableSet_Ioi
      _ ≤ P ({ω | |X 1 ω| ∈ Set.Ioi (n : ℝ)}) := by
            refine measure_mono fun ω hω ↦ ?_
            have hω' : (n + 1 : ℝ) < |X 1 ω| := by
              simpa [Set.mem_Ioi] using hω
            simpa [Set.mem_Ioi] using lt_trans (by exact_mod_cast Nat.lt_succ_self n) hω'
  exact lt_of_le_of_lt hle htop

omit [MeasurableSpace Ω] in
/-- Helper for Lemma 5.18: once the truncation agrees with the original sequence on the tail, the
difference of the corresponding partial sums is frozen. -/
private theorem strongLawTruncation_gap_eq_of_tail_eq
    (X : ℕ → Ω → ℝ) (ω : Ω) {N n : ℕ}
    (hn : N ≤ n)
    (h_tail : ∀ m ≥ N, strongLawTruncation X m ω = X (m + 1) ω) :
    strongLawTruncationPartialSum X n ω - ∑ i ∈ Finset.range n, X (i + 1) ω =
      strongLawTruncationPartialSum X N ω - ∑ i ∈ Finset.range N, X (i + 1) ω := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hsum :
      ∑ j ∈ Finset.range k, strongLawTruncation X (N + j) ω =
        ∑ j ∈ Finset.range k, X (N + j + 1) ω := by
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    exact h_tail (N + j) (Nat.le_add_right N j)
  -- Proof comment: split both partial sums at the last mismatch index `N` and cancel the common
  -- tail, which agrees termwise by hypothesis.
  rw [strongLawTruncationPartialSum, strongLawTruncationPartialSum,
    Finset.sum_range_add, Finset.sum_range_add]
  rw [hsum]
  abel

omit [MeasurableSpace Ω] in
/-- Helper for Lemma 5.18: after the last mismatch, the truncation gap is eventually constant. -/
private theorem strongLawTruncation_gap_eventually_constant
    (X : ℕ → Ω → ℝ) (ω : Ω) (N : ℕ)
    (h_tail : ∀ m ≥ N, strongLawTruncation X m ω = X (m + 1) ω) :
    ∀ᶠ n in atTop,
      strongLawTruncationPartialSum X n ω - ∑ i ∈ Finset.range n, X (i + 1) ω =
        strongLawTruncationPartialSum X N ω - ∑ i ∈ Finset.range N, X (i + 1) ω := by
  -- Proof comment: every sufficiently large partial sum has the same tail, so the gap stabilizes.
  filter_upwards [eventually_ge_atTop N] with n hn
  exact strongLawTruncation_gap_eq_of_tail_eq X ω hn h_tail

/-- Helper for Lemma 5.18: the normalized gap between the truncated and original partial sums tends
to `0` almost surely. -/
private theorem ae_tendsto_strongLawTruncation_gap_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_integrable : Integrable (X 1) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun n : ℕ ↦
          (strongLawTruncationPartialSum X n ω - ∑ i ∈ Finset.range n, X (i + 1) ω) / n)
        atTop (𝓝 0) := by
  have hsummable :
      (∑' n : ℕ, P ({ω | strongLawTruncation X n ω ≠ X (n + 1) ω})) < ⊤ :=
    strongLawTruncation_mismatch_prob_summable P X hX_integrable hX_ident
  filter_upwards [MeasureTheory.ae_eventually_notMem hsummable.ne] with ω hω
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hω
  have htail : ∀ m ≥ N, strongLawTruncation X m ω = X (m + 1) ω := by
    intro m hm
    exact not_not.mp (hN m hm)
  have hconst :
      (fun n : ℕ ↦
        (strongLawTruncationPartialSum X n ω - ∑ i ∈ Finset.range n, X (i + 1) ω) / n) =ᶠ[atTop]
        (fun n : ℕ ↦
          (strongLawTruncationPartialSum X N ω - ∑ i ∈ Finset.range N, X (i + 1) ω) / n) := by
    filter_upwards [strongLawTruncation_gap_eventually_constant X ω N htail] with n hn
    exact congrArg (fun x : ℝ ↦ x / n) hn
  -- Proof comment: the numerator is eventually constant, so dividing by `n` forces convergence to
  -- `0`.
  refine Tendsto.congr' hconst.symm ?_
  exact tendsto_const_div_atTop_nhds_zero_nat
    (strongLawTruncationPartialSum X N ω - ∑ i ∈ Finset.range N, X (i + 1) ω)

/-- Lemma 5.18: if the truncated averages `Tₙ / n` converge almost surely to `𝔼[X₁]`, then the
textbook sequence `X₁, X₂, …`, encoded as `fun n ↦ X (n + 1)`, satisfies the strong law of large
numbers. -/
theorem satisfies_strong_law_of_large_numbers_of_ae_tendsto_strongLawTruncation_average
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_integrable : Integrable (X 1) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (h_trunc :
      ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ ↦ strongLawTruncationPartialSum X n ω / n) atTop (𝓝 P[X 1])) :
    satisfies_strong_law_of_large_numbers P (fun n ↦ X (n + 1)) := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: each shifted summand is integrable because it has the same distribution as
    -- the integrable random variable `X 1`.
    intro n
    exact (hX_ident n).symm.integrable_snd hX_integrable
  · -- Proof comment: Borel-Cantelli shows that the truncation gap is negligible after division by
    -- `n`, so the raw averages have the same almost sure limit as the truncated averages.
    have hgap :
        ∀ᵐ ω ∂P,
          Tendsto
            (fun n : ℕ ↦
              (strongLawTruncationPartialSum X n ω - ∑ i ∈ Finset.range n, X (i + 1) ω) / n)
            atTop (𝓝 0) :=
      ae_tendsto_strongLawTruncation_gap_zero P X hX_integrable hX_ident
    have hraw :
        ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, X (i + 1) ω) / n) atTop
          (𝓝 P[X 1]) := by
      filter_upwards [h_trunc, hgap] with ω hω_trunc hω_gap
      have hsub :
          Tendsto
            (fun n : ℕ ↦
              strongLawTruncationPartialSum X n ω / n -
                (strongLawTruncationPartialSum X n ω -
                  ∑ i ∈ Finset.range n, X (i + 1) ω) / n)
            atTop (𝓝 (P[X 1] - 0)) := by
        exact hω_trunc.sub hω_gap
      have hrawω :
          Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, X (i + 1) ω) / n) atTop
            (𝓝 (P[X 1] - 0)) := by
        refine Tendsto.congr' ?_ hsub
        refine Filter.Eventually.of_forall fun n ↦ ?_
        change
          strongLawTruncationPartialSum X n ω / n -
              (strongLawTruncationPartialSum X n ω - ∑ i ∈ Finset.range n, X (i + 1) ω) / n =
            (∑ i ∈ Finset.range n, X (i + 1) ω) / n
        rw [← sub_div, sub_sub_cancel]
      simpa using hrawω
    exact ae_tendsto_centered_average_of_ae_tendsto_raw_average P X hX_ident hraw
