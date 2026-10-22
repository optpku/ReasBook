/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_26

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators ENNReal NNReal Topology

namespace MeasureTheory
namespace FiniteMeasure

/- Layer triage for Exercise 13.3.1.
- `source-facing`: existence of a measurable coercive weight with uniformly bounded integrals.
- `core/canonical`: `MeasureTheory.IsTightMeasureSet`.
- `bridge/view`: `tight_family_iff_forall_exists_isCompact_measure_compl_lt` is the chapter's
  compact-control reformulation of the same owner predicate for finite-measure families.
-/

-- Proof sketch: for the forward implication, extract compact sets with uniformly small complement
-- mass and assemble from them a measurable coercive weight by summing suitably scaled indicators of
-- those compacts. For the reverse implication, use Markov-type estimates on the sublevel sets of
-- the coercive weight to obtain compact sets whose complement mass is uniformly small over the
-- family.
/-
This is a source-facing bridge theorem over the canonical owner abstraction
`MeasureTheory.IsTightMeasureSet`, specialized to families of finite measures on `ℝ`.
-/
/-- Helper for Exercise 13.3.1: tightness yields radii with uniformly geometric control of norm
tails. -/
private lemma existsTailRadii (ℱ : Set (FiniteMeasure ℝ))
    (hℱ : IsTightMeasureSet (toMeasure '' ℱ)) :
    ∃ R : ℕ → ℝ,
      (∀ n : ℕ, (n : ℝ) ≤ R n) ∧
      ∀ n μ, μ ∈ ℱ → toMeasure μ {x : ℝ | R n < ‖x‖} ≤ ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) := by
  classical
  -- Tightness on `ℝ` is equivalent to uniform decay of the norm tails.
  have htail : Tendsto (fun r : ℝ ↦ ⨆ ν ∈ toMeasure '' ℱ, ν {x : ℝ | r < ‖x‖}) atTop (𝓝 0) :=
    (isTightMeasureSet_iff_tendsto_measure_norm_gt).mp hℱ
  rw [ENNReal.tendsto_atTop_zero] at htail
  have hchoose :
      ∀ n : ℕ, ∃ r : ℝ, (n : ℝ) ≤ r ∧
        (⨆ ν ∈ toMeasure '' ℱ, ν {x : ℝ | r < ‖x‖}) ≤ ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) := by
    intro n
    have hε : 0 < ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) := by
      exact bot_lt_iff_ne_bot.mpr <| pow_ne_zero _ (by simp)
    obtain ⟨r, hr⟩ := htail (((2 : ℝ≥0∞)⁻¹) ^ (n + 1)) hε
    refine ⟨max n r, le_max_left _ _, hr (max n r) (le_max_right _ _)⟩
  choose R hR_ge hR_tail using hchoose
  refine ⟨R, hR_ge, ?_⟩
  intro n μ hμ
  -- Each concrete measure tail is bounded by the corresponding uniform supremum.
  have hle :
      toMeasure μ {x : ℝ | R n < ‖x‖} ≤
        ⨆ ν ∈ toMeasure '' ℱ, ν {x : ℝ | R n < ‖x‖} :=
    le_iSup_of_le (toMeasure μ) <| le_iSup_of_le ⟨μ, hμ, rfl⟩ le_rfl
  exact hle.trans (hR_tail n)

/-- Helper for Exercise 13.3.1: the strict norm tail attached to the radius sequence `R`. -/
private def tailSet (R : ℕ → ℝ) (n : ℕ) : Set ℝ :=
  {x : ℝ | R n < ‖x‖}

/-- Helper for Exercise 13.3.1: the `ℝ≥0∞`-valued indicator-series weight built from `R`. -/
private noncomputable def tailIndicatorWeightENNReal (R : ℕ → ℝ) : ℝ → ℝ≥0∞ :=
  fun x ↦ ∑' n : ℕ, (tailSet R n).indicator (fun _ ↦ (1 : ℝ≥0∞)) x

/-- Helper for Exercise 13.3.1: the `ℝ≥0`-valued weight obtained from the indicator series. -/
private noncomputable def tailIndicatorWeight (R : ℕ → ℝ) : ℝ → ℝ≥0 :=
  fun x ↦ (tailIndicatorWeightENNReal R x).toNNReal

/-- Helper for Exercise 13.3.1: each tail set `{x | R n < ‖x‖}` is measurable. -/
private lemma tailSet_measurableSet (R : ℕ → ℝ) (n : ℕ) :
    MeasurableSet (tailSet R n) := by
  simpa [tailSet] using measurableSet_lt measurable_const measurable_norm

/-- Helper for Exercise 13.3.1: each indicator term in the tail series is measurable. -/
private lemma tailIndicatorTermMeasurable (R : ℕ → ℝ) (n : ℕ) :
    Measurable fun x ↦ (tailSet R n).indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
  exact Measurable.indicator measurable_const (tailSet_measurableSet R n)

/-- Helper for Exercise 13.3.1: the `ℝ≥0∞`-valued indicator-series weight is measurable. -/
private lemma tailIndicatorWeightENNReal_measurable (R : ℕ → ℝ) :
    Measurable (tailIndicatorWeightENNReal R) := by
  -- Measurability comes from countable summation of measurable indicator terms.
  simpa [tailIndicatorWeightENNReal] using
    Measurable.ennreal_tsum (tailIndicatorTermMeasurable R)

/-- Helper for Exercise 13.3.1: the indicator-series weight is pointwise finite because only
finitely many tail indicators can be nonzero at a fixed point. -/
private lemma tailIndicatorWeightSeriesFinite (R : ℕ → ℝ)
    (hR_ge : ∀ n : ℕ, (n : ℝ) ≤ R n) :
    ∀ x : ℝ, tailIndicatorWeightENNReal R x < ∞ := by
  intro x
  let N : ℕ := ⌈‖x‖⌉₊
  have hxN : ‖x‖ ≤ N := by
    exact_mod_cast Nat.le_ceil ‖x‖
  have hzero :
      ∀ n ∉ Finset.range (N + 1),
        (tailSet R n).indicator (fun _ ↦ (1 : ℝ≥0∞)) x = 0 := by
    intro n hn
    have hn' : N + 1 ≤ n := Nat.not_lt.mp (by simpa [Finset.mem_range] using hn)
    have hNn : (N : ℝ) < n := by
      exact_mod_cast Nat.lt_of_lt_of_le (Nat.lt_succ_self N) hn'
    have hxlt : ‖x‖ < R n := by
      calc
        ‖x‖ ≤ N := hxN
        _ < n := hNn
        _ ≤ R n := hR_ge n
    have hxle : ‖x‖ ≤ R n := hxlt.le
    have hnot : x ∉ tailSet R n := by
      simpa [tailSet] using not_lt.mpr hxle
    simp [hnot]
  -- Only finitely many nonzero terms remain, so the `tsum` is finite.
  rw [show tailIndicatorWeightENNReal R x =
      ∑' n : ℕ, (tailSet R n).indicator (fun _ ↦ (1 : ℝ≥0∞)) x by rfl]
  rw [tsum_eq_sum (s := Finset.range (N + 1)) hzero]
  exact ENNReal.sum_lt_top.mpr fun n _hn => by
    by_cases hxA : x ∈ tailSet R n <;> simp [hxA]

/-- Helper for Exercise 13.3.1: the `ℝ≥0`-valued weight is measurable. -/
private lemma tailIndicatorWeight_measurable (R : ℕ → ℝ) :
    Measurable (tailIndicatorWeight R) := by
  -- Measurability is inherited from the measurable `ℝ≥0∞` series.
  simpa [tailIndicatorWeight] using
    (tailIndicatorWeightENNReal_measurable R).ennreal_toNNReal

/-- Helper for Exercise 13.3.1: outside a sufficiently large centered ball, the weight dominates
any prescribed lower bound. -/
private lemma weightEventuallyLargeOutsideBall (R : ℕ → ℝ)
    (hR_ge : ∀ n : ℕ, (n : ℝ) ≤ R n) :
    ∀ b : ℝ≥0, ∃ S : ℝ, (Metric.closedBall 0 S)ᶜ ⊆ {x | b ≤ tailIndicatorWeight R x} := by
  intro b
  let N : ℕ := ⌈(b : ℝ)⌉₊
  have hbN : b ≤ N := by
    exact_mod_cast Nat.le_ceil (b : ℝ)
  let S : ℝ := (Finset.range (N + 1)).sum R
  refine ⟨S, ?_⟩
  intro x hx
  have hxnorm : S < ‖x‖ := by
    simpa [Metric.mem_closedBall, dist_zero_right, Set.mem_compl_iff, not_le] using hx
  have hpartial : (N + 1 : ℝ≥0∞) ≤ tailIndicatorWeightENNReal R x := by
    calc
      (N + 1 : ℝ≥0∞) = (Finset.range (N + 1)).sum (fun _ ↦ (1 : ℝ≥0∞)) := by
        simp
      _ =
          (Finset.range (N + 1)).sum
            (fun k ↦ (tailSet R k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              have hk_le : R k ≤ S := by
                unfold S
                exact Finset.single_le_sum
                  (fun i hi ↦ le_trans (by exact_mod_cast Nat.zero_le i) (hR_ge i)) hk
              have hk_lt : R k < ‖x‖ := lt_of_le_of_lt hk_le hxnorm
              have hx_mem : x ∈ tailSet R k := by
                simpa [tailSet] using hk_lt
              simp [hx_mem]
      _ ≤ tailIndicatorWeightENNReal R x := by
            unfold tailIndicatorWeightENNReal
            exact ENNReal.sum_le_tsum _
  have hfx : (N + 1 : ℝ≥0) ≤ tailIndicatorWeight R x := by
    refine ENNReal.le_toNNReal_of_coe_le hpartial ?_
    exact (tailIndicatorWeightSeriesFinite R hR_ge x).ne
  change b ≤ tailIndicatorWeight R x
  exact hbN.trans <|
    (show (N : ℝ≥0) ≤ (N + 1 : ℝ≥0) by exact_mod_cast Nat.le_succ N).trans hfx

/-- Helper for Exercise 13.3.1: the `ℝ≥0∞`-valued tail weight has uniformly bounded integral on
the tight family. -/
private lemma tailIndicatorWeightENNReal_lintegral_le_one
    (ℱ : Set (FiniteMeasure ℝ)) (R : ℕ → ℝ)
    (hR_tail :
      ∀ n μ, μ ∈ ℱ →
        toMeasure μ (tailSet R n) ≤ ((2 : ℝ≥0∞)⁻¹) ^ (n + 1))
    (μ : FiniteMeasure ℝ) (hμ : μ ∈ ℱ) :
    ∫⁻ x, tailIndicatorWeightENNReal R x ∂(μ : Measure ℝ) ≤ 1 := by
  -- Expand the integral termwise and compare with the geometric tail estimates.
  calc
    ∫⁻ x, tailIndicatorWeightENNReal R x ∂(μ : Measure ℝ)
        =
          ∑' n : ℕ,
            ∫⁻ x, (tailSet R n).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂(μ : Measure ℝ) := by
              simpa [tailIndicatorWeightENNReal] using
                (lintegral_tsum
                  (f := fun n x ↦ (tailSet R n).indicator (fun _ ↦ (1 : ℝ≥0∞)) x)
                  (μ := (μ : Measure ℝ))
                  (fun n ↦ (tailIndicatorTermMeasurable R n).aemeasurable))
    _ = ∑' n : ℕ, (μ : Measure ℝ) (tailSet R n) := by
          congr with n
          exact lintegral_indicator_one (tailSet_measurableSet R n)
    _ ≤ ∑' n : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) := by
          refine ENNReal.tsum_le_tsum ?_
          intro n
          exact hR_tail n μ hμ
    _ = 1 := by
          calc
            ∑' n : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (n + 1)
                = (2⁻¹ : ℝ≥0∞) * (1 - (2⁻¹ : ℝ≥0∞))⁻¹ :=
                  ENNReal.tsum_geometric_add_one _
            _ = 1 := by
                  simpa using ENNReal.inv_mul_cancel (Ne.symm (NeZero.ne' 2))
                    (by simp : (2 : ℝ≥0∞) ≠ ∞)

/-- Helper for Exercise 13.3.1: the `ℝ≥0` tail weight inherits the same uniform integral bound. -/
private lemma tailIndicatorWeight_lintegral_le_one
    (ℱ : Set (FiniteMeasure ℝ)) (R : ℕ → ℝ)
    (hR_tail :
      ∀ n μ, μ ∈ ℱ →
        toMeasure μ (tailSet R n) ≤ ((2 : ℝ≥0∞)⁻¹) ^ (n + 1))
    (μ : FiniteMeasure ℝ) (hμ : μ ∈ ℱ) :
    ∫⁻ x, ↑(tailIndicatorWeight R x) ∂(μ : Measure ℝ) ≤ 1 := by
  refine (lintegral_mono fun x ↦ ?_).trans
    (tailIndicatorWeightENNReal_lintegral_le_one ℱ R hR_tail μ hμ)
  exact ENNReal.coe_toNNReal_le_self

/-- Helper for Exercise 13.3.1: a measurable cocompact weight with uniformly bounded integrals
forces uniformly small escape mass outside a centered closed ball. -/
private lemma smallEscapeOfBoundedWeight
    (ℱ : Set (FiniteMeasure ℝ)) (f : ℝ → ℝ≥0) (hf_meas : Measurable f)
    (hf_top : Tendsto f (cocompact ℝ) atTop)
    (hbound : (⨆ μ ∈ ℱ, ∫⁻ x, ↑(f x) ∂μ) < ∞) :
    ∀ ε : ℝ, 0 < ε → ∃ r : ℝ,
      ∀ μ ∈ ℱ, (μ : Measure ℝ) (Metric.closedBall 0 r)ᶜ < ENNReal.ofReal ε := by
  intro ε hε
  let M : ℝ≥0∞ := ⨆ μ ∈ ℱ, ∫⁻ x, ↑(f x) ∂μ
  have hM : M < ∞ := by
    simpa [M] using hbound
  obtain ⟨n, hn⟩ : ∃ n : ℕ, M.toReal / ε < n := exists_nat_gt (M.toReal / ε)
  have hn_pos : (0 : ℝ) < n := by
    have hnonneg : 0 ≤ M.toReal / ε := by
      positivity
    exact lt_of_le_of_lt hnonneg hn
  let S : Set ℝ := {x : ℝ | (n : ℝ≥0) ≤ f x}
  have hS_mem : S ∈ cocompact ℝ := by
    -- Cocompact growth supplies a global superlevel set outside a large ball.
    simpa [S] using (tendsto_atTop.1 hf_top (n : ℝ≥0))
  obtain ⟨r, hr⟩ := Metric.closedBall_compl_subset_of_mem_cocompact hS_mem 0
  refine ⟨r, ?_⟩
  intro μ hμ
  have hn_ne_zero : (n : ℝ≥0∞) ≠ 0 := by
    have hn_nat_pos : 0 < n := by
      exact_mod_cast hn_pos
    simp [hn_nat_pos.ne']
  have hmarkov :
      (μ : Measure ℝ) S ≤ (∫⁻ x, ↑(f x) ∂(μ : Measure ℝ)) / (n : ℝ≥0∞) := by
    -- Markov's inequality turns the superlevel set into an integral estimate.
    simpa [S] using
      (meas_ge_le_lintegral_div (μ := (μ : Measure ℝ))
        (f := fun x ↦ (f x : ℝ≥0∞))
        hf_meas.coe_nnreal_ennreal.aemeasurable hn_ne_zero (by simp))
  have h_int_le : ∫⁻ x, ↑(f x) ∂(μ : Measure ℝ) ≤ M :=
    le_iSup_of_le μ <| le_iSup_of_le hμ le_rfl
  have hdiv_lt : M / (n : ℝ≥0∞) < ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_toReal hM.ne]
    rw [show (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) by simp]
    rw [← ENNReal.ofReal_div_of_pos hn_pos]
    refine (ENNReal.ofReal_lt_ofReal_iff hε).2 ?_
    have hmul : M.toReal < ε * n := by
      simpa [mul_comm] using (div_lt_iff₀ hε).1 hn
    exact (div_lt_iff₀ hn_pos).2 hmul
  calc
    (μ : Measure ℝ) (Metric.closedBall 0 r)ᶜ ≤ (μ : Measure ℝ) S := measure_mono hr
    _ ≤ (∫⁻ x, ↑(f x) ∂(μ : Measure ℝ)) / (n : ℝ≥0∞) := hmarkov
    _ ≤ M / (n : ℝ≥0∞) := by
          gcongr
    _ < ENNReal.ofReal ε := hdiv_lt

/-- Exercise 13.3.1: a family `ℱ` of finite measures on `ℝ` is tight if and only if there exists
a measurable weight `f : ℝ → [0, ∞)` that tends to `∞` along `cocompact ℝ` and whose integrals
are uniformly bounded on `ℱ`. -/
theorem tight_family_iff_exists_measurable_coercive_weight (ℱ : Set (FiniteMeasure ℝ)) :
    IsTightMeasureSet (toMeasure '' ℱ) ↔
      ∃ f : ℝ → ℝ≥0,
        Measurable f ∧
          Tendsto f (cocompact ℝ) atTop ∧
            (⨆ μ ∈ ℱ, ∫⁻ x, ↑(f x) ∂μ) < ∞ := by
  constructor
  · intro htight
    obtain ⟨R, hR_ge, hR_tail⟩ := existsTailRadii ℱ htight
    refine ⟨tailIndicatorWeight R, tailIndicatorWeight_measurable R, ?_, ?_⟩
    · -- The indicator-series weight grows arbitrarily large outside a large centered ball.
      refine tendsto_atTop.2 ?_
      intro b
      obtain ⟨S, hS⟩ := weightEventuallyLargeOutsideBall R hR_ge b
      exact Metric.mem_cocompact_of_closedBall_compl_subset 0 ⟨S, hS⟩
    · -- The geometric tail control bounds every family integral by `1`.
      have hbound_le :
          (⨆ μ ∈ ℱ, ∫⁻ x, ↑(tailIndicatorWeight R x) ∂μ) ≤ 1 := by
        refine iSup_le ?_
        intro μ
        refine iSup_le ?_
        intro hμ
        exact tailIndicatorWeight_lintegral_le_one ℱ R hR_tail μ hμ
      exact lt_of_le_of_lt hbound_le (by simp)
  · rintro ⟨f, hf_meas, hf_top, hbound⟩
    refine
      (tight_family_iff_forall_exists_isCompact_measure_compl_lt ℱ).2 ?_
    intro ε hε
    obtain ⟨r, hr⟩ := smallEscapeOfBoundedWeight ℱ f hf_meas hf_top hbound ε hε
    refine ⟨Metric.closedBall 0 r, isCompact_closedBall (0 : ℝ) r, ?_⟩
    intro μ hμ
    simpa using hr μ hμ

end FiniteMeasure
end MeasureTheory
