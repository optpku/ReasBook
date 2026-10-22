/-
Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open scoped Topology

section Chap03
section Section02

/-- Definition 3.2: Pointwise convergence. A sequence of functions
`f` converges pointwise to `g` on `X` if for every `x`, the sequence
`n ↦ f n x` tends to `g x` (equivalently: for every `x` and `ε > 0` there
exists `N` such that for all `n ≥ N`, `dist (f n x) (g x) < ε`). -/
def PointwiseConvergent {X Y : Type*} [MetricSpace Y]
    (f : ℕ → X → Y) (g : X → Y) : Prop :=
  ∀ x : X, Filter.Tendsto (fun n : ℕ => f n x) Filter.atTop (𝓝 (g x))

/-- Example 3.2.3: for any fixed `x ∈ ℝ`, the sequence `n ↦ x / n`
converges to `0` as `n → ∞`. -/
theorem tendsto_const_div_nat_atTop (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => x / (n : ℝ)) Filter.atTop (𝓝 (0 : ℝ)) := by
  simpa using (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) x)

/-- Helper for Example 3.2.4: if `0 ≤ r < 1` then `|r| < 1`. -/
lemma helperForExample_3_2_4_abs_lt_one_of_nonneg_of_lt_one
    {r : ℝ} (hr : 0 ≤ r) (h : r < 1) : |r| < 1 := by
  simp [abs_of_nonneg hr, h]

/-- Helper for Example 3.2.4: if `r ≤ 1` and `¬ r < 1`, then `r = 1`. -/
lemma helperForExample_3_2_4_eq_one_of_le_one_of_not_lt_one
    {r : ℝ} (hr : r ≤ 1) (h : ¬ r < 1) : r = 1 := by
  exact le_antisymm hr (not_lt.mp h)

/-- Example 3.2.4: for `f^{(n)}(x) := x^n` on `[0,1]`, the pointwise limit
`f` is given by `f(x) = 0` for `0 ≤ x < 1` and `f(1) = 1`. -/
theorem pointwiseConvergent_pow_on_unitInterval :
    PointwiseConvergent
      (X := {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1})
      (Y := ℝ)
      (fun n x => (x : ℝ) ^ n)
      (fun x => if (x : ℝ) < 1 then 0 else 1) := by
  dsimp [PointwiseConvergent]
  intro x
  by_cases hx : (x : ℝ) < 1
  · have hxabs : |(x : ℝ)| < 1 :=
      helperForExample_3_2_4_abs_lt_one_of_nonneg_of_lt_one x.property.1 hx
    simpa [hx] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := (x : ℝ)) hxabs)
  · have h_eq : (x : ℝ) = 1 :=
      helperForExample_3_2_4_eq_one_of_le_one_of_not_lt_one x.property.2 hx
    simp [h_eq]

/-- Helper for Example 3.2.5: the within-neighborhood filter on `Ico 0 1` at `1` is nontrivial. -/
lemma helperForExample_3_2_5_nhdsWithin_Ico_neBot :
    (Filter.NeBot (𝓝[Set.Ico (0 : ℝ) 1] (1 : ℝ))) := by
  have hIcc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · norm_num
    · norm_num
  have hclosure : closure (Set.Ico (0 : ℝ) 1) = Set.Icc (0 : ℝ) 1 := by
    simpa using (closure_Ico (a := (0 : ℝ)) (b := (1 : ℝ)) zero_ne_one)
  have hmem : (1 : ℝ) ∈ closure (Set.Ico (0 : ℝ) 1) := by
    simpa [hclosure] using hIcc
  exact (mem_closure_iff_nhdsWithin_neBot.mp hmem)

/-- Example 3.2.5: for `f^{(n)}(x) = x^n` on `[0,1)`, each `f^{(n)}` has
limit `1` as `x → 1` within `[0,1)`, while the pointwise limit on `[0,1)`
is `0`, so iterated limits need not agree and pointwise convergence does
not preserve limits. -/
theorem pointwiseConvergence_not_preserve_limit_on_Ico :
    (∀ n : ℕ,
      Filter.Tendsto (fun x : ℝ => x ^ n) (𝓝[Set.Ico (0 : ℝ) 1] (1 : ℝ))
        (𝓝 (1 : ℝ))) ∧
    (∀ x ∈ Set.Ico (0 : ℝ) 1,
      Filter.Tendsto (fun n : ℕ => x ^ n) Filter.atTop (𝓝 (0 : ℝ))) ∧
    (Filter.Tendsto (fun x : ℝ => (0 : ℝ)) (𝓝[Set.Ico (0 : ℝ) 1] (1 : ℝ))
        (𝓝 (0 : ℝ))) ∧
    (¬ Filter.Tendsto (fun x : ℝ => (0 : ℝ)) (𝓝[Set.Ico (0 : ℝ) 1] (1 : ℝ))
        (𝓝 (1 : ℝ))) := by
  refine And.intro ?h1 ?hrest
  · intro n
    have hcont :
        ContinuousWithinAt (fun x : ℝ => x ^ n) (Set.Ico (0 : ℝ) 1) (1 : ℝ) :=
      (continuousAt_pow (x := (1 : ℝ)) n).continuousWithinAt
    simpa using hcont.tendsto
  · refine And.intro ?h2 ?hrest2
    · intro x hx
      have hxabs : |x| < 1 :=
        helperForExample_3_2_4_abs_lt_one_of_nonneg_of_lt_one hx.1 hx.2
      simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := x) hxabs)
    · refine And.intro ?h3 ?h4
      ·
        simpa using
          (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
              (𝓝[Set.Ico (0 : ℝ) 1] (1 : ℝ)) (𝓝 (0 : ℝ)))
      · intro h
        haveI : (Filter.NeBot (𝓝[Set.Ico (0 : ℝ) 1] (1 : ℝ))) :=
          helperForExample_3_2_5_nhdsWithin_Ico_neBot
        have hEq : (0 : ℝ) = (1 : ℝ) :=
          (tendsto_const_nhds_iff.mp h)
        exact zero_ne_one hEq

/-- A spike function on `[0,1]` used in a pointwise-convergence counterexample. -/
noncomputable def spikeFunction (n : ℕ) (x : ℝ) : ℝ :=
  if x ∈ Set.Icc (1 / (2 * (n + 1 : ℝ))) (1 / (n + 1 : ℝ)) then
    2 * (n + 1 : ℝ)
  else
    0

/-- Helper for Example 3.2.6: rewrite `spikeFunction` as an indicator of an interval. -/
lemma helperForExample_3_2_6_spikeFunction_as_indicator (n : ℕ) :
    spikeFunction n =
      Set.indicator (Set.Icc (1 / (2 * (n + 1 : ℝ))) (1 / (n + 1 : ℝ)))
        (fun _ : ℝ => 2 * (n + 1 : ℝ)) := by
  funext x
  by_cases hx :
      x ∈ Set.Icc (1 / (2 * (n + 1 : ℝ))) (1 / (n + 1 : ℝ))
  · simp [spikeFunction, Set.indicator, hx]
  · simp [spikeFunction, Set.indicator, hx]

/-- Helper for Example 3.2.6: basic inequalities for the spike interval endpoints. -/
lemma helperForExample_3_2_6_endpoints_properties (n : ℕ) :
    (0 : ℝ) < 1 / (2 * (n + 1 : ℝ)) ∧
    1 / (2 * (n + 1 : ℝ)) ≤ 1 / (n + 1 : ℝ) ∧
    1 / (n + 1 : ℝ) ≤ (1 : ℝ) := by
  have hn : (0 : ℝ) < (n + 1 : ℝ) := by
    exact_mod_cast (Nat.succ_pos n)
  have hpos : (0 : ℝ) < 2 * (n + 1 : ℝ) := by
    nlinarith
  have h_le : (n + 1 : ℝ) ≤ 2 * (n + 1 : ℝ) := by
    nlinarith
  have h1 : (0 : ℝ) < 1 / (2 * (n + 1 : ℝ)) := by
    exact one_div_pos.mpr hpos
  have h2 : 1 / (2 * (n + 1 : ℝ)) ≤ 1 / (n + 1 : ℝ) := by
    exact one_div_le_one_div_of_le hn h_le
  have h3 : 1 / (n + 1 : ℝ) ≤ (1 : ℝ) := by
    have h_one_le : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    have hpos1 : (0 : ℝ) < (1 : ℝ) := by
      norm_num
    have h3' : 1 / (n + 1 : ℝ) ≤ 1 / (1 : ℝ) :=
      one_div_le_one_div_of_le hpos1 h_one_le
    simpa using h3'
  exact And.intro h1 (And.intro h2 h3)

/-- Helper for Example 3.2.6: the spike functions are eventually zero at each point. -/
lemma helperForExample_3_2_6_eventually_spikeFunction_eq_zero (x : ℝ) :
    (∀ᶠ n in Filter.atTop, spikeFunction n x = 0) := by
  by_cases hx : x ≤ 0
  · refine Filter.eventually_atTop.2 ?_
    refine ⟨0, ?_⟩
    intro n hn
    have hpos : (0 : ℝ) < 1 / (2 * (n + 1 : ℝ)) :=
      (helperForExample_3_2_6_endpoints_properties n).1
    have hxlt : x < 1 / (2 * (n + 1 : ℝ)) :=
      lt_of_le_of_lt hx hpos
    have hnot :
        x ∉ Set.Icc (1 / (2 * (n + 1 : ℝ))) (1 / (n + 1 : ℝ)) := by
      intro hxmem
      exact (not_lt_of_ge hxmem.1) hxlt
    unfold spikeFunction
    exact if_neg hnot
  · have hxpos : 0 < x := lt_of_not_ge hx
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hxpos
    refine Filter.eventually_atTop.2 ?_
    refine ⟨N, ?_⟩
    intro n hn
    have hNpos : (0 : ℝ) < (N + 1 : ℝ) := by
      exact_mod_cast (Nat.succ_pos N)
    have hle : (N + 1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ hn)
    have hle_div : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) :=
      one_div_le_one_div_of_le hNpos hle
    have hux : (1 / (n + 1 : ℝ)) < x := lt_of_le_of_lt hle_div hN
    have hnot :
        x ∉ Set.Icc (1 / (2 * (n + 1 : ℝ))) (1 / (n + 1 : ℝ)) := by
      intro hxmem
      exact (not_lt_of_ge hxmem.2) hux
    unfold spikeFunction
    exact if_neg hnot

/-- Helper for Example 3.2.6: the spike functions are interval integrable on `[0,1]`. -/
lemma helperForExample_3_2_6_intervalIntegrable_spikeFunction (n : ℕ) :
    IntervalIntegrable (spikeFunction n) (μ := MeasureTheory.volume) (0 : ℝ) 1 := by
  have h_eq := helperForExample_3_2_6_spikeFunction_as_indicator n
  have hμ : MeasureTheory.volume (Set.Ioc (0 : ℝ) 1) ≠ (⊤ : ENNReal) := by
    simp
  have hconst :
      MeasureTheory.IntegrableOn (fun _ : ℝ => 2 * (n + 1 : ℝ))
        (Set.Ioc (0 : ℝ) 1) (MeasureTheory.volume) := by
    simpa using
      (MeasureTheory.integrableOn_const (μ := MeasureTheory.volume) (s := Set.Ioc (0 : ℝ) 1)
        (C := (2 * (n + 1 : ℝ))) (hs := hμ))
  have h_ind :
      MeasureTheory.IntegrableOn
        (Set.indicator (Set.Icc (1 / (2 * (n + 1 : ℝ))) (1 / (n + 1 : ℝ)))
          (fun _ : ℝ => 2 * (n + 1 : ℝ)))
        (Set.Ioc (0 : ℝ) 1) (MeasureTheory.volume) :=
    MeasureTheory.IntegrableOn.indicator hconst measurableSet_Icc
  have h_int :
      MeasureTheory.IntegrableOn (spikeFunction n) (Set.Ioc (0 : ℝ) 1)
        (MeasureTheory.volume) := by
    simpa [h_eq] using h_ind
  have h0 : (0 : ℝ) ≤ (1 : ℝ) := by
    norm_num
  exact
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
        (f := spikeFunction n) (μ := MeasureTheory.volume) h0).2 h_int

/-- Helper for Example 3.2.6: the spike interval integral equals `1`. -/ 
lemma helperForExample_3_2_6_intervalIntegral_spikeFunction (n : ℕ) :
    ∫ x in (0 : ℝ)..(1 : ℝ), spikeFunction n x = (1 : ℝ) := by
  let l : ℝ := 1 / (2 * (n + 1 : ℝ))
  let u : ℝ := 1 / (n + 1 : ℝ)
  have h_eq :
      spikeFunction n =
        Set.indicator (Set.Icc l u) (fun _ : ℝ => 2 * (n + 1 : ℝ)) := by
    simpa [l, u] using helperForExample_3_2_6_spikeFunction_as_indicator n
  have hprops := helperForExample_3_2_6_endpoints_properties n
  have hl : (0 : ℝ) < l := by
    simpa [l, u] using hprops.1
  have hle : l ≤ u := by
    simpa [l, u] using hprops.2.1
  have hu : u ≤ (1 : ℝ) := by
    simpa [l, u] using hprops.2.2
  have hsubset : Set.Icc l u ⊆ Set.Ioc (0 : ℝ) 1 := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hl hx.1
    have hxle : x ≤ (1 : ℝ) := le_trans hx.2 hu
    exact And.intro hxpos hxle
  have hinter : Set.Ioc (0 : ℝ) 1 ∩ Set.Icc l u = Set.Icc l u :=
    Set.inter_eq_right.mpr hsubset
  have h0 : (0 : ℝ) ≤ (1 : ℝ) := by
    norm_num
  calc
    ∫ x in (0 : ℝ)..(1 : ℝ), spikeFunction n x
        = ∫ x in Set.Ioc (0 : ℝ) 1, spikeFunction n x := by
            simpa using
              (intervalIntegral.integral_of_le (μ := MeasureTheory.volume)
                (f := spikeFunction n) (a := (0 : ℝ)) (b := (1 : ℝ)) h0)
    _ = ∫ x in Set.Ioc (0 : ℝ) 1,
          Set.indicator (Set.Icc l u) (fun _ : ℝ => 2 * (n + 1 : ℝ)) x := by
            simpa [h_eq]
    _ = ∫ x in Set.Ioc (0 : ℝ) 1 ∩ Set.Icc l u,
          (fun _ : ℝ => 2 * (n + 1 : ℝ)) x := by
            simpa using
              (MeasureTheory.setIntegral_indicator (μ := MeasureTheory.volume)
                (s := Set.Ioc (0 : ℝ) 1)
                (t := Set.Icc l u) (f := (fun _ : ℝ => 2 * (n + 1 : ℝ)))
                measurableSet_Icc)
    _ = ∫ x in Set.Icc l u, (fun _ : ℝ => 2 * (n + 1 : ℝ)) x := by
            simp [hinter]
    _ = (1 : ℝ) := by
            have hn : (n + 1 : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.succ_ne_zero n)
            have htwo : (2 : ℝ) ≠ 0 := by
              norm_num
            have h2 : (2 * (n + 1 : ℝ)) ≠ 0 := by
              exact mul_ne_zero htwo hn
            calc
              ∫ x in Set.Icc l u, (fun _ : ℝ => 2 * (n + 1 : ℝ)) x
                  = (MeasureTheory.volume.real (Set.Icc l u)) • (2 * (n + 1 : ℝ)) := by
                      simpa using
                        (MeasureTheory.setIntegral_const (μ := MeasureTheory.volume)
                          (s := Set.Icc l u)
                          (c := (2 * (n + 1 : ℝ))))
              _ = (u - l) * (2 * (n + 1 : ℝ)) := by
                      simp [Real.volume_real_Icc_of_le hle, smul_eq_mul]
              _ = (1 : ℝ) := by
                      simp [l, u]
                      field_simp [hn, h2]
                      ring_nf

/-- Example 3.2.6: the spike functions on `[0,1]` converge pointwise to `0`, each has
integral `1`, and hence the limit of the integrals is not the integral of the pointwise
limit. -/
theorem counterexample_pointwiseIntegral_limit :
    PointwiseConvergent spikeFunction (fun _ : ℝ => 0) ∧
    (∀ n : ℕ,
      IntervalIntegrable (spikeFunction n) (μ := MeasureTheory.volume) (0 : ℝ) 1) ∧
    (∀ n : ℕ, ∫ x in (0 : ℝ)..(1 : ℝ), spikeFunction n x = (1 : ℝ)) ∧
    (∫ x in (0 : ℝ)..(1 : ℝ), (0 : ℝ)) = (0 : ℝ) ∧
    (Filter.Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..(1 : ℝ), spikeFunction n x)
        Filter.atTop (𝓝 (1 : ℝ))) ∧
    (1 : ℝ) ≠ (0 : ℝ) := by
  refine And.intro ?h_pointwise ?hrest
  · dsimp [PointwiseConvergent]
    intro x
    have h_eventual := helperForExample_3_2_6_eventually_spikeFunction_eq_zero x
    have h_tendsto :
        Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds
    have h_eq :
        (fun n : ℕ => spikeFunction n x) =ᶠ[Filter.atTop] (fun _ : ℕ => (0 : ℝ)) :=
      h_eventual
    exact (Filter.tendsto_congr' h_eq).2 h_tendsto
  · refine And.intro ?h_integrable ?hrest2
    · intro n
      exact helperForExample_3_2_6_intervalIntegrable_spikeFunction n
    · refine And.intro ?h_integral ?hrest3
      · intro n
        exact helperForExample_3_2_6_intervalIntegral_spikeFunction n
      · refine And.intro ?h_zero ?hrest4
        · simp
        · refine And.intro ?h_tendsto ?h_ne
          · have hconst :
                (fun n : ℕ =>
                  ∫ x in (0 : ℝ)..(1 : ℝ), spikeFunction n x) =
                fun _ : ℕ => (1 : ℝ) := by
              funext n
              exact helperForExample_3_2_6_intervalIntegral_spikeFunction n
            have h_tendsto_const :
                Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (𝓝 (1 : ℝ)) :=
              tendsto_const_nhds
            simpa [hconst] using h_tendsto_const
          · norm_num

/-- A moving bump function on `ℝ` given by the indicator of `[n, n+1]`. -/
noncomputable def movingBump (n : ℕ) (x : ℝ) : ℝ :=
  if x ∈ Set.Icc (n : ℝ) (n + 1) then 1 else 0

/-- Helper for Example 3.2.7: `movingBump` is the indicator of `[n, n+1]`. -/
lemma helperForExample_3_2_7_movingBump_eq_indicator (n : ℕ) :
    movingBump n = (Set.Icc (n : ℝ) (n + 1)).indicator (1 : ℝ → ℝ) := by
  funext x
  by_cases hx : x ∈ Set.Icc (n : ℝ) (n + 1)
  · simp [movingBump, hx]
  · simp [movingBump, hx]

/-- Helper for Example 3.2.7: for fixed `x`, the moving bump is eventually zero. -/
lemma helperForExample_3_2_7_eventually_movingBump_eq_zero (x : ℝ) :
    (fun n : ℕ => movingBump n x) =ᶠ[Filter.atTop] (fun _ : ℕ => (0 : ℝ)) := by
  refine Filter.eventually_atTop.2 ?_
  obtain ⟨N, hN⟩ := exists_nat_gt x
  refine ⟨N, ?_⟩
  intro n hn
  have hle : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hlt : x < (n : ℝ) := lt_of_lt_of_le hN hle
  have hnot : x ∉ Set.Icc (n : ℝ) (n + 1) := by
    intro hx
    exact (not_le_of_gt hlt) hx.1
  simp [movingBump, hnot]

/-- Helper for Example 3.2.7: the Lebesgue measure of `[n, n+1]` is `1`. -/
lemma helperForExample_3_2_7_volume_real_Icc_nat (n : ℕ) :
    MeasureTheory.volume.real (Set.Icc (n : ℝ) (n + 1)) = (1 : ℝ) := by
  have hle : (n : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast (Nat.le_succ n)
  simpa [Real.volume_real_Icc_of_le hle]

/-- Helper for Example 3.2.7: the integral of `movingBump n` is `1`. -/
lemma helperForExample_3_2_7_integral_movingBump (n : ℕ) :
    (∫ x : ℝ, movingBump n x) = (1 : ℝ) := by
  calc
    ∫ x : ℝ, movingBump n x
        = ∫ x : ℝ, (Set.Icc (n : ℝ) (n + 1)).indicator (1 : ℝ → ℝ) x := by
            simpa [helperForExample_3_2_7_movingBump_eq_indicator n]
    _ = MeasureTheory.volume.real (Set.Icc (n : ℝ) (n + 1)) := by
            simpa using
              (MeasureTheory.integral_indicator_one (μ := MeasureTheory.volume)
                (s := Set.Icc (n : ℝ) (n + 1)) (hs := measurableSet_Icc))
    _ = (1 : ℝ) := by
            simpa using (helperForExample_3_2_7_volume_real_Icc_nat n)

/-- Example 3.2.7: [Moving bump: pointwise convergence does not commute with integration]
for `f_n` the indicator of `[n, n+1]`, (1) `f_n(x) → 0` pointwise on `ℝ`,
(2) `∫ f_n = 1` for all `n`, and (3) `∫ (lim_n f_n) = 0`, hence
`lim_n ∫ f_n ≠ ∫ lim_n f_n`. -/
theorem movingBump_pointwiseIntegral_counterexample :
    PointwiseConvergent movingBump (fun _ : ℝ => 0) ∧
    (∀ n : ℕ, ∫ x, movingBump n x = (1 : ℝ)) ∧
    ((∫ x : ℝ, (0 : ℝ)) = (0 : ℝ)) ∧
    (Filter.Tendsto (fun n : ℕ => ∫ x, movingBump n x) Filter.atTop (𝓝 (1 : ℝ))) ∧
    (1 : ℝ) ≠ (0 : ℝ) := by
  refine And.intro ?h_pointwise ?hrest
  · dsimp [PointwiseConvergent]
    intro x
    have h_eventual := helperForExample_3_2_7_eventually_movingBump_eq_zero x
    have h_tendsto :
        Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds
    exact (Filter.tendsto_congr' h_eventual).2 h_tendsto
  · refine And.intro ?h_integral ?hrest2
    · intro n
      exact helperForExample_3_2_7_integral_movingBump n
    · refine And.intro ?h_zero ?hrest3
      · simp
      · refine And.intro ?h_tendsto ?h_ne
        · have hconst :
              (fun n : ℕ => ∫ x, movingBump n x) = fun _ : ℕ => (1 : ℝ) := by
            funext n
            exact helperForExample_3_2_7_integral_movingBump n
          have h_tendsto_const :
              Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (𝓝 (1 : ℝ)) :=
            tendsto_const_nhds
          simpa [hconst] using h_tendsto_const
        · norm_num

/-- Example 3.2.8: [Pointwise limit of `x^n` on `[0,1]`]. For `f_n(x) = x^n` on
`[0,1]`, the pointwise limit is `f(x) = 0` for `0 ≤ x < 1` and `f(1) = 1`. -/
theorem pointwiseConvergent_pow_on_Icc_zero_one :
    PointwiseConvergent
      (X := {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1})
      (Y := ℝ)
      (fun n x => (x : ℝ) ^ n)
      (fun x => if (x : ℝ) < 1 then 0 else 1) := by
  simpa using pointwiseConvergent_pow_on_unitInterval

/-- Helper for Example 3.2.9: the pointwise limit evaluates to `1` at `x = 2`. -/
lemma helperForExample_3_2_9_limitValue_at_two :
    (if (2 : ℝ) < 1 then (0 : ℝ) else 1) = 1 := by
  have hnot : ¬ (2 : ℝ) < 1 := by
    norm_num
  simp [hnot]

/-- Helper for Example 3.2.9: the sequence `2^n` does not converge to `1`. -/
lemma helperForExample_3_2_9_not_tendsto_pow_two_nhds_one :
    ¬ Filter.Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)) Filter.atTop (𝓝 (1 : ℝ)) := by
  intro h
  have hlt : (1 : ℝ) < 2 := by
    norm_num
  have hIio : Set.Iio (2 : ℝ) ∈ 𝓝 (1 : ℝ) :=
    Iio_mem_nhds hlt
  have h_eventually_lt :
      ∀ᶠ n in Filter.atTop, (2 : ℝ) ^ n ∈ Set.Iio (2 : ℝ) :=
    (Filter.Tendsto.eventually h hIio)
  have hpow_atTop :
      Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hlt
  have h_eventually_ge :
      ∀ᶠ n in Filter.atTop, (2 : ℝ) ≤ (2 : ℝ) ^ n :=
    (Filter.tendsto_atTop.1 hpow_atTop (2 : ℝ))
  rcases (Filter.eventually_atTop.1 h_eventually_lt) with ⟨N1, hN1⟩
  rcases (Filter.eventually_atTop.1 h_eventually_ge) with ⟨N2, hN2⟩
  have hlt' : (2 : ℝ) ^ (max N1 N2) < 2 := by
    have hmem : (2 : ℝ) ^ (max N1 N2) ∈ Set.Iio (2 : ℝ) :=
      hN1 (max N1 N2) (le_max_left _ _)
    exact hmem
  have hge' : (2 : ℝ) ≤ (2 : ℝ) ^ (max N1 N2) := by
    exact hN2 (max N1 N2) (le_max_right _ _)
  exact (not_lt_of_ge hge' hlt')

/-- Example 3.2.9: [`x^n` does not converge uniformly on `[0,1]`]. Let `f_n(x) = x^n`
on `[0,1]`, and let `f` be the pointwise limit above. Then `f_n` does not
converge uniformly to `f` on `[0,1]`. -/
theorem not_tendstoUniformly_pow_on_Icc_zero_one :
    ¬ TendstoUniformly
        (fun n x => (x : ℝ) ^ n)
        (fun x => if (x : ℝ) < 1 then 0 else 1)
        Filter.atTop := by
  intro hU
  have hpoint :
      Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n) Filter.atTop
        (𝓝 (if (2 : ℝ) < 1 then 0 else 1)) :=
    (TendstoUniformly.tendsto_at
      (F := fun n x => (x : ℝ) ^ n)
      (f := fun x => if (x : ℝ) < 1 then 0 else 1)
      (p := Filter.atTop) hU (2 : ℝ))
  have hpoint' :
      Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n) Filter.atTop (𝓝 (1 : ℝ)) := by
    simpa [helperForExample_3_2_9_limitValue_at_two] using hpoint
  exact helperForExample_3_2_9_not_tendsto_pow_two_nhds_one hpoint'

/-- Definition 3.3: Uniform convergence. A sequence `f` converges uniformly to `g` on
`X` if for every `ε > 0` there exists `N` such that for all `n ≥ N` and all `x`,
`dist (f n x) (g x) < ε`. In this case, `g` is the uniform limit of the sequence. -/
def UniformlyConvergent {X Y : Type*} [MetricSpace Y]
    (f : ℕ → X → Y) (g : X → Y) : Prop :=
  TendstoUniformly f g Filter.atTop

/-- Example 3.2.10: if a sequence of functions converges uniformly to `f` on `X`,
then it converges pointwise to `f` on `X`. -/
theorem uniformlyConvergent_implies_pointwiseConvergent
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : ℕ → X → Y) (g : X → Y) :
    UniformlyConvergent f g → PointwiseConvergent f g := by
  intro hU
  dsimp [UniformlyConvergent, PointwiseConvergent] at *
  intro x
  simpa using
    (TendstoUniformly.tendsto_at
      (F := f) (f := g) (p := Filter.atTop) hU x)

/-- Helper for Example 3.2.11: points in `[0,1]` have absolute value at most `1`. -/
lemma helperForExample_3_2_11_abs_val_le_one
    (x : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}) : |(x : ℝ)| ≤ 1 := by
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := x.property.1
  have hx1 : (x : ℝ) ≤ (1 : ℝ) := x.property.2
  simpa [abs_of_nonneg hx0] using hx1

/-- Helper for Example 3.2.11: the distance from `0` to `x/n` is bounded by `1/n`. -/
lemma helperForExample_3_2_11_dist_zero_div_nat_le_one_div_nat
    (x : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}) (n : ℕ) :
    dist (0 : ℝ) ((x : ℝ) / (n : ℝ)) ≤ 1 / (n : ℝ) := by
  have hx : |(x : ℝ)| ≤ 1 :=
    helperForExample_3_2_11_abs_val_le_one x
  have hnnonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast (Nat.cast_nonneg n)
  have hdivle : |(x : ℝ)| / (n : ℝ) ≤ 1 / (n : ℝ) :=
    div_le_div_of_nonneg_right hx hnnonneg
  simpa [Real.dist_eq, abs_div, abs_of_nonneg hnnonneg] using hdivle

/-- Example 3.2.11: [Uniform convergence of `x/n` on `[0,1]`]. Let
`f_n(x) = x/n` on `[0,1]` and `f(x) = 0`. Then `f_n` converges uniformly
to `f` on `[0,1]`. -/
theorem uniformlyConvergent_x_div_nat_on_Icc_zero_one :
    UniformlyConvergent
      (X := {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1})
      (Y := ℝ)
      (fun n x => (x : ℝ) / (n : ℝ))
      (fun _ => (0 : ℝ)) := by
  dsimp [UniformlyConvergent]
  refine (Metric.tendstoUniformly_iff).2 ?_
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine Filter.eventually_atTop.2 ?_
  refine ⟨N + 1, ?_⟩
  intro n hn
  intro x
  have hdist :
      dist (0 : ℝ) ((x : ℝ) / (n : ℝ)) ≤ 1 / (n : ℝ) :=
    helperForExample_3_2_11_dist_zero_div_nat_le_one_div_nat x n
  have hNpos : (0 : ℝ) < (N + 1 : ℝ) := by
    exact_mod_cast (Nat.succ_pos N)
  have hle' : (N + 1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hle : (1 / (n : ℝ)) ≤ 1 / (N + 1 : ℝ) :=
    one_div_le_one_div_of_le hNpos hle'
  have hlt : (1 / (n : ℝ)) < ε := lt_of_le_of_lt hle hN
  exact lt_of_le_of_lt hdist hlt

/-- Example 3.2.12: (i) pointwise convergence on `X` restricts to pointwise
convergence on `E`; (ii) uniform convergence on `X` restricts to uniform
convergence on `E`. -/
theorem convergence_restrict_subset
    {X Y : Type*} [MetricSpace Y] (E : Set X)
    (f : ℕ → X → Y) (g : X → Y) :
    (PointwiseConvergent f g →
        PointwiseConvergent (X := {x : X // x ∈ E}) (Y := Y)
          (fun n x => f n x) (fun x => g x)) ∧
      (UniformlyConvergent f g →
        UniformlyConvergent (X := {x : X // x ∈ E}) (Y := Y)
          (fun n x => f n x) (fun x => g x)) := by
  refine And.intro ?hpoint ?hunif
  · intro hpoint
    dsimp [PointwiseConvergent] at hpoint ⊢
    intro x
    exact hpoint x
  · intro hunif
    dsimp [UniformlyConvergent] at hunif ⊢
    refine (Metric.tendstoUniformly_iff).2 ?_
    have hunif' := (Metric.tendstoUniformly_iff).1 hunif
    intro ε hε
    refine Filter.Eventually.mono (hunif' ε hε) ?_
    intro n hn x
    exact hn x

end Section02
end Chap03
