/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.IdentDistribIndep
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

universe u v

section

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]

-- Semantic recall note: leansearch did not surface a sharper tail-law theorem here, so this file
-- uses the local specialization of `tendstoInDistribution_of_identDistrib`.
-- Proof sketch: the convergence in distribution is immediate from
-- `tendstoInDistribution_of_identDistrib`; the primitive input is equality in distribution of the
-- tail variables with `X 0`, and the i.i.d. version is just its source-facing specialization.
private theorem tail_tendstoInDistribution_of_identDistrib
    {X : ℕ → Ω → E}
    (hX_ident : ∀ n : ℕ, IdentDistrib (X (n + 1)) (X 0) μ μ) :
    TendstoInDistribution (fun n ↦ X (n + 1)) atTop (X 0) (fun _ ↦ μ) μ := by
  -- Proof comment: apply the constant-law convergence theorem to the tail family, using the first
  -- tail variable `X 1` as the reference coordinate.
  refine tendstoInDistribution_of_identDistrib 0 ?_ (hX_ident 0)
  intro j
  -- Proof comment: every tail coordinate has the same law as `X 0`, hence also as `X 1`.
  exact (hX_ident 0).trans (hX_ident j).symm

/-- Example 13.20 (1): if `X 0, X 1, X 2, ...` are i.i.d., then the tail sequence `X (n + 1)`
converges in distribution to `X 0`. -/
theorem iid_tail_tendstoInDistribution
    {X : ℕ → Ω → E}
    (hX_iid : IsIID X μ) :
    TendstoInDistribution (fun n ↦ X (n + 1)) atTop (X 0) (fun _ ↦ μ) μ := by
  -- Proof comment: specialize the previous tail-law lemma to the pairwise identical laws coming
  -- from the i.i.d. hypothesis.
  exact tail_tendstoInDistribution_of_identDistrib fun n ↦ hX_iid.identDistrib (n + 1) 0

end

section

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {E : Type v} [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E]
variable [BorelSpace E]

/-- Helper for Example 13.20: the distance from `X 0` to any tail coordinate `X (n + 1)` has the
same law as the distance from `X 0` to `X 1`. -/
private lemma identDistrib_tailDist_first
    {X : ℕ → Ω → E}
    (hX_iid : IsIID X μ) (n : ℕ) :
    IdentDistrib (fun ω ↦ dist (X (n + 1) ω) (X 0 ω))
      (fun ω ↦ dist (X 1 ω) (X 0 ω)) μ μ := by
  have hX0_meas : AEMeasurable (X 0) μ := (hX_iid.identDistrib 0 0).aemeasurable_fst
  have hpair :
      IdentDistrib (fun ω ↦ (X (n + 1) ω, X 0 ω))
        (fun ω ↦ (X 1 ω, X 0 ω)) μ μ := by
    -- Proof comment: pair the common marginal law with the fixed `X 0` marginal and use the
    -- independence of distinct coordinates.
    refine ProbabilityTheory.IdentDistrib.prodMk
      (hX_iid.identDistrib (n + 1) 1) (ProbabilityTheory.IdentDistrib.refl hX0_meas) ?_ ?_
    · exact hX_iid.iIndepFun.indepFun (Nat.succ_ne_zero n)
    · exact hX_iid.iIndepFun.indepFun (by decide : (1 : ℕ) ≠ 0)
  -- Proof comment: push the pair law through the measurable distance map.
  exact hpair.comp (measurable_fst.dist measurable_snd)

/-- Helper for Example 13.20: if two independent identically distributed random variables agree
almost surely, then their common law is a Dirac mass. -/
private lemma exists_dirac_of_indepFun_identDistrib_ae_eq
    {Y Z : Ω → E}
    (hYZ_ident : IdentDistrib Y Z μ μ)
    (hYZ_indep : Y ⟂ᵢ[μ] Z)
    (hYZ_ae : Y =ᵐ[μ] Z) :
    ∃ c : E, μ.map Y = Measure.dirac c := by
  let ν : Measure E := μ.map Y
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hYZ_ident.aemeasurable_fst
  have hZeroOne : ∀ s : Set E, MeasurableSet s → ν s = 0 ∨ ν s = 1 := by
    intro s hs
    have hY_map : μ (Y ⁻¹' s) = ν s := by
      simp [ν, Measure.map_apply_of_aemeasurable hYZ_ident.aemeasurable_fst hs]
    have h_inter :
        μ (Y ⁻¹' s ∩ Z ⁻¹' s) = μ (Y ⁻¹' s) := by
      -- Proof comment: the almost-sure equality identifies the two membership events.
      refine measure_congr ?_
      filter_upwards [hYZ_ae] with ω hω
      apply propext
      constructor
      · intro h
        exact h.1
      · intro h
        change Y ω ∈ s at h
        refine ⟨h, ?_⟩
        simpa [hω] using h
    have h_sq : ν s = ν s * ν s := by
      -- Proof comment: independence factors the intersection event, while identical laws replace
      -- the `Z` marginal by the `Y` marginal.
      calc
        ν s = μ (Y ⁻¹' s) := hY_map.symm
        _ = μ (Y ⁻¹' s ∩ Z ⁻¹' s) := h_inter.symm
        _ = μ (Y ⁻¹' s) * μ (Z ⁻¹' s) :=
          hYZ_indep.measure_inter_preimage_eq_mul s s hs hs
        _ = μ (Y ⁻¹' s) * μ (Y ⁻¹' s) := by rw [hYZ_ident.measure_mem_eq hs]
        _ = ν s * ν s := by rw [hY_map]
    have h_sq_real : (ν s).toReal = (ν s).toReal * (ν s).toReal := by
      simpa using congrArg ENNReal.toReal h_sq
    have h_factor : (ν s).toReal * ((ν s).toReal - 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp h_factor with h_zero | h_one
    · left
      have hs_zero_or_top := (ENNReal.toReal_eq_zero_iff (ν s)).mp h_zero
      rcases hs_zero_or_top with hs_zero | hs_top
      · exact hs_zero
      · exact (measure_ne_top ν s hs_top).elim
    · right
      have h_toReal_one : (ν s).toReal = 1 := by
        linarith
      exact (ENNReal.toReal_eq_one_iff (ν s)).mp h_toReal_one
  have hsupport_subsingleton : ν.support.Subsingleton := by
    intro x hx y hy
    by_contra hxy
    let r : ℝ := dist x y / 2
    have hr : 0 < r := by
      dsimp [r]
      have hdist_pos : 0 < dist x y := dist_pos.mpr hxy
      linarith
    have hx_ball_pos : 0 < ν (Metric.ball x r) := by
      -- Proof comment: every support point assigns positive mass to each of its open balls.
      exact (Measure.mem_support_iff_forall x).mp hx _ (Metric.ball_mem_nhds x hr)
    have hy_ball_pos : 0 < ν (Metric.ball y r) := by
      exact (Measure.mem_support_iff_forall y).mp hy _ (Metric.ball_mem_nhds y hr)
    have hx_ball_one : ν (Metric.ball x r) = 1 := by
      rcases hZeroOne (Metric.ball x r) measurableSet_ball with hx_zero | hx_one
      · exact (hx_ball_pos.ne' hx_zero).elim
      · exact hx_one
    have hx_ball_compl_zero : ν (Metric.ball x r)ᶜ = 0 := by
      exact
        (prob_compl_eq_zero_iff measurableSet_ball).2 hx_ball_one
    have hdisj : Disjoint (Metric.ball x r) (Metric.ball y r) := by
      refine Metric.ball_disjoint_ball ?_
      dsimp [r]
      nlinarith
    have hy_ball_zero : ν (Metric.ball y r) = 0 := by
      exact measure_mono_null hdisj.symm.subset_compl_right hx_ball_compl_zero
    exact (hy_ball_pos.ne' hy_ball_zero).elim
  have hν_ne_zero : ν ≠ 0 := IsProbabilityMeasure.ne_zero ν
  obtain ⟨c, hc⟩ : ν.support.Nonempty := Measure.nonempty_support hν_ne_zero
  have hsupport_eq : ν.support = ({c} : Set E) := by
    ext x
    constructor
    · intro hx
      exact Set.mem_singleton_iff.mpr (hsupport_subsingleton hx hc)
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hc
  refine ⟨c, Measure.ext fun s hs ↦ ?_⟩
  have hsingleton_compl_zero : ν ({c} : Set E)ᶜ = 0 := by
    -- Proof comment: a probability measure is concentrated on its support, which is `{c}` here.
    simpa [hsupport_eq] using (Measure.measure_compl_support : ν ν.supportᶜ = 0)
  by_cases hc_mem : c ∈ s
  · have hs_compl_zero : ν sᶜ = 0 := by
      refine measure_mono_null ?_ hsingleton_compl_zero
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hxc
      exact hx (hxc ▸ hc_mem)
    have hs_one : ν s = 1 := (prob_compl_eq_zero_iff hs).mp hs_compl_zero
    simpa [ν, Measure.dirac_apply' c hs, hc_mem] using hs_one
  · have hs_zero : ν s = 0 := by
      refine measure_mono_null ?_ hsingleton_compl_zero
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hxc
      exact hc_mem (hxc ▸ hx)
    simpa [ν, Measure.dirac_apply' c hs, hc_mem] using hs_zero

/-- Example 13.20 (2): if `X 0, X 1, X 2, ...` are independent, identically distributed, and the
common law is nontrivial, then the tail sequence `X (n + 1)` does not converge in probability to
`X 0`. -/
theorem iid_tail_not_tendstoInMeasure
    {X : ℕ → Ω → E}
    (hX_iid : IsIID X μ)
    (h_nontrivial : ¬ ∃ c : E, μ.map (X 0) = Measure.dirac c) :
    ¬ TendstoInMeasure μ (fun n ↦ X (n + 1)) atTop (X 0) := by
  intro h_tendsto
  have hdist_tendsto := (tendstoInMeasure_iff_dist.mp h_tendsto)
  have hdist_zero :
      ∀ n : ℕ, μ {ω | (1 : ℝ) / (n + 1) ≤ dist (X 1 ω) (X 0 ω)} = 0 := by
    intro n
    have hconst :
        Tendsto (fun _ : ℕ ↦ μ {ω | (1 : ℝ) / (n + 1) ≤ dist (X 1 ω) (X 0 ω)}) atTop (𝓝 0) := by
      -- Proof comment: each distance-threshold probability is constant in `n` because the law of
      -- `dist (X (n + 1), X 0)` is the same as the law of `dist (X 1, X 0)`.
      convert hdist_tendsto ((1 : ℝ) / (n + 1)) (by positivity) using 1
      ext m
      exact
        ((identDistrib_tailDist_first hX_iid m).measure_mem_eq measurableSet_Ici).symm
    exact tendsto_const_nhds_iff.mp hconst
  have hdist_ne_zero :
      μ {ω | dist (X 1 ω) (X 0 ω) ≠ 0} = 0 := by
    have h_union :
        {ω | dist (X 1 ω) (X 0 ω) ≠ 0}
          = ⋃ n : ℕ, {ω | (1 : ℝ) / (n + 1) ≤ dist (X 1 ω) (X 0 ω)} := by
      ext ω
      constructor
      · intro hω
        have hdist_pos : 0 < dist (X 1 ω) (X 0 ω) := lt_of_le_of_ne dist_nonneg hω.symm
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hdist_pos
        refine Set.mem_iUnion.mpr ⟨n, ?_⟩
        simp only [Set.mem_setOf_eq]
        exact le_of_lt hn
      · intro hω
        rcases Set.mem_iUnion.mp hω with ⟨n, hn⟩
        exact fun hdist_zero ↦ by
          have : (0 : ℝ) < (1 : ℝ) / (n + 1) := by positivity
          simpa [hdist_zero] using lt_of_lt_of_le this hn
    rw [h_union, measure_iUnion_null_iff]
    intro n
    exact hdist_zero n
  have hdist_ae : ∀ᵐ ω ∂μ, dist (X 1 ω) (X 0 ω) = 0 := by
    rw [ae_iff]
    simpa using hdist_ne_zero
  have hX1_eq_X0 : X 1 =ᵐ[μ] X 0 := by
    -- Proof comment: the distance vanishes almost surely, so the first tail variable agrees with
    -- `X 0` almost surely.
    filter_upwards [hdist_ae] with ω hω
    exact dist_eq_zero.mp hω
  obtain ⟨c, hc⟩ :=
    exists_dirac_of_indepFun_identDistrib_ae_eq
      (hX_iid.identDistrib 1 0)
      (hX_iid.iIndepFun.indepFun (by norm_num : (1 : ℕ) ≠ 0))
      hX1_eq_X0
  exact h_nontrivial ⟨c, (hX_iid.identDistrib 1 0).map_eq.symm.trans hc⟩

end
