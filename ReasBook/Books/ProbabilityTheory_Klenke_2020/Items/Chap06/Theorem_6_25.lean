/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Definition_6_8

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Helper for Theorem 6.25: a sequence that is Cauchy in the canonical `L¹` seminorm has a
limit in the chapter's owner notion `TendstoInMean`. -/
private lemma l1_cauchy_has_tendstoInMean (fSeq : ℕ → Ω → ℝ)
    (h_memL1 : ∀ n, Integrable (fSeq n) μ)
    (h_cauchy :
      Tendsto (fun n : ℕ × ℕ ↦ eLpNorm (fSeq n.1 - fSeq n.2) 1 μ) atTop (𝓝 0)) :
    ∃ f : Ω → ℝ, TendstoInMean μ fSeq f := by
  let fLp : ℕ → Lp ℝ 1 μ := fun n ↦ (memLp_one_iff_integrable.2 (h_memL1 n)).toLp (fSeq n)
  have h_pairwise_eq :
      (fun n : ℕ × ℕ ↦ eLpNorm (⇑(fLp n.1) - ⇑(fLp n.2)) 1 μ) =
        fun n : ℕ × ℕ ↦ eLpNorm (fSeq n.1 - fSeq n.2) 1 μ := by
    funext n
    apply eLpNorm_congr_ae
    filter_upwards
      [(memLp_one_iff_integrable.2 (h_memL1 n.1)).coeFn_toLp,
        (memLp_one_iff_integrable.2 (h_memL1 n.2)).coeFn_toLp] with x hx₁ hx₂
    simp [fLp, hx₁, hx₂]
  haveI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  have hLp_cauchy : CauchySeq fLp := by
    exact (Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm fLp).2 <| by
      simpa only [h_pairwise_eq] using h_cauchy
  obtain ⟨fLpLim, hLp_tendsto⟩ := cauchySeq_tendsto_of_complete hLp_cauchy
  let f : Ω → ℝ := fLpLim
  have hf_memLp : MemLp f 1 μ := Lp.memLp fLpLim
  have hf_integrable : Integrable f μ := memLp_one_iff_integrable.1 hf_memLp
  have h_tendsto_toLp :
      Tendsto (fun n ↦ (memLp_one_iff_integrable.2 (h_memL1 n)).toLp (fSeq n)) atTop
        (𝓝 (hf_memLp.toLp f)) := by
    simpa [f] using hLp_tendsto
  have h_tendsto_norm :
      Tendsto (fun n ↦ eLpNorm (fSeq n - f) 1 μ) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fSeq
      (fun n ↦ memLp_one_iff_integrable.2 (h_memL1 n)) f hf_memLp).1 h_tendsto_toLp
  exact ⟨f, (tendstoInMean_iff).2 ⟨h_memL1, hf_integrable, h_tendsto_norm⟩⟩

/-- Helper for Theorem 6.25: convergence in mean yields convergence in `μ`-measure together with
the canonical owner predicate `UniformIntegrable`. -/
private lemma tendstoInMean_yields_limit_in_measure_and_uniformIntegrable
    [IsFiniteMeasure μ] (fSeq : ℕ → Ω → ℝ) {f : Ω → ℝ} (h_mean : TendstoInMean μ fSeq f) :
    ∃ g : Ω → ℝ, TendstoInMeasure μ fSeq atTop g ∧ UniformIntegrable fSeq 1 μ := by
  have h_memL1 : ∀ n, Integrable (fSeq n) μ := h_mean.integrableSeq
  have hf_integrable : Integrable f μ := h_mean.integrable
  have h_tendsto_L1 :
      Tendsto (fun n ↦ eLpNorm (fSeq n - f) 1 μ) atTop (𝓝 0) := h_mean.tendsto_eLpNorm
  have h_tendsto_measure : TendstoInMeasure μ fSeq atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (fun n ↦ (h_mean.memLpSeq n).aestronglyMeasurable)
      h_mean.memLp.aestronglyMeasurable h_tendsto_L1
  have h_memLpSeq : ∀ n, MemLp (fSeq n) 1 μ := fun n ↦ memLp_one_iff_integrable.2 (h_memL1 n)
  have hf_memLp : MemLp f 1 μ := memLp_one_iff_integrable.2 hf_integrable
  have h_unif : UnifIntegrable fSeq 1 μ :=
    unifIntegrable_of_tendsto_Lp le_rfl ENNReal.one_ne_top h_memLpSeq hf_memLp h_tendsto_L1
  have h_eventually_small :
      ∀ᶠ n in atTop, eLpNorm (fSeq n - f) 1 μ ≤ 1 := by
    exact (ENNReal.tendsto_nhds_zero.1 h_tendsto_L1) 1 zero_lt_one
  obtain ⟨N, hN_tail⟩ := Filter.eventually_atTop.mp h_eventually_small
  let Cprefix : NNReal := Finset.sum (Finset.range N) fun i ↦ (eLpNorm (fSeq i) 1 μ).toNNReal
  let Clim : NNReal := (1 : NNReal) + (eLpNorm f 1 μ).toNNReal
  have h_bound : ∀ n, eLpNorm (fSeq n) 1 μ ≤ max Cprefix Clim := by
    intro n
    by_cases hn : n < N
    · have h_mem : n ∈ Finset.range N := Finset.mem_range.2 hn
      have h_le : (eLpNorm (fSeq n) 1 μ).toNNReal ≤ max Cprefix Clim := by
        refine le_trans ?_ (le_max_left _ _)
        have h_prefix :
            (eLpNorm (fSeq n) 1 μ).toNNReal ≤
              Finset.sum (Finset.range N) fun i ↦ (eLpNorm (fSeq i) 1 μ).toNNReal := by
          let term : ℕ → NNReal := fun i ↦ (eLpNorm (fSeq i) 1 μ).toNNReal
          have h_prefix' : term n ≤ Finset.sum (Finset.range N) term := by
            exact Finset.single_le_sum (fun _ _ ↦ by exact zero_le _) h_mem
          simpa [term] using h_prefix'
        simpa [Cprefix] using h_prefix
      have h_eq :
          ((eLpNorm (fSeq n) 1 μ).toNNReal : ℝ≥0∞) = eLpNorm (fSeq n) 1 μ := by
        exact ENNReal.coe_toNNReal ((h_memLpSeq n).eLpNorm_lt_top).ne
      calc
        eLpNorm (fSeq n) 1 μ = ((eLpNorm (fSeq n) 1 μ).toNNReal : ℝ≥0∞) := h_eq.symm
        _ ≤ max Cprefix Clim := by
          exact_mod_cast h_le
    · have h_tail : eLpNorm (fSeq n - f) 1 μ ≤ 1 := hN_tail n (Nat.le_of_not_lt hn)
      have h_triangle :
          eLpNorm (fSeq n) 1 μ ≤ eLpNorm (fSeq n - f) 1 μ + eLpNorm f 1 μ := by
        simpa [sub_eq_add_neg, add_assoc] using
          (eLpNorm_add_le
            ((h_memL1 n).aestronglyMeasurable.sub hf_integrable.aestronglyMeasurable)
            hf_integrable.aestronglyMeasurable le_rfl :
            eLpNorm ((fSeq n - f) + f) 1 μ ≤
              eLpNorm (fSeq n - f) 1 μ + eLpNorm f 1 μ)
      calc
        eLpNorm (fSeq n) 1 μ ≤ eLpNorm (fSeq n - f) 1 μ + eLpNorm f 1 μ := h_triangle
        _ ≤ 1 + eLpNorm f 1 μ := add_le_add h_tail le_rfl
        _ = (Clim : ℝ≥0∞) := by
          simp [Clim, ENNReal.coe_add, ENNReal.coe_toNNReal hf_memLp.eLpNorm_lt_top.ne,
            add_comm]
        _ ≤ max Cprefix Clim := by
          exact_mod_cast le_max_right Cprefix Clim
  refine ⟨f, h_tendsto_measure, ?_⟩
  exact ⟨fun n ↦ (h_memL1 n).aestronglyMeasurable, h_unif, ⟨max Cprefix Clim, h_bound⟩⟩

-- Proof sketch: clauses `(i)` and `(ii)` are the canonical `L¹` completeness statement. The
-- source-facing clause `(iii)` is the textbook global convergence-in-measure condition together
-- with canonical uniform integrability, so the theorem belongs on a finite measure space, where
-- the owner theorem
-- `tendstoInMeasure_iff_tendsto_Lp_finite` applies directly.
/-- Theorem 6.25: on a finite measure space, for a sequence of real-valued `L¹(μ)` functions,
the following are equivalent:
(i) convergence in mean, namely `TendstoInMean μ fSeq f` for some limit `f`;
(ii) the canonical `L¹(μ)`-Cauchy condition
`eLpNorm (fₙ - fₘ) 1 μ → 0` as `n, m → ∞`; and
(iii) convergence in `μ`-measure to some limit together with `UniformIntegrable`. -/
theorem integrable_sequence_tfae_tendstoInL1_cauchy_uniformIntegrable_tendstoInMeasure
    [IsFiniteMeasure μ] (fSeq : ℕ → Ω → ℝ) (h_memL1 : ∀ n, Integrable (fSeq n) μ) :
    List.TFAE
      [ ∃ f : Ω → ℝ, TendstoInMean μ fSeq f
      , Tendsto (fun n : ℕ × ℕ ↦ eLpNorm (fSeq n.1 - fSeq n.2) 1 μ) atTop (𝓝 0)
      , ∃ f : Ω → ℝ, TendstoInMeasure μ fSeq atTop f ∧ UniformIntegrable fSeq 1 μ
      ] := by
  tfae_have 1 → 2 := by
    rintro ⟨f, h_mean⟩
    have hf_memLp : MemLp f 1 μ := memLp_one_iff_integrable.2 h_mean.integrable
    haveI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
    let g : ℕ → Lp ℝ 1 μ := fun n ↦ (h_mean.memLpSeq n).toLp (fSeq n)
    let gLim : Lp ℝ 1 μ := hf_memLp.toLp f
    have h_pairwise_eq :
        (fun n : ℕ × ℕ ↦ eLpNorm (⇑(g n.1) - ⇑(g n.2)) 1 μ) =
          fun n : ℕ × ℕ ↦ eLpNorm (fSeq n.1 - fSeq n.2) 1 μ := by
      funext n
      apply eLpNorm_congr_ae
      filter_upwards [h_mean.memLpSeq n.1 |>.coeFn_toLp, h_mean.memLpSeq n.2 |>.coeFn_toLp] with
        x hx₁ hx₂
      simp [g, hx₁, hx₂]
    have h_tendsto_Lp : Tendsto g atTop (𝓝 gLim) := by
      exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fSeq h_mean.memLpSeq f hf_memLp).2
        h_mean.tendsto_eLpNorm
    have h_cauchy : CauchySeq g := h_tendsto_Lp.cauchy_map
    simpa only [h_pairwise_eq] using (Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm g).1 h_cauchy
  tfae_have 2 → 1 := by
    intro h_cauchy
    exact l1_cauchy_has_tendstoInMean fSeq h_memL1 h_cauchy
  tfae_have 1 → 3 := by
    rintro ⟨f, h_mean⟩
    exact tendstoInMean_yields_limit_in_measure_and_uniformIntegrable fSeq h_mean
  tfae_have 3 → 1 := by
    rintro ⟨f, h_tendsto_measure, h_uniform⟩
    have hf_integrable : Integrable f μ :=
      h_uniform.integrable_of_tendstoInMeasure h_tendsto_measure
    have h_tendsto_L1 :
        Tendsto (fun n ↦ eLpNorm (fSeq n - f) 1 μ) atTop (𝓝 0) :=
      (tendstoInMeasure_iff_tendsto_Lp_finite le_rfl ENNReal.one_ne_top
        (fun n ↦ memLp_one_iff_integrable.2 (h_memL1 n))
        (memLp_one_iff_integrable.2 hf_integrable)).1
        ⟨h_tendsto_measure, h_uniform.unifIntegrable⟩
    exact ⟨f, (tendstoInMean_iff).2 ⟨h_memL1, hf_integrable, h_tendsto_L1⟩⟩
  tfae_finish

-- Proof sketch: `L¹` convergence implies convergence in measure by
-- `tendstoInMeasure_of_tendsto_eLpNorm`, and limits in measure are a.e.-unique by
-- `tendstoInMeasure_ae_unique`.
/-- If a real-valued `L¹(μ)` sequence converges in mean to `f` and in `μ`-measure to `g`, then the
two limits coincide almost everywhere. In particular, the limits in clauses `(i)` and `(iii)` of
Theorem 6.25 agree `μ`-a.e. -/
theorem ae_eq_of_tendstoInMean_and_tendstoInMeasure
    {fSeq : ℕ → Ω → ℝ} {f g : Ω → ℝ}
    (h_mean : TendstoInMean μ fSeq f)
    (h_tendsto_measure : TendstoInMeasure μ fSeq atTop g) :
    f =ᵐ[μ] g := by
  have h_tendsto_measure_f : TendstoInMeasure μ fSeq atTop f := by
    exact tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (fun n ↦ (h_mean.memLpSeq n).aestronglyMeasurable)
      h_mean.memLp.aestronglyMeasurable h_mean.tendsto_eLpNorm
  exact tendstoInMeasure_ae_unique h_tendsto_measure_f h_tendsto_measure
