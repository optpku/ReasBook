/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

private theorem unifTight_one_of_dominated
    {fSeq : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hg_integrable : Integrable g μ) (h_dom : ∀ n, ∀ᵐ x ∂μ, ‖fSeq n x‖ ≤ g x) :
    UnifTight fSeq 1 μ := by
  have hg_memLp : MemLp g 1 μ := memLp_one_iff_integrable.mpr hg_integrable
  have hg_tight : UnifTight (fun _ : ℕ ↦ g) 1 μ := unifTight_const ENNReal.one_ne_top hg_memLp
  intro ε hε
  obtain ⟨s, hμs, hs⟩ := hg_tight hε
  refine ⟨s, hμs, fun n ↦ ?_⟩
  have hle : ∀ᵐ x ∂μ, ‖sᶜ.indicator (fSeq n) x‖ ≤ sᶜ.indicator g x := by
    filter_upwards [h_dom n] with x hx
    by_cases hsx : x ∈ sᶜ
    · simp [Set.indicator_of_mem hsx]
      simpa [Real.norm_eq_abs] using hx
    · simp [Set.indicator_of_notMem hsx]
  exact (eLpNorm_mono_ae_real hle).trans (hs n)

private theorem uniformIntegrable_one_of_dominated
    {fSeq : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hfSeq_integrable : ∀ n, Integrable (fSeq n) μ)
    (hg_integrable : Integrable g μ) (h_dom : ∀ n, ∀ᵐ x ∂μ, ‖fSeq n x‖ ≤ g x) :
    UniformIntegrable fSeq 1 μ := by
  have hg_memLp : MemLp g 1 μ := memLp_one_iff_integrable.mpr hg_integrable
  refine ⟨fun n ↦ (hfSeq_integrable n).aestronglyMeasurable,
    ?_, ?_⟩
  · have hg_unif : UnifIntegrable (fun _ : ℕ ↦ g) 1 μ :=
      unifIntegrable_const le_rfl ENNReal.one_ne_top hg_memLp
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := hg_unif hε
    refine ⟨δ, hδpos, fun n s hs hμs ↦ ?_⟩
    have hle : ∀ᵐ x ∂μ, ‖s.indicator (fSeq n) x‖ ≤ s.indicator g x := by
      filter_upwards [h_dom n] with x hx
      by_cases hsx : x ∈ s
      · simp [Set.indicator_of_mem hsx]
        simpa [Real.norm_eq_abs] using hx
      · simp [Set.indicator_of_notMem hsx]
    exact (eLpNorm_mono_ae_real hle).trans (hδ n s hs hμs)
  refine ⟨(eLpNorm g 1 μ).toNNReal, fun n ↦ ?_⟩
  refine (eLpNorm_mono_ae_real (h_dom n)).trans ?_
  exact le_of_eq (ENNReal.coe_toNNReal hg_memLp.2.ne).symm

/-- Corollary 6.26: if an `L¹` sequence `(fₙ)` converges in measure to `f` and is dominated almost
everywhere in norm by an integrable function `g`, then `f` is integrable and `fₙ` converges to `f`
in `L¹`. -/
theorem dominated_convergence_in_measure_in_L1
    {f : Ω → ℝ} {fSeq : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hfSeq_integrable : ∀ n, Integrable (fSeq n) μ)
    (h_tendsto : TendstoInMeasure μ fSeq atTop f) (hg_integrable : Integrable g μ)
    (h_dom : ∀ n, ∀ᵐ x ∂μ, ‖fSeq n x‖ ≤ g x) :
    Integrable f μ ∧ Tendsto (fun n ↦ eLpNorm (fSeq n - f) 1 μ) atTop (nhds 0) := by
  have h_uniform : UniformIntegrable fSeq 1 μ :=
    uniformIntegrable_one_of_dominated hfSeq_integrable hg_integrable h_dom
  have h_tight : UnifTight fSeq 1 μ := unifTight_one_of_dominated hg_integrable h_dom
  have hf_integrable : Integrable f μ :=
    h_uniform.integrable_of_tendstoInMeasure h_tendsto
  refine ⟨hf_integrable, ?_⟩
  exact tendsto_Lp_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    h_uniform.aestronglyMeasurable
    (memLp_one_iff_integrable.mpr hf_integrable)
    h_uniform.unifIntegrable h_tight
    h_tendsto

-- Proof sketch: use `dominated_convergence_in_measure_in_L1` to get `L¹` convergence, then apply
-- continuity of the Bochner integral with respect to `L¹` convergence.
/-- Under the hypotheses of `dominated_convergence_in_measure_in_L1`, the integrals of `fₙ`
converge to the integral of `f`. -/
theorem tendsto_integral_of_tendstoInMeasure_of_dominated
    {f : Ω → ℝ} {fSeq : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hfSeq_integrable : ∀ n, Integrable (fSeq n) μ)
    (h_tendsto : TendstoInMeasure μ fSeq atTop f) (hg_integrable : Integrable g μ)
    (h_dom : ∀ n, ∀ᵐ x ∂μ, ‖fSeq n x‖ ≤ g x) :
    Tendsto (fun n ↦ ∫ x, fSeq n x ∂μ) atTop (nhds (∫ x, f x ∂μ)) := by
  obtain ⟨hf_integrable, hL1⟩ :=
    dominated_convergence_in_measure_in_L1 hfSeq_integrable h_tendsto hg_integrable h_dom
  exact tendsto_integral_of_L1' f hf_integrable (Filter.Eventually.of_forall hfSeq_integrable) hL1
