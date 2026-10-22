/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Definition_7_2

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {p : ℝ≥0∞}

-- Proof sketch: interpret `fₙ` as elements of `MeasureTheory.Lp ℝ p μ` via `MemLp.toLp`,
-- use completeness of `Lp` for `1 ≤ p` to get the Cauchy-criterion direction, and express the
-- limit via the chapter's owner notion `TendstoInLp`.
/-- Theorem 7.3 (1): for `1 ≤ p ≤ ∞`, a sequence of real-valued `L^p(μ)` functions converges in
`L^p(μ)` in the sense of Definition 7.2 if and only if the associated sequence in the canonical
metric space `Lp ℝ p μ` is Cauchy. -/
theorem lp_sequence_has_lp_limit_iff_cauchy
    [Fact (1 ≤ p)] (fSeq : ℕ → Ω → ℝ) (h_memLp : ∀ n, MemLp (fSeq n) p μ) :
    (∃ f : Ω → ℝ, TendstoInLp p μ fSeq f) ↔
      CauchySeq (fun n ↦ (h_memLp n).toLp (fSeq n)) := by
  constructor
  · rintro ⟨f, h_tendsto⟩
    have h_toLp :
        (fun n ↦ (h_tendsto.memLpSeq n).toLp (fSeq n)) =
          fun n ↦ (h_memLp n).toLp (fSeq n) := by
      funext n
      exact MemLp.toLp_congr (h_tendsto.memLpSeq n) (h_memLp n) Filter.EventuallyEq.rfl
    simpa [h_toLp] using h_tendsto.tendsto_toLp.cauchySeq
  · intro h_cauchy
    obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete h_cauchy
    exact ⟨(F : Ω → ℝ), ⟨h_memLp, Lp.memLp F, by simpa using hF⟩⟩

-- Proof sketch: combine the previous Cauchy criterion with the general Vitali owner theorem
-- `tendstoInMeasure_iff_tendsto_Lp`, whose source-facing hypotheses are convergence in measure,
-- `UnifIntegrable`, and `UnifTight`.
/-- Theorem 7.3 (2): if `p < ∞`, then the following are equivalent for a real-valued `L^p(μ)`
sequence `fSeq`: (i) `fSeq` converges in `L^p(μ)`, (ii) `fSeq` is Cauchy in `L^p(μ)`, and (iii)
`fSeq` converges in `μ`-measure to an `L^p(μ)` limit and is uniformly integrable and uniformly
tight in the canonical measure-theoretic senses `UnifIntegrable` and `UnifTight`. -/
theorem lp_sequence_tfae_has_lp_limit_cauchy_uniformly_integrable_power_limit_in_measure
    [Fact (1 ≤ p)] (fSeq : ℕ → Ω → ℝ)
    (h_memLp : ∀ n, MemLp (fSeq n) p μ) (hp_top : p ≠ ∞) :
    List.TFAE
      [ ∃ f : Ω → ℝ, TendstoInLp p μ fSeq f
      , CauchySeq (fun n ↦ (h_memLp n).toLp (fSeq n))
      , ∃ f : Ω → ℝ, MemLp f p μ ∧ TendstoInMeasure μ fSeq atTop f ∧
          UnifIntegrable fSeq p μ ∧ UnifTight fSeq p μ
      ] := by
  -- Source/core/bridge triage:
  -- * source-facing: `TendstoInLp p μ fSeq f`
  -- * core/canonical owner: `MeasureTheory.Lp ℝ p μ`
  -- * bridge/view: `tendstoInMeasure_iff_tendsto_Lp`
  tfae_have 1 ↔ 2 := lp_sequence_has_lp_limit_iff_cauchy fSeq h_memLp
  tfae_have 1 → 3 := by
    rintro ⟨f, h_tendsto⟩
    exact ⟨f, h_tendsto.memLp, (tendstoInMeasure_iff_tendsto_Lp ‹Fact (1 ≤ p)›.out hp_top
      h_tendsto.memLpSeq h_tendsto.memLp).2 h_tendsto.tendsto_eLpNorm⟩
  tfae_have 3 → 1 := by
    rintro ⟨f, hf_memLp, h_meas, h_ui, h_tight⟩
    exact ⟨f, (tendstoInLp_iff_tendsto_eLpNorm).2
      ⟨h_memLp, hf_memLp, (tendstoInMeasure_iff_tendsto_Lp ‹Fact (1 ≤ p)›.out hp_top
        h_memLp hf_memLp).1 ⟨h_meas, h_ui, h_tight⟩⟩⟩
  tfae_finish

-- Proof sketch: each `L^p` convergence hypothesis implies convergence in measure by
-- `tendstoInMeasure_of_tendsto_eLpNorm`; the measure-limit is unique up to almost-everywhere
-- equality by `tendstoInMeasure_ae_unique`.
/-- Theorem 7.3 (3): if a real-valued `L^p(μ)` sequence converges in `L^p(μ)` to `f` and in
`μ`-measure to `g`, then the two limits agree almost everywhere. In particular, the limits in
clauses (i) and (iii) of Theorem 7.3 (2) coincide `μ`-a.e. -/
theorem ae_eq_of_tendstoInLp_and_tendstoInMeasure
    [Fact (1 ≤ p)] {fSeq : ℕ → Ω → ℝ} {f g : Ω → ℝ}
    (h_tendsto_lp : TendstoInLp p μ fSeq f) (h_tendsto_measure : TendstoInMeasure μ fSeq atTop g) :
    f =ᵐ[μ] g := by
  have hp_ne_zero : p ≠ 0 := (lt_of_lt_of_le zero_lt_one ‹Fact (1 ≤ p)›.out).ne'
  have h_tendsto_measure_lp : TendstoInMeasure μ fSeq atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm hp_ne_zero
      (fun n ↦ (h_tendsto_lp.memLpSeq n).aestronglyMeasurable)
      h_tendsto_lp.memLp.aestronglyMeasurable h_tendsto_lp.tendsto_eLpNorm
  exact tendstoInMeasure_ae_unique h_tendsto_measure_lp h_tendsto_measure

/-- Companion uniqueness statement: two `L^p` limits of the same sequence agree almost
everywhere. -/
theorem ae_eq_of_tendstoInLp_of_tendstoInLp
    [Fact (1 ≤ p)] {fSeq : ℕ → Ω → ℝ} {f g : Ω → ℝ}
    (h_tendsto_f : TendstoInLp p μ fSeq f) (h_tendsto_g : TendstoInLp p μ fSeq g) :
    f =ᵐ[μ] g := by
  have hp_ne_zero : p ≠ 0 := (lt_of_lt_of_le zero_lt_one ‹Fact (1 ≤ p)›.out).ne'
  exact ae_eq_of_tendstoInLp_and_tendstoInMeasure h_tendsto_f
    (tendstoInMeasure_of_tendsto_eLpNorm hp_ne_zero
      (fun n ↦ (h_tendsto_g.memLpSeq n).aestronglyMeasurable)
      h_tendsto_g.memLp.aestronglyMeasurable h_tendsto_g.tendsto_eLpNorm)
