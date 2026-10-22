/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap04.Definition_4_7

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Theorem 4.20: an almost-everywhere monotone sequence stays below its almost-
everywhere limit at every fixed index, in particular at `0`. -/
private theorem ae_le_limit_of_ae_monotone_tendsto
    (μ : Measure Ω) {fSeq : ℕ → Ω → EReal} {f : Ω → EReal}
    (h_mono : ∀ᵐ ω ∂μ, Monotone fun n ↦ fSeq n ω)
    (h_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω))) :
    fSeq 0 ≤ᵐ[μ] f := by
  -- On the good set, monotonicity and convergence force each fixed term below the limit.
  filter_upwards [h_mono, h_tendsto] with ω hω_mono hω_tendsto
  simpa using hω_mono.ge_of_tendsto hω_tendsto 0

/-- Helper for Theorem 4.20: the monotone limit has finite negative part because `fSeq 0`
provides an integrable lower bound. -/
private theorem hasFiniteIntegral_neg_toENNReal_of_monotone_convergence
    (μ : Measure Ω) {fSeq : ℕ → Ω → EReal} {f : Ω → EReal}
    (hfSeq : ∀ n, erealIntegrable (fSeq n) μ)
    (h_mono : ∀ᵐ ω ∂μ, Monotone fun n ↦ fSeq n ω)
    (h_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω))) :
    HasFiniteIntegral (fun ω ↦ (-f ω).toENNReal) μ := by
  -- Compare the negative part of the limit against the already integrable negative part of `fSeq 0`.
  have hle : fSeq 0 ≤ᵐ[μ] f :=
    ae_le_limit_of_ae_monotone_tendsto μ h_mono h_tendsto
  have hneg_seq0 : HasFiniteIntegral (fun ω ↦ (-fSeq 0 ω).toENNReal) μ :=
    (hfSeq 0).hasFiniteIntegral_neg_toENNReal
  rw [hasFiniteIntegral_def] at hneg_seq0 ⊢
  have hneg_mono : ∀ᵐ ω ∂μ, (-f ω).toENNReal ≤ (-fSeq 0 ω).toENNReal :=
    hle.mono fun ω hω ↦
      EReal.toENNReal_le_toENNReal <| by
        simpa using EReal.neg_le_neg_iff.2 hω
  exact lt_of_le_of_lt (lintegral_mono_ae hneg_mono) hneg_seq0

private theorem erealIntegralDefined_of_monotone_convergence
    (μ : Measure Ω) {fSeq : ℕ → Ω → EReal} {f : Ω → EReal}
    (hfSeq : ∀ n, erealIntegrable (fSeq n) μ)
    (hf : Measurable f)
    (h_mono : ∀ᵐ ω ∂μ, Monotone fun n ↦ fSeq n ω)
    (h_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω))) :
    erealIntegralDefined f μ := by
  -- The lower bound from `fSeq 0` keeps the negative part finite, so the textbook integral is defined.
  exact ⟨hf, Or.inr <|
    hasFiniteIntegral_neg_toENNReal_of_monotone_convergence μ hfSeq h_mono h_tendsto⟩

-- Proof sketch: subtract the first integrable term to reduce to a nonnegative increasing sequence,
-- apply the nonnegative monotone convergence theorem to the positive and negative parts in the
-- canonical extended-real integral expression, and then add back the constant term `fSeq 0`.
/-- Theorem 4.20: Beppo Levi monotone convergence for extended-real integrals. If
`fSeq n` belongs to `ℒ¹(μ)` for every `n`, `f` is measurable, and `fSeq n` increases almost
everywhere to `f`, then the textbook extended-real integrals `erealIntegral (fSeq n) μ`
converge to `erealIntegral f μ`. The limit is allowed to be `+∞`; under the hypotheses the lower
integrable bound `fSeq 0` guarantees that `erealIntegral f μ` is defined in the textbook sense. -/
theorem erealIntegral_tendsto_of_monotone_convergence
    (μ : Measure Ω) {fSeq : ℕ → Ω → EReal} {f : Ω → EReal}
    (hfSeq : ∀ n, erealIntegrable (fSeq n) μ)
    (hf : Measurable f)
    (h_mono : ∀ᵐ ω ∂μ, Monotone fun n ↦ fSeq n ω)
    (h_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω))) :
    Tendsto (fun n ↦ erealIntegral (fSeq n) μ (hfSeq n).defined) atTop
      (𝓝 (erealIntegral f μ
        (erealIntegralDefined_of_monotone_convergence μ hfSeq hf h_mono h_tendsto))) := by
  -- The limit function has a defined textbook integral because the negative part is finite.
  let hf_defined : erealIntegralDefined f μ :=
    erealIntegralDefined_of_monotone_convergence μ hfSeq hf h_mono h_tendsto
  have hneg_fin : HasFiniteIntegral (fun ω ↦ (-f ω).toENNReal) μ :=
    hasFiniteIntegral_neg_toENNReal_of_monotone_convergence μ hfSeq h_mono h_tendsto
  -- The positive parts form a nonnegative monotone sequence converging pointwise to the positive part.
  have hpos :
      Tendsto (fun n ↦ ∫⁻ ω, (fSeq n ω).toENNReal ∂μ) atTop
        (𝓝 (∫⁻ ω, (f ω).toENNReal ∂μ)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_
    · intro n
      exact (hfSeq n).1.ereal_toENNReal.aemeasurable
    · exact h_mono.mono fun ω hω_mono ↦
        fun i j hij ↦ EReal.toENNReal_le_toENNReal (hω_mono hij)
    · exact h_tendsto.mono fun ω hω_tendsto ↦
        EReal.continuous_toENNReal.continuousAt.tendsto.comp hω_tendsto
  -- Negating turns the monotone sequence into an antitone sequence, so the negative parts converge too.
  have hneg :
      Tendsto (fun n ↦ ∫⁻ ω, (-fSeq n ω).toENNReal ∂μ) atTop
        (𝓝 (∫⁻ ω, (-f ω).toENNReal ∂μ)) := by
    refine lintegral_tendsto_of_tendsto_of_antitone ?_ ?_ ?_ ?_
    · intro n
      exact (hfSeq n).1.neg.ereal_toENNReal.aemeasurable
    · exact h_mono.mono fun ω hω_mono ↦
        fun i j hij ↦ EReal.toENNReal_le_toENNReal <| by
          simpa using EReal.neg_le_neg_iff.2 (hω_mono hij)
    · exact ne_of_lt <| by
        simpa [hasFiniteIntegral_def] using (hfSeq 0).hasFiniteIntegral_neg_toENNReal
    · exact h_tendsto.mono fun ω hω_tendsto ↦
        EReal.continuous_toENNReal.continuousAt.tendsto.comp
          (continuous_neg.continuousAt.tendsto.comp hω_tendsto)
  have hpos_ereal :
      Tendsto (fun n ↦ ((∫⁻ ω, (fSeq n ω).toENNReal ∂μ) : EReal)) atTop
        (𝓝 (((∫⁻ ω, (f ω).toENNReal ∂μ) : EReal))) := by
    simpa using EReal.tendsto_coe_ennreal.2 hpos
  have hneg_ereal :
      Tendsto (fun n ↦ ((∫⁻ ω, (-fSeq n ω).toENNReal ∂μ) : EReal)) atTop
        (𝓝 (((∫⁻ ω, (-f ω).toENNReal ∂μ) : EReal))) := by
    simpa using EReal.tendsto_coe_ennreal.2 hneg
  have hneg_ereal_neg :
      Tendsto
        (fun n ↦ -(((∫⁻ ω, (-fSeq n ω).toENNReal ∂μ) : EReal))) atTop
        (𝓝 (-(((∫⁻ ω, (-f ω).toENNReal ∂μ) : EReal)))) := by
    exact continuous_neg.continuousAt.tendsto.comp hneg_ereal
  have hneg_limit_ne_top : (∫⁻ ω, (-f ω).toENNReal ∂μ) ≠ ⊤ := by
    exact ne_of_lt <| by
      simpa [hasFiniteIntegral_def] using hneg_fin
  -- Rewrite the textbook integral into the canonical `EReal` sum and combine both convergences.
  simp_rw [erealIntegral_spec, sub_eq_add_neg]
  exact
    (EReal.continuousAt_add
      (Or.inr <| by
        simpa [EReal.neg_eq_bot_iff] using hneg_limit_ne_top)
      (Or.inl <| by
        exact EReal.coe_ennreal_ne_bot (∫⁻ ω, (f ω).toENNReal ∂μ))).tendsto.comp
      (hpos_ereal.prodMk_nhds hneg_ereal_neg)
