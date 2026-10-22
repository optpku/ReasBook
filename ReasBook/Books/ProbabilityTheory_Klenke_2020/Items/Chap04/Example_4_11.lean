/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap04.Definition_4_7

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]

/-- Helper for Example 4.11: on a discrete measurable space with canonical weighted counting
measure `Measure.count.withDensity α`, an `EReal`-valued function is integrable if and only if the
weighted absolute-value series `∑' ω, |f ω| α ω` is finite. -/
theorem weightedDiscreteMeasure_integrable_iff {f : Ω → EReal} (α : Ω → ℝ≥0∞) :
    erealIntegrable f (Measure.count.withDensity α) ↔
      (∑' ω, (f ω).abs * α ω) < ⊤ := by
  rw [erealIntegrable, hasFiniteIntegral_def,
    lintegral_withDensity_eq_lintegral_mul _ Measurable.of_discrete
    Measurable.of_discrete,
    lintegral_count]
  simpa [mul_comm] using
    (and_iff_right (show Measurable f from Measurable.of_discrete))

-- Proof sketch: expand `erealIntegral` into the difference of the lower integrals of the positive
-- and negative parts, compute each lower integral on `Measure.count.withDensity α` as a weighted
-- series over the atoms, and recombine the resulting series into the weighted sum of the values.
/-- Helper for Example 4.11: each weighted atomic summand has the expected positive-minus-negative
real decomposition after applying `EReal.toReal`. -/
lemma weightedDiscreteSummandToReal {f : Ω → EReal} (α : Ω → ℝ≥0∞) (ω : Ω) :
    (((α ω : EReal) * f ω).toReal) =
      (((f ω).toENNReal * α ω).toReal - (((-f ω).toENNReal * α ω).toReal)) := by
  -- Split the extended real value into its nonnegative and negative branches.
  cases f ω using EReal.recENNReal with
  | coe x =>
      -- On the nonnegative branch, the negative part vanishes.
      have hx_nonneg : 0 ≤ x.toReal := ENNReal.toReal_nonneg
      have hzero : ENNReal.ofReal (-x.toReal) = 0 := by
        exact ENNReal.ofReal_eq_zero.2 (by linarith [hx_nonneg])
      simpa [EReal.toReal_mul, ENNReal.toReal_mul, hzero, mul_comm]
  | neg_coe x hx =>
      -- On the strictly negative branch, the positive part vanishes.
      have hx_nonneg : 0 ≤ x.toReal := ENNReal.toReal_nonneg
      have hzero : ENNReal.ofReal (-x.toReal) = 0 := by
        exact ENNReal.ofReal_eq_zero.2 (by linarith [hx_nonneg])
      simpa [EReal.toReal_mul, ENNReal.toReal_mul, hzero, sub_eq_add_neg, mul_comm]

/-- Helper for Example 4.11: finiteness of the weighted absolute-value series forces each weighted
atomic summand `α ω * f ω` to be finite. -/
lemma weightedDiscreteSummandFinite {f : Ω → EReal} (α : Ω → ℝ≥0∞)
    (habs : (∑' ω, (f ω).abs * α ω) < ⊤) (ω : Ω) :
    (α ω * f ω) ≠ ⊤ ∧ (α ω * f ω) ≠ ⊥ := by
  have hω_le : (f ω).abs * α ω ≤ ∑' ω', (f ω').abs * α ω' :=
    ENNReal.le_tsum ω
  have hω_lt : (f ω).abs * α ω < ⊤ :=
    lt_of_le_of_lt hω_le habs
  have hαabs : ((α ω : EReal).abs) = α ω := by
    cases α ω using ENNReal.recTopCoe with
    | top =>
        simp
    | coe a =>
        change ENNReal.ofReal |(a : ℝ)| = (a : ℝ≥0∞)
        simpa [abs_of_nonneg a.2] using (ENNReal.ofReal_coe_nnreal (p := a))
  have habs_weighted : (α ω * f ω).abs < ⊤ := by
    calc
      (α ω * f ω).abs = ((α ω : EReal).abs) * (f ω).abs := EReal.abs_mul _ _
      _ = α ω * (f ω).abs := by rw [hαabs]
      _ = (f ω).abs * α ω := by rw [mul_comm]
      _ < ⊤ := hω_lt
  constructor
  · intro htop
    simpa [htop] using habs_weighted
  · intro hbot
    simpa [hbot] using habs_weighted

/-- Helper for Example 4.11: the weighted `EReal` series is the coercion of the series of the real
parts of its finite atomic summands. -/
lemma weightedDiscreteTsum_eq_coe_tsumToReal {f : Ω → EReal} (α : Ω → ℝ≥0∞)
    (habs : (∑' ω, (f ω).abs * α ω) < ⊤) :
    (∑' ω, α ω * f ω) = ((∑' ω, (((α ω : EReal) * f ω).toReal) : ℝ) : EReal) := by
  let s : Ω → ℝ := fun ω ↦ (((α ω : EReal) * f ω).toReal)
  let positivePart : Ω → ℝ := fun ω ↦ (((f ω).toENNReal * α ω).toReal)
  let negativePart : Ω → ℝ := fun ω ↦ (((-f ω).toENNReal * α ω).toReal)
  have hpositive_ne_top : ∑' ω, (f ω).toENNReal * α ω ≠ ⊤ := by
    have hfinite := (weightedDiscreteMeasure_integrable_iff α).2 habs
    have hfinite_pos : ∫⁻ ω, (f ω).toENNReal ∂Measure.count.withDensity α ≠ ∞ := by
      simpa [hasFiniteIntegral_def] using hfinite.hasFiniteIntegral_toENNReal.ne
    rw [lintegral_withDensity_eq_lintegral_mul _ Measurable.of_discrete Measurable.of_discrete,
      lintegral_count] at hfinite_pos
    simpa [mul_comm] using hfinite_pos
  have hnegative_ne_top : ∑' ω, (-f ω).toENNReal * α ω ≠ ⊤ := by
    have hfinite := (weightedDiscreteMeasure_integrable_iff α).2 habs
    have hfinite_neg : ∫⁻ ω, (-f ω).toENNReal ∂Measure.count.withDensity α ≠ ∞ := by
      simpa [hasFiniteIntegral_def] using hfinite.hasFiniteIntegral_neg_toENNReal.ne
    rw [lintegral_withDensity_eq_lintegral_mul _ Measurable.of_discrete Measurable.of_discrete,
      lintegral_count] at hfinite_neg
    simpa [mul_comm] using hfinite_neg
  have hs_positive : Summable positivePart := by
    simpa [positivePart] using ENNReal.summable_toReal hpositive_ne_top
  have hs_negative : Summable negativePart := by
    simpa [negativePart] using ENNReal.summable_toReal hnegative_ne_top
  have hs_eq : s = fun ω ↦ positivePart ω - negativePart ω := by
    funext ω
    -- Rewrite each summand to the positive-minus-negative decomposition.
    simpa [s, positivePart, negativePart] using weightedDiscreteSummandToReal α ω
  have hs_summable : Summable s := by
    -- The real summands are summable because both positive and negative parts are.
    rw [hs_eq]
    exact hs_positive.sub hs_negative
  have hs_coe :
      ((∑' ω, s ω : ℝ) : EReal) = ∑' ω, (s ω : EReal) := by
    -- Transport the convergent real series across the continuous real embedding into `EReal`.
    let coeAddHom : ℝ →+ EReal :=
      { toFun := fun r ↦ (r : EReal)
        map_zero' := by simp
        map_add' := fun x y ↦ by simp }
    simpa [s] using
      hs_summable.map_tsum coeAddHom continuous_coe_real_ereal
  have hterm : ∀ ω, (s ω : EReal) = α ω * f ω := by
    intro ω
    rcases weightedDiscreteSummandFinite α habs ω with ⟨htop, hbot⟩
    -- Each term is finite, so coercing its `toReal` value recovers the original summand.
    simpa [s] using (EReal.coe_toReal htop hbot)
  calc
    (∑' ω, α ω * f ω) = ∑' ω, (s ω : EReal) := by
      refine tsum_congr ?_
      intro ω
      symm
      exact hterm ω
    _ = ((∑' ω, s ω : ℝ) : EReal) := hs_coe.symm
    _ = ((∑' ω, (((α ω : EReal) * f ω).toReal) : ℝ) : EReal) := by
      simp [s]

/-- Helper for Example 4.11: applying `EReal.toReal` to the weighted atomic series commutes with
the sum once the weighted absolute-value series is finite. -/
lemma weightedDiscreteTsum_toReal {f : Ω → EReal} (α : Ω → ℝ≥0∞)
    (habs : (∑' ω, (f ω).abs * α ω) < ⊤) :
    (∑' ω, α ω * f ω).toReal = ∑' ω, (((α ω : EReal) * f ω).toReal) := by
  -- First express the `EReal` series as the coercion of a real series, then apply `toReal`.
  simpa using congrArg EReal.toReal (weightedDiscreteTsum_eq_coe_tsumToReal α habs)

/-- Example 4.11: for the canonical weighted counting measure `Measure.count.withDensity α`, the
textbook extended-real integral equals the weighted sum of the atomic values whenever `f` is
integrable. -/
theorem weightedDiscreteMeasure_erealIntegral_eq_tsum {f : Ω → EReal} (α : Ω → ℝ≥0∞)
    (hf : erealIntegrable f (Measure.count.withDensity α)) :
    erealIntegral f (Measure.count.withDensity α) hf.defined =
      ∑' ω, α ω * f ω := by
  let μ : Measure Ω := Measure.count.withDensity α
  have habs : (∑' ω, (f ω).abs * α ω) < ⊤ :=
    (weightedDiscreteMeasure_integrable_iff α).1 hf
  have hpositiveIntegral_ne_top : ∫⁻ ω, (f ω).toENNReal ∂μ ≠ ∞ := by
    simpa [μ, hasFiniteIntegral_def] using hf.hasFiniteIntegral_toENNReal.ne
  have hnegativeIntegral_ne_top : ∫⁻ ω, (-f ω).toENNReal ∂μ ≠ ∞ := by
    simpa [μ, hasFiniteIntegral_def] using hf.hasFiniteIntegral_neg_toENNReal.ne
  have hpositive_ne_top : ∑' ω, (f ω).toENNReal * α ω ≠ ⊤ := by
    have hfinite_pos : ∫⁻ ω, (f ω).toENNReal ∂μ ≠ ∞ := by
      simpa [μ, hasFiniteIntegral_def] using hf.hasFiniteIntegral_toENNReal.ne
    rw [lintegral_withDensity_eq_lintegral_mul _ Measurable.of_discrete Measurable.of_discrete,
      lintegral_count] at hfinite_pos
    simpa [mul_comm] using hfinite_pos
  have hnegative_ne_top : ∑' ω, (-f ω).toENNReal * α ω ≠ ⊤ := by
    have hfinite_neg : ∫⁻ ω, (-f ω).toENNReal ∂μ ≠ ∞ := by
      simpa [μ, hasFiniteIntegral_def] using hf.hasFiniteIntegral_neg_toENNReal.ne
    rw [lintegral_withDensity_eq_lintegral_mul _ Measurable.of_discrete Measurable.of_discrete,
      lintegral_count] at hfinite_neg
    simpa [mul_comm] using hfinite_neg
  lift (∫⁻ ω, (f ω).toENNReal ∂μ) to NNReal using hpositiveIntegral_ne_top with p hp
  lift (∫⁻ ω, (-f ω).toENNReal ∂μ) to NNReal using hnegativeIntegral_ne_top with q hq
  have hleft_realized :
      erealIntegral f μ hf.defined = (((p : ℝ) - (q : ℝ)) : EReal) := by
    -- Integrability makes both positive and negative parts finite, so the integral is a real.
    rw [erealIntegral_spec, ← hp, ← hq]
    rfl
  have hleft_ne_top : erealIntegral f μ hf.defined ≠ ⊤ := by
    rw [hleft_realized, sub_eq_add_neg]
    exact EReal.add_ne_top (by simp) (by simp)
  have hleft_ne_bot : erealIntegral f μ hf.defined ≠ ⊥ := by
    rw [hleft_realized, sub_eq_add_neg]
    exact (EReal.add_ne_bot_iff).2 ⟨by simp, by simp⟩
  have hright_eq_coe :
      (∑' ω, α ω * f ω) = ((∑' ω, (((α ω : EReal) * f ω).toReal) : ℝ) : EReal) :=
    weightedDiscreteTsum_eq_coe_tsumToReal α habs
  have hright_ne_top : (∑' ω, α ω * f ω) ≠ ⊤ := by
    rw [hright_eq_coe]
    simp
  have hright_ne_bot : (∑' ω, α ω * f ω) ≠ ⊥ := by
    rw [hright_eq_coe]
    simp
  have hleft_toReal :
      (erealIntegral f μ hf.defined).toReal =
        (∑' ω, (((α ω : EReal) * f ω).toReal) : ℝ) := by
    -- Expand the textbook integral into the weighted positive and negative part series.
    have hpositiveEReal_ne_top :
        (((∫⁻ ω, (f ω).toENNReal ∂μ) : ENNReal) : EReal) ≠ ⊤ := by
      simpa using (show ∫⁻ ω, (f ω).toENNReal ∂μ ≠ ∞ by
        simpa [μ, hasFiniteIntegral_def] using hf.hasFiniteIntegral_toENNReal.ne)
    have hnegativeEReal_ne_top :
        (((∫⁻ ω, (-f ω).toENNReal ∂μ) : ENNReal) : EReal) ≠ ⊤ := by
      simpa using (show ∫⁻ ω, (-f ω).toENNReal ∂μ ≠ ∞ by
        simpa [μ, hasFiniteIntegral_def] using hf.hasFiniteIntegral_neg_toENNReal.ne)
    rw [erealIntegral_spec,
      EReal.toReal_sub hpositiveEReal_ne_top (by simp) hnegativeEReal_ne_top (by simp)]
    rw [lintegral_withDensity_eq_lintegral_mul _ Measurable.of_discrete Measurable.of_discrete,
      lintegral_withDensity_eq_lintegral_mul _ Measurable.of_discrete Measurable.of_discrete,
      lintegral_count, lintegral_count]
    simp only [EReal.toReal_coe_ennreal, Pi.mul_apply]
    have hpositive_tsum_toReal :
        (∑' ω, α ω * (f ω).toENNReal).toReal =
          ∑' ω, (α ω * (f ω).toENNReal).toReal :=
      ENNReal.tsum_toReal_eq fun ω ↦ by
        simpa [mul_comm] using ENNReal.ne_top_of_tsum_ne_top hpositive_ne_top ω
    have hnegative_tsum_toReal :
        (∑' ω, α ω * (-f ω).toENNReal).toReal =
          ∑' ω, (α ω * (-f ω).toENNReal).toReal :=
      ENNReal.tsum_toReal_eq fun ω ↦ by
        simpa [mul_comm] using ENNReal.ne_top_of_tsum_ne_top hnegative_ne_top ω
    rw [hpositive_tsum_toReal, hnegative_tsum_toReal]
    have hs_positive :
        Summable (fun ω ↦ ((α ω * (f ω).toENNReal).toReal : ℝ)) := by
      simpa [mul_comm] using ENNReal.summable_toReal hpositive_ne_top
    have hs_negative :
        Summable (fun ω ↦ ((α ω * (-f ω).toENNReal).toReal : ℝ)) := by
      simpa [mul_comm] using ENNReal.summable_toReal hnegative_ne_top
    rw [← hs_positive.tsum_sub hs_negative]
    refine tsum_congr ?_
    intro ω
    simpa [mul_comm] using (weightedDiscreteSummandToReal α ω).symm
  -- Route correction: rather than canceling `EReal` series directly, compare finite values via
  -- `toReal`, then use `EReal.coe_toReal` to return to `EReal`.
  calc
    erealIntegral f μ hf.defined = ((erealIntegral f μ hf.defined).toReal : EReal) := by
      exact (EReal.coe_toReal hleft_ne_top hleft_ne_bot).symm
    _ = ((∑' ω, (((α ω : EReal) * f ω).toReal) : ℝ) : EReal) := by
      exact congrArg (fun r : ℝ ↦ (r : EReal)) hleft_toReal
    _ = (((∑' ω, α ω * f ω).toReal : ℝ) : EReal) := by
      exact congrArg (fun r : ℝ ↦ (r : EReal)) (weightedDiscreteTsum_toReal α habs).symm
    _ = ∑' ω, α ω * f ω := by
      exact EReal.coe_toReal hright_ne_top hright_ne_bot
