/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E]

/-- The countable weighted sum `ω ↦ ∑' n, weights n • X n ω` of a family of measure-valued random
variables. -/
def weightedRandomMeasureSeries (weights : ℕ → NNReal)
    (X : ℕ → Ω → Measure E) : Ω → Measure E :=
  fun ω ↦ Measure.sum fun n ↦ (weights n : ENNReal) • (X n ω : Measure E)

-- Proof sketch: unfold `weightedRandomMeasureSeries` and evaluate the countable sum of measures on
-- the measurable set `A`; then use `Measure.sum_apply` and `Measure.smul_apply`.
/-- Evaluating the weighted random-measure series on a measurable set gives the corresponding
weighted series of evaluations. -/
theorem weightedRandomMeasureSeries_apply
    {Ω : Type u} {E : Type v} [MeasurableSpace E]
    (weights : ℕ → NNReal) (X : ℕ → Ω → Measure E)
    (ω : Ω) {A : Set E} (hA : MeasurableSet A) :
    weightedRandomMeasureSeries weights X ω A =
      ∑' n, (weights n : ENNReal) * (X n ω : Measure E) A := by
  -- Unfold the series of measures and evaluate the countable sum on the measurable set `A`.
  rw [weightedRandomMeasureSeries, Measure.sum_apply _ hA]
-- Each summand is a scalar multiple of a measure, so evaluation turns into scalar multiplication.
  simp only [Measure.smul_apply, smul_eq_mul]

/-- Source-facing boundedly-finite random-measure owner: a measurable `Measure E`-valued random
variable whose values are finite on every bounded measurable set almost surely. -/
def IsBoundedlyFiniteRandomMeasure
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) : Prop :=
  Measurable X ∧
    ∀ A : Set E, MeasurableSet A → Bornology.IsBounded A →
      ∀ᵐ ω ∂(P : Measure Ω), X ω A < ∞

namespace IsBoundedlyFiniteRandomMeasure

/-- A boundedly finite random measure is measurable as a `Measure E`-valued map. -/
theorem measurable
    {P : ProbabilityMeasure Ω} {X : Ω → Measure E} (hX : IsBoundedlyFiniteRandomMeasure P X) :
    Measurable X :=
  hX.1

/-- A boundedly finite random measure is finite on each bounded measurable set almost surely. -/
theorem ae_lt_top_apply
    {P : ProbabilityMeasure Ω} {X : Ω → Measure E}
    (hX : IsBoundedlyFiniteRandomMeasure P X)
    {A : Set E} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A) :
    ∀ᵐ ω ∂(P : Measure Ω), X ω A < ∞ :=
  hX.2 A hA hA_bdd

/-- Helper for Exercise 24.1.1: measurability of the weighted series follows from measurability of
its measurable-set evaluations. -/
lemma weightedRandomMeasureSeries_measurable
    {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (weights : ℕ → NNReal) (X : ℕ → Ω → Measure E) (hX : ∀ n, Measurable (X n)) :
    Measurable (weightedRandomMeasureSeries weights X) := by
  -- Proof comment: measurability of a `Measure E`-valued map is detected by measurable-set
  -- evaluations, and each such evaluation is a measurable `ℝ≥0∞`-valued series.
  refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
  have hrepr :
      (fun ω ↦ weightedRandomMeasureSeries weights X ω A) =
        fun ω ↦ ∑' n, (weights n : ENNReal) * (X n ω : Measure E) A := by
    funext ω
    rw [weightedRandomMeasureSeries_apply (weights := weights) (X := X) (ω := ω) hA]
  rw [hrepr]
  -- Proof comment: every summand is a constant multiple of a measurable evaluation map.
  refine Measurable.ennreal_tsum fun n ↦ ?_
  exact measurable_const.mul ((Measure.measurable_coe hA).comp (hX n))

/-- Helper for Exercise 24.1.1: finiteness on the dense-sequence unit balls implies local
finiteness of the measure. -/
lemma denseSeqUnitBallFinite_isLocallyFiniteMeasure
    [BorelSpace E] [ProperSpace E] [Nonempty E]
    (μ : Measure E)
    (hμ :
      ∀ n, μ (Metric.ball (TopologicalSpace.denseSeq E n) 1) < ∞) :
    IsLocallyFiniteMeasure μ := by
  -- Proof comment: the countable family of unit balls around a dense sequence covers the whole
  -- space, so one finite ball around a nearby dense-sequence point gives a finite neighborhood.
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨n, hn⟩ :=
    Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq E) x (1 / 2 : ℝ) (by norm_num)
  refine ⟨Metric.ball (TopologicalSpace.denseSeq E n) 1, ?_, hμ n⟩
  have hxBall : x ∈ Metric.ball (TopologicalSpace.denseSeq E n) 1 := by
    rw [Metric.mem_ball]
    exact lt_trans hn (by norm_num)
  exact Metric.isOpen_ball.mem_nhds hxBall

/-- Helper for Exercise 24.1.1: almost-sure finiteness on the dense-sequence unit balls upgrades
to almost-sure local finiteness. -/
lemma ae_isLocallyFiniteMeasure_of_denseSeqUnitBallFinite
    [BorelSpace E] [ProperSpace E] [Nonempty E]
    {P : ProbabilityMeasure Ω} {X : Ω → Measure E}
    (hX :
      ∀ n, ∀ᵐ ω ∂(P : Measure Ω),
        X ω (Metric.ball (TopologicalSpace.denseSeq E n) 1) < ∞) :
    ∀ᵐ ω ∂(P : Measure Ω), IsLocallyFiniteMeasure (X ω) := by
  -- Proof comment: `ae_all_iff` puts the countable dense-sequence family on one full-measure
  -- event, after which the pointwise local-finiteness lemma applies.
  filter_upwards [ae_all_iff.2 hX] with ω hω
  exact denseSeqUnitBallFinite_isLocallyFiniteMeasure (μ := X ω) hω

/-- On a proper Borel space, source-level bounded-set finiteness upgrades to the chapter's
locally-finite `IsRandomMeasure` owner. -/
theorem isRandomMeasure
    [BorelSpace E] [ProperSpace E]
    {P : ProbabilityMeasure Ω} {X : Ω → Measure E}
    (hX : IsBoundedlyFiniteRandomMeasure P X) :
    IsRandomMeasure P X := by
  refine ⟨hX.measurable, ?_⟩
  by_cases hE : Nonempty E
  · letI := hE
    -- Proof comment: the boundedly finite hypothesis gives finite mass on the countable dense
    -- family of unit balls, which is enough to recover local finiteness almost surely.
    exact ae_isLocallyFiniteMeasure_of_denseSeqUnitBallFinite
      (P := P) (X := X) fun n ↦
        hX.ae_lt_top_apply
          (A := Metric.ball (TopologicalSpace.denseSeq E n) 1)
          Metric.isOpen_ball.measurableSet Metric.isBounded_ball
  · have hEmpty : IsEmpty E := not_nonempty_iff.mp hE
    -- Proof comment: on the empty space every measure is locally finite by the unique-point
    -- neighborhood filter.
    exact Filter.Eventually.of_forall fun _ ↦ ⟨fun x ↦ False.elim (hEmpty.false x)⟩

end IsBoundedlyFiniteRandomMeasure

-- Semantic recall note: the source-facing owner is bounded-set finiteness almost surely; the
-- chapter's `IsRandomMeasure` owner is recovered only later under `[BorelSpace E] [ProperSpace E]`.
/-- Exercise 24.1.1: the weighted series of source-level random measures is a source-level random
measure exactly when every bounded measurable-set evaluation is finite almost surely. -/
theorem isBoundedlyFiniteRandomMeasure_weightedRandomMeasureSeries_iff_ae_lt_top_on_bounded
    (P : ProbabilityMeasure Ω) (weights : ℕ → NNReal)
    (X : ℕ → Ω → Measure E)
    (hX : ∀ n, IsBoundedlyFiniteRandomMeasure P (X n)) :
    IsBoundedlyFiniteRandomMeasure P (weightedRandomMeasureSeries weights X) ↔
      ∀ A : Set E, MeasurableSet A → Bornology.IsBounded A →
        ∀ᵐ ω ∂(P : Measure Ω), weightedRandomMeasureSeries weights X ω A < ∞ := by
  constructor
  · -- Proof comment: the forward direction is exactly the bounded-set finiteness field.
    intro hSeries
    exact hSeries.2
  · intro hSeries
    refine ⟨IsBoundedlyFiniteRandomMeasure.weightedRandomMeasureSeries_measurable
      weights X fun n ↦ (hX n).measurable, ?_⟩
    -- Proof comment: once measurability is isolated, the reverse direction is just the given
    -- almost-sure finiteness hypothesis on bounded measurable sets.
    exact hSeries

-- Companion corollary: a boundedly finite intensity packages the source condition `E[X] ∈ 𝓜(E)`.
/-- If a measurable `Measure E`-valued random variable has boundedly finite intensity, then it is
a source-level random measure. -/
theorem isBoundedlyFiniteRandomMeasure_of_intensityMeasure_lt_top_on_bounded
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (hX : Measurable X)
    (μ : BoundedlyFiniteMeasure E)
    (hμ :
      ∀ A : Set E, MeasurableSet A →
        ∫⁻ ω, X ω A ∂(P : Measure Ω) = (μ : Measure E) A) :
    IsBoundedlyFiniteRandomMeasure P X := by
  refine ⟨hX, ?_⟩
  intro A hA hA_bdd
  have hEvalMeas : Measurable fun ω ↦ X ω A :=
    (Measure.measurable_coe hA).comp hX
  have hEvalLtTop :
      ∫⁻ ω, X ω A ∂(P : Measure Ω) ≠ ∞ := by
    -- Proof comment: the intensity identity reduces the lower integral to the boundedly finite
    -- intensity mass, which is finite on bounded measurable sets.
    rw [hμ A hA]
    exact (μ.lt_top_of_isBounded hA hA_bdd).ne
  -- Proof comment: a finite `ℝ≥0∞`-valued integral forces almost-sure finiteness of the
  -- evaluation map.
  exact MeasureTheory.ae_lt_top' hEvalMeas.aemeasurable hEvalLtTop

end ProbabilityTheory
