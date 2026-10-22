/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Mathlib.Probability.UniformOn
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Example_1_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Example_1_37

-- Declarations for this item will be appended below by the statement pipeline.

open Set MeasureTheory ProbabilityTheory

open scoped ENNReal

universe u

variable {Ω : Type u} {C : Set (Set Ω)}

-- Proof sketch: every summand vanishes on `∅`, so the weighted series also vanishes on `∅`.
/-- The empty-set value needed to define weighted sums of additive contents. -/
private theorem weightedAddContentSeries_empty (w : ℕ → NNReal) (m : ℕ → AddContent ℝ≥0∞ C) :
    (∑' n, (w n : ℝ≥0∞) * m n ∅) = 0 := by
  -- Each summand vanishes on `∅`, so the whole nonnegative series collapses to zero.
  simp [addContent_empty]

-- Proof sketch: use finite additivity for each `m n`, then exchange the finite sum with the
-- infinite weighted sum.
/-- The finite additivity clause needed to define weighted sums of additive contents. -/
private theorem weightedAddContentSeries_sUnion (w : ℕ → NNReal) (m : ℕ → AddContent ℝ≥0∞ C)
    (I : Finset (Set Ω)) (hI : ↑I ⊆ C)
    (h_dis : PairwiseDisjoint (I : Set (Set Ω)) id)
    (h_mem : ⋃₀ ↑I ∈ C) :
    (∑' n, (w n : ℝ≥0∞) * m n (⋃₀ ↑I)) =
      ∑ s ∈ I, (∑' n, (w n : ℝ≥0∞) * m n s) := by
  -- Rewrite each summand using finite additivity before swapping the finite and countable sums.
  calc
    ∑' n, (w n : ℝ≥0∞) * m n (⋃₀ ↑I)
      = ∑' n, ∑ s ∈ I, (w n : ℝ≥0∞) * m n s := by
          refine tsum_congr fun n ↦ ?_
          rw [addContent_sUnion hI h_dis h_mem, Finset.mul_sum]
    _ = ∑ s ∈ I, ∑' n, (w n : ℝ≥0∞) * m n s := by
          rw [Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]

-- Proof sketch: apply `Measure.sum_apply` to the canonical measure
-- `Measure.sum fun n ↦ w n • μ n`.
/-- Item (iv) of Example 1.30 (7). The canonical countable nonnegative linear combination
`Measure.sum fun n ↦ w n • μ n` evaluates on measurable sets as the corresponding weighted
series. -/
theorem weightedMeasureSeries_apply [MeasurableSpace Ω] (w : ℕ → NNReal) (μ : ℕ → Measure Ω)
    {s : Set Ω} (hs : MeasurableSet s) :
    (Measure.sum fun n ↦ w n • μ n) s = ∑' n, (w n : ℝ≥0∞) * μ n s := by
  simp [Measure.sum_apply, hs, Measure.smul_apply]

/-- Item (iv) of Example 1.30 (8). A countable nonnegative linear combination of additive contents is
again an additive content on the same family of sets. -/
noncomputable def weightedAddContentSeries (w : ℕ → NNReal) (m : ℕ → AddContent ℝ≥0∞ C) :
    AddContent ℝ≥0∞ C :=
  { toFun := fun s ↦ ∑' n, (w n : ℝ≥0∞) * m n s
    empty' := weightedAddContentSeries_empty w m
    sUnion' := weightedAddContentSeries_sUnion w m }

/- Item (i) of Example 1.30 (1). The Dirac measure at a point is a probability measure; this is the
canonical mathlib instance `Measure.dirac.isProbabilityMeasure`. -/
recall Measure.dirac.isProbabilityMeasure [MeasurableSpace Ω] (ω : Ω) :
  IsProbabilityMeasure (Measure.dirac ω)

-- Proof sketch: use the explicit formula for the uniform counting measure on the whole finite
-- space.
/-- Item (ii) of Example 1.30 (2). On a finite space, the uniform distribution on the whole space
assigns mass `#A / #Ω` to a set `A`. -/
theorem uniformOn_univ_eq_encard_div [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Ω]
    (A : Set Ω) :
    uniformOn (Set.univ : Set Ω) A = A.encard / Fintype.card Ω := by
  have h :
      uniformOn (Set.univ : Set Ω) A = Measure.count A / Fintype.card Ω :=
    uniformOn_univ
  simpa [Measure.count_apply (Set.toFinite A).measurableSet] using
    h

/- Item (ii) of Example 1.30 (3). On a finite nonempty space, the uniform distribution on the whole
space is a probability measure; this is the canonical mathlib instance
`ProbabilityTheory.instIsProbabilityMeasure_uniformOn_univ`. -/
recall ProbabilityTheory.instIsProbabilityMeasure_uniformOn_univ [MeasurableSpace Ω] [Finite Ω]
    [Nonempty Ω] :
  IsProbabilityMeasure (uniformOn (Set.univ : Set Ω))

/- Item (iii) of Example 1.30 (4). On a countably infinite space, the finite-or-cofinite subsets
form an algebra of sets; this is the canonical earlier-project theorem
`finiteOrCofiniteFamily_isSetAlgebra`. -/
recall finiteOrCofiniteFamily_isSetAlgebra

-- Proof sketch: evaluate the content on the disjoint union of singleton sets and compare with the
-- corresponding series of values.
/- Item (iii) of Example 1.30 (6). On a countably infinite space, the finite-or-cofinite content is
not a premeasure; this is the canonical earlier-project theorem
`finiteCofiniteZeroInfiniteContent_not_isSigmaSubadditive`. -/
recall finiteCofiniteZeroInfiniteContent_not_isSigmaSubadditive

-- Proof sketch: apply the premeasure property termwise and exchange the countable weighted sum
-- with the countable union formula.
/-- Example 1.30 (9): Item (iv). A countable nonnegative linear combination of premeasures is again
a premeasure. -/
theorem weightedAddContentSeries_isPremeasureOn (w : ℕ → NNReal) (m : ℕ → AddContent ℝ≥0∞ C)
    (hm : ∀ n, (m n).IsSigmaSubadditive) :
    (weightedAddContentSeries w m).IsSigmaSubadditive := by
  intro f hf hUnion
  -- Compare the countable cover termwise and then commute the two nonnegative series.
  calc
    (weightedAddContentSeries w m) (⋃ i, f i)
      = ∑' n, (w n : ℝ≥0∞) * m n (⋃ i, f i) := rfl
    _ ≤ ∑' n, (w n : ℝ≥0∞) * ∑' i, m n (f i) := by
          refine ENNReal.tsum_le_tsum fun n ↦ ?_
          gcongr
          exact hm n hf hUnion
    _ = ∑' n, ∑' i, (w n : ℝ≥0∞) * m n (f i) := by
          refine tsum_congr fun n ↦ ?_
          rw [← ENNReal.tsum_mul_left]
    _ = ∑' i, ∑' n, (w n : ℝ≥0∞) * m n (f i) := ENNReal.tsum_comm
    _ = ∑' i, (weightedAddContentSeries w m) (f i) := by
          refine tsum_congr fun i ↦ ?_
          rfl

-- Proof sketch: expand the canonical weighted counting measure
-- `Measure.count.withDensity fun ω ↦ (p ω : ℝ≥0∞)`.
/-- Item (v) of Example 1.30 (10). On a countable space, the canonical weighted counting measure
`Measure.count.withDensity fun ω ↦ (p ω : ℝ≥0∞)` sends a set `A` to the sum of the weights over
the points of `A`. -/
theorem weightedCountMeasure_apply [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Countable Ω] (p : Ω → NNReal) (A : Set Ω) :
    (Measure.count.withDensity fun ω ↦ (p ω : ℝ≥0∞)) A = ∑' ω : A, (p ω : ℝ≥0∞) := by
  rw [withDensity_apply' _ A, lintegral_countable]
  · simp
  · exact Set.to_countable A

/- Item (v) of Example 1.30 (11). On a countable space, the canonical weighted counting measure
`Measure.count.withDensity fun ω ↦ (p ω : ℝ≥0∞)` is sigma-finite, by the generic
`SigmaFinite.withDensity` instance. -/
theorem weightedCountMeasure_sigmaFinite [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Countable Ω] (p : Ω → NNReal) :
    SigmaFinite (Measure.count.withDensity fun ω ↦ (p ω : ℝ≥0∞)) := inferInstance

-- Proof sketch: compute the mass of the whole space as the total sum of the weights and use the
-- hypothesis that this sum is `1`.
/-- Item (vi) of Example 1.30 (12). If the total weight is `1`, then the canonical weighted counting
measure `Measure.count.withDensity fun ω ↦ (p ω : ℝ≥0∞)` is a probability measure. -/
theorem weightedCountMeasure_isProbabilityMeasure [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : Ω → NNReal) (hp : (∑' ω, (p ω : ℝ≥0∞)) = 1) :
    IsProbabilityMeasure (Measure.count.withDensity fun ω ↦ (p ω : ℝ≥0∞)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count]
  exact hp

/- Item (vii) of Example 1.30 (13). Constant weight `1` recovers the underlying measure; the
counting-measure case is the specialization of the canonical theorem `withDensity_one`. -/
recall withDensity_one {α : Type u} [MeasurableSpace α] {μ : Measure α} :
  μ.withDensity 1 = μ

-- Proof sketch: on a finite space the counting measure has finite total mass, so the constant-one
-- weighted counting measure is finite.
/-- Item (vii) of Example 1.30 (14). On a finite space, counting measure is finite. -/
theorem weightedCountMeasure_const_one_isFiniteMeasure
    [MeasurableSpace Ω] [Finite Ω] :
    IsFiniteMeasure
      (Measure.count.withDensity fun _ : Ω ↦ (1 : ℝ≥0∞)) := by
  simpa [withDensity_one] using (inferInstance : IsFiniteMeasure (Measure.count : Measure Ω))

/- Item (viii) of Example 1.30 (15). Lebesgue measure gives an interval `(a, b]` mass `b - a`,
realizing the textbook interval-length content; this is the canonical theorem `Real.volume_Ioc`. -/
recall Real.volume_Ioc (a b : ℝ) :
  volume (Set.Ioc a b) = ENNReal.ofReal (b - a)

/- Item (viii) of Example 1.30 (16). Lebesgue measure on `ℝ` is sigma-finite. -/
theorem real_volume_sigmaFinite : SigmaFinite (volume : Measure ℝ) := inferInstance

/-- Helper for Example 1.30: on an ordered interval `(a, b]`, `withDensity` by a continuous
nonnegative function agrees with the corresponding interval integral. -/
private theorem continuousDensity_measure_Ioc_of_le (f : ℝ → ℝ) (hf : Continuous f)
    (hf_nonneg : ∀ x, 0 ≤ f x) {a b : ℝ} (hab : a ≤ b) :
    (volume.withDensity fun x ↦ ENNReal.ofReal (f x)) (Set.Ioc a b) =
      ENNReal.ofReal (∫ x in a..b, f x ∂volume) := by
  have h_integrable : IntegrableOn f (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 (hf.intervalIntegrable a b)
  have h_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc a b)] f :=
    Filter.Eventually.of_forall hf_nonneg
  -- Rewrite the weighted measure of `(a, b]` as a restricted `lintegral`, then convert it to the
  -- corresponding real integral on the same interval.
  rw [withDensity_apply _ measurableSet_Ioc]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_integrable h_nonneg]
  simp [intervalIntegral.integral_of_le hab]

-- Proof sketch: unfold `withDensity` on the interval `(a, b]` and rewrite the result as the
-- interval integral of the continuous nonnegative density.
/-- Item (ix) of Example 1.30 (17). A continuous nonnegative density defines a measure whose mass on
`(a, b]` is the integral of the density over that interval. -/
theorem continuousDensity_measure_Ioc (f : ℝ → ℝ) (hf : Continuous f)
    (hf_nonneg : ∀ x, 0 ≤ f x) (a b : ℝ) :
    (volume.withDensity fun x ↦ ENNReal.ofReal (f x)) (Set.Ioc a b) =
      ENNReal.ofReal (∫ x in a..b, f x ∂volume) := by
  by_cases hab : a ≤ b
  · -- In the ordered case, the helper performs the `withDensity` to interval-integral transport.
    exact continuousDensity_measure_Ioc_of_le f hf hf_nonneg hab
  · have hba : b ≤ a := le_of_not_ge hab
    -- If `a > b`, then `(a, b]` is empty and the interval integral is nonpositive, hence its
    -- `ENNReal.ofReal` vanishes.
    rw [Set.Ioc_eq_empty_of_le hba, measure_empty, intervalIntegral.integral_of_ge hba]
    symm
    rw [ENNReal.ofReal_eq_zero]
    exact neg_nonpos.mpr (integral_nonneg_of_ae <| Filter.Eventually.of_forall hf_nonneg)

/- Item (ix) of Example 1.30 (18). A continuous nonnegative density on `ℝ` yields a sigma-finite
measure; this is the concrete specialization of the canonical theorem
`MeasureTheory.SigmaFinite.withDensity_ofReal`. -/
recall MeasureTheory.SigmaFinite.withDensity_ofReal {α : Type u} {m0 : MeasurableSpace α}
    {μ : Measure α} [SigmaFinite μ] (f : α → ℝ) :
  SigmaFinite (μ.withDensity fun x ↦ ENNReal.ofReal (f x))
