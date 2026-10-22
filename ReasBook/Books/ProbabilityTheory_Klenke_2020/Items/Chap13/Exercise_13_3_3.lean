/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set

open scoped ENNReal

universe u v

/- Exercise 13.3.3 is `source-facing`: the textbook object is the size-biased probability law of
a law on `[0, ∞)`, obtained by normalizing the weighted measure `x P(dx)` by the first moment.
Its `core/canonical` owner abstractions are `Measure.withDensity` for the weighted law,
`FiniteMeasure.normalize` for the normalization step, `IsTightMeasureSet` for tightness, and
`UniformIntegrable` for the underlying family of nonnegative random variables. The general
formula `\hat P(A) = m_P⁻¹ \int_A x P(dx)` is the main `source-facing` statement below; the
unit-mean specialization is the `bridge/view` in which the normalization factor is `1`, so the
size-biased law is represented directly by the weighted measure. -/

/-- The first moment of a probability law on `NNReal`, written as a Lebesgue integral in
`ℝ≥0∞`. -/
noncomputable def sizeBiasedFirstMoment (μ : ProbabilityMeasure NNReal) : ENNReal :=
  ∫⁻ x, (x : ENNReal) ∂(μ : Measure NNReal)

theorem sizeBiasedFirstMoment_pos
    {μ : ProbabilityMeasure NNReal}
    (hmean : sizeBiasedFirstMoment μ = 1) :
    0 < sizeBiasedFirstMoment μ := by
  simp [hmean]

theorem sizeBiasedFirstMoment_lt_top
    {μ : ProbabilityMeasure NNReal}
    (hmean : sizeBiasedFirstMoment μ = 1) :
    sizeBiasedFirstMoment μ < ∞ := by
  simp [hmean]

private noncomputable def sizeBiasedWeightedMeasure (μ : ProbabilityMeasure NNReal)
    (hmean_finite : sizeBiasedFirstMoment μ < ∞) :
    FiniteMeasure NNReal :=
  ⟨(μ : Measure NNReal).withDensity fun x ↦ (x : ENNReal),
    isFiniteMeasure_withDensity hmean_finite.ne⟩

private theorem sizeBiasedWeightedMeasure_mass (μ : ProbabilityMeasure NNReal)
    (hmean_finite : sizeBiasedFirstMoment μ < ∞) :
    ((sizeBiasedWeightedMeasure μ hmean_finite).mass : ENNReal) =
      sizeBiasedFirstMoment μ := by
  rw [FiniteMeasure.ennreal_mass]
  change ((μ : Measure NNReal).withDensity fun x ↦ (x : ENNReal)) Set.univ =
    sizeBiasedFirstMoment μ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, sizeBiasedFirstMoment]

private theorem sizeBiasedWeightedMeasure_ne_zero (μ : ProbabilityMeasure NNReal)
    (hmean_pos : 0 < sizeBiasedFirstMoment μ)
    (hmean_finite : sizeBiasedFirstMoment μ < ∞) :
    sizeBiasedWeightedMeasure μ hmean_finite ≠ 0 := by
  refine (FiniteMeasure.mass_nonzero_iff _).mp ?_
  rw [← ENNReal.coe_ne_zero, sizeBiasedWeightedMeasure_mass]
  exact hmean_pos.ne'

/-- The size-biased distribution attached to a probability law on `NNReal` is the canonical
normalization of the weighted measure `x μ(dx)` by the first moment. Since
`FiniteMeasure.normalize` uses a default probability measure at zero mass, the textbook hypothesis
`0 < m_P < ∞` is recorded in the specification theorem `sizeBiasedDistribution_apply`, not in the
constructor itself. -/
noncomputable def sizeBiasedDistribution (μ : ProbabilityMeasure NNReal)
    (hmean_finite : sizeBiasedFirstMoment μ < ∞) :
    ProbabilityMeasure NNReal :=
  (sizeBiasedWeightedMeasure μ hmean_finite).normalize

/-- Under the unit-mean hypothesis, the size-biased distribution is the normalization of
`x μ(dx)` with normalization constant `1`. -/
noncomputable def sizeBiasedDistributionOfUnitMean (μ : ProbabilityMeasure NNReal)
    (hmean : sizeBiasedFirstMoment μ = 1) :
    ProbabilityMeasure NNReal :=
  sizeBiasedDistribution μ (sizeBiasedFirstMoment_lt_top hmean)

/-- Formula (13.14): for a measurable set `A`, the size-biased law satisfies
`\hat P(A) = m_P⁻¹ \int_A x \, P(dx)` whenever the first moment `m_P` is positive and finite. -/
theorem sizeBiasedDistribution_apply (μ : ProbabilityMeasure NNReal)
    (hmean_pos : 0 < sizeBiasedFirstMoment μ)
    (hmean_finite : sizeBiasedFirstMoment μ < ∞) {s : Set NNReal}
    (hs : MeasurableSet s) :
    (sizeBiasedDistribution μ hmean_finite : Measure NNReal) s =
      (sizeBiasedFirstMoment μ)⁻¹ *
        ∫⁻ x in s, (x : ENNReal) ∂(μ : Measure NNReal) := by
  rw [sizeBiasedDistribution,
    (sizeBiasedWeightedMeasure μ hmean_finite).toMeasure_normalize_eq_of_nonzero
      (sizeBiasedWeightedMeasure_ne_zero μ hmean_pos hmean_finite),
    Measure.smul_apply]
  change (((sizeBiasedWeightedMeasure μ hmean_finite).mass⁻¹ : NNReal) : ENNReal) *
      ((μ : Measure NNReal).withDensity fun x ↦ (x : ENNReal)) s =
    (sizeBiasedFirstMoment μ)⁻¹ *
      ∫⁻ x in s, (x : ENNReal) ∂(μ : Measure NNReal)
  rw [withDensity_apply _ hs]
  change (((sizeBiasedWeightedMeasure μ hmean_finite).mass⁻¹ : NNReal) : ENNReal) *
      ∫⁻ x in s, (x : ENNReal) ∂(μ : Measure NNReal) =
    (sizeBiasedFirstMoment μ)⁻¹ *
      ∫⁻ x in s, (x : ENNReal) ∂(μ : Measure NNReal)
  rw [← sizeBiasedWeightedMeasure_mass μ hmean_finite]
  simp [sizeBiasedWeightedMeasure_ne_zero μ hmean_pos hmean_finite]

-- Proof sketch: under the unit-mean hypothesis, the normalization constant is `1`, so
-- formula (13.14) reduces to the weighted-measure formula `\hat P(A) = ∫_A x P(dx)`.
/-- Under the unit-mean hypothesis, the general size-biased formula simplifies to
`\hat P(A) = ∫_A x \, P(dx)`. -/
theorem sizeBiasedDistribution_apply_of_unit_mean (μ : ProbabilityMeasure NNReal)
    (hmean : sizeBiasedFirstMoment μ = 1) {s : Set NNReal}
    (hs : MeasurableSet s) :
    (sizeBiasedDistributionOfUnitMean μ hmean : Measure NNReal) s =
      ∫⁻ x in s, (x : ENNReal) ∂(μ : Measure NNReal) := by
  rw [sizeBiasedDistributionOfUnitMean]
  rw [sizeBiasedDistribution_apply μ (sizeBiasedFirstMoment_pos hmean)
    (sizeBiasedFirstMoment_lt_top hmean) hs]
  simp [hmean]

/-- Pushing a probability law forward by a nonnegative random variable turns its first moment into
the integral of that random variable. -/
theorem sizeBiasedFirstMoment_map {Ω : Type v} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    {X : Ω → NNReal} (hX : AEMeasurable X (P : Measure Ω)) :
    sizeBiasedFirstMoment (P.map hX) =
      ∫⁻ ω, X ω ∂(P : Measure Ω) := by
  rw [sizeBiasedFirstMoment, ProbabilityMeasure.toMeasure_map]
  simpa using
    (lintegral_map' measurable_coe_nnreal_ennreal.aemeasurable hX)

/-- If a nonnegative random variable has mean `1`, then the first moment of its pushed-forward law
is also `1`. -/
theorem sizeBiasedFirstMoment_map_eq_one {Ω : Type v} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω)
    {X : Ω → NNReal} (hX : AEMeasurable X (P : Measure Ω))
    (hmean : ∫⁻ ω, X ω ∂(P : Measure Ω) = 1) :
    sizeBiasedFirstMoment (P.map hX) = 1 := by
  rw [sizeBiasedFirstMoment_map P hX]
  exact hmean

/-- The size-biased law of the distribution of a nonnegative unit-mean random variable. This is
the `bridge/view` from a common-space random variable to the law-level owner
`sizeBiasedDistribution`. -/
noncomputable def sizeBiasedDistributionOfUnitMeanMap {Ω : Type v} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω)
    (X : Ω → NNReal) (hX : AEMeasurable X (P : Measure Ω))
    (hmean : ∫⁻ ω, X ω ∂(P : Measure Ω) = 1) :
    ProbabilityMeasure NNReal :=
  sizeBiasedDistributionOfUnitMean (P.map hX) (sizeBiasedFirstMoment_map_eq_one P hX hmean)

/-- Helper for Exercise 13.3.3: the strict upper tail of the size-biased law at level `R`
matches the truncated first moment of the original nonnegative random variable. -/
private lemma sizeBiasedDistributionOfUnitMeanMap_Ioi_apply
    {Ω : Type v} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    {X : Ω → NNReal} (hX : AEMeasurable X (P : Measure Ω))
    (hmean : ∫⁻ ω, X ω ∂(P : Measure Ω) = 1) (R : ℝ) (hR : 0 ≤ R) :
    (sizeBiasedDistributionOfUnitMeanMap P X hX hmean : Measure NNReal) (Set.Ioi R.toNNReal) =
      ∫⁻ ω in {ω | R < X ω}, (X ω : ENNReal) ∂(P : Measure Ω) := by
  have hs : MeasurableSet (Set.Ioi R.toNNReal : Set NNReal) := measurableSet_Ioi
  have hsTail : NullMeasurableSet {ω | R.toNNReal < X ω} (P : Measure Ω) := by
    simpa [Set.preimage] using hX.nullMeasurableSet_preimage measurableSet_Ioi
  -- Rewrite the tail mass of the pushed-forward law as an indicator integral on `Ω`.
  calc
    (sizeBiasedDistributionOfUnitMeanMap P X hX hmean : Measure NNReal) (Set.Ioi R.toNNReal) =
        ∫⁻ x in Set.Ioi R.toNNReal, (x : ENNReal) ∂((P.map hX : ProbabilityMeasure NNReal) :
          Measure NNReal) := by
          simpa [sizeBiasedDistributionOfUnitMeanMap] using
            sizeBiasedDistribution_apply_of_unit_mean
              (μ := P.map hX)
              (hmean := sizeBiasedFirstMoment_map_eq_one P hX hmean) hs
    _ = ∫⁻ ω, (Set.Ioi R.toNNReal).indicator (fun x : NNReal ↦ (x : ENNReal)) (X ω) ∂
          (P : Measure Ω) := by
          simpa [ProbabilityMeasure.toMeasure_map] using
            (MeasureTheory.lintegral_map'
              (((measurable_coe_nnreal_ennreal).indicator hs).aemeasurable) hX)
    _ = ∫⁻ ω, ({ω | R.toNNReal < X ω}.indicator fun ω ↦ (X ω : ENNReal)) ω ∂
          (P : Measure Ω) := by
          refine lintegral_congr_ae ?_
          filter_upwards with ω
          rfl
    _ = ∫⁻ ω in {ω | R.toNNReal < X ω}, (X ω : ENNReal) ∂(P : Measure Ω) := by
          rw [MeasureTheory.lintegral_indicator₀ hsTail]
    _ = ∫⁻ ω in {ω | R < X ω}, (X ω : ENNReal) ∂(P : Measure Ω) := by
          rw [show {ω | R.toNNReal < X ω} = {ω | R < X ω} by
            ext ω
            change R.toNNReal < X ω ↔ R < (X ω : ℝ)
            constructor
            · intro h
              have h' : (R.toNNReal : ℝ) < (X ω : ℝ) := by
                exact_mod_cast h
              simpa [Real.toNNReal_of_nonneg hR] using h'
            · intro h
              have h' : (R.toNNReal : ℝ) < (X ω : ℝ) := by
                simpa [Real.toNNReal_of_nonneg hR] using h
              exact_mod_cast h']

/-- Helper for Exercise 13.3.3: the `L¹` cutoff seminorm of a nonnegative family is its truncated
first moment over the corresponding non-strict tail set. -/
private lemma eLpNorm_indicator_ge_coe_nnreal_eq_tailIntegral
    {Ω : Type v} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → NNReal}
    (hf : AEMeasurable f μ) (C : NNReal) :
    eLpNorm ({ω | C ≤ ‖(f ω : ℝ)‖₊}.indicator fun ω ↦ (f ω : ℝ)) 1 μ =
      ∫⁻ ω in {ω | (C : ℝ) ≤ f ω}, (f ω : ENNReal) ∂μ := by
  have hs : NullMeasurableSet {ω | C ≤ f ω} μ := by
    simpa [Set.preimage] using
      (hf.nullMeasurableSet_preimage measurableSet_Ici)
  -- Expand the `L¹` seminorm and simplify the cutoff indicator pointwise.
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
  calc
    ∫⁻ ω, ‖({ω | C ≤ ‖(f ω : ℝ)‖₊}.indicator fun ω ↦ (f ω : ℝ)) ω‖ₑ ∂μ =
        ∫⁻ ω, ‖({ω | C ≤ f ω}.indicator fun ω ↦ (f ω : ℝ)) ω‖ₑ ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards with ω
        by_cases hω : C ≤ f ω <;> simp [hω]
    _ = ∫⁻ ω, ({ω | C ≤ f ω}.indicator fun ω ↦ (f ω : ENNReal)) ω ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards with ω
        by_cases hω : C ≤ f ω <;> simp [hω]
    _ = ∫⁻ ω in {ω | C ≤ f ω}, (f ω : ENNReal) ∂μ := by
        rw [MeasureTheory.lintegral_indicator₀ hs]
    _ = ∫⁻ ω in {ω | (C : ℝ) ≤ f ω}, (f ω : ENNReal) ∂μ := by
        rw [show {ω | C ≤ f ω} = {ω | (C : ℝ) ≤ f ω} by
          ext ω
          change C ≤ f ω ↔ (C : ℝ) ≤ (f ω : ℝ)
          constructor
          · intro h
            exact_mod_cast h
          · intro h
            exact_mod_cast h]

/-- Helper for Exercise 13.3.3: on `NNReal`, the complement of the closed ball centered at `0`
with radius `r` is the strict upper tail `Set.Ioi r.toNNReal`. -/
private lemma compl_closedBall_zero_eq_Ioi (r : ℝ) (hr : 0 ≤ r) :
    (((Metric.closedBall (0 : NNReal) r)ᶜ : Set NNReal)) = Set.Ioi r.toNNReal := by
  ext x
  simp [NNReal.closedBall_zero_eq_Icc hr]

-- Proof sketch: rewrite tightness of the size-biased laws via complements of closed balls around
-- `0 : NNReal`, identify those complements with strict tails `Set.Ioi r.toNNReal`, and use the
-- size-biased tail formula to transport the estimate back to truncated first moments of `X i`.
-- The same truncated first moments are exactly the `L¹` cutoff seminorms appearing in the owner
-- predicate `UniformIntegrable` for the associated real-valued family.
/-- Exercise 13.3.3: for a family of nonnegative unit-mean random variables, the size-biased laws
of their distributions form a tight family if and only if the family is uniformly integrable when
viewed as real-valued random variables. -/
theorem isTightMeasureSet_range_sizeBiasedDistribution_iff_uniformIntegrable
    {I : Type u} {Ω : Type v} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (X : I → Ω → NNReal) (hX : ∀ i, AEMeasurable (X i) (P : Measure Ω))
    (hmean : ∀ i, ∫⁻ ω, X i ω ∂(P : Measure Ω) = 1) :
    IsTightMeasureSet
      (Set.range fun i ↦
        (sizeBiasedDistributionOfUnitMeanMap P (X i) (hX i) (hmean i) : Measure NNReal)) ↔
      UniformIntegrable (fun i ω ↦ (X i ω : ℝ)) 1 (P : Measure Ω) := by
  have hXreal :
      ∀ i, AEMeasurable (fun ω ↦ (X i ω : ℝ)) (P : Measure Ω) := fun i ↦
        (hX i).coe_nnreal_real
  -- Route correction: on `NNReal`, tightness is expressed by closed-ball complements, not norms.
  constructor
  · intro htight
    refine MeasureTheory.uniformIntegrable_of le_rfl ENNReal.one_ne_top
      (fun i ↦ (hXreal i).aestronglyMeasurable) ?_
    intro ε hε
    have htail :
        Tendsto
          (fun r : ℝ ↦
            ⨆ ν ∈ Set.range fun i ↦
              (sizeBiasedDistributionOfUnitMeanMap P (X i) (hX i) (hmean i) : Measure NNReal),
              ν ((Metric.closedBall (0 : NNReal) r)ᶜ))
          atTop (nhds 0) :=
      (MeasureTheory.isTightMeasureSet_iff_tendsto_measure_compl_closedBall (0 : NNReal)).mp htight
    rw [ENNReal.tendsto_atTop_zero] at htail
    obtain ⟨R, hR⟩ := htail (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
    let r : ℝ := max R 0
    let C : NNReal := ⟨r + 1, by positivity⟩
    -- Convert the tight size-biased tail bound into the owner cutoff estimate for UI.
    refine ⟨C, fun i ↦ ?_⟩
    have hr : R ≤ r := le_max_left _ _
    have hr_nonneg : 0 ≤ r := le_max_right _ _
    have htail_i :
        (sizeBiasedDistributionOfUnitMeanMap P (X i) (hX i) (hmean i) : Measure NNReal)
          ((Metric.closedBall (0 : NNReal) r)ᶜ) ≤ ENNReal.ofReal ε := by
      refine le_trans ?_ (hR r hr)
      exact
        le_iSup_of_le
          (sizeBiasedDistributionOfUnitMeanMap P (X i) (hX i) (hmean i) : Measure NNReal) <|
          le_iSup_of_le ⟨i, rfl⟩ le_rfl
    calc
      eLpNorm ({ω | C ≤ ‖(X i ω : ℝ)‖₊}.indicator fun ω ↦ (X i ω : ℝ)) 1
          (P : Measure Ω) =
          ∫⁻ ω in {ω | (C : ℝ) ≤ X i ω}, (X i ω : ENNReal) ∂(P : Measure Ω) := by
            exact eLpNorm_indicator_ge_coe_nnreal_eq_tailIntegral (hX i) C
      _ ≤ ∫⁻ ω in {ω | r < X i ω}, (X i ω : ENNReal) ∂(P : Measure Ω) := by
            refine MeasureTheory.lintegral_mono_set ?_
            intro ω hω
            have hω' : (r : ℝ) + 1 ≤ X i ω := by
              simpa [C, r] using hω
            exact lt_of_lt_of_le (by linarith) hω'
      _ = (sizeBiasedDistributionOfUnitMeanMap P (X i) (hX i) (hmean i) : Measure NNReal)
            (Set.Ioi r.toNNReal) := by
            symm
            exact sizeBiasedDistributionOfUnitMeanMap_Ioi_apply P (hX i) (hmean i) r hr_nonneg
      _ = (sizeBiasedDistributionOfUnitMeanMap P (X i) (hX i) (hmean i) : Measure NNReal)
            ((Metric.closedBall (0 : NNReal) r)ᶜ) := by
            rw [compl_closedBall_zero_eq_Ioi r hr_nonneg]
      _ ≤ ENNReal.ofReal ε := htail_i
  · intro hUI
    refine
      MeasureTheory.isTightMeasureSet_of_tendsto_measure_compl_closedBall (x := (0 : NNReal)) ?_
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    by_cases hε_top : ε = ∞
    · refine ⟨0, fun r hr ↦ ?_⟩
      simp [hε_top]
    · have hε_real : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
      obtain ⟨C, hC⟩ :=
        hUI.spec one_ne_zero ENNReal.one_ne_top (ε := ε.toReal) hε_real
      refine ⟨(C : ℝ), fun r hr ↦ ?_⟩
      have hr_nonneg : 0 ≤ r := le_trans C.2 hr
      -- Compare the strict size-biased tail at radius `r` with the non-strict UI cutoff at `C`.
      simp only [iSup_range]
      refine iSup_le fun i ↦ ?_
      calc
        (sizeBiasedDistributionOfUnitMeanMap P (X i) (hX i) (hmean i) : Measure NNReal)
            ((Metric.closedBall (0 : NNReal) r)ᶜ) =
            (sizeBiasedDistributionOfUnitMeanMap P (X i) (hX i) (hmean i) : Measure NNReal)
              (Set.Ioi r.toNNReal) := by
                rw [compl_closedBall_zero_eq_Ioi r hr_nonneg]
        _ = ∫⁻ ω in {ω | r < X i ω}, (X i ω : ENNReal) ∂(P : Measure Ω) := by
              exact sizeBiasedDistributionOfUnitMeanMap_Ioi_apply P (hX i) (hmean i) r hr_nonneg
        _ ≤ ∫⁻ ω in {ω | (C : ℝ) ≤ X i ω}, (X i ω : ENNReal) ∂(P : Measure Ω) := by
              refine MeasureTheory.lintegral_mono_set ?_
              intro ω hω
              exact le_trans hr hω.le
        _ = eLpNorm ({ω | C ≤ ‖(X i ω : ℝ)‖₊}.indicator fun ω ↦ (X i ω : ℝ)) 1
              (P : Measure Ω) := by
              symm
              exact eLpNorm_indicator_ge_coe_nnreal_eq_tailIntegral (hX i) C
        _ ≤ ENNReal.ofReal ε.toReal := hC i
        _ ≤ ε := ENNReal.ofReal_toReal_le
