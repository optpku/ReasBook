/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_46
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Exercise_14_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace IsNonnegativeConvolutionSemigroup

variable {ν : NNReal → ProbabilityMeasure ℝ} [IsNonnegativeConvolutionSemigroup ν]

/-- Helper for Exercise 14.4.3: the canonical continuous linear equivalence between the chapter's
`Fin 1 → ℝ` model of `ℝ¹` and `ℝ`. -/
private noncomputable abbrev fin1RealEquiv : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ

/-- Helper for Exercise 14.4.3: the same equivalence viewed as a measurable equivalence. -/
private noncomputable abbrev fin1RealMeasEquiv : (Fin 1 → ℝ) ≃ᵐ ℝ :=
  fin1RealEquiv.toHomeomorph.toMeasurableEquiv

/-- Helper for Exercise 14.4.3: transport the real convolution semigroup to the
one-dimensional vector model `Fin 1 → ℝ`. -/
private noncomputable abbrev transportedFin1Law
    (ν : NNReal → ProbabilityMeasure ℝ) : NNReal → ProbabilityMeasure (Fin 1 → ℝ) :=
  fun t ↦ ProbabilityMeasure.map (ν t) fin1RealMeasEquiv.symm.measurable.aemeasurable

/-- Helper for Exercise 14.4.3: transporting a real probability measure to `Fin 1 → ℝ` and back
recovers the original law. -/
@[simp] private theorem mapBackTransportedFin1Law (μ : ProbabilityMeasure ℝ) :
    ProbabilityMeasure.map
      (ProbabilityMeasure.map μ fin1RealMeasEquiv.symm.measurable.aemeasurable)
      fin1RealMeasEquiv.measurable.aemeasurable = μ := by
  -- Proof comment: the measurable equivalence cancels after the two successive pushforwards.
  apply Subtype.ext
  simpa [ProbabilityMeasure.map] using
    (MeasurableEquiv.map_map_symm (ν := (μ : Measure ℝ)) fin1RealMeasEquiv)

/-- Helper for Exercise 14.4.3: mapping the Dirac mass at the origin of `Fin 1 → ℝ` back to `ℝ`
still gives the Dirac mass at `0`. -/
@[simp] private theorem mapDiracProbaFin1RealZero :
    ProbabilityMeasure.map
      (diracProba (0 : Fin 1 → ℝ))
      fin1RealMeasEquiv.measurable.aemeasurable =
      diracProba (0 : ℝ) := by
  -- Proof comment: the canonical equivalence sends the zero vector of `ℝ¹` to the real number `0`.
  apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
  intro s hs
  rw [ProbabilityMeasure.toMeasure_map, MeasurableEquiv.map_apply]
  by_cases h : (0 : ℝ) ∈ s
  · simp [h, fin1RealMeasEquiv, fin1RealEquiv]
  · simp [h, fin1RealMeasEquiv, fin1RealEquiv]

/-- Helper for Exercise 14.4.3: the transported `Fin 1 → ℝ` family still satisfies the
convolution-semigroup law. -/
private theorem transportedFin1ConvolutionSemigroup :
    IsConvolutionSemigroup (transportedFin1Law ν) where
  convolution_eq s t := by
    -- Proof comment: push the original semigroup identity forward through the linear equivalence.
    apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
    intro A hA
    have hConvMap :
        Measure.map fin1RealEquiv.symm ((ν s : Measure ℝ) ∗ (ν t : Measure ℝ)) =
          Measure.map fin1RealEquiv.symm (ν s : Measure ℝ) ∗
            Measure.map fin1RealEquiv.symm (ν t : Measure ℝ) :=
      by
        simpa using
          (Measure.map_conv_continuousLinearMap
            (μ := (ν s : Measure ℝ))
            (ν := (ν t : Measure ℝ))
            (fin1RealEquiv.symm : ℝ →L[ℝ] (Fin 1 → ℝ)))
    have hMap :
        ((ν (s + t) : Measure ℝ).map fin1RealEquiv.symm) A =
          ((((ν s : Measure ℝ).map fin1RealEquiv.symm) ∗
              ((ν t : Measure ℝ).map fin1RealEquiv.symm)) A) := by
      calc
        ((ν (s + t) : Measure ℝ).map fin1RealEquiv.symm) A
            = (Measure.map fin1RealEquiv.symm ((ν s : Measure ℝ) ∗ (ν t : Measure ℝ))) A := by
                rw [IsConvolutionSemigroup.convolution_eq_toMeasure (ν := ν) s t]
        _ = ((((ν s : Measure ℝ).map fin1RealEquiv.symm) ∗
              ((ν t : Measure ℝ).map fin1RealEquiv.symm)) A) := by
              exact congrArg (fun μ : Measure (Fin 1 → ℝ) ↦ μ A) hConvMap
    simpa [transportedFin1Law, ProbabilityMeasure.map] using hMap

/-- Helper for Exercise 14.4.3: the `t / n` subdivision laws on `ℝ` converge weakly to
`diracProba 0`. -/
private theorem tendstoDivPNatDiracProbaZeroReal (t : NNReal) :
    Tendsto (fun n : ℕ+ ↦ ν (t / (n : NNReal))) atTop (𝓝 (diracProba (0 : ℝ))) := by
  -- Proof comment: first apply Exercise 14.4.2 after transporting the semigroup to `Fin 1 → ℝ`.
  letI : IsConvolutionSemigroup (transportedFin1Law ν) :=
    transportedFin1ConvolutionSemigroup (ν := ν)
  have hVec :
      Tendsto (fun n : ℕ+ ↦ transportedFin1Law ν (t / (n : NNReal))) atTop
        (𝓝 (diracProba (0 : Fin 1 → ℝ))) :=
    IsConvolutionSemigroup.tendsto_div_pNat_diracProba_zero
      (ν := transportedFin1Law ν) t
  -- Proof comment: then map that weak limit back through the inverse equivalence to return to `ℝ`.
  have hBack :
      Tendsto
        (fun n : ℕ+ ↦
          ProbabilityMeasure.map
            (transportedFin1Law ν (t / (n : NNReal)))
            fin1RealMeasEquiv.measurable.aemeasurable)
        atTop
        (𝓝
          (ProbabilityMeasure.map
            (diracProba (0 : Fin 1 → ℝ))
            fin1RealMeasEquiv.measurable.aemeasurable)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (νs := fun n : ℕ+ ↦ transportedFin1Law ν (t / (n : NNReal)))
      (ν := diracProba (0 : Fin 1 → ℝ))
      hVec fin1RealEquiv.continuous
  -- Proof comment: both the sequence and the limit simplify because the transport is invertible.
  simpa only [transportedFin1Law, mapBackTransportedFin1Law, mapDiracProbaFin1RealZero]
    using hBack

/-- Helper for Exercise 14.4.3: the time-zero law of a nonnegative convolution semigroup is
already `diracProba 0`. -/
private theorem zeroEqDiracProba : ν 0 = diracProba (0 : ℝ) := by
  -- Proof comment: the `t / n` theorem at `t = 0` is a constant sequence, so uniqueness of limits
  -- identifies that constant value with `diracProba 0`.
  have hZero :
      Tendsto (fun n : ℕ+ ↦ ν (0 / (n : NNReal))) atTop (𝓝 (diracProba (0 : ℝ))) :=
    tendstoDivPNatDiracProbaZeroReal (ν := ν) 0
  have hConst : Tendsto (fun _ : ℕ+ ↦ ν 0) atTop (𝓝 (ν 0)) :=
    tendsto_const_nhds
  have hDirac : Tendsto (fun _ : ℕ+ ↦ ν 0) atTop (𝓝 (diracProba (0 : ℝ))) := by
    simpa using hZero
  exact tendsto_nhds_unique hConst hDirac

/-- Helper for Exercise 14.4.3: along the subdivision times `1 / n`, the positive tail
`Set.Ici a` has vanishing mass for every `a > 0`. -/
private theorem tendstoSubdivisionTail (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun n : ℕ+ ↦ ((ν ((1 : NNReal) / (n : NNReal)) : Measure ℝ) (Set.Ici a)))
      atTop (𝓝 0) := by
  -- Proof comment: apply the closed-set Portmanteau inequality to the weak limit `diracProba 0`.
  have hDiv : Tendsto (fun n : ℕ+ ↦ ν ((1 : NNReal) / (n : NNReal))) atTop
      (𝓝 (diracProba (0 : ℝ))) :=
    tendstoDivPNatDiracProbaZeroReal (ν := ν) 1
  have hUpper :
      limsup
          (fun n : ℕ+ ↦ ((ν ((1 : NNReal) / (n : NNReal)) : Measure ℝ) (Set.Ici a)))
          atTop = 0 := by
    simpa [Set.mem_Ici, not_le_of_gt ha] using
      (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
        (μs := fun n : ℕ+ ↦ ν ((1 : NNReal) / (n : NNReal)))
        (μ := diracProba (0 : ℝ))
        hDiv
        (F := Set.Ici a)
        isClosed_Ici)
  exact tendsto_of_le_liminf_of_limsup_le bot_le hUpper.le

/-- Helper for Exercise 14.4.3: positive tails can only increase with time because the
increment laws are supported on `[0, ∞)`. -/
private theorem measureIciMonotoneOfNonnegative {s t : NNReal} (hst : s ≤ t) (a : ℝ) :
    ((ν s : Measure ℝ) (Set.Ici a)) ≤ ((ν t : Measure ℝ) (Set.Ici a)) := by
  let η : Measure ℝ := ν (t - s)
  have h_nonneg_ae : ∀ᵐ y ∂η, 0 ≤ y := by
    -- Proof comment: every increment law gives zero mass to the negative half-line.
    dsimp [η]
    refine ae_iff.2 ?_
    simpa [Set.mem_Ici, not_le] using
      (IsNonnegativeConvolutionSemigroup.measure_Iio_zero (ν := ν) (t - s))
  have hconv : (ν t : Measure ℝ) = (ν s : Measure ℝ) ∗ η := by
    -- Proof comment: write the later time as the earlier law convolved with its increment law.
    dsimp [η]
    rw [← IsConvolutionSemigroup.convolution_eq_toMeasure (ν := ν) s (t - s),
      add_tsub_cancel_of_le hst]
  calc
    ((ν s : Measure ℝ) (Set.Ici a))
        = ∫⁻ x, (Set.Ici a).indicator (fun _ ↦ (1 : ENNReal)) x ∂(ν s : Measure ℝ) := by
            symm
            exact lintegral_indicator_one measurableSet_Ici
    _ ≤
        ∫⁻ x,
          ∫⁻ y, (Set.Ici a).indicator (fun _ ↦ (1 : ENNReal)) (x + y) ∂η ∂(ν s : Measure ℝ) := by
          refine lintegral_mono fun x ↦ ?_
          calc
            (Set.Ici a).indicator (fun _ ↦ (1 : ENNReal)) x
                = ∫⁻ y, (Set.Ici a).indicator (fun _ ↦ (1 : ENNReal)) x ∂η := by
                    dsimp [η]
                    simp
            _ ≤ ∫⁻ y, (Set.Ici a).indicator (fun _ ↦ (1 : ENNReal)) (x + y) ∂η := by
                  refine lintegral_mono_ae ?_
                  filter_upwards [h_nonneg_ae] with y hy
                  by_cases hx : a ≤ x
                  · have hxy : a ≤ x + y := le_trans hx (le_add_of_nonneg_right hy)
                    simp [Set.mem_Ici, hx, hxy]
                  · simp [Set.mem_Ici, hx]
    _ = ∫⁻ z, (Set.Ici a).indicator (fun _ ↦ (1 : ENNReal)) z ∂((ν s : Measure ℝ) ∗ η) := by
          symm
          simpa using
            (Measure.lintegral_conv
              (μ := (ν s : Measure ℝ))
              (ν := η)
              (f := (Set.Ici a).indicator (fun _ ↦ (1 : ENNReal)))
              (measurable_const.indicator measurableSet_Ici))
    _ = (((ν s : Measure ℝ) ∗ η) (Set.Ici a)) := by
          exact lintegral_indicator_one measurableSet_Ici
    _ = ((ν t : Measure ℝ) (Set.Ici a)) := by rw [hconv]

/-- Helper for Exercise 14.4.3: any closed set that stays away from `0` has vanishing mass along
every time sequence converging to `0`. -/
private theorem tendstoSeqClosedAwayFromZero {u : ℕ → NNReal}
    (hu : Tendsto u atTop (𝓝 0)) {F : Set ℝ} (hF : IsClosed F) (h0F : (0 : ℝ) ∉ F) :
    Tendsto (fun n ↦ ((ν (u n) : Measure ℝ) F)) atTop (𝓝 0) := by
  -- Proof comment: choose a positive gap separating `F` from the origin on the nonnegative ray.
  have hmem : Fᶜ ∈ 𝓝 (0 : ℝ) :=
    IsOpen.mem_nhds hF.isOpen_compl h0F
  rcases Metric.mem_nhds_iff.mp hmem with ⟨ε, hεpos, hεball⟩
  have hFsubset : F ⊆ Set.Iio 0 ∪ Set.Ici ε := by
    intro x hx
    by_cases hxneg : x < 0
    · exact Or.inl hxneg
    · have hxnonneg : 0 ≤ x := by linarith
      right
      by_contra hxIci
      have hxlt : x < ε := lt_of_not_ge hxIci
      have hxball : x ∈ Metric.ball (0 : ℝ) ε := by
        simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg hxnonneg] using hxlt
      exact (hεball hxball) hx
  -- Proof comment: domination by one fixed subdivision tail turns the closed-set bound into a
  -- standard `ε`-argument in the order topology on `ℝ≥0∞`.
  rw [tendsto_order]
  constructor
  · intro a ha
    exact (not_lt_of_ge bot_le ha).elim
  · intro b hb
    have hSubdivision := tendstoSubdivisionTail (ν := ν) ε hεpos
    have hSubdivisionEventually :
        ∀ᶠ m : ℕ+ in atTop,
          ((ν ((1 : NNReal) / (m : NNReal)) : Measure ℝ) (Set.Ici ε)) < b := by
      exact (tendsto_order.1 hSubdivision).2 b hb
    rcases eventually_atTop.1 hSubdivisionEventually with ⟨m, hm⟩
    have huEventually :
        ∀ᶠ n in atTop, u n < (1 : NNReal) / (m : NNReal) := by
      exact (tendsto_order.1 hu).2 ((1 : NNReal) / (m : NNReal)) (by positivity)
    filter_upwards [huEventually] with n hn
    have hFle :
        ((ν (u n) : Measure ℝ) F) ≤ ((ν (u n) : Measure ℝ) (Set.Ici ε)) := by
      calc
        ((ν (u n) : Measure ℝ) F)
            ≤ ((ν (u n) : Measure ℝ) (Set.Iio 0 ∪ Set.Ici ε)) :=
              MeasureTheory.measure_mono hFsubset
        _ ≤ ((ν (u n) : Measure ℝ) (Set.Iio 0)) +
              ((ν (u n) : Measure ℝ) (Set.Ici ε)) :=
              measure_union_le _ _
        _ = 0 + ((ν (u n) : Measure ℝ) (Set.Ici ε)) := by
              rw [IsNonnegativeConvolutionSemigroup.measure_Iio_zero (ν := ν) (u n)]
        _ = ((ν (u n) : Measure ℝ) (Set.Ici ε)) := by simp
    have hTailLe :
        ((ν (u n) : Measure ℝ) (Set.Ici ε)) ≤
          ((ν ((1 : NNReal) / (m : NNReal)) : Measure ℝ) (Set.Ici ε)) :=
      measureIciMonotoneOfNonnegative (ν := ν) (le_of_lt hn) ε
    exact lt_of_le_of_lt (le_trans hFle hTailLe) (hm m le_rfl)

/-- Exercise 14.4.3: every nonnegative convolution semigroup on `[0, ∞)` with values in
probability measures on `ℝ` is continuous at the origin in the weak topology. -/
-- Proof sketch: use the nonnegativity assumption to identify the family as a subprobability
-- semigroup supported on `[0, ∞)`, then prove that the semigroup law forces the weak limit at
-- `t → 0` to be the Dirac mass at `0`.
instance toIsContinuousConvolutionSemigroup
    :
    IsContinuousConvolutionSemigroup ν where
  toIsConvolutionSemigroup := inferInstance
  tendsto_zero := by
    -- Proof comment: continuity at `0` follows once every convergent sequence of times yields weak
    -- convergence of the corresponding probability laws.
    apply Filter.tendsto_of_seq_tendsto
    intro u hu
    -- Proof comment: Portmanteau reduces the weak convergence statement to closed-set limsup
    -- bounds against the candidate limit `diracProba 0`.
    apply MeasureTheory.tendsto_of_forall_isClosed_limsup_le'
    intro F hF
    by_cases h0F : (0 : ℝ) ∈ F
    · have hLe :
          ∀ᶠ n in atTop, ((ν (u n) : Measure ℝ) F) ≤ (1 : ENNReal) := by
            exact Filter.Eventually.of_forall fun n ↦ by
              simpa using
                (measure_mono (μ := (ν (u n) : Measure ℝ)) (Set.subset_univ F))
      have hUpper :=
        Filter.limsup_le_of_le (u := fun n ↦ ((ν (u n) : Measure ℝ) F)) (h := hLe)
      simpa [h0F] using hUpper
    · have hAway :
          Tendsto (fun n ↦ ((ν (u n) : Measure ℝ) F)) atTop (𝓝 0) :=
        tendstoSeqClosedAwayFromZero (ν := ν) hu hF h0F
      have hUpper : limsup (fun n ↦ ((ν (u n) : Measure ℝ) F)) atTop = 0 := by
        simpa [Function.comp] using hAway.limsup_eq
      simpa [h0F] using hUpper.le

end IsNonnegativeConvolutionSemigroup
