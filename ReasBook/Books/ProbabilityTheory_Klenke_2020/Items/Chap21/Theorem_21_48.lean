/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Lemma_21_46
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Lemma_21_47
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped NNReal

noncomputable section

universe u

namespace ProbabilityTheory

/-- Helper for Theorem 21.48: a Kolmogorov package with the fixed admissible exponent `1 / 8`
produces a real-valued modification with almost surely continuous paths. -/
private lemma existsContinuousRealModificationOfKolmogorov
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : NNReal → Ω → ℝ}
    (hbound :
      ∀ T : NNReal, ∃ C : ℝ≥0, IsKolmogorovProcessOnIcc μ X T (4 : ℝ≥0) (1 : ℝ≥0) C) :
    ∃ Xc : NNReal → Ω → ℝ,
      AreModifications μ X Xc ∧
        HasAlmostSurelyContinuousPaths μ Xc := by
  let γ : ℝ≥0 := (1 : ℝ≥0) / 8
  have hγpos : 0 < γ := by
    norm_num [γ]
  have hγlt : (γ : ℝ) < (1 : ℝ) / 4 := by
    norm_num [γ]
  have hγle : γ ≤ 1 := by
    have h8 : (1 : ℝ≥0) ≤ 8 := by norm_num
    have h : ((1 : ℝ≥0) / 8 : ℝ≥0) ≤ 1 := by
      exact div_le_self (by positivity : 0 ≤ (1 : ℝ≥0)) h8
    change ((1 : ℝ≥0) / 8 : ℝ≥0) ≤ 1
    exact h
  have hkolm :
      ∀ T : NNReal, ∃ α β C : ℝ≥0, IsKolmogorovProcessOnIcc μ X T α β C := by
    intro T
    rcases hbound T with ⟨C, hC⟩
    exact ⟨(4 : ℝ≥0), (1 : ℝ≥0), C, hC⟩
  rcases exists_modification_with_locally_holder_paths (μ := μ) (X := X) hkolm with
    ⟨Xc, hmod, hholder, -⟩
  refine ⟨Xc, hmod, ?_⟩
  let γIoc : Set.Ioc (0 : ℝ≥0) (1 : ℝ≥0) := ⟨γ, ⟨hγpos, hγle⟩⟩
  refine Filter.Eventually.of_forall fun ω ↦ ?_
  -- Proof comment: Theorem 21.6 gives local Hölder control at exponent `1 / 8`, and
  -- positive-exponent local Hölder regularity implies continuity.
  exact
    continuous_of_locallyHolderWith (γ := γIoc) <| by
      simpa [γIoc, γ] using hholder γ hγpos
        (fun T ↦ by
          rcases hbound T with ⟨C, hC⟩
          refine ⟨(4 : ℝ≥0), (1 : ℝ≥0), C, hC, ?_⟩
          simpa using hγlt)
        ω

/-- Helper for Theorem 21.48: a real-valued continuous modification of an `NNReal`-valued process
can be transported back to an `NNReal`-valued continuous modification using `Real.toNNReal`. -/
private lemma continuousNnrealVersionOfRealModification
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {Ynn : NNReal → Ω → NNReal} {Yr YrC : NNReal → Ω → ℝ}
    (hmod : AreModifications μ Yr YrC)
    (hYr : ∀ t ω, Yr t ω = (Ynn t ω : ℝ))
    (hcont : HasAlmostSurelyContinuousPaths μ YrC) :
    ∃ Yc : NNReal → Ω → NNReal,
      AreModifications μ Ynn Yc ∧
        HasAlmostSurelyContinuousPaths μ Yc := by
  let Yc : NNReal → Ω → NNReal := fun t ω ↦ Real.toNNReal (YrC t ω)
  refine ⟨Yc, ?_, ?_⟩
  · intro t
    filter_upwards [hmod t] with ω hω
    -- Proof comment: the original process is nonnegative because it already lands in `NNReal`,
    -- so `Real.toNNReal` collapses the transported real equality back to the original value.
    change Ynn t ω = Real.toNNReal (YrC t ω)
    rw [← hω, hYr t ω]
    exact (Real.toNNReal_coe : Real.toNNReal ((Ynn t ω : NNReal) : ℝ) = Ynn t ω).symm
  · filter_upwards [hcont] with ω hω
    -- Proof comment: composing a continuous real path with `Real.toNNReal` preserves continuity.
    simpa [HasAlmostSurelyContinuousPaths, processPath, Yc] using
      continuous_real_toNNReal.comp hω

/-- Helper for Theorem 21.48: the time-`t` kernel row started from `y` has the explicit fourth
centered moment coming from Lemma 21.47. -/
private lemma branchingDiffusionKernelRow_fourthCenteredMoment
    {Ω : Type u} [MeasurableSpace Ω]
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (t y : NNReal) :
    ∫ z, (((z : ℝ) - (y : ℝ)) ^ 4) ∂κ t y =
      24 * (y : ℝ) * (t : ℝ) ^ 3 + 12 * (y : ℝ) ^ 2 * (t : ℝ) ^ 2 := by
  have hcentral :
      centralMoment (fun ω ↦ (Y t ω : ℝ)) 4 (P y : Measure Ω) =
        24 * (y : ℝ) * (t : ℝ) ^ 3 + 12 * (y : ℝ) ^ 2 * (t : ℝ) ^ 2 :=
    branchingDiffusion_fourth_centralMoment hY hκ (x := y) (t := t)
  have hmean :
      (P y : Measure Ω)[fun ω ↦ (Y t ω : ℝ)] = (y : ℝ) :=
    by simpa [moment_one] using branchingDiffusion_first_moment hY hκ (x := y) (t := t)
  have hrealization :
      ∫ ω, (((Y t ω : ℝ) - (y : ℝ)) ^ 4) ∂(P y : Measure Ω) =
        24 * (y : ℝ) * (t : ℝ) ^ 3 + 12 * (y : ℝ) ^ 2 * (t : ℝ) ^ 2 := by
    -- Proof comment: identify the center in the fourth central moment with the explicit first
    -- moment from Lemma 21.47.
    simpa [ProbabilityTheory.centralMoment, hmean] using hcentral
  -- Proof comment: push the fourth-power observable through the time-`t` marginal identity to
  -- replace the realized process by the kernel row itself.
  calc
    ∫ z, (((z : ℝ) - (y : ℝ)) ^ 4) ∂κ t y =
        ∫ z, (((z : ℝ) - (y : ℝ)) ^ 4) ∂((P y : Measure Ω).map (Y t)) := by
          rw [hY.transition_eq y t]
    _ = ∫ ω, (((Y t ω : ℝ) - (y : ℝ)) ^ 4) ∂(P y : Measure Ω) := by
          symm
          rw [MeasureTheory.integral_map (hY.measurable_process t).aemeasurable]
          · fun_prop
    _ = 24 * (y : ℝ) * (t : ℝ) ^ 3 + 12 * (y : ℝ) ^ 2 * (t : ℝ) ^ 2 := hrealization

/-- Helper for Theorem 21.48: conditioning the future-state event `{Y (s + t) ∈ A}` on the
present state `Y s` gives the kernel row `κ t (Y s ·)`. -/
private lemma markovRealization_futureEventCondExp_eqKernelRow
    {Ω : Type u} [MeasurableSpace Ω]
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (hY : IsMarkovProcessRealization κ P Y) (x s t : NNReal)
    {A : Set NNReal} (hA : MeasurableSet A) :
    (P x : Measure Ω)⟦Y (s + t) ⁻¹' A | MeasurableSpace.comap (Y s) inferInstance⟧ =ᵐ[
        (P x : Measure Ω)]
      fun ω ↦ ((κ t) (Y s ω)).real A := by
  let μ : Measure Ω := (P x : Measure Ω)
  have hHist :
      μ⟦Y (s + t) ⁻¹' A | generatedFiltrationSpace Y s⟧ =ᵐ[μ]
        fun ω ↦ ((κ t) (Y s ω)).real A := by
    -- Proof comment: this is exactly the event-level Markov property stored in the realization.
    simpa [μ, add_comm, add_left_comm, add_assoc] using hY.markov_property x hA s t
  have hNat :
      μ⟦Y (s + t) ⁻¹' A | generatedFiltrationSpace Y s⟧ =ᵐ[μ]
        μ⟦Y (s + t) ⁻¹' A | MeasurableSpace.comap (Y s) inferInstance⟧ := by
    -- Proof comment: the derived natural Markov property collapses the full history down to the
    -- present-state sigma-algebra.
    simpa [μ] using
      (hY.hasNaturalMarkovProperty x).2
        (s := s) (t := s + t) (le_add_of_nonneg_right t.2) (A := A) hA
  exact hNat.symm.trans hHist

/-- Helper for Theorem 21.48: the rectangle mass of the joint law of the present state `Y s` and
the future state `Y (s + t)` is the present-state integral of the kernel row `κ t`. -/
private lemma markovRealization_pairLawRealProdEqStateIntegral
    {Ω : Type u} [MeasurableSpace Ω]
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (hY : IsMarkovProcessRealization κ P Y) (x s t : NNReal)
    {hs ht : Set NNReal} (hs_meas : MeasurableSet hs) (ht_meas : MeasurableSet ht) :
    let μ : Measure Ω := (P x : Measure Ω)
    let H : Ω → NNReal := Y s
    let next : Ω → NNReal := Y (s + t)
    (μ.map (fun ω ↦ (H ω, next ω))).real (hs ×ˢ ht) =
      ∫ ω in H ⁻¹' hs, ((κ t) (H ω)).real ht ∂μ := by
  set μ : Measure Ω := (P x : Measure Ω)
  set H : Ω → NNReal := Y s
  set next : Ω → NNReal := Y (s + t)
  have hH_meas : Measurable H := by
    -- Proof comment: the present-state coordinate is measurable by the realization interface.
    simpa [H] using hY.measurable_process s
  have hnext_meas : Measurable next := by
    -- Proof comment: the future-state coordinate is just another measurable time slice.
    simpa [next] using hY.measurable_process (s + t)
  have hpair_meas : Measurable (fun ω ↦ (H ω, next ω)) := by
    -- Proof comment: the pair map is measurable coordinatewise.
    fun_prop
  have hnext_pre_meas : MeasurableSet (next ⁻¹' ht) := hnext_meas ht_meas
  have hIndicatorInt :
      Integrable (Set.indicator (next ⁻¹' ht) (fun _ ↦ (1 : ℝ))) μ := by
    -- Proof comment: indicators of measurable events are integrable under the probability law.
    exact (integrable_const (1 : ℝ)).indicator hnext_pre_meas
  have hcond :
      μ⟦next ⁻¹' ht | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ]
        fun ω ↦ ((κ t) (H ω)).real ht := by
    -- Proof comment: specialize the present-state conditional law to the future event `ht`.
    simpa [μ, H, next] using
      markovRealization_futureEventCondExp_eqKernelRow hY x s t ht_meas
  calc
    (μ.map (fun ω ↦ (H ω, next ω))).real (hs ×ˢ ht)
        = ENNReal.toReal ((μ.map (fun ω ↦ (H ω, next ω))) (hs ×ˢ ht)) := by
            rfl
    _ = ENNReal.toReal (μ ((fun ω ↦ (H ω, next ω)) ⁻¹' (hs ×ˢ ht))) := by
          rw [Measure.map_apply hpair_meas (hs_meas.prod ht_meas)]
    _ = ENNReal.toReal (μ (H ⁻¹' hs ∩ next ⁻¹' ht)) := by
          have hpre :
              (fun ω ↦ (H ω, next ω)) ⁻¹' (hs ×ˢ ht) = H ⁻¹' hs ∩ next ⁻¹' ht := by
            ext ω
            simp [Set.preimage, H, next]
          rw [hpre]
    _ = ∫ ω in H ⁻¹' hs ∩ next ⁻¹' ht, (1 : ℝ) ∂μ := by
          symm
          exact MeasureTheory.setIntegral_one_eq_measureReal
    _ = ∫ ω in H ⁻¹' hs, Set.indicator (next ⁻¹' ht) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
          -- Proof comment: expose the future event inside the restriction to the present-state
          -- event.
          calc
            ∫ ω in H ⁻¹' hs ∩ next ⁻¹' ht, (1 : ℝ) ∂μ
                = (μ.restrict (H ⁻¹' hs)).real (next ⁻¹' ht) := by
                    rw [MeasureTheory.measureReal_restrict_apply (μ := μ) (s := H ⁻¹' hs)
                      (t := next ⁻¹' ht) hnext_pre_meas, Set.inter_comm,
                      ← MeasureTheory.setIntegral_one_eq_measureReal]
            _ = ∫ ω, Set.indicator (next ⁻¹' ht) (fun _ ↦ (1 : ℝ)) ω ∂μ.restrict (H ⁻¹' hs) := by
                  symm
                  simpa using
                    (MeasureTheory.integral_indicator_one
                      (μ := μ.restrict (H ⁻¹' hs)) hnext_pre_meas)
            _ = ∫ ω in H ⁻¹' hs, Set.indicator (next ⁻¹' ht) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
                  rfl
    _ = ∫ ω in H ⁻¹' hs,
          (μ⟦next ⁻¹' ht | MeasurableSpace.comap H inferInstance⟧) ω ∂μ := by
          -- Proof comment: conditional expectation preserves integrals over `σ(Y s)`-measurable
          -- events.
          symm
          exact
            MeasureTheory.setIntegral_condExp hH_meas.comap_le hIndicatorInt
              ⟨hs, hs_meas, rfl⟩
    _ = ∫ ω in H ⁻¹' hs, ((κ t) (H ω)).real ht ∂μ := by
          -- Proof comment: replace the conditional probability by the kernel row.
          refine MeasureTheory.setIntegral_congr_ae (hH_meas hs_meas) ?_
          filter_upwards [hcond] with ω hω hωhs
          exact hω

/-- Helper for Theorem 21.48: the rectangle mass of the composition product
`(P x).map (Y s) ⊗ₘ κ t` matches the same present-state integral as the joint law. -/
private lemma markovRealization_compProdRealProdEqStateIntegral
    {Ω : Type u} [MeasurableSpace Ω]
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (hY : IsMarkovProcessRealization κ P Y) (x s t : NNReal)
    {hs ht : Set NNReal} (hs_meas : MeasurableSet hs) (ht_meas : MeasurableSet ht) :
    let μ : Measure Ω := (P x : Measure Ω)
    let H : Ω → NNReal := Y s
    (μ.map H ⊗ₘ κ t).real (hs ×ˢ ht) =
      ∫ ω in H ⁻¹' hs, ((κ t) (H ω)).real ht ∂μ := by
  set μ : Measure Ω := (P x : Measure Ω)
  set H : Ω → NNReal := Y s
  letI : IsMarkovKernel (κ t) := by
    -- Proof comment: each row `κ t y` is a realized time-`t` marginal and hence a probability
    -- measure.
    refine ⟨fun y ↦ ?_⟩
    rw [← hY.transition_eq y t]
    exact
      Measure.isProbabilityMeasure_map
        (μ := (P y : Measure Ω)) (f := Y t) (hY.measurable_process t).aemeasurable
  have hH_meas : Measurable H := by
    -- Proof comment: the present-state coordinate is measurable.
    simpa [H] using hY.measurable_process s
  have hrow_meas : Measurable fun y ↦ ((κ t) y).real ht := by
    -- Proof comment: kernel-row masses on a measurable target set vary measurably with the
    -- present state.
    exact ((κ t).measurable_coe ht_meas).ennreal_toReal
  calc
    (μ.map H ⊗ₘ κ t).real (hs ×ˢ ht)
        = ∫ z in hs ×ˢ ht, (1 : ℝ) ∂(μ.map H ⊗ₘ κ t) := by
            symm
            exact MeasureTheory.setIntegral_one_eq_measureReal
    _ = ∫ y in hs, ∫ z in ht, (1 : ℝ) ∂(κ t y) ∂(μ.map H) := by
          have hone :
              Integrable (fun _ : NNReal × NNReal ↦ (1 : ℝ)) (μ.map H ⊗ₘ κ t) := by
            simp
          exact MeasureTheory.Measure.setIntegral_compProd hs_meas ht_meas hone.integrableOn
    _ = ∫ y in hs, ((κ t) y).real ht ∂(μ.map H) := by
          refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
          simp
    _ = ∫ ω in H ⁻¹' hs, ((κ t) (H ω)).real ht ∂μ := by
          exact
            MeasureTheory.setIntegral_map hs_meas hrow_meas.aestronglyMeasurable
              hH_meas.aemeasurable

/-- Helper for Theorem 21.48: the joint law of `(Y s, Y (s + t))` factors as the law of `Y s`
followed by the kernel row `κ t`. -/
private lemma branchingDiffusionPresentFuturePair_eq_compProd
    {Ω : Type u} [MeasurableSpace Ω]
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (hY : IsMarkovProcessRealization κ P Y) (x s t : NNReal) :
    (P x : Measure Ω).map (fun ω ↦ (Y s ω, Y (s + t) ω)) =
      ((P x : Measure Ω).map (Y s)) ⊗ₘ κ t := by
  letI : IsMarkovKernel (κ t) := by
    -- Proof comment: the candidate row kernel is Markov because each row is a realized marginal.
    refine ⟨fun y ↦ ?_⟩
    rw [← hY.transition_eq y t]
    exact
      Measure.isProbabilityMeasure_map
        (μ := (P y : Measure Ω)) (f := Y t) (hY.measurable_process t).aemeasurable
  -- Proof comment: compare the two candidate measures on measurable rectangles and invoke
  -- product-measure extensionality.
  refine Measure.ext_prod ?_
  intro hs ht hs_meas ht_meas
  have hreal :
      ((P x : Measure Ω).map (fun ω ↦ (Y s ω, Y (s + t) ω))).real (hs ×ˢ ht) =
        ((((P x : Measure Ω).map (Y s)) ⊗ₘ κ t).real (hs ×ˢ ht)) := by
    calc
      ((P x : Measure Ω).map (fun ω ↦ (Y s ω, Y (s + t) ω))).real (hs ×ˢ ht)
          = ∫ ω in (Y s) ⁻¹' hs, ((κ t) (Y s ω)).real ht ∂(P x : Measure Ω) := by
              simpa using
                (markovRealization_pairLawRealProdEqStateIntegral hY x s t hs_meas ht_meas)
      _ = ((((P x : Measure Ω).map (Y s)) ⊗ₘ κ t).real (hs ×ˢ ht)) := by
            symm
            simpa using
              (markovRealization_compProdRealProdEqStateIntegral hY x s t hs_meas ht_meas)
  exact
    (MeasureTheory.measureReal_eq_measureReal_iff
      (μ := (P x : Measure Ω).map (fun ω ↦ (Y s ω, Y (s + t) ω)))
      (ν := ((P x : Measure Ω).map (Y s)) ⊗ₘ κ t)
      (s := hs ×ˢ ht) (t := hs ×ˢ ht)
      (measure_lt_top _ _).ne (measure_lt_top _ _).ne).mp hreal

/-- Helper for Theorem 21.48: the auxiliary product-start law stores the deterministic initial
state in the first coordinate and the realized sample in the second coordinate. -/
private def branchingDiffusionProductStartMeasure
    {Ω : Type u} [MeasurableSpace Ω]
    (P : NNReal → ProbabilityMeasure Ω) (x : NNReal) :
    ProbabilityMeasure (NNReal × Ω) :=
  ⟨(Measure.dirac x).prod (P x : Measure Ω), inferInstance⟩

/-- Helper for Theorem 21.48: the product-start row is the pushforward of `P x` along the fixed
start embedding `ω ↦ (x, ω)`. -/
private lemma branchingDiffusionProductStartMeasure_eq_map_fixedStart
    {Ω : Type u} [MeasurableSpace Ω]
    (P : NNReal → ProbabilityMeasure Ω) (x : NNReal) :
    (branchingDiffusionProductStartMeasure P x : Measure (NNReal × Ω)) =
      (P x : Measure Ω).map (fun ω ↦ (x, ω)) := by
  -- Proof comment: `Measure.dirac_prod` identifies the deterministic first coordinate with the
  -- fixed-start embedding.
  change ((Measure.dirac x).prod (P x : Measure Ω)) = (P x : Measure Ω).map (fun ω ↦ (x, ω))
  rw [Measure.dirac_prod]

/-- Helper for Theorem 21.48: freezing the first coordinate of the product-start process recovers
the original realized process on the second coordinate. -/
private lemma branchingDiffusionProductStartProcess_comp_fixedStart
    {Ω : Type u} [MeasurableSpace Ω]
    {Y : NNReal → Ω → NNReal} (x t : NNReal) :
    (fun s : NNReal × Ω ↦ Y t s.2) ∘ (fun ω ↦ (x, ω)) = Y t := by
  -- Proof comment: evaluating at a fixed first coordinate simply projects to the original sample.
  funext ω
  rfl

/-- Helper for Theorem 21.48: the realized process started from `0` stays at `0` almost surely at
every deterministic time. -/
private lemma branchingDiffusion_ae_eq_zero_of_zero_start
    {Ω : Type u} [MeasurableSpace Ω]
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (t : NNReal) :
    (fun ω ↦ (Y t ω : ℝ)) =ᵐ[(P 0 : Measure Ω)] fun _ ↦ 0 := by
  let μ : Measure Ω := (P 0 : Measure Ω)
  let X : Ω → ℝ := fun ω ↦ (Y t ω : ℝ)
  have hX_int : Integrable X μ := by
    -- Proof comment: the first moment formula already gives integrability of the coordinate.
    simpa [X, μ] using branchingDiffusion_integrable hY hκ 0 t
  have hX_nonneg : 0 ≤ᵐ[μ] X := Filter.Eventually.of_forall fun _ ↦ by positivity
  have hX_mean : ∫ ω, X ω ∂μ = 0 := by
    -- Proof comment: starting from `0`, the first moment stays equal to `0`.
    simpa [X, μ, moment_one] using branchingDiffusion_first_moment hY hκ (x := 0) (t := t)
  exact (integral_eq_zero_iff_of_nonneg_ae hX_nonneg hX_int).1 hX_mean

/-- Helper for Theorem 21.48: the fourth power of a branching-diffusion coordinate is
integrable. -/
private lemma branchingDiffusion_integrablePowFour
    {Ω : Type u} [MeasurableSpace Ω]
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (x t : NNReal) :
    Integrable (fun ω ↦ ((Y t ω : ℝ) ^ 4)) (P x : Measure Ω) := by
  by_cases hx : x = 0
  · have hzero :
        (fun ω ↦ ((Y t ω : ℝ) ^ 4)) =ᵐ[(P x : Measure Ω)] fun _ ↦ 0 := by
      simpa [hx] using
        (branchingDiffusion_ae_eq_zero_of_zero_start hY hκ t).mono fun ω hω ↦ by
          simp [hω]
    exact (integrable_zero Ω ℝ (P x : Measure Ω)).congr hzero.symm
  · by_contra hbad
    have hmoment :
        moment (fun ω ↦ (Y t ω : ℝ)) 4 (P x : Measure Ω) =
          24 * (x : ℝ) * (t : ℝ) ^ 3 + 36 * (x : ℝ) ^ 2 * (t : ℝ) ^ 2 +
            12 * (x : ℝ) ^ 3 * (t : ℝ) + (x : ℝ) ^ 4 :=
      branchingDiffusion_fourth_moment hY hκ
    have hzero :
        moment (fun ω ↦ (Y t ω : ℝ)) 4 (P x : Measure Ω) = 0 := by
      simpa [moment_def] using
        (integral_undef hbad :
          ∫ ω, ((fun ω ↦ (Y t ω : ℝ)) ^ 4) ω ∂(P x : Measure Ω) = 0)
    have hx_pos : 0 < (x : ℝ) := by
      exact_mod_cast (show 0 < x from pos_iff_ne_zero.mpr hx)
    have hrhs_pos :
        0 <
          24 * (x : ℝ) * (t : ℝ) ^ 3 + 36 * (x : ℝ) ^ 2 * (t : ℝ) ^ 2 +
            12 * (x : ℝ) ^ 3 * (t : ℝ) + (x : ℝ) ^ 4 := by
      positivity
    linarith

/-- Helper for Theorem 21.48: the second power of a branching-diffusion coordinate is
integrable. -/
private lemma branchingDiffusion_integrablePowTwo
    {Ω : Type u} [MeasurableSpace Ω]
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (x t : NNReal) :
    Integrable (fun ω ↦ ((Y t ω : ℝ) ^ 2)) (P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  have hpow4 : Integrable (fun ω ↦ ((Y t ω : ℝ) ^ 4)) μ :=
    branchingDiffusion_integrablePowFour hY hκ x t
  have habs4 : Integrable (fun ω ↦ |(Y t ω : ℝ)| ^ 4) μ := by
    refine hpow4.congr ?_
    filter_upwards with ω
    simp
  have hdom : Integrable (fun ω ↦ 1 + |(Y t ω : ℝ)| ^ 4) μ := (integrable_const 1).add habs4
  have hmeas :
      AEStronglyMeasurable (fun ω ↦ ((Y t ω : ℝ) ^ 2)) μ := by
    exact
      (((continuous_subtype_val : Continuous fun y : NNReal ↦ (y : ℝ)).measurable.comp
        (hY.measurable_process t)).aemeasurable.aestronglyMeasurable).pow 2
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards with ω
  have hineq : |(Y t ω : ℝ)| ^ 2 ≤ 1 + |(Y t ω : ℝ)| ^ 4 := by
    have hsq : 0 ≤ (|(Y t ω : ℝ)| ^ 2 - (1 / 2 : ℝ)) ^ 2 := sq_nonneg _
    nlinarith
  simpa [Real.norm_eq_abs, abs_pow] using hineq

/-- Helper for Theorem 21.48: the quartic increment of the realized branching diffusion is
integrable under every fixed start law. -/
private lemma branchingDiffusion_incrementFourthIntegrable
    {Ω : Type u} [MeasurableSpace Ω]
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (x s t : NNReal) :
    Integrable (fun ω ↦ (((Y (s + t) ω : ℝ) - Y s ω) ^ 4)) (P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  have hpow4_now : Integrable (fun ω ↦ ((Y (s + t) ω : ℝ) ^ 4)) μ :=
    branchingDiffusion_integrablePowFour hY hκ x (s + t)
  have hpow4_prev : Integrable (fun ω ↦ ((Y s ω : ℝ) ^ 4)) μ :=
    branchingDiffusion_integrablePowFour hY hκ x s
  have habs4_now : Integrable (fun ω ↦ |(Y (s + t) ω : ℝ)| ^ 4) μ := by
    refine hpow4_now.congr ?_
    filter_upwards with ω
    simp
  have habs4_prev : Integrable (fun ω ↦ |(Y s ω : ℝ)| ^ 4) μ := by
    refine hpow4_prev.congr ?_
    filter_upwards with ω
    simp
  have hdom :
      Integrable (fun ω ↦ 8 * (|(Y (s + t) ω : ℝ)| ^ 4 + |(Y s ω : ℝ)| ^ 4)) μ :=
    (habs4_now.add habs4_prev).const_mul 8
  have hmeas :
      AEStronglyMeasurable (fun ω ↦ (((Y (s + t) ω : ℝ) - Y s ω) ^ 4)) μ := by
    exact
      ((((continuous_subtype_val : Continuous fun y : NNReal ↦ (y : ℝ)).measurable.comp
        (hY.measurable_process (s + t))).aemeasurable.aestronglyMeasurable).sub
        (((continuous_subtype_val : Continuous fun y : NNReal ↦ (y : ℝ)).measurable.comp
          (hY.measurable_process s)).aemeasurable.aestronglyMeasurable)).pow 4
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards with ω
  have habs :
      |((Y (s + t) ω : NNReal) : ℝ) - Y s ω| ≤
        |(Y (s + t) ω : ℝ)| + |(Y s ω : ℝ)| := by
    simpa using (_root_.abs_sub_le ((Y (s + t) ω : ℝ)) 0 (Y s ω : ℝ))
  have hpow :
      |((Y (s + t) ω : NNReal) : ℝ) - Y s ω| ^ 4 ≤
        (|(Y (s + t) ω : ℝ)| + |(Y s ω : ℝ)|) ^ 4 := by
    gcongr
  have hsum :
      (|(Y (s + t) ω : ℝ)| + |(Y s ω : ℝ)|) ^ 4 ≤
        8 * (|(Y (s + t) ω : ℝ)| ^ 4 + |(Y s ω : ℝ)| ^ 4) := by
    have hnonneg :
        0 ≤
          8 * (|(Y (s + t) ω : ℝ)| ^ 4 + |(Y s ω : ℝ)| ^ 4) -
            (|(Y (s + t) ω : ℝ)| + |(Y s ω : ℝ)|) ^ 4 := by
      have hfac :
          8 * (|(Y (s + t) ω : ℝ)| ^ 4 + |(Y s ω : ℝ)| ^ 4) -
              (|(Y (s + t) ω : ℝ)| + |(Y s ω : ℝ)|) ^ 4 =
            (|(Y (s + t) ω : ℝ)| - |(Y s ω : ℝ)|) ^ 2 *
              (7 * |(Y (s + t) ω : ℝ)| ^ 2 +
                10 * |(Y (s + t) ω : ℝ)| * |(Y s ω : ℝ)| +
                7 * |(Y s ω : ℝ)| ^ 2) := by
        ring
      rw [hfac]
      positivity
    linarith
  have hineq :
      |((Y (s + t) ω : NNReal) : ℝ) - Y s ω| ^ 4 ≤
        8 * (|(Y (s + t) ω : ℝ)| ^ 4 + |(Y s ω : ℝ)| ^ 4) := hpow.trans hsum
  simpa [Real.norm_eq_abs, abs_pow] using hineq

/-- Helper for Theorem 21.48: `edist^4` on real-valued coordinates is the `ENNReal.ofReal` image
of the quartic increment polynomial. -/
private lemma realEdist_pow_four_eq_ofReal_sub_pow_four (a b : ℝ) :
    edist a b ^ (4 : ℝ) = ENNReal.ofReal ((b - a) ^ 4) := by
  rw [show (4 : ℝ) = (4 : ℕ) by norm_num, ENNReal.rpow_natCast]
  rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg (a - b))]
  congr 1
  have habs : |a - b| ^ 4 = (a - b) ^ 4 := by
    rw [show |a - b| ^ 4 = (|a - b| ^ 2) ^ 2 by ring,
      show (a - b) ^ 4 = ((a - b) ^ 2) ^ 2 by ring, sq_abs]
  calc
    |a - b| ^ 4 = (a - b) ^ 4 := habs
    _ = (b - a) ^ 4 := by ring_nf

/-- Helper for Theorem 21.48: the quartic increment moment has the explicit source polynomial
form. -/
private lemma branchingDiffusionIncrementFourthMomentEq
    {Ω : Type u} [MeasurableSpace Ω]
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (x s t : NNReal) :
    ∫ ω, (((Y (s + t) ω : ℝ) - Y s ω) ^ 4) ∂(P x : Measure Ω) =
      24 * (x : ℝ) * (t : ℝ) ^ 3 +
        12 * (2 * (s : ℝ) * (x : ℝ) + (x : ℝ) ^ 2) * (t : ℝ) ^ 2 := by
  let μ : Measure Ω := (P x : Measure Ω)
  let pairMap : Ω → NNReal × NNReal := fun ω ↦ (Y s ω, Y (s + t) ω)
  let F : NNReal × NNReal → ℝ := fun p ↦ (((p.2 : ℝ) - (p.1 : ℝ)) ^ 4)
  have hpair_meas : Measurable pairMap := by
    -- Proof comment: the present/future pair map is measurable coordinatewise.
    simpa [pairMap] using (hY.measurable_process s).prodMk (hY.measurable_process (s + t))
  have hF_meas : Measurable F := by
    -- Proof comment: the quartic observable on the state pair is continuous.
    fun_prop
  have hinc_int :
      Integrable (fun ω ↦ (((Y (s + t) ω : ℝ) - Y s ω) ^ 4)) μ :=
    branchingDiffusion_incrementFourthIntegrable hY hκ x s t
  have hjoint_int : Integrable F (μ.map pairMap) := by
    -- Proof comment: push the already-integrable quartic increment through the pair map.
    refine
      (MeasureTheory.integrable_map_measure (μ := μ) (f := pairMap) (g := F)
        hF_meas.aestronglyMeasurable hpair_meas.aemeasurable).2 ?_
    simpa [μ, pairMap, F] using hinc_int
  have hcomp_int : Integrable F (((μ.map (Y s)) ⊗ₘ κ t)) := by
    -- Proof comment: the present/future pair law agrees with the composition product.
    rw [branchingDiffusionPresentFuturePair_eq_compProd hY x s t] at hjoint_int
    simpa using hjoint_int
  letI : IsMarkovKernel (κ t) := by
    -- Proof comment: each kernel row is a realized time-`t` marginal and hence a probability
    -- measure.
    refine ⟨fun y ↦ ?_⟩
    rw [← hY.transition_eq y t]
    exact
      Measure.isProbabilityMeasure_map
        (μ := (P y : Measure Ω)) (f := Y t) (hY.measurable_process t).aemeasurable
  have hmap1_int : Integrable (fun y : NNReal ↦ (y : ℝ)) (μ.map (Y s)) := by
    refine
      (MeasureTheory.integrable_map_measure (μ := μ) (f := Y s)
        (g := fun y : NNReal ↦ (y : ℝ))
        (continuous_subtype_val : Continuous fun y : NNReal ↦ (y : ℝ)).aestronglyMeasurable
        (hY.measurable_process s).aemeasurable).2 ?_
    simpa [μ] using branchingDiffusion_integrable hY hκ x s
  have hmap2_int : Integrable (fun y : NNReal ↦ (y : ℝ) ^ 2) (μ.map (Y s)) := by
    refine
      (MeasureTheory.integrable_map_measure (μ := μ) (f := Y s)
        (g := fun y : NNReal ↦ (y : ℝ) ^ 2)
        (by fun_prop) (hY.measurable_process s).aemeasurable).2 ?_
    simpa [μ] using branchingDiffusion_integrablePowTwo hY hκ x s
  have hmap1 :
      ∫ y, (y : ℝ) ∂(μ.map (Y s)) = (x : ℝ) := by
    -- Proof comment: the present-state mean is the first moment at time `s`.
    rw [MeasureTheory.integral_map (hY.measurable_process s).aemeasurable]
    · simpa [μ, moment_one] using branchingDiffusion_first_moment hY hκ (x := x) (t := s)
    · exact (continuous_subtype_val : Continuous fun y : NNReal ↦ (y : ℝ)).aestronglyMeasurable
  have hmap2 :
      ∫ y, (y : ℝ) ^ 2 ∂(μ.map (Y s)) =
        2 * (x : ℝ) * (s : ℝ) + (x : ℝ) ^ 2 := by
    -- Proof comment: the present-state quadratic moment is the second moment at time `s`.
    rw [MeasureTheory.integral_map (hY.measurable_process s).aemeasurable]
    · simpa [μ, moment_def] using branchingDiffusion_second_moment hY hκ (x := x) (t := s)
    · fun_prop
  have hpoly :
      ∫ y, (24 * (y : ℝ) * (t : ℝ) ^ 3 + 12 * (y : ℝ) ^ 2 * (t : ℝ) ^ 2) ∂(μ.map (Y s)) =
        24 * (x : ℝ) * (t : ℝ) ^ 3 +
          12 * (2 * (s : ℝ) * (x : ℝ) + (x : ℝ) ^ 2) * (t : ℝ) ^ 2 := by
    have hpoly_fun :
        (fun y : NNReal ↦ 24 * (y : ℝ) * (t : ℝ) ^ 3 + 12 * (y : ℝ) ^ 2 * (t : ℝ) ^ 2) =
          (fun y : NNReal ↦
            (24 * (t : ℝ) ^ 3) * (y : ℝ) + (12 * (t : ℝ) ^ 2) * ((y : ℝ) ^ 2)) := by
      funext y
      ring
    rw [hpoly_fun, integral_add (hmap1_int.const_mul _) (hmap2_int.const_mul _)]
    simp_rw [integral_const_mul]
    rw [hmap1, hmap2]
    ring
  -- Proof comment: factor the pair law, evaluate the inner kernel-row fourth moment, and then
  -- substitute the present-state first and second moments.
  calc
    ∫ ω, (((Y (s + t) ω : ℝ) - Y s ω) ^ 4) ∂μ =
        ∫ p, F p ∂(μ.map pairMap) := by
          symm
          rw [MeasureTheory.integral_map hpair_meas.aemeasurable hF_meas.aestronglyMeasurable]
    _ = ∫ p, F p ∂(((μ.map (Y s)) ⊗ₘ κ t)) := by
          rw [branchingDiffusionPresentFuturePair_eq_compProd hY x s t]
    _ = ∫ y, ∫ z, (((z : ℝ) - (y : ℝ)) ^ 4) ∂κ t y ∂(μ.map (Y s)) := by
          simpa [F] using
            (MeasureTheory.Measure.integral_compProd (μ := μ.map (Y s)) (κ := κ t) hcomp_int)
    _ = ∫ y, (24 * (y : ℝ) * (t : ℝ) ^ 3 + 12 * (y : ℝ) ^ 2 * (t : ℝ) ^ 2)
          ∂(μ.map (Y s)) := by
          refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
          simpa using branchingDiffusionKernelRow_fourthCenteredMoment hY hκ t y
    _ =
        24 * (x : ℝ) * (t : ℝ) ^ 3 +
          12 * (2 * (s : ℝ) * (x : ℝ) + (x : ℝ) ^ 2) * (t : ℝ) ^ 2 := hpoly

/-- Helper for Theorem 21.48: for ordered times in `Set.Icc (0,T)`, the squared interval
distance is the squared real time gap. -/
private lemma subtypeIccEdistPowTwoEqOfLe
    {T : NNReal} {s t : Set.Icc (0 : NNReal) T} (hst : s.1 ≤ t.1) :
    edist s t ^ (2 : ℝ) = ENNReal.ofReal (((t.1 : ℝ) - s.1) ^ 2) := by
  -- Proof comment: on an ordered interval pair, the subtype distance is just the ambient real
  -- difference `t - s`, so squaring it removes the remaining metric wrapper.
  rw [show (2 : ℝ) = (2 : ℕ) by norm_num, ENNReal.rpow_natCast]
  rw [edist_dist, Subtype.dist_eq, NNReal.dist_eq]
  have hst_real : (s.1 : ℝ) ≤ t.1 := by
    exact_mod_cast hst
  have hgap_nonneg : 0 ≤ (t.1 : ℝ) - s.1 := sub_nonneg.mpr hst_real
  have habs : |(s.1 : ℝ) - t.1| = (t.1 : ℝ) - s.1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hst_real)]
    ring
  rw [habs, ← ENNReal.ofReal_pow hgap_nonneg]

/-- Helper for Theorem 21.48: on an ordered pair of interval times, the realized branching
diffusion satisfies the quartic Kolmogorov bound with the finite-horizon constant
`48Tx + 12x²`. -/
private lemma branchingDiffusionKolmogorovOrderedPairBound
    {Ω : Type u} [MeasurableSpace Ω]
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (x T : NNReal) :
    ∀ {s t : Set.Icc (0 : NNReal) T}, s.1 ≤ t.1 →
      (∫⁻ ω, edist ((Y s.1 ω : ℝ)) (Y t.1 ω : ℝ) ^ (4 : ℝ) ∂(P x : Measure Ω)) ≤
        ENNReal.ofReal
          ((((48 * T * x + 12 * x ^ 2 : NNReal) : ℝ) * (((t.1 : ℝ) - s.1) ^ 2))) := by
  intro s t hst
  let μ : Measure Ω := (P x : Measure Ω)
  let u : NNReal := t.1 - s.1
  have hu_sq :
      ((u : ℝ) ^ 2) = (((t.1 : ℝ) - s.1) ^ 2) := by
    simp [u, NNReal.coe_sub hst]
  have hinc_int :
      Integrable (fun ω ↦ (((Y t.1 ω : ℝ) - Y s.1 ω) ^ 4)) μ := by
    -- Proof comment: rewrite the ordered pair `(s,t)` into the increment form
    -- `(s, s + (t - s))` used by the existing integrability lemma.
    refine (branchingDiffusion_incrementFourthIntegrable hY hκ x s.1 u).congr ?_
    filter_upwards with ω
    simp [u, add_tsub_cancel_of_le hst]
  have hmoment :
      ∫ ω, (((Y t.1 ω : ℝ) - Y s.1 ω) ^ 4) ∂μ =
        24 * (x : ℝ) * (u : ℝ) ^ 3 +
          12 * (2 * (s.1 : ℝ) * (x : ℝ) + (x : ℝ) ^ 2) * (u : ℝ) ^ 2 := by
    -- Proof comment: the exact fourth-increment identity already exists once the time gap is
    -- named as `u = t - s`.
    simpa [μ, u, add_tsub_cancel_of_le hst] using
      branchingDiffusionIncrementFourthMomentEq hY hκ x s.1 u
  have hpoly_le :
      24 * (x : ℝ) * (u : ℝ) ^ 3 +
          12 * (2 * (s.1 : ℝ) * (x : ℝ) + (x : ℝ) ^ 2) * (u : ℝ) ^ 2 ≤
        ((48 * T * x + 12 * x ^ 2 : NNReal) : ℝ) * (u : ℝ) ^ 2 := by
    have hs_le_T : (s.1 : ℝ) ≤ T := by exact_mod_cast s.2.2
    have hu_le_t : u ≤ t.1 := by
      exact tsub_le_self
    have hu_le_T : (u : ℝ) ≤ T := by
      exact_mod_cast (le_trans hu_le_t t.2.2)
    have hcoeff :
        (((48 * T * x + 12 * x ^ 2 : NNReal) : ℝ)) =
          48 * (T : ℝ) * (x : ℝ) + 12 * (x : ℝ) ^ 2 := by
      norm_num
    have hx_nonneg : 0 ≤ (x : ℝ) := by positivity
    have hu_sq_nonneg : 0 ≤ (u : ℝ) ^ 2 := by positivity
    have hu_mul_le : (u : ℝ) * (u : ℝ) ^ 2 ≤ T * (u : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hu_le_T hu_sq_nonneg
    have hs_mul_le : (s.1 : ℝ) * (u : ℝ) ^ 2 ≤ T * (u : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hs_le_T hu_sq_nonneg
    rw [hcoeff, pow_three]
    nlinarith [hu_mul_le, hs_mul_le, hx_nonneg]
  -- Proof comment: convert the quartic `lintegral` back to the explicit real moment identity,
  -- then compare the resulting polynomial with the finite-horizon bound.
  have hedist_eq :
      ∫⁻ ω, edist ((Y s.1 ω : ℝ)) (Y t.1 ω : ℝ) ^ (4 : ℝ) ∂(P x : Measure Ω) =
        ∫⁻ ω, ENNReal.ofReal (((Y t.1 ω : ℝ) - Y s.1 ω) ^ 4) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with ω
    simpa using
      realEdist_pow_four_eq_ofReal_sub_pow_four (Y s.1 ω) (Y t.1 ω)
  calc
    ∫⁻ ω, edist ((Y s.1 ω : ℝ)) (Y t.1 ω : ℝ) ^ (4 : ℝ) ∂(P x : Measure Ω)
        = ENNReal.ofReal
            (∫ ω, (((Y t.1 ω : ℝ) - Y s.1 ω) ^ 4) ∂μ) := by
            rw [hedist_eq]
            symm
            exact
              MeasureTheory.ofReal_integral_eq_lintegral_ofReal hinc_int
                (Filter.Eventually.of_forall fun ω ↦ by positivity)
    _ = ENNReal.ofReal
          (24 * (x : ℝ) * (u : ℝ) ^ 3 +
            12 * (2 * (s.1 : ℝ) * (x : ℝ) + (x : ℝ) ^ 2) * (u : ℝ) ^ 2) := by
          rw [hmoment]
    _ ≤ ENNReal.ofReal (((48 * T * x + 12 * x ^ 2 : NNReal) : ℝ) * (u : ℝ) ^ 2) := by
          exact ENNReal.ofReal_le_ofReal hpoly_le
    _ = ENNReal.ofReal
          ((((48 * T * x + 12 * x ^ 2 : NNReal) : ℝ) * (((t.1 : ℝ) - s.1) ^ 2))) := by
          rw [hu_sq]

/-- Helper for Theorem 21.48: under a fixed start law, the realized branching diffusion satisfies
the finite-horizon Kolmogorov criterion with exponents `4` and `1`. -/
private lemma branchingDiffusionKolmogorovOnIccAtStart
    {Ω : Type u} [MeasurableSpace Ω]
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (x T : NNReal) :
    ∃ C : ℝ≥0, IsKolmogorovProcessOnIcc
      (P x : Measure Ω) (fun t ω ↦ (Y t ω : ℝ)) T (4 : ℝ≥0) (1 : ℝ≥0) C := by
  let C : ℝ≥0 := 48 * T * x + 12 * x ^ 2
  refine ⟨C, ?_⟩
  refine ⟨by positivity, by positivity, ?_⟩
  -- Route correction: the failed monolithic wrapper is replaced by one ordered-pair moment bound
  -- plus a symmetry step, so the owner packaging only has to assemble the stable local pieces.
  refine IsKolmogorovProcess.mk_of_secondCountableTopology ?_ ?_ (by positivity) (by norm_num)
  · intro t
    -- Proof comment: each restricted time slice is measurable because the realization is
    -- measurable at every ambient time.
    exact
      (continuous_subtype_val : Continuous fun y : NNReal ↦ (y : ℝ)).measurable.comp
        (hY.measurable_process t.1)
  · intro s t
    -- Proof comment: use the ordered-pair bound when `s ≤ t`, and otherwise swap the pair and
    -- exploit symmetry of `edist` in both the state and time coordinates.
    by_cases hst : s.1 ≤ t.1
    · have hq : (1 + ((1 : ℝ≥0) : ℝ)) = (2 : ℝ) := by norm_num
      have hcoeff_nonneg : 0 ≤ ((C : ℝ≥0) : ℝ) := by
        positivity
      have hbranch :
          (∫⁻ ω, edist ((fun t ω ↦ (Y t ω : ℝ)) s ω) ((fun t ω ↦ (Y t ω : ℝ)) t ω) ^
              ((4 : ℝ≥0) : ℝ) ∂(P x : Measure Ω)) ≤
            ENNReal.ofNNReal C * edist s t ^ (2 : ℝ) := by
        rw [subtypeIccEdistPowTwoEqOfLe hst]
        calc
          ∫⁻ ω, edist ((fun t ω ↦ (Y t ω : ℝ)) s ω) ((fun t ω ↦ (Y t ω : ℝ)) t ω) ^ (4 : ℝ)
              ∂(P x : Measure Ω)
              ≤ ENNReal.ofReal (((C : ℝ≥0) : ℝ) * (((t.1 : ℝ) - s.1) ^ 2)) := by
                simpa [C] using
                  branchingDiffusionKolmogorovOrderedPairBound hY hκ x T (s := s) (t := t) hst
          _ = ENNReal.ofNNReal C * ENNReal.ofReal (((t.1 : ℝ) - s.1) ^ 2) := by
              rw [ENNReal.ofReal_mul hcoeff_nonneg, ENNReal.coe_nnreal_eq]
      convert hbranch using 1 <;> norm_num
    · have hts : t.1 ≤ s.1 := le_of_not_ge hst
      have hswap :=
        branchingDiffusionKolmogorovOrderedPairBound hY hκ x T (s := t) (t := s) hts
      have hq : (1 + ((1 : ℝ≥0) : ℝ)) = (2 : ℝ) := by norm_num
      have hcoeff_nonneg : 0 ≤ ((C : ℝ≥0) : ℝ) := by
        positivity
      have hbranch :
          (∫⁻ ω, edist ((fun t ω ↦ (Y t ω : ℝ)) s ω) ((fun t ω ↦ (Y t ω : ℝ)) t ω) ^
              ((4 : ℝ≥0) : ℝ) ∂(P x : Measure Ω)) ≤
            ENNReal.ofNNReal C * edist s t ^ (2 : ℝ) := by
        rw [edist_comm, subtypeIccEdistPowTwoEqOfLe hts]
        calc
          ∫⁻ ω, edist ((fun t ω ↦ (Y t ω : ℝ)) s ω) ((fun t ω ↦ (Y t ω : ℝ)) t ω) ^ (4 : ℝ)
              ∂(P x : Measure Ω)
              = ∫⁻ ω, edist ((fun t ω ↦ (Y t ω : ℝ)) t ω) ((fun t ω ↦ (Y t ω : ℝ)) s ω) ^ (4 : ℝ)
                  ∂(P x : Measure Ω) := by
                    refine lintegral_congr_ae ?_
                    filter_upwards with ω
                    rw [edist_comm]
          _ ≤ ENNReal.ofReal (((C : ℝ≥0) : ℝ) * (((s.1 : ℝ) - t.1) ^ 2)) := by
              simpa [C] using hswap
          _ = ENNReal.ofNNReal C * ENNReal.ofReal (((s.1 : ℝ) - t.1) ^ 2) := by
              rw [ENNReal.ofReal_mul hcoeff_nonneg, ENNReal.coe_nnreal_eq]
      convert hbranch using 1 <;> norm_num

/-- Helper for Theorem 21.48: each fixed start law admits a continuous `NNReal`-valued version on
the original realization space. -/
private lemma existsContinuousVersionAtStart
    {Ω : Type u} [MeasurableSpace Ω]
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (x : NNReal) :
    ∃ Ycx : NNReal → Ω → NNReal,
      AreModifications (P x : Measure Ω) Y Ycx ∧
        HasAlmostSurelyContinuousPaths (P x : Measure Ω) Ycx := by
  let Yr : NNReal → Ω → ℝ := fun t ω ↦ (Y t ω : ℝ)
  have hkolm :
      ∀ T : NNReal, ∃ C : ℝ≥0,
        IsKolmogorovProcessOnIcc (P x : Measure Ω) Yr T (4 : ℝ≥0) (1 : ℝ≥0) C := by
    intro T
    simpa [Yr] using branchingDiffusionKolmogorovOnIccAtStart hY hκ x T
  rcases existsContinuousRealModificationOfKolmogorov (μ := (P x : Measure Ω)) (X := Yr) hkolm with
    ⟨YrC, hmod, hcont⟩
  -- Proof comment: once the real-valued continuous version exists, `Real.toNNReal` transports it
  -- back to an `NNReal`-valued continuous version of the original process.
  exact
    continuousNnrealVersionOfRealModification (μ := (P x : Measure Ω)) (Ynn := Y)
      (Yr := Yr) (YrC := YrC) hmod (fun t ω ↦ rfl) hcont

-- Proof sketch: first use
-- `exists_markovProcessRealization_of_branchingDiffusionKernel` to realize the kernel family by a
-- Markov process `(P, Y)`. Then identify the one-time marginals through
-- `IsMarkovProcessRealization.hasBranchingDiffusionMarginalLaplaceTransform`, derive the required
-- fourth-moment increment bounds from Lemma 21.47, and apply
-- `exists_modification_with_locally_holder_paths` under each initial law `P x`. Finally, forget
-- the stronger local Hölder conclusion and retain only almost sure continuity.
/-- Theorem 21.48: if `κ` is the branching-diffusion transition semigroup from `(21.44)`, then
there exist a Markov-process realization `Y` of `κ` and a process `Yc` on the same measurable
space such that, for every initial state `x`, `Yc` is a version of `Y` under `P x` with almost
surely continuous sample paths. This continuous version is Feller's branching diffusion. -/
theorem exists_continuous_branchingDiffusion_version
    {κ : NNReal → Kernel NNReal NNReal} (hκ : HasBranchingDiffusionLaplaceTransform κ) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (Y : NNReal → Ω → NNReal)
      (P : NNReal → ProbabilityMeasure Ω) (Yc : NNReal → Ω → NNReal),
        IsMarkovProcessRealization κ P Y ∧
          ∀ x : NNReal,
            AreModifications (P x : Measure Ω) Y Yc ∧
              HasAlmostSurelyContinuousPaths (P x : Measure Ω) Yc := by
  have hrealization :
      ∃ (Ω : Type u), ∃ _ : MeasurableSpace Ω, ∃ Y : NNReal → Ω → NNReal,
        ∃ P : NNReal → ProbabilityMeasure Ω, IsMarkovProcessRealization κ P Y := by
    exact
      (show
          ∃ (Ω : Type u), ∃ _ : MeasurableSpace Ω, ∃ Y : NNReal → Ω → NNReal,
            ∃ P : NNReal → ProbabilityMeasure Ω, IsMarkovProcessRealization κ P Y from
        exists_markovProcessRealization_of_branchingDiffusionKernel hκ)
  rcases hrealization with ⟨Ω, mΩ, Y, P, hY⟩
  have hstart :
      ∀ x : NNReal, ∃ Ycx : NNReal → Ω → NNReal,
        AreModifications (P x : Measure Ω) Y Ycx ∧
          HasAlmostSurelyContinuousPaths (P x : Measure Ω) Ycx := by
    intro x
    exact existsContinuousVersionAtStart hY hκ x
  classical
  choose Ystart hYstart using hstart
  let Yc : NNReal → Ω → NNReal := fun t ω ↦ Ystart (Y 0 ω) t ω
  refine ⟨Ω, mΩ, Y, P, Yc, hY, ?_⟩
  intro x
  have hinit :
      (fun ω ↦ Y 0 ω) =ᵐ[(P x : Measure Ω)] fun _ ↦ x := by
    have hmap0 :
        (P x : Measure Ω).map (Y 0) = Measure.dirac x := by
      calc
        (P x : Measure Ω).map (Y 0) = κ 0 x := hY.transition_eq x 0
        _ = Measure.dirac x := by
          simpa [Kernel.id_apply] using
            congrArg (fun k : Kernel NNReal NNReal ↦ k x)
              (branchingDiffusionKernel_zero_eq_id hκ)
    have hzero_pre :
        (P x : Measure Ω) ((Y 0) ⁻¹' (({x} : Set NNReal)ᶜ)) = 0 := by
      simpa [Measure.map_apply (hY.measurable_process 0) (MeasurableSet.singleton _).compl] using
        congrArg (fun ν : Measure NNReal ↦ ν (({x} : Set NNReal)ᶜ)) hmap0
    rw [Filter.EventuallyEq, ae_iff]
    simpa using hzero_pre
  refine ⟨?_, ?_⟩
  · intro t
    -- Proof comment: on the full-measure event `{Y 0 = x}`, the global version specializes to
    -- the chosen startwise version `Ystart x`.
    filter_upwards [hinit, (hYstart x).1 t] with ω hω0 hωt
    simpa [Yc, hω0] using hωt
  · filter_upwards [hinit, (hYstart x).2] with ω hω0 hωcont
    -- Proof comment: the sample path of the global process agrees with the chosen startwise
    -- continuous path on the same full-measure event.
    have hpath : processPath Yc ω = processPath (Ystart x) ω := by
      funext t
      simp [processPath, Yc, hω0]
    simpa [hpath] using hωcont

end ProbabilityTheory
