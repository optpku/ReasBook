/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Corollary_15_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_1_2

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ωn : ℕ → Type u} [∀ n : ℕ, MeasurableSpace (Ωn n)]
variable {Ω : Type v} [MeasurableSpace Ω]

/-- Natural Markov property localized for Theorem 21.50: every coordinate is measurable, and for
`s ≤ t` the conditional law of the future state event `{Y t ∈ A}` given the full history up to
time `s` agrees almost surely with conditioning only on the present state `Y s`. -/
def HasNaturalMarkovProperty (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : NNReal → Ω → NNReal) :
    Prop :=
  (∀ t : NNReal, Measurable (Y t)) ∧
    ∀ ⦃s t : NNReal⦄, s ≤ t → ∀ ⦃A : Set NNReal⦄, MeasurableSet A →
      μ⟦Y t ⁻¹' A | generatedFiltrationSpace Y s⟧ =ᵐ[μ]
        μ⟦Y t ⁻¹' A | MeasurableSpace.comap (Y s) inferInstance⟧

/-- Markov-process realization shell localized for Theorem 21.50: each time slice is measurable,
one-time marginals are the kernel rows, and the source-faithful future-event Markov property is
available on the generated filtration. -/
class IsMarkovProcessRealization (κ : NNReal → Kernel NNReal NNReal)
    (P : NNReal → ProbabilityMeasure Ω) (Y : NNReal → Ω → NNReal) : Prop where
  /-- Every time slice of the realized process is measurable. -/
  measurable_process : ∀ t : NNReal, Measurable (Y t)
  /-- The one-time marginal at time `t` started from `x` is the kernel row `κ t x`. -/
  transition_eq : ∀ x : NNReal, ∀ t : NNReal, (P x : Measure Ω).map (Y t) = κ t x
  /-- The faithful future-event Markov property carried by the realization. -/
  markov_property :
    ∀ x : NNReal, ∀ ⦃A : Set NNReal⦄, MeasurableSet A → ∀ s t : NNReal,
      (P x)⟦Y (t + s) ⁻¹' A | generatedFiltrationSpace Y s⟧ =ᵐ[(P x : Measure Ω)]
        fun ω ↦ ((κ t) (Y s ω)).real A

/-- The kernel family `κ` has the branching-diffusion Laplace transform
`E_x[e^{-λ Y_t}] = exp (- λ x / (1 + λ t))` for all nonnegative times and Laplace parameters. -/
def HasBranchingDiffusionLaplaceTransform (κ : NNReal → Kernel NNReal NNReal) : Prop :=
  ∀ x t lam : NNReal,
    ∫ y, Real.exp (-((lam : ℝ) * (y : ℝ))) ∂κ t x =
      Real.exp (-((lam : ℝ) * (x : ℝ)) / (((lam : ℝ) * (t : ℝ)) + 1))

/-- The textbook Laplace transform of the branching diffusion started from `x` and observed at time
`t`. -/
def branchingDiffusionLaplaceTransform (t x : NNReal) : ℝ → ℝ :=
  fun l ↦ Real.exp (-((x : ℝ) * l / (l * (t : ℝ) + 1)))

/-- Evaluating `branchingDiffusionLaplaceTransform` gives the explicit exponential formula
`exp (-x λ / (1 + t λ))`. -/
theorem branchingDiffusionLaplaceTransform_apply (t x : NNReal) (l : ℝ) :
    branchingDiffusionLaplaceTransform t x l =
      Real.exp (-((x : ℝ) * l / (l * (t : ℝ) + 1))) := by
  -- Proof comment: this is just the defining equation of the textbook Laplace transform.
  rfl

/-- Helper for Theorem 21.50: the present-state sigma-algebra at time `s` is one of the
generators of `generatedFiltrationSpace Y s`. -/
private lemma present_le_generatedFiltrationSpace (Y : NNReal → Ω → NNReal) (s : NNReal) :
    MeasurableSpace.comap (Y s) inferInstance ≤ generatedFiltrationSpace Y s := by
  -- Proof comment: the defining supremum for the generated filtration already contains the
  -- coordinate `Y s`.
  exact le_iSup_of_le s <| le_iSup_of_le le_rfl le_rfl

/-- Helper for Theorem 21.50: every earlier coordinate `Y r` with `r ≤ s` is measurable for the
history sigma-algebra `generatedFiltrationSpace Y s`. -/
private lemma past_le_generatedFiltrationSpace (Y : NNReal → Ω → NNReal) {r s : NNReal}
    (hrs : r ≤ s) :
    MeasurableSpace.comap (Y r) inferInstance ≤ generatedFiltrationSpace Y s := by
  -- Proof comment: the generator indexed by the earlier time `r` is one of the terms in the
  -- supremum defining the time-`s` history.
  exact le_iSup_of_le r <| le_iSup_of_le hrs le_rfl

/-- Helper for Theorem 21.50: if every coordinate of `Y` is ambient measurable, then the generated
history sigma-algebra is ambient as well. -/
private lemma generatedFiltrationSpace_le_ambient (Y : NNReal → Ω → NNReal)
    (hY : ∀ t : NNReal, Measurable (Y t)) (s : NNReal) :
    generatedFiltrationSpace Y s ≤ ‹MeasurableSpace Ω› := by
  -- Proof comment: every generator `MeasurableSpace.comap (Y r)` already lies inside the ambient
  -- measurable space.
  refine iSup_le fun r ↦ ?_
  refine iSup_le fun hr ↦ ?_
  exact (hY r).comap_le

/-- Helper for Theorem 21.50: multiplying the future Laplace factor by the present exponential
weight simply adds the two coefficients in the exponent. -/
theorem branchingDiffusionLaplaceTransform_updateCoeff (t y l a : NNReal) :
    ProbabilityTheory.branchingDiffusionLaplaceTransform t y l *
        Real.exp (-((a : ℝ) * (y : ℝ))) =
      Real.exp (-((((a : ℝ) + (l : ℝ) / (((l : ℝ) * (t : ℝ)) + 1)) * (y : ℝ)))) := by
  -- Proof comment: rewrite the branching-diffusion Laplace factor explicitly and then combine the
  -- two exponentials into one by collecting the coefficient of `y`.
  rw [ProbabilityTheory.branchingDiffusionLaplaceTransform_apply]
  have hden : (((l : ℝ) * (t : ℝ)) + 1) ≠ 0 := by
    positivity
  rw [← Real.exp_add]
  congr 1
  field_simp [hden]
  ring

/-- Helper for Theorem 21.50: the realization-level future-event Markov field descends to the
present-state sigma-algebra. -/
-- TODO(Theorem 21.50): descend the event-level conditional expectation from
-- `generatedFiltrationSpace Y s` to `MeasurableSpace.comap (Y s)` using the present-state
-- measurability inclusion and a conditional-expectation uniqueness lemma.
theorem IsMarkovProcessRealization.hasNaturalMarkovProperty
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (hY : IsMarkovProcessRealization κ P Y) (x : NNReal) :
    HasNaturalMarkovProperty (P x : Measure Ω) Y := by
  refine ⟨hY.measurable_process, ?_⟩
  intro s t hst A hA
  let μ : Measure Ω := (P x : Measure Ω)
  let g : Ω → ℝ := fun ω ↦ ((κ (t - s)) (Y s ω)).real A
  letI : IsMarkovKernel (κ (t - s)) := by
    -- Proof comment: every row of `κ (t - s)` is a realized one-time marginal, hence a
    -- probability measure.
    refine ⟨fun y ↦ ?_⟩
    rw [← hY.transition_eq y (t - s)]
    exact
      Measure.isProbabilityMeasure_map (hY.measurable_process (t - s)).aemeasurable
  have hsmall_le :
      MeasurableSpace.comap (Y s) inferInstance ≤ generatedFiltrationSpace Y s := by
    -- Proof comment: the present-state sigma-algebra is one of the generators of the history.
    exact present_le_generatedFiltrationSpace Y s
  have hlarge_le : generatedFiltrationSpace Y s ≤ ‹MeasurableSpace Ω› := by
    -- Proof comment: the realized process is coordinatewise measurable, so its generated history
    -- lives inside the ambient measurable space.
    exact generatedFiltrationSpace_le_ambient Y hY.measurable_process s
  have hg :
      AEStronglyMeasurable[MeasurableSpace.comap (Y s) inferInstance] g μ := by
    have hg_meas :
        Measurable[MeasurableSpace.comap (Y s) inferInstance] g := by
      -- Proof comment: kernel-row masses are measurable in the state argument, and `Y s` is
      -- measurable for its own pullback sigma-algebra.
      refine (((κ (t - s)).measurable_coe hA).ennreal_toReal).comp ?_
      exact Measurable.of_comap_le le_rfl
    exact hg_meas.aestronglyMeasurable
  have hg_int : Integrable g μ := by
    -- Proof comment: kernel-row masses lie in `[0, 1]`, so they are integrable under the
    -- probability law `μ`.
    refine Integrable.mono' (integrable_const (1 : ℝ))
      ((((κ (t - s)).measurable_coe hA).ennreal_toReal.comp
        (hY.measurable_process s)).aestronglyMeasurable) ?_
    filter_upwards with ω
    have hnonneg : 0 ≤ g ω := MeasureTheory.measureReal_nonneg
    have hle : g ω ≤ 1 := MeasureTheory.measureReal_le_one
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hmarkov :
      μ⟦Y t ⁻¹' A | generatedFiltrationSpace Y s⟧ =ᵐ[μ] g := by
    -- Proof comment: rewrite `t` as `(t - s) + s` and apply the source-faithful event-level
    -- Markov field carried by the realization.
    simpa [μ, g, add_comm, add_left_comm, add_assoc, add_tsub_cancel_of_le hst] using
      hY.markov_property x hA s (t - s)
  have hdesc :
      μ⟦Y t ⁻¹' A | MeasurableSpace.comap (Y s) inferInstance⟧ =ᵐ[μ]
        μ⟦Y t ⁻¹' A | generatedFiltrationSpace Y s⟧ := by
    -- Proof comment: descend the conditional expectation from the whole history to the present
    -- state by the tower property and then identify the present-state conditional expectation
    -- with the already measurable kernel-row function `g`.
    calc
      μ⟦Y t ⁻¹' A | MeasurableSpace.comap (Y s) inferInstance⟧ =ᵐ[μ]
          μ[μ[((Y t ⁻¹' A).indicator fun _ ↦ (1 : ℝ)) | generatedFiltrationSpace Y s] |
            MeasurableSpace.comap (Y s) inferInstance] := by
              symm
              exact condExp_condExp_of_le hsmall_le hlarge_le
      _ =ᵐ[μ] μ[g | MeasurableSpace.comap (Y s) inferInstance] := by
            exact condExp_congr_ae hmarkov
      _ =ᵐ[μ] g := by
            exact condExp_of_aestronglyMeasurable' (hsmall_le.trans hlarge_le) hg hg_int
      _ =ᵐ[μ] μ⟦Y t ⁻¹' A | generatedFiltrationSpace Y s⟧ := hmarkov.symm
  exact hdesc.symm

/-- Helper for Theorem 21.50: a realization of the branching-diffusion kernel inherits the
textbook one-time Laplace-transform formula. -/
theorem IsMarkovProcessRealization.branchingDiffusionLaplaceTransform
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (x t l : NNReal) :
    ∫ ω, Real.exp (-((l : ℝ) * (Y t ω : ℝ))) ∂(P x : Measure Ω) =
      ProbabilityTheory.branchingDiffusionLaplaceTransform t x l := by
  let laplaceWeight : NNReal → ℝ := fun y ↦ Real.exp (-((l : ℝ) * (y : ℝ)))
  have hlaplaceWeight_meas : Measurable laplaceWeight := by
    -- Proof comment: the Laplace observable is a continuous function of the state variable.
    exact
      Real.continuous_exp.measurable.comp
        (((continuous_subtype_val : Continuous fun y : NNReal ↦ (y : ℝ)).measurable.const_mul
          (l : ℝ)).neg)
  -- Proof comment: rewrite the integral through the pushed-forward one-time marginal and then
  -- apply the kernel Laplace formula `hκ` to the row `κ t x`.
  calc
    ∫ ω, Real.exp (-((l : ℝ) * (Y t ω : ℝ))) ∂(P x : Measure Ω) =
        ∫ y, laplaceWeight y ∂((P x : Measure Ω).map (Y t)) := by
          symm
          simpa [laplaceWeight] using
            (MeasureTheory.integral_map
              (hY.measurable_process t).aemeasurable hlaplaceWeight_meas.aestronglyMeasurable)
    _ = ∫ y, laplaceWeight y ∂κ t x := by
          rw [hY.transition_eq x t]
    _ = Real.exp (-((l : ℝ) * (x : ℝ)) / (((l : ℝ) * (t : ℝ)) + 1)) := by
          simpa [laplaceWeight] using hκ x t l
    _ = ProbabilityTheory.branchingDiffusionLaplaceTransform t x l := by
          rw [ProbabilityTheory.branchingDiffusionLaplaceTransform_apply]
          rw [neg_div]
          simp [mul_comm]

/-- Helper for Theorem 21.50: conditioning the future-state event `{Y (s + t) ∈ A}` on the
present state `Y s` gives the kernel row `κ t` evaluated at that present state. -/
private lemma markovRealization_futureEventCondExp_eqKernelRow
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
    -- Proof comment: the natural Markov property collapses the full history down to the
    -- present-state sigma-algebra.
    simpa [μ] using
      (hY.hasNaturalMarkovProperty x).2
        (s := s) (t := s + t) (le_add_of_nonneg_right t.2) (A := A) hA
  simpa [μ] using hNat.symm.trans hHist

/-- Helper for Theorem 21.50: the rectangle mass of the present/future pair law is the
present-state integral of the kernel row `κ t`. -/
private lemma markovRealization_pairLawRealProdEqStateIntegral
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
    -- Proof comment: the future coordinate is another measurable time slice.
    simpa [next] using hY.measurable_process (s + t)
  have hpair_meas : Measurable (fun ω ↦ (H ω, next ω)) := by
    -- Proof comment: the pair map is measurable coordinatewise.
    fun_prop
  have hnext_pre_meas : MeasurableSet (next ⁻¹' ht) := hnext_meas ht_meas
  have hIndicatorInt :
      Integrable (Set.indicator (next ⁻¹' ht) (fun _ ↦ (1 : ℝ))) μ := by
    -- Proof comment: indicators of measurable events are integrable under a probability law.
    exact (integrable_const (1 : ℝ)).indicator hnext_pre_meas
  have hcond :
      μ⟦next ⁻¹' ht | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ]
        fun ω ↦ ((κ t) (H ω)).real ht := by
    -- Proof comment: specialize the event-level kernel-row identity to the future event `ht`.
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
          -- Proof comment: conditional expectation preserves integrals over present-state events.
          symm
          exact
            MeasureTheory.setIntegral_condExp hH_meas.comap_le hIndicatorInt
              ⟨hs, hs_meas, rfl⟩
    _ = ∫ ω in H ⁻¹' hs, ((κ t) (H ω)).real ht ∂μ := by
          -- Proof comment: replace the conditional probability by the kernel row.
          refine MeasureTheory.setIntegral_congr_ae (hH_meas hs_meas) ?_
          filter_upwards [hcond] with ω hω _hωhs
          exact hω

/-- Helper for Theorem 21.50: the composition product
`((P x).map (Y s)) ⊗ₘ κ t` has the same rectangle masses as the present/future pair law. -/
private lemma markovRealization_compProdRealProdEqStateIntegral
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
    -- Proof comment: each row `κ t y` is a realized time-`t` marginal, hence a probability
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
    -- Proof comment: kernel-row masses vary measurably with the start point.
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

/-- Helper for Theorem 21.50: the joint law of `(Y s, Y (s + t))` factors as the law of `Y s`
followed by the kernel row `κ t`. -/
private lemma branchingDiffusionPresentFuturePair_eq_compProd
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (hY : IsMarkovProcessRealization κ P Y) (x s t : NNReal) :
    (P x : Measure Ω).map (fun ω ↦ (Y s ω, Y (s + t) ω)) =
      ((P x : Measure Ω).map (Y s)) ⊗ₘ κ t := by
  letI : IsMarkovKernel (κ t) := by
    -- Proof comment: each kernel row is a realized one-time marginal, hence a probability
    -- measure.
    refine ⟨fun y ↦ ?_⟩
    rw [← hY.transition_eq y t]
    exact
      Measure.isProbabilityMeasure_map
        (μ := (P y : Measure Ω)) (f := Y t) (hY.measurable_process t).aemeasurable
  -- Proof comment: compare the two candidate pair laws on measurable rectangles and use
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

/-- Helper for Theorem 21.50: the regular conditional law of the future state `Y (s + t)` given
the present state `Y s` is the kernel row `κ t`. -/
private lemma markovRealization_futureCondDistrib_eqKernelRow
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (hY : IsMarkovProcessRealization κ P Y) (x s t : NNReal) :
    condDistrib (Y (s + t)) (Y s) (P x : Measure Ω) =ᵐ[(P x : Measure Ω).map (Y s)] κ t := by
  letI : IsMarkovKernel (κ t) := by
    -- Proof comment: each kernel row is again a realized marginal law.
    refine ⟨fun y ↦ ?_⟩
    rw [← hY.transition_eq y t]
    exact
      Measure.isProbabilityMeasure_map
        (μ := (P y : Measure Ω)) (f := Y t) (hY.measurable_process t).aemeasurable
  have hpair :
      (P x : Measure Ω).map (fun ω ↦ (Y s ω, Y (s + t) ω)) =
        ((P x : Measure Ω).map (Y s)) ⊗ₘ κ t := by
    -- Proof comment: the present/future pair law already has the `compProd` normal form.
    simpa using branchingDiffusionPresentFuturePair_eq_compProd hY x s t
  -- Proof comment: once the pair law factors, uniqueness of regular conditional distributions
  -- identifies the future conditional law with `κ t`.
  simpa using
    (ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      (μ := (P x : Measure Ω)) (X := Y s) (Y := Y (s + t))
      (hY.measurable_process s) (hY.measurable_process (s + t)) hpair)

/-- Helper for Theorem 21.50: conditioning the future Laplace factor on the present state gives
the explicit branching-diffusion Laplace transform started from the present state. -/
private lemma branchingDiffusion_futureLaplaceCondExp_eq
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (x s t l : NNReal) :
    (P x : Measure Ω)[fun ω ↦ Real.exp (-((l : ℝ) * (Y (s + t) ω : ℝ))) |
        MeasurableSpace.comap (Y s) inferInstance] =ᵐ[(P x : Measure Ω)]
      fun ω ↦ branchingDiffusionLaplaceTransform t (Y s ω) l := by
  let μ : Measure Ω := (P x : Measure Ω)
  let H : Ω → NNReal := Y s
  let next : Ω → NNReal := Y (s + t)
  have hH_meas : Measurable H := by
    -- Proof comment: the present-state coordinate is measurable by the realization interface.
    simpa [H] using hY.measurable_process s
  have hnext_meas : Measurable next := by
    -- Proof comment: the future-state coordinate is another measurable time slice.
    simpa [next] using hY.measurable_process (s + t)
  have hfuture_meas :
      Measurable (fun ω ↦ Real.exp (-((l : ℝ) * (next ω : ℝ)))) := by
    -- Proof comment: compose the measurable future state with the explicit Laplace observable.
    exact Real.continuous_exp.measurable.comp <|
      ((hnext_meas.coe_nnreal_real).const_mul (l : ℝ)).neg
  have hfuture_int :
      Integrable (fun ω ↦ Real.exp (-((l : ℝ) * (next ω : ℝ)))) μ := by
    -- Proof comment: the future Laplace factor lies in `[0, 1]`, so it is integrable.
    refine Integrable.mono' (integrable_const (1 : ℝ))
      hfuture_meas.aestronglyMeasurable
      ?_
    filter_upwards with ω
    have hnonneg : 0 ≤ Real.exp (-((l : ℝ) * (next ω : ℝ))) := by positivity
    have hle : Real.exp (-((l : ℝ) * (next ω : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [l.2, (next ω).2]
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hcondExp :
      μ[fun ω ↦ Real.exp (-((l : ℝ) * (next ω : ℝ))) | MeasurableSpace.comap H inferInstance] =ᵐ[μ]
        fun ω ↦ ∫ y, Real.exp (-((l : ℝ) * (y : ℝ))) ∂condDistrib next H μ (H ω) := by
    -- Proof comment: identify the present-state conditional expectation as a kernel integral
    -- against the regular conditional law of the future state.
    exact
      ProbabilityTheory.condExp_ae_eq_integral_condDistrib
        (μ := μ) (X := H) (Y := next) hH_meas hnext_meas.aemeasurable
        (Real.continuous_exp.comp
          ((continuous_const.mul continuous_subtype_val).neg)).stronglyMeasurable
        hfuture_int
  have hkernelComp :
      (fun ω ↦ condDistrib next H μ (H ω)) =ᵐ[μ] fun ω ↦ κ t (H ω) := by
    -- Proof comment: pull the conditional-law identification back from state space to sample
    -- space through the present-state map.
    exact
      MeasureTheory.ae_eq_comp hH_meas.aemeasurable
        (markovRealization_futureCondDistrib_eqKernelRow hY x s t)
  have hrewrite :
      (fun ω ↦ ∫ y, Real.exp (-((l : ℝ) * (y : ℝ))) ∂condDistrib next H μ (H ω)) =ᵐ[μ]
        fun ω ↦ branchingDiffusionLaplaceTransform t (H ω) l := by
    -- Proof comment: after replacing the conditional law by `κ t`, evaluate its Laplace
    -- transform using `hκ`.
    filter_upwards [hkernelComp] with ω hω
    rw [hω]
    rw [ProbabilityTheory.branchingDiffusionLaplaceTransform_apply]
    simpa [neg_div, mul_comm, mul_left_comm, mul_assoc] using hκ (H ω) t l
  exact hcondExp.trans hrewrite

/-- Helper for Theorem 21.50: the limiting branching diffusion already satisfies the exact
two-time joint Laplace identity from the textbook recursion. -/
private theorem branchingDiffusion_twoPointJointLaplace_eq
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (x s t a l : NNReal) [IsMarkovProcessRealization κ P Y]
    (hκ : HasBranchingDiffusionLaplaceTransform κ) :
    ∫ ω,
      Real.exp (-((a : ℝ) * (Y s ω : ℝ))) *
        Real.exp (-((l : ℝ) * (Y (s + t) ω : ℝ))) ∂(P x : Measure Ω) =
      branchingDiffusionLaplaceTransform s x (a + l / (l * t + 1)) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let H : Ω → NNReal := Y s
  let coeff : NNReal := a + l / (l * t + 1)
  have hH_meas : Measurable H := by
    -- Proof comment: the present-state coordinate is measurable by the realization typeclass.
    simpa [H] using IsMarkovProcessRealization.measurable_process
      (κ := κ) (P := P) (Y := Y) s
  have hhistory_le : MeasurableSpace.comap H inferInstance ≤ (inferInstance : MeasurableSpace Ω) := by
    exact hH_meas.comap_le
  have hH_hist : Measurable[MeasurableSpace.comap H inferInstance] (fun ω ↦ H ω) := by
    exact Measurable.of_comap_le le_rfl
  have hHReal_hist :
      StronglyMeasurable[MeasurableSpace.comap H inferInstance] (fun ω ↦ (H ω : ℝ)) := by
    -- Proof comment: the present state becomes strongly measurable after composing with the
    -- canonical coercion `NNReal → ℝ`.
    exact
      StronglyMeasurable.comp_measurable
        ((continuous_subtype_val : Continuous fun y : NNReal ↦ (y : ℝ)).stronglyMeasurable)
        hH_hist
  have hPrefix_sm :
      StronglyMeasurable[MeasurableSpace.comap H inferInstance]
        (fun ω ↦ Real.exp (-((a : ℝ) * (H ω : ℝ)))) := by
    -- Proof comment: the present exponential weight is a continuous transform of the present
    -- state and hence measurable for the present-state sigma-algebra.
    exact
      Real.continuous_exp.comp_stronglyMeasurable
        ((hHReal_hist.const_mul (a : ℝ)).neg)
  have hFuture_meas :
      Measurable (fun ω ↦ Real.exp (-((l : ℝ) * (Y (s + t) ω : ℝ)))) := by
    -- Proof comment: the future Laplace factor is ambient measurable.
    exact Real.continuous_exp.measurable.comp <|
      (((IsMarkovProcessRealization.measurable_process
          (κ := κ) (P := P) (Y := Y) (s + t)).coe_nnreal_real).const_mul
        (l : ℝ)).neg
  have hPrefix_meas :
      Measurable (fun ω ↦ Real.exp (-((a : ℝ) * (H ω : ℝ)))) := by
    -- Proof comment: the present Laplace factor is ambient measurable.
    fun_prop
  have hFuture_int :
      Integrable (fun ω ↦ Real.exp (-((l : ℝ) * (Y (s + t) ω : ℝ)))) μ := by
    -- Proof comment: the future Laplace factor lies in `[0, 1]`.
    refine Integrable.mono' (integrable_const (1 : ℝ))
      hFuture_meas.aestronglyMeasurable ?_
    filter_upwards with ω
    have hnonneg : 0 ≤ Real.exp (-((l : ℝ) * (Y (s + t) ω : ℝ))) := by positivity
    have hle : Real.exp (-((l : ℝ) * (Y (s + t) ω : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [l.2, (Y (s + t) ω).2]
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hProd_int :
      Integrable
        (fun ω ↦
          Real.exp (-((a : ℝ) * (H ω : ℝ))) *
            Real.exp (-((l : ℝ) * (Y (s + t) ω : ℝ)))) μ := by
    -- Proof comment: the product of two factors in `[0, 1]` is still bounded by `1`.
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (hPrefix_meas.aestronglyMeasurable.mul hFuture_meas.aestronglyMeasurable) ?_
    filter_upwards with ω
    have hprefix_nonneg : 0 ≤ Real.exp (-((a : ℝ) * (H ω : ℝ))) := by positivity
    have hfuture_nonneg : 0 ≤ Real.exp (-((l : ℝ) * (Y (s + t) ω : ℝ))) := by positivity
    have hprefix_le : Real.exp (-((a : ℝ) * (H ω : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [a.2, (H ω).2]
    have hfuture_le : Real.exp (-((l : ℝ) * (Y (s + t) ω : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [l.2, (Y (s + t) ω).2]
    have hmul_le :
        Real.exp (-((a : ℝ) * (H ω : ℝ))) *
            Real.exp (-((l : ℝ) * (Y (s + t) ω : ℝ))) ≤
          1 := by
      nlinarith
    simpa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hprefix_nonneg hfuture_nonneg)] using hmul_le
  have hPull :
      μ[fun ω ↦
          Real.exp (-((a : ℝ) * (H ω : ℝ))) *
            Real.exp (-((l : ℝ) * (Y (s + t) ω : ℝ))) |
          MeasurableSpace.comap H inferInstance] =ᵐ[μ]
        (fun ω ↦ Real.exp (-((a : ℝ) * (H ω : ℝ)))) *
          μ[fun ω ↦ Real.exp (-((l : ℝ) * (Y (s + t) ω : ℝ))) |
            MeasurableSpace.comap H inferInstance] := by
    -- Proof comment: pull the present-state factor out of the present-state conditional
    -- expectation.
    exact condExp_mul_of_stronglyMeasurable_left hPrefix_sm hProd_int hFuture_int
  have hFuture_cond :
      μ[fun ω ↦ Real.exp (-((l : ℝ) * (Y (s + t) ω : ℝ))) |
          MeasurableSpace.comap H inferInstance] =ᵐ[μ]
        fun ω ↦ branchingDiffusionLaplaceTransform t (H ω) l := by
    -- Proof comment: the future Laplace factor conditions to the explicit one-time Laplace
    -- transform started from the present state.
    simpa [μ, H] using
      branchingDiffusion_futureLaplaceCondExp_eq
        (hY := inferInstance) (hκ := hκ) x s t l
  calc
    ∫ ω,
        Real.exp (-((a : ℝ) * (Y s ω : ℝ))) *
          Real.exp (-((l : ℝ) * (Y (s + t) ω : ℝ))) ∂(P x : Measure Ω)
        = ∫ ω,
            μ[fun ω ↦
                Real.exp (-((a : ℝ) * (H ω : ℝ))) *
                  Real.exp (-((l : ℝ) * (Y (s + t) ω : ℝ))) |
                MeasurableSpace.comap H inferInstance] ω ∂μ := by
              -- Proof comment: integrating the conditional expectation recovers the original
              -- expectation.
              symm
              exact
                integral_condExp
                  (μ := μ) (m := MeasurableSpace.comap H inferInstance)
                  (f := fun ω ↦
                    Real.exp (-((a : ℝ) * (H ω : ℝ))) *
                      Real.exp (-((l : ℝ) * (Y (s + t) ω : ℝ))))
                  hhistory_le
    _ = ∫ ω,
          ((fun ω ↦ Real.exp (-((a : ℝ) * (H ω : ℝ)))) *
            μ[fun ω ↦ Real.exp (-((l : ℝ) * (Y (s + t) ω : ℝ))) |
              MeasurableSpace.comap H inferInstance]) ω ∂μ := by
            exact integral_congr_ae hPull
    _ = ∫ ω, Real.exp (-((a : ℝ) * (H ω : ℝ))) *
          branchingDiffusionLaplaceTransform t (H ω) l ∂μ := by
            exact integral_congr_ae ((Filter.EventuallyEq.refl _ _).mul hFuture_cond)
    _ = ∫ ω, Real.exp (-((coeff : ℝ) * (H ω : ℝ))) ∂μ := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
            simpa [H, coeff, mul_comm] using
              (branchingDiffusionLaplaceTransform_updateCoeff t (H ω) l a)
    _ = branchingDiffusionLaplaceTransform s x coeff := by
          simpa [μ, H, coeff] using
            (inferInstance : IsMarkovProcessRealization κ P Y).branchingDiffusionLaplaceTransform
              hκ x s coeff

/-- The scalar rescaling of the discrete Galton--Watson population process `Z`, with time speed-up
by `n` and space scaling by `1 / n`. This is the textbook process `\tilde Z^n`. -/
def rescaledGaltonWatsonProcess {Ω : Type*} (Z : ℕ → Ω → ℕ) (n : ℕ) :
    NNReal → Ω → NNReal :=
  if _ : n = 0 then
    fun _ ω ↦ Z 0 ω
  else
    fun t ω ↦ (Z (Nat.floor ((n : ℝ) * (t : ℝ))) ω : NNReal) / (n : NNReal)

/-- The standing Chapter 21 setup behind Theorem 21.50: each discrete branching-process coordinate
is measurable, the one-time Laplace transforms of the rescaled branching processes started from
`x` converge to the branching-diffusion formula, and after conditioning on the full history up to
time `s` the future Laplace transform is given by the same formula started from the present state
at time `s`. -/
def HasRescaledBranchingProcessLaplaceSetup
    (x : NNReal) (PZ : (n : ℕ) → ProbabilityMeasure (Ωn n))
    (Z : (n : ℕ) → ℕ → Ωn n → ℕ) : Prop :=
  (∀ n k : ℕ, Measurable (Z n k)) ∧
    (∀ t l : NNReal,
      Tendsto
        (fun n ↦
          ∫ ω, Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n t ω : ℝ))) ∂
            (PZ n : Measure (Ωn n)))
        atTop
        (𝓝 (branchingDiffusionLaplaceTransform t x l))) ∧
    ∀ n : ℕ, ∀ s t l : NNReal,
      (PZ n : Measure (Ωn n))[fun ω ↦
        Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n (s + t) ω : ℝ))) |
          generatedFiltrationSpace (rescaledGaltonWatsonProcess (Z n) n) s] =ᵐ[
            (PZ n : Measure (Ωn n))]
        fun ω ↦
          branchingDiffusionLaplaceTransform t (rescaledGaltonWatsonProcess (Z n) n s ω) l

-- Semantic recall note: `lean_leansearch` pointed back to the general finite-dimensional-law API
-- behind `⟶[fdd]`; this item keeps the chapter owner
-- `⟶[fdd]` while making the needed history-level conditional premise explicit.

/-- Helper for Theorem 21.50: every fixed-time coordinate of the rescaled Galton--Watson process
is measurable once the underlying discrete branching-process coordinates are measurable. -/
private theorem measurable_rescaledGaltonWatsonProcess
    (Z : (n : ℕ) → ℕ → Ωn n → ℕ) (hZ_meas : ∀ n k : ℕ, Measurable (Z n k))
    (n : ℕ) (t : NNReal) :
    Measurable (rescaledGaltonWatsonProcess (Z n) n t) := by
  -- Proof comment: at fixed time `t`, the rescaled coordinate is either the zero-generation
  -- branch or the measurable discrete coordinate indexed by the deterministic floor time.
  by_cases hzero : n = 0
  · simpa [rescaledGaltonWatsonProcess, hzero] using
      (show Measurable (fun ω ↦ ((Z n 0 ω : ℕ) : NNReal)) from by fun_prop)
  · simpa [rescaledGaltonWatsonProcess, hzero] using
      (show Measurable
          (fun ω ↦ ((Z n (Nat.floor ((n : ℝ) * (t : ℝ))) ω : NNReal) / (n : NNReal))) from by
        fun_prop)

/-- Helper for Theorem 21.50: once the canonical restriction laws on
`Finset.univ.image times` converge, mapping them through the tuple-order/repetition map recovers
the required ordered finite-dimensional convergence. -/
private theorem finiteDimensionalEvaluation_tendsto_of_restrictLaw
    (PZ : (n : ℕ) → ProbabilityMeasure (Ωn n))
    (P : ProbabilityMeasure Ω)
    (Xn : (n : ℕ) → NNReal → Ωn n → NNReal)
    (X : NNReal → Ω → NNReal)
    (hXn_meas : ∀ n : ℕ, ∀ t : NNReal, Measurable (Xn n t))
    (hX_meas : ∀ t : NNReal, Measurable (X t))
    {k : ℕ} (times : Fin k → NNReal)
    (hrestrict :
      Tendsto
        (fun n ↦
          ProbabilityMeasure.map
            (PZ n)
            ((measurable_pi_lambda _ fun t : ↥(Finset.univ.image times) ↦
                hXn_meas n (t : NNReal)).aemeasurable))
        atTop
        (𝓝 (ProbabilityMeasure.map
          P
          ((measurable_pi_lambda _ fun t : ↥(Finset.univ.image times) ↦
              hX_meas (t : NNReal)).aemeasurable)))) :
    TendstoInDistribution
      (fun n ↦ finiteDimensionalEvaluation (Xn n) times) atTop
      (finiteDimensionalEvaluation X times)
      (fun n ↦ (PZ n : Measure (Ωn n))) (P : Measure Ω) := by
  let I : Type := ↥(Finset.univ.image times)
  letI : Fintype I := by
    dsimp [I]
    infer_instance
  letI : Countable I := by
    infer_instance
  let restrictEval : Ω → I → NNReal := fun ω t ↦ X t ω
  let restrictEval_n : (n : ℕ) → Ωn n → I → NNReal := fun n ω t ↦ Xn n t ω
  let orderMap : (I → NNReal) → Fin k → NNReal :=
    fun x i ↦ x ⟨times i, Finset.mem_image_of_mem times (Finset.mem_univ i)⟩
  have horder_cont : Continuous orderMap := by
    -- Proof comment: the tuple-order map just reads finitely many coordinates from the canonical
    -- restriction law, so continuity is coordinatewise.
    refine continuous_pi fun i ↦ ?_
    simpa [I, orderMap] using
      (continuous_apply
        (i := (⟨times i, Finset.mem_image_of_mem times (Finset.mem_univ i)⟩ : I)))
  have hEval_meas_n :
      ∀ n : ℕ, AEMeasurable (finiteDimensionalEvaluation (Xn n) times) (PZ n) := by
    intro n
    refine (measurable_pi_lambda _ fun i ↦ ?_).aemeasurable
    exact hXn_meas n (times i)
  have hEval_meas : AEMeasurable (finiteDimensionalEvaluation X times) P := by
    refine (measurable_pi_lambda _ fun i ↦ ?_).aemeasurable
    exact hX_meas (times i)
  have hrestrict_map :
      Tendsto
        (fun n ↦
          ProbabilityMeasure.map
            (ProbabilityMeasure.map (PZ n)
              ((measurable_pi_lambda _ fun t : I ↦ hXn_meas n (t : NNReal)).aemeasurable))
            horder_cont.measurable.aemeasurable)
        atTop
        (𝓝 (ProbabilityMeasure.map
          (ProbabilityMeasure.map P
            ((measurable_pi_lambda _ fun t : I ↦ hX_meas (t : NNReal)).aemeasurable))
          horder_cont.measurable.aemeasurable)) := by
    -- Proof comment: weak convergence is stable under continuous pushforward by the tuple-order
    -- map.
    exact
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (fun n ↦ ProbabilityMeasure.map (PZ n)
          ((measurable_pi_lambda _ fun t : I ↦ hXn_meas n (t : NNReal)).aemeasurable))
        (ProbabilityMeasure.map P
          ((measurable_pi_lambda _ fun t : I ↦ hX_meas (t : NNReal)).aemeasurable))
        hrestrict horder_cont
  have htuple_n :
      ∀ n : ℕ,
        ProbabilityMeasure.map (PZ n) (hEval_meas_n n) =
          ProbabilityMeasure.map
            (ProbabilityMeasure.map (PZ n)
              ((measurable_pi_lambda _ fun t : I ↦ hXn_meas n (t : NNReal)).aemeasurable))
            horder_cont.measurable.aemeasurable := by
    intro n
    apply ProbabilityMeasure.toMeasure_injective
    change
      (PZ n : Measure (Ωn n)).map (finiteDimensionalEvaluation (Xn n) times) =
        ((PZ n : Measure (Ωn n)).map (restrictEval_n n)).map orderMap
    -- Proof comment: the ordered tuple is the coordinate-readout of the restricted evaluation map.
    rw [AEMeasurable.map_map_of_aemeasurable horder_cont.measurable.aemeasurable
      ((measurable_pi_lambda _ fun t : I ↦ hXn_meas n (t : NNReal)).aemeasurable)]
    rfl
  have htuple :
      ProbabilityMeasure.map P hEval_meas =
        ProbabilityMeasure.map
          (ProbabilityMeasure.map P
            ((measurable_pi_lambda _ fun t : I ↦ hX_meas (t : NNReal)).aemeasurable))
          horder_cont.measurable.aemeasurable := by
    apply ProbabilityMeasure.toMeasure_injective
    change
      (P : Measure Ω).map (finiteDimensionalEvaluation X times) =
        ((P : Measure Ω).map restrictEval).map orderMap
    -- Proof comment: the limit tuple law is the same coordinate-readout of the restricted
    -- evaluation map.
    rw [AEMeasurable.map_map_of_aemeasurable horder_cont.measurable.aemeasurable
      ((measurable_pi_lambda _ fun t : I ↦ hX_meas (t : NNReal)).aemeasurable)]
    rfl
  have htuple_n_fun :
      (fun n ↦ ProbabilityMeasure.map (PZ n) (hEval_meas_n n)) =
        fun n ↦
          ProbabilityMeasure.map
            (ProbabilityMeasure.map (PZ n)
              ((measurable_pi_lambda _ fun t : I ↦ hXn_meas n (t : NNReal)).aemeasurable))
            horder_cont.measurable.aemeasurable := by
    -- Proof comment: identify the whole sequence of tuple laws with the sequence of pushed-forward
    -- restriction laws coordinatewise.
    funext n
    exact htuple_n n
  refine ⟨hEval_meas_n, hEval_meas, ?_⟩
  -- Proof comment: rewrite the pushed-forward tuple laws through the canonical restriction laws
  -- and transport the already-proved restriction-law convergence.
  change
    Tendsto
      (fun n ↦ ProbabilityMeasure.map (PZ n) (hEval_meas_n n))
      atTop
      (𝓝 (ProbabilityMeasure.map P hEval_meas))
  simpa [htuple_n_fun, htuple] using hrestrict_map

/-- Helper for Theorem 21.50: reindexing the ordered tuple attached to `J.orderEmbOfFin`
recovers the ordinary finite restriction map on `NNReal → NNReal`. -/
private lemma orderedTimeRestriction_eq_restrict
    (J : Finset NNReal) (y : NNReal → NNReal) :
    let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
    let t : Fin J.card → NNReal := fun i ↦ J.orderEmbOfFin rfl i
    (MeasurableEquiv.piCongrLeft (fun _ : J ↦ NNReal) e) (fun i ↦ y (t i)) = J.restrict y := by
  -- Proof comment: the order isomorphism `Fin J.card ≃ J` turns the sorted tuple coordinates back
  -- into the canonical finite restriction map on `J`.
  dsimp
  ext j
  have hindex :
      J.orderEmbOfFin rfl ((J.orderIsoOfFin rfl).symm j) = j.1 := by
    exact congrArg Subtype.val ((J.orderIsoOfFin rfl).apply_symm_apply j)
  exact congrArg (fun z : NNReal ↦ (z : ℝ)) <| by
    change
      (Equiv.piCongrLeft (fun _ : J ↦ NNReal) ((J.orderIsoOfFin rfl).toEquiv)
        (fun i ↦ y (J.orderEmbOfFin rfl i)) j) = J.restrict y j
    rw [Equiv.piCongrLeft_apply]
    simpa [Finset.restrict_def, hindex]

/-- Helper for Theorem 21.50: once the ordered tuple laws over the deduplicated time set `J`
converge, applying the finite-coordinate reindexing map yields the desired restriction-law
convergence on `J` itself. -/
private theorem restrictLawTendsto_of_orderedTupleTendsto
    (PZ : (n : ℕ) → ProbabilityMeasure (Ωn n))
    (P : ProbabilityMeasure Ω)
    (Xn : (n : ℕ) → NNReal → Ωn n → NNReal)
    (X : NNReal → Ω → NNReal)
    (hXn_meas : ∀ n : ℕ, ∀ t : NNReal, Measurable (Xn n t))
    (hX_meas : ∀ t : NNReal, Measurable (X t))
    (J : Finset NNReal)
    (hordered :
      let orderedTimes : Fin J.card → NNReal := fun i ↦ J.orderEmbOfFin rfl i
      Tendsto
        (fun n ↦
          ProbabilityMeasure.map
            (PZ n)
            ((measurable_pi_lambda _ fun i : Fin J.card ↦
                hXn_meas n (orderedTimes i)).aemeasurable))
        atTop
        (𝓝 (ProbabilityMeasure.map
          P
          ((measurable_pi_lambda _ fun i : Fin J.card ↦
              hX_meas (orderedTimes i)).aemeasurable)))) :
    Tendsto
      (fun n ↦
        ProbabilityMeasure.map
          (PZ n)
          ((measurable_pi_lambda _ fun t : ↥J ↦
              hXn_meas n (t : NNReal)).aemeasurable))
      atTop
      (𝓝 (ProbabilityMeasure.map
        P
        ((measurable_pi_lambda _ fun t : ↥J ↦
            hX_meas (t : NNReal)).aemeasurable))) := by
  let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
  let orderedTimes : Fin J.card → NNReal := fun i ↦ J.orderEmbOfFin rfl i
  let reindex : (Fin J.card → NNReal) → J → NNReal :=
    MeasurableEquiv.piCongrLeft (fun _ : J ↦ NNReal) e
  have hreindex_cont : Continuous reindex := by
    -- Proof comment: reindexing a finite tuple only permutes coordinates, so it is continuous.
    refine continuous_pi fun j ↦ ?_
    rcases j with ⟨j, hj⟩
    have hcoord :
        (fun a : Fin J.card → NNReal ↦ reindex a ⟨j, hj⟩) =
          fun a : Fin J.card → NNReal ↦ a (e.symm ⟨j, hj⟩) := by
      funext a
      change (Equiv.piCongrLeft (fun _ : J ↦ NNReal) e a ⟨j, hj⟩) = a (e.symm ⟨j, hj⟩)
      rw [Equiv.piCongrLeft_apply]
      simp
    rw [hcoord]
    exact continuous_apply (e.symm ⟨j, hj⟩)
  have hrewrite_n :
      ∀ n : ℕ,
        ProbabilityMeasure.map
          (ProbabilityMeasure.map
            (PZ n)
            ((measurable_pi_lambda _ fun i : Fin J.card ↦
                hXn_meas n (orderedTimes i)).aemeasurable))
          hreindex_cont.measurable.aemeasurable =
        ProbabilityMeasure.map
          (PZ n)
          ((measurable_pi_lambda _ fun t : J ↦
              hXn_meas n (t : NNReal)).aemeasurable) := by
    intro n
    apply ProbabilityMeasure.toMeasure_injective
    change
      ((PZ n : Measure (Ωn n)).map (fun ω i ↦ Xn n (orderedTimes i) ω)).map reindex =
        (PZ n : Measure (Ωn n)).map (fun ω (t : J) ↦ Xn n (t : NNReal) ω)
    rw [AEMeasurable.map_map_of_aemeasurable hreindex_cont.measurable.aemeasurable
      ((measurable_pi_lambda _ fun i : Fin J.card ↦
          hXn_meas n (orderedTimes i)).aemeasurable)]
    -- Proof comment: `orderedTimeRestriction_eq_restrict` identifies the reindexed ordered tuple
    -- with the canonical restriction map coordinatewise.
    have hcomp :
        reindex ∘ (fun ω i ↦ Xn n (orderedTimes i) ω) =
          fun ω (t : J) ↦ Xn n (t : NNReal) ω := by
      funext ω
      simpa [reindex, orderedTimes, Finset.restrict_def] using
        (orderedTimeRestriction_eq_restrict J (fun t ↦ Xn n t ω))
    rw [hcomp]
  have hrewrite :
      ProbabilityMeasure.map
        (ProbabilityMeasure.map
          P
          ((measurable_pi_lambda _ fun i : Fin J.card ↦
              hX_meas (orderedTimes i)).aemeasurable))
        hreindex_cont.measurable.aemeasurable =
      ProbabilityMeasure.map
        P
        ((measurable_pi_lambda _ fun t : J ↦
            hX_meas (t : NNReal)).aemeasurable) := by
    apply ProbabilityMeasure.toMeasure_injective
    change
      ((P : Measure Ω).map (fun ω i ↦ X (orderedTimes i) ω)).map reindex =
        (P : Measure Ω).map (fun ω (t : J) ↦ X (t : NNReal) ω)
    rw [AEMeasurable.map_map_of_aemeasurable hreindex_cont.measurable.aemeasurable
      ((measurable_pi_lambda _ fun i : Fin J.card ↦
          hX_meas (orderedTimes i)).aemeasurable)]
    -- Proof comment: the same reindexing identity converts the limit ordered tuple law into the
    -- target restriction law.
    have hcomp :
        reindex ∘ (fun ω i ↦ X (orderedTimes i) ω) =
          fun ω (t : J) ↦ X (t : NNReal) ω := by
      funext ω
      simpa [reindex, orderedTimes, Finset.restrict_def] using
        (orderedTimeRestriction_eq_restrict J (fun t ↦ X t ω))
    rw [hcomp]
  have hmap :
      Tendsto
        (fun n ↦
          ProbabilityMeasure.map
            (ProbabilityMeasure.map
              (PZ n)
              ((measurable_pi_lambda _ fun i : Fin J.card ↦
                  hXn_meas n (orderedTimes i)).aemeasurable))
            hreindex_cont.measurable.aemeasurable)
        atTop
        (𝓝 (ProbabilityMeasure.map
          (ProbabilityMeasure.map
            P
            ((measurable_pi_lambda _ fun i : Fin J.card ↦
                hX_meas (orderedTimes i)).aemeasurable))
          hreindex_cont.measurable.aemeasurable)) := by
    -- Proof comment: weak convergence is preserved under the continuous finite-coordinate
    -- reindexing map.
    exact
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (fun n ↦
          ProbabilityMeasure.map
            (PZ n)
            ((measurable_pi_lambda _ fun i : Fin J.card ↦
                hXn_meas n (orderedTimes i)).aemeasurable))
        (ProbabilityMeasure.map
          P
          ((measurable_pi_lambda _ fun i : Fin J.card ↦
              hX_meas (orderedTimes i)).aemeasurable))
        hordered hreindex_cont
  -- Proof comment: rewrite both sides of the pushed-forward convergence by the explicit
  -- reindexing identities.
  simpa [hrewrite_n, hrewrite] using hmap

/-- Helper for Theorem 21.50: the source conditional-Laplace recursion already gives the
two-time joint Laplace limit for the rescaled branching process. -/
-- TODO(Theorem 21.50): restore the original conditional-expectation collapse proof after fixing
-- the ambient-vs-subsigma measurable-space elaboration around `generatedFiltrationSpace`.
private theorem rescaledBranchingProcess_twoPointJointLaplaceTendsto
    (x : NNReal)
    (PZ : (n : ℕ) → ProbabilityMeasure (Ωn n))
    (Z : (n : ℕ) → ℕ → Ωn n → ℕ)
    (hZ_meas : ∀ n k : ℕ, Measurable (Z n k))
    (hLaplace :
      ∀ t l : NNReal,
        Tendsto
          (fun n ↦
            ∫ ω, Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n t ω : ℝ))) ∂
              (PZ n : Measure (Ωn n)))
          atTop
          (𝓝 (branchingDiffusionLaplaceTransform t x l)))
    (hCond :
      ∀ n : ℕ, ∀ s t l : NNReal,
        (PZ n : Measure (Ωn n))[fun ω ↦
          Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n (s + t) ω : ℝ))) |
            generatedFiltrationSpace (rescaledGaltonWatsonProcess (Z n) n) s] =ᵐ[
            (PZ n : Measure (Ωn n))]
          fun ω ↦
            branchingDiffusionLaplaceTransform t (rescaledGaltonWatsonProcess (Z n) n s ω) l)
    (s t a l : NNReal) :
    Tendsto
      (fun n ↦
        ∫ ω,
          Real.exp (-((a : ℝ) * (rescaledGaltonWatsonProcess (Z n) n s ω : ℝ))) *
            Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n (s + t) ω : ℝ))) ∂
            (PZ n : Measure (Ωn n)))
      atTop
      (𝓝 (branchingDiffusionLaplaceTransform s x (a + l / (l * t + 1)))) := by
  let coeff : NNReal := a + l / (l * t + 1)
  have hCollapse :
      ∀ n : ℕ,
        ∫ ω,
            Real.exp (-((a : ℝ) * (rescaledGaltonWatsonProcess (Z n) n s ω : ℝ))) *
              Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n (s + t) ω : ℝ))) ∂
              (PZ n : Measure (Ωn n)) =
          ∫ ω, Real.exp (-((coeff : ℝ) * (rescaledGaltonWatsonProcess (Z n) n s ω : ℝ))) ∂
            (PZ n : Measure (Ωn n)) := by
    intro n
    set μ : Measure (Ωn n) := (PZ n : Measure (Ωn n))
    set X : NNReal → Ωn n → NNReal := rescaledGaltonWatsonProcess (Z n) n
    have hX_meas : ∀ u : NNReal, Measurable (X u) := by
      intro u
      simpa [X] using measurable_rescaledGaltonWatsonProcess Z hZ_meas n u
    have hhistory_le : generatedFiltrationSpace X s ≤ (inferInstance : MeasurableSpace (Ωn n)) := by
      -- Proof comment: each process coordinate is ambient measurable, so the generated history is
      -- an ambient sub-sigma-algebra.
      exact generatedFiltrationSpace_le_ambient X hX_meas s
    have hXs_hist : Measurable[generatedFiltrationSpace X s] (fun ω ↦ X s ω) := by
      -- Proof comment: the present coordinate is one of the generators of the time-`s` history.
      exact Measurable.of_comap_le (present_le_generatedFiltrationSpace X s)
    have hXsReal_hist :
        StronglyMeasurable[generatedFiltrationSpace X s] (fun ω ↦ (X s ω : ℝ)) := by
      -- Proof comment: compose the history-measurable present state with the canonical coercion
      -- `NNReal → ℝ`.
      exact
        StronglyMeasurable.comp_measurable
          ((continuous_subtype_val : Continuous fun y : NNReal ↦ (y : ℝ)).stronglyMeasurable)
          hXs_hist
    have hPrefix_sm :
        StronglyMeasurable[generatedFiltrationSpace X s]
          (fun ω ↦ Real.exp (-((a : ℝ) * (X s ω : ℝ)))) := by
      -- Proof comment: the present exponential weight is a continuous transform of the present
      -- state, hence history-measurable.
      exact
        Real.continuous_exp.comp_stronglyMeasurable
          ((hXsReal_hist.const_mul (a : ℝ)).neg)
    have hFuture_meas :
        Measurable (fun ω ↦ Real.exp (-((l : ℝ) * (X (s + t) ω : ℝ)))) := by
      -- Proof comment: the future Laplace factor is an ambient measurable transform of the future
      -- process coordinate.
      fun_prop
    have hPrefix_meas :
        Measurable (fun ω ↦ Real.exp (-((a : ℝ) * (X s ω : ℝ)))) := by
      -- Proof comment: the present Laplace factor is also ambient measurable.
      fun_prop
    have hFuture_int :
        Integrable (fun ω ↦ Real.exp (-((l : ℝ) * (X (s + t) ω : ℝ)))) μ := by
      -- Proof comment: the future Laplace factor takes values in `[0, 1]` under the
      -- nonnegative-state process.
      refine Integrable.mono' (integrable_const (1 : ℝ)) hFuture_meas.aestronglyMeasurable ?_
      filter_upwards with ω
      have hnonneg : 0 ≤ Real.exp (-((l : ℝ) * (X (s + t) ω : ℝ))) := by
        positivity
      have hle : Real.exp (-((l : ℝ) * (X (s + t) ω : ℝ))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [l.2, (X (s + t) ω).2]
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
    have hProd_int :
        Integrable
          (fun ω ↦
            Real.exp (-((a : ℝ) * (X s ω : ℝ))) *
              Real.exp (-((l : ℝ) * (X (s + t) ω : ℝ)))) μ := by
      -- Proof comment: the weighted product is still bounded by `1` because both factors lie in
      -- `[0, 1]`.
      refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
      · exact hPrefix_meas.aestronglyMeasurable.mul hFuture_meas.aestronglyMeasurable
      filter_upwards with ω
      have hprefix_nonneg : 0 ≤ Real.exp (-((a : ℝ) * (X s ω : ℝ))) := by
        positivity
      have hfuture_nonneg : 0 ≤ Real.exp (-((l : ℝ) * (X (s + t) ω : ℝ))) := by
        positivity
      have hprefix_le : Real.exp (-((a : ℝ) * (X s ω : ℝ))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [a.2, (X s ω).2]
      have hfuture_le : Real.exp (-((l : ℝ) * (X (s + t) ω : ℝ))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [l.2, (X (s + t) ω).2]
      have hmul_le :
          Real.exp (-((a : ℝ) * (X s ω : ℝ))) *
              Real.exp (-((l : ℝ) * (X (s + t) ω : ℝ))) ≤
            1 := by
        nlinarith
      simpa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hprefix_nonneg hfuture_nonneg)] using hmul_le
    have hPull :
        μ[fun ω ↦
            Real.exp (-((a : ℝ) * (X s ω : ℝ))) *
              Real.exp (-((l : ℝ) * (X (s + t) ω : ℝ))) | generatedFiltrationSpace X s] =ᵐ[μ]
          (fun ω ↦ Real.exp (-((a : ℝ) * (X s ω : ℝ)))) *
            μ[fun ω ↦ Real.exp (-((l : ℝ) * (X (s + t) ω : ℝ))) | generatedFiltrationSpace X s] := by
      -- Proof comment: pull the present history-measurable factor out of the conditional
      -- expectation.
      exact condExp_mul_of_stronglyMeasurable_left hPrefix_sm hProd_int hFuture_int
    have hFuture_cond :
        μ[fun ω ↦ Real.exp (-((l : ℝ) * (X (s + t) ω : ℝ))) | generatedFiltrationSpace X s] =ᵐ[μ]
          fun ω ↦ branchingDiffusionLaplaceTransform t (X s ω) l := by
      -- Proof comment: this is exactly the conditional Laplace recursion from the standing
      -- chapter setup.
      simpa [μ, X] using hCond n s t l
    calc
      ∫ ω,
          Real.exp (-((a : ℝ) * (X s ω : ℝ))) *
            Real.exp (-((l : ℝ) * (X (s + t) ω : ℝ))) ∂μ
          = ∫ ω,
              μ[fun ω ↦
                  Real.exp (-((a : ℝ) * (X s ω : ℝ))) *
                    Real.exp (-((l : ℝ) * (X (s + t) ω : ℝ))) | generatedFiltrationSpace X s] ω ∂μ := by
              symm
              exact
                integral_condExp
                  (μ := μ) (m := generatedFiltrationSpace X s)
                  (f := fun ω ↦
                    Real.exp (-((a : ℝ) * (X s ω : ℝ))) *
                      Real.exp (-((l : ℝ) * (X (s + t) ω : ℝ))))
                  hhistory_le
      _ = ∫ ω,
            ((fun ω ↦ Real.exp (-((a : ℝ) * (X s ω : ℝ)))) *
              μ[fun ω ↦ Real.exp (-((l : ℝ) * (X (s + t) ω : ℝ))) |
                generatedFiltrationSpace X s]) ω ∂μ := by
            exact integral_congr_ae hPull
      _ = ∫ ω, Real.exp (-((a : ℝ) * (X s ω : ℝ))) *
            branchingDiffusionLaplaceTransform t (X s ω) l ∂μ := by
            exact integral_congr_ae ((Filter.EventuallyEq.refl _ _).mul hFuture_cond)
      _ = ∫ ω, Real.exp (-((coeff : ℝ) * (X s ω : ℝ))) ∂μ := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
            simpa [coeff, mul_comm] using
              (branchingDiffusionLaplaceTransform_updateCoeff t (X s ω) l a)
  have hSeq :
      (fun n ↦
        ∫ ω,
          Real.exp (-((a : ℝ) * (rescaledGaltonWatsonProcess (Z n) n s ω : ℝ))) *
            Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n (s + t) ω : ℝ))) ∂
            (PZ n : Measure (Ωn n))) =
        (fun n ↦
          ∫ ω, Real.exp (-((coeff : ℝ) * (rescaledGaltonWatsonProcess (Z n) n s ω : ℝ))) ∂
            (PZ n : Measure (Ωn n))) := by
    -- Proof comment: the conditional-expectation collapse identifies the whole sequence with the
    -- one-time Laplace sequence at the updated coefficient.
    funext n
    exact hCollapse n
  simpa [coeff, hSeq] using hLaplace s coeff

/-- Helper for Theorem 21.50: the two-time joint Laplace limit is most useful on an ordered pair
`u ≤ v`, so this corollary rewrites the increment form to the source-facing ordered-time form. -/
private theorem rescaledBranchingProcess_twoPointJointLaplaceTendsto_of_le
    (x : NNReal)
    (PZ : (n : ℕ) → ProbabilityMeasure (Ωn n))
    (Z : (n : ℕ) → ℕ → Ωn n → ℕ)
    (hZ_meas : ∀ n k : ℕ, Measurable (Z n k))
    (hLaplace :
      ∀ t l : NNReal,
        Tendsto
          (fun n ↦
            ∫ ω, Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n t ω : ℝ))) ∂
              (PZ n : Measure (Ωn n)))
          atTop
          (𝓝 (branchingDiffusionLaplaceTransform t x l)))
    (hCond :
      ∀ n : ℕ, ∀ s t l : NNReal,
        (PZ n : Measure (Ωn n))[fun ω ↦
          Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n (s + t) ω : ℝ))) |
            generatedFiltrationSpace (rescaledGaltonWatsonProcess (Z n) n) s] =ᵐ[
            (PZ n : Measure (Ωn n))]
          fun ω ↦
            branchingDiffusionLaplaceTransform t (rescaledGaltonWatsonProcess (Z n) n s ω) l)
    {u v : NNReal} (huv : u ≤ v) (a l : NNReal) :
    Tendsto
      (fun n ↦
        ∫ ω,
          Real.exp (-((a : ℝ) * (rescaledGaltonWatsonProcess (Z n) n u ω : ℝ))) *
            Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n v ω : ℝ))) ∂
            (PZ n : Measure (Ωn n)))
      atTop
      (𝓝 (branchingDiffusionLaplaceTransform u x (a + l / (l * (v - u) + 1)))) := by
  -- Proof comment: rewrite the ordered pair `(u, v)` as `(u, u + (v - u))` and apply the
  -- increment-form two-time limit already proved above.
  simpa [add_tsub_cancel_of_le huv, NNReal.coe_sub huv] using
    rescaledBranchingProcess_twoPointJointLaplaceTendsto
      x PZ Z hZ_meas hLaplace hCond u (v - u) a l

/-- Helper for Theorem 21.50: coerce an `NNReal`-valued ordered tuple to the Euclidean coordinate
space on the same finite index set. -/
private def orderedTupleToEuclidean (m : ℕ) :
    (Fin m → NNReal) → EuclideanSpace ℝ (Fin m) :=
  fun z ↦ WithLp.toLp 2 (fun i ↦ (z i : ℝ))

/-- Helper for Theorem 21.50: the coordinatewise coercion from `NNReal` tuples to Euclidean space
is continuous. -/
private lemma continuous_orderedTupleToEuclidean (m : ℕ) :
    Continuous (orderedTupleToEuclidean m) := by
  -- Proof comment: each Euclidean coordinate is just the continuous coercion `NNReal → ℝ`
  -- composed with one tuple projection, followed by the standard `toLp` homeomorphism.
  let coords : (Fin m → NNReal) → Fin m → ℝ := fun z i ↦ (z i : ℝ)
  have hcoords : Continuous coords := by
    refine continuous_pi fun i ↦ ?_
    simpa [coords] using
      (continuous_subtype_val.comp
        (continuous_apply i : Continuous fun z : Fin m → NNReal ↦ z i))
  simpa [orderedTupleToEuclidean, coords] using
    (PiLp.continuous_toLp 2 (fun _ : Fin m ↦ ℝ)).comp hcoords

/-- Helper for Theorem 21.50: every image point of `orderedTupleToEuclidean` lies in the
nonnegative orthant. -/
private lemma orderedTupleToEuclidean_nonneg (m : ℕ) (z : Fin m → NNReal) :
    ∀ i, 0 ≤ orderedTupleToEuclidean m z i := by
  -- Proof comment: each coordinate is the coercion of an `NNReal`, so it is automatically
  -- nonnegative.
  intro i
  simpa [orderedTupleToEuclidean, PiLp.toLp_apply] using (z i).2

/-- Helper for Theorem 21.50: the coordinatewise coercion remembers the whole `NNReal` tuple. -/
private lemma orderedTupleToEuclidean_injective (m : ℕ) :
    Function.Injective (orderedTupleToEuclidean m) := by
  -- Proof comment: equality in Euclidean coordinates gives equality of every real coordinate,
  -- and `NNReal` values are determined by their coercions to `ℝ`.
  intro z w h
  ext i
  have hi :
      orderedTupleToEuclidean m z i = orderedTupleToEuclidean m w i := by
    exact congrArg (fun u : EuclideanSpace ℝ (Fin m) ↦ u i) h
  simpa [orderedTupleToEuclidean, PiLp.toLp_apply] using hi

/-- Helper for Theorem 21.50: `orderedTupleToEuclidean` is a measurable embedding, so its
pushforward on measures is injective. -/
private lemma measurableEmbedding_orderedTupleToEuclidean (m : ℕ) :
    MeasurableEmbedding (orderedTupleToEuclidean m) :=
  (continuous_orderedTupleToEuclidean m).measurableEmbedding (orderedTupleToEuclidean_injective m)

/-- Helper for Theorem 21.50: every pushed-forward ordered tuple law is supported on the
nonnegative orthant of the Euclidean coordinate space. -/
private lemma ae_nonneg_orderedTupleToEuclidean_map
    (m : ℕ) (μ : Measure (Fin m → NNReal)) :
    ∀ᵐ x ∂(Measure.map (orderedTupleToEuclidean m) μ), ∀ i, 0 ≤ x i := by
  -- Proof comment: the tuple-to-Euclidean map only coerces nonnegative coordinates to `ℝ`.
  rw [(measurableEmbedding_orderedTupleToEuclidean m).ae_map_iff]
  exact Filter.Eventually.of_forall fun z i ↦ orderedTupleToEuclidean_nonneg m z i

/-- Helper for Theorem 21.50: equality of the Euclidean pushforwards of ordered tuple laws can be
pulled back to equality of the original tuple laws. -/
private lemma map_orderedTupleToEuclidean_injective (m : ℕ) :
    Function.Injective
      (fun μ : Measure (Fin m → NNReal) ↦ Measure.map (orderedTupleToEuclidean m) μ) :=
  (measurableEmbedding_orderedTupleToEuclidean m).map_injective

/-- Helper for Theorem 21.50: the Euclidean inner product against a coerced ordered tuple is the
weighted sum of its coordinates. -/
private lemma inner_orderedTupleToEuclidean_eq_sum
    (m : ℕ) (t : EuclideanSpace ℝ (Fin m)) (z : Fin m → NNReal) :
    inner ℝ t (orderedTupleToEuclidean m z) = ∑ i, t i * (z i : ℝ) := by
  -- Proof comment: `PiLp.inner_apply` expands the Euclidean inner product coordinatewise.
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [PiLp.toLp_apply]
  simpa using (RCLike.inner_apply' (t i) (z i : ℝ))

/-- Helper for Theorem 21.50: the Laplace kernel on the Euclidean pushforward of an ordered tuple
is the same pointwise exponential as the ordered joint Laplace functional on the original tuple
space. -/
private lemma mgf_orderedTupleToEuclidean_map_eq
    (m : ℕ) (μ : Measure (Fin m → NNReal)) (t : EuclideanSpace ℝ (Fin m)) :
    ProbabilityTheory.mgf (fun x ↦ -inner ℝ t x)
        (Measure.map (orderedTupleToEuclidean m) μ) 1 =
      ∫ z, Real.exp (-∑ i, t i * (z i : ℝ)) ∂μ := by
  have hExpMeas :
      AEStronglyMeasurable
        (fun x : EuclideanSpace ℝ (Fin m) ↦ Real.exp (1 * (-inner ℝ t x)))
        (Measure.map (orderedTupleToEuclidean m) μ) := by
    -- Proof comment: the Euclidean Laplace kernel is continuous, hence measurable on the
    -- pushforward law.
    exact (by fun_prop :
      Measurable (fun x : EuclideanSpace ℝ (Fin m) ↦ Real.exp (1 * (-inner ℝ t x)))).aestronglyMeasurable
  calc
    ProbabilityTheory.mgf (fun x ↦ -inner ℝ t x)
        (Measure.map (orderedTupleToEuclidean m) μ) 1 =
      ProbabilityTheory.mgf
        (fun z : Fin m → NNReal ↦ -inner ℝ t (orderedTupleToEuclidean m z)) μ 1 := by
          simpa [Function.comp] using
            (ProbabilityTheory.mgf_map
              (μ := μ)
              (Y := orderedTupleToEuclidean m)
              (X := fun x : EuclideanSpace ℝ (Fin m) ↦ -inner ℝ t x)
              (measurableEmbedding_orderedTupleToEuclidean m).measurable.aemeasurable
              hExpMeas)
    _ = ∫ z, Real.exp (-∑ i, t i * (z i : ℝ)) ∂μ := by
          rw [ProbabilityTheory.mgf]
          refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
          simp [inner_orderedTupleToEuclidean_eq_sum]

/-- Helper for Theorem 21.50: finite boxes in the ordered `NNReal` tuple space are compact. -/
private lemma isCompact_orderedTupleBox (m : ℕ) (R : NNReal) :
    IsCompact (Set.pi Set.univ (fun _ : Fin m ↦ Set.Icc (0 : NNReal) R)) := by
  -- Proof comment: this is the finite product of the compact intervals `[0, R]`.
  simpa using
    (isCompact_univ_pi fun _ : Fin m ↦
      (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) R)))

/-- Helper for Theorem 21.50: a nonnegative random variable has a tail bound controlled by any
positive Laplace parameter. -/
private lemma measureReal_gt_le_laplaceGap
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {X : α → NNReal} (hX : Measurable X) {l R : NNReal} (hl : 0 < l) (hR : 0 < R) :
    μ.real {ω | R < X ω} ≤
      (1 - ∫ ω, Real.exp (-((l : ℝ) * (X ω : ℝ))) ∂μ) /
        (1 - Real.exp (-((l : ℝ) * (R : ℝ)))) := by
  let s : Set α := {ω | R < X ω}
  let gap : ℝ := 1 - Real.exp (-((l : ℝ) * (R : ℝ)))
  have hs : MeasurableSet s := by
    -- Proof comment: the tail event is the preimage of the open ray `(R, ∞)`.
    simpa [s, Set.Ioi] using hX isOpen_Ioi.measurableSet
  have hgap_pos : 0 < gap := by
    -- Proof comment: `l > 0` and `R > 0` make the exponent strictly negative, so the Laplace
    -- gap `1 - exp (- l R)` is positive.
    have hexp_lt : Real.exp (-((l : ℝ) * (R : ℝ))) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith [hl, hR]
    dsimp [gap]
    linarith
  have hExp_meas : Measurable fun ω ↦ Real.exp (-((l : ℝ) * (X ω : ℝ))) := by
    -- Proof comment: the Laplace observable is a continuous transform of the measurable
    -- nonnegative random variable `X`.
    fun_prop
  have hExp_int :
      Integrable (fun ω ↦ Real.exp (-((l : ℝ) * (X ω : ℝ)))) μ := by
    -- Proof comment: the Laplace observable takes values in `[0, 1]`, so it is integrable under
    -- the probability law `μ`.
    refine Integrable.mono' (integrable_const (1 : ℝ)) hExp_meas.aestronglyMeasurable ?_
    filter_upwards with ω
    have hnonneg : 0 ≤ Real.exp (-((l : ℝ) * (X ω : ℝ))) := by positivity
    have hle : Real.exp (-((l : ℝ) * (X ω : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [l.2, (X ω).2]
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hGap_int : Integrable (s.indicator fun _ ↦ gap) μ := by
    -- Proof comment: the indicator of the tail event is integrable because it is a bounded
    -- constant on a measurable set.
    exact (integrable_const gap).indicator hs
  have hGap_le :
      ∀ ω, s.indicator (fun _ ↦ gap) ω ≤ 1 - Real.exp (-((l : ℝ) * (X ω : ℝ))) := by
    -- Proof comment: on the tail event we compare `exp (- l X)` with `exp (- l R)`; away from the
    -- tail event the indicator vanishes.
    intro ω
    by_cases hω : ω ∈ s
    · have hXR : (R : ℝ) < (X ω : ℝ) := by
        simpa [s] using hω
      have hmul : (l : ℝ) * (R : ℝ) < (l : ℝ) * (X ω : ℝ) := by
        exact mul_lt_mul_of_pos_left hXR hl
      have hexp_le :
          Real.exp (-((l : ℝ) * (X ω : ℝ))) ≤ Real.exp (-((l : ℝ) * (R : ℝ))) := by
        refine Real.exp_le_exp.mpr ?_
        linarith
      have hsub :
          gap ≤ 1 - Real.exp (-((l : ℝ) * (X ω : ℝ))) := by
        dsimp [gap]
        linarith
      simpa [s, hω] using hsub
    · have hnonneg : 0 ≤ (l : ℝ) * (X ω : ℝ) := by positivity
      have hle : Real.exp (-((l : ℝ) * (X ω : ℝ))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith
      simp [s, hω, gap]
      linarith
  have hmono :
      ∫ ω, s.indicator (fun _ ↦ gap) ω ∂μ ≤
        ∫ ω, (1 - Real.exp (-((l : ℝ) * (X ω : ℝ)))) ∂μ := by
    -- Proof comment: integrate the pointwise tail inequality.
    refine integral_mono_ae hGap_int ((integrable_const (1 : ℝ)).sub hExp_int) ?_
    exact Filter.Eventually.of_forall hGap_le
  have hleft :
      ∫ ω, s.indicator (fun _ ↦ gap) ω ∂μ = gap * μ.real s := by
    -- Proof comment: the left-hand side is the tail-event mass times the positive constant gap.
    rw [MeasureTheory.integral_indicator_const gap hs]
    simpa [smul_eq_mul, mul_comm] using (MeasureTheory.setIntegral_const (μ := μ) (s := s) gap)
  have hright :
      ∫ ω, (1 - Real.exp (-((l : ℝ) * (X ω : ℝ)))) ∂μ =
        1 - ∫ ω, Real.exp (-((l : ℝ) * (X ω : ℝ))) ∂μ := by
    -- Proof comment: integrate the Laplace gap under the probability law `μ`.
    rw [integral_sub (integrable_const (1 : ℝ)) hExp_int, integral_const]
    simp
  have htail :
      gap * μ.real s ≤ 1 - ∫ ω, Real.exp (-((l : ℝ) * (X ω : ℝ))) ∂μ := by
    simpa [hleft, hright] using hmono
  -- Proof comment: divide by the positive Laplace gap.
  refine (le_div_iff₀ hgap_pos).2 ?_
  simpa [mul_comm] using htail

/-- Helper for Theorem 21.50: finite weighted sums of nonnegative coordinates give measurable
Laplace kernels. -/
private lemma measurable_expNegFinSum_nnreal
    {α : Type*} [MeasurableSpace α] {k : ℕ}
    (X : Fin k → α → NNReal) (hX : ∀ i : Fin k, Measurable (X i))
    (a : Fin k → NNReal) :
    Measurable (fun ω ↦ Real.exp (-∑ i, (a i : ℝ) * (X i ω : ℝ))) := by
  have hsum :
      Measurable (fun ω ↦ ∑ i : Fin k, (a i : ℝ) * (X i ω : ℝ)) := by
    -- Proof comment: the weighted coordinate sum is measurable term by term.
    refine Finset.measurable_sum Finset.univ fun i _ ↦ ?_
    exact (hX i).coe_nnreal_real.const_mul (a i : ℝ)
  -- Proof comment: the Laplace kernel is the exponential of the negative weighted sum.
  exact Real.continuous_exp.measurable.comp hsum.neg

/-- Helper for Theorem 21.50: the finite ordered-joint Laplace kernels are integrable under any
probability law because they take values in `[0, 1]`. -/
private lemma integrable_expNegFinSum_nnreal
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {k : ℕ} (X : Fin k → α → NNReal) (hX : ∀ i : Fin k, Measurable (X i))
    (a : Fin k → NNReal) :
    Integrable (fun ω ↦ Real.exp (-∑ i, (a i : ℝ) * (X i ω : ℝ))) μ := by
  have hmeas :
      Measurable (fun ω ↦ Real.exp (-∑ i, (a i : ℝ) * (X i ω : ℝ))) :=
    measurable_expNegFinSum_nnreal X hX a
  refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  have hnonneg :
      0 ≤ Real.exp (-∑ i : Fin k, (a i : ℝ) * (X i ω : ℝ)) := by
    positivity
  have hsum_nonneg :
      0 ≤ ∑ i : Fin k, (a i : ℝ) * (X i ω : ℝ) := by
    refine Finset.sum_nonneg fun i _ ↦ ?_
    exact mul_nonneg (by exact_mod_cast (a i).2) (by exact_mod_cast (X i ω).2)
  have hle :
      Real.exp (-∑ i : Fin k, (a i : ℝ) * (X i ω : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle

/-- Helper for Theorem 21.50: splitting a `Fin (m + 2)` weighted sum at the last coordinate
separates the `Fin.castSucc` prefix from the terminal term. -/
private lemma sum_univ_castSucc_mul_nnreal
    {m : ℕ} (a z : Fin (m + 2) → NNReal) :
    (∑ i : Fin (m + 2), (a i : ℝ) * (z i : ℝ)) =
      (∑ i : Fin (m + 1), (a i.castSucc : ℝ) * (z i.castSucc : ℝ)) +
        (a (Fin.last (m + 1)) : ℝ) * (z (Fin.last (m + 1)) : ℝ) := by
  -- Proof comment: `Fin.sum_univ_castSucc` is exactly the bookkeeping split used by the
  -- backward ordered-joint Laplace recursion.
  simpa using
    (Fin.sum_univ_castSucc
      (f := fun i : Fin (m + 2) ↦ (a i : ℝ) * (z i : ℝ)))

/-- Helper for Theorem 21.50: the ordered-joint Laplace prefix up to the penultimate ordered time
is measurable for the history sigma-algebra at that penultimate time. -/
private lemma orderedJointLaplacePrefix_stronglyMeasurable
    {α : Type*} [MeasurableSpace α] (X : NNReal → α → NNReal)
    {m : ℕ} (times : Fin (m + 2) → NNReal) (htimes : Monotone times)
    (a : Fin (m + 1) → NNReal) :
    StronglyMeasurable[generatedFiltrationSpace X (times (Fin.castSucc (Fin.last m)))]
      (fun ω ↦ Real.exp (-∑ i : Fin (m + 1), (a i : ℝ) * (X (times i.castSucc) ω : ℝ))) := by
  have hcoord :
      ∀ i : Fin (m + 1),
        Measurable[generatedFiltrationSpace X (times (Fin.castSucc (Fin.last m)))]
          (fun ω ↦ X (times i.castSucc) ω) := by
    intro i
    -- Proof comment: every prefix coordinate occurs no later than the penultimate ordered time.
    refine Measurable.of_comap_le ?_
    exact
      past_le_generatedFiltrationSpace X
        (htimes (Fin.castSucc_le_castSucc_iff.mpr i.le_last))
  have hsum_meas :
      Measurable[generatedFiltrationSpace X (times (Fin.castSucc (Fin.last m)))]
        (fun ω ↦ ∑ i : Fin (m + 1), (a i : ℝ) * (X (times i.castSucc) ω : ℝ)) := by
    -- Proof comment: the whole prefix sum is strongly measurable because each coordinate term is.
    refine
      Finset.measurable_sum (Finset.univ : Finset (Fin (m + 1))) fun i _ ↦ ?_
    exact measurable_const.mul (hcoord i).coe_nnreal_real
  have hsum :
      StronglyMeasurable[generatedFiltrationSpace X (times (Fin.castSucc (Fin.last m)))]
        (fun ω ↦ ∑ i : Fin (m + 1), (a i : ℝ) * (X (times i.castSucc) ω : ℝ)) :=
    hsum_meas.stronglyMeasurable
  -- Proof comment: exponentiating the negative prefix sum keeps the history measurability.
  exact Real.continuous_exp.comp_stronglyMeasurable hsum.neg

/-- Helper for Theorem 21.50: a finite tuple of time evaluations is measurable once each sampled
coordinate is measurable. -/
private lemma measurable_historyTuple
    {α : Type*} [MeasurableSpace α] (X : NNReal → α → NNReal)
    {m : ℕ} (times : Fin (m + 1) → NNReal) (hX : ∀ t : NNReal, Measurable (X t)) :
    Measurable (fun ω i ↦ X (times i) ω) := by
  -- Proof comment: measurability on the finite product is coordinatewise.
  exact measurable_pi_lambda _ fun i ↦ hX (times i)

/-- Helper for Theorem 21.50: a measurable event in the prefix tuple is measurable for the
generated filtration at the predecessor time. -/
private lemma prefixTuple_preimage_measurable_generatedFiltration
    {α : Type*} [MeasurableSpace α] (X : NNReal → α → NNReal)
    {m : ℕ} (times : Fin (m + 2) → NNReal) (htimes : Monotone times)
    {B : Set (Fin (m + 1) → NNReal)} (hB : MeasurableSet B) :
    let prefixTimes : Fin (m + 1) → NNReal := fun i ↦ times i.castSucc
    let prefixTuple : α → Fin (m + 1) → NNReal := fun ω i ↦ X (prefixTimes i) ω
    let sPrev : NNReal := prefixTimes (Fin.last m)
    MeasurableSet[generatedFiltrationSpace X sPrev] (prefixTuple ⁻¹' B) := by
  let prefixTimes : Fin (m + 1) → NNReal := fun i ↦ times i.castSucc
  let prefixTuple : α → Fin (m + 1) → NNReal := fun ω i ↦ X (prefixTimes i) ω
  let sPrev : NNReal := prefixTimes (Fin.last m)
  have hprefixMeas :
      Measurable[generatedFiltrationSpace X sPrev] prefixTuple := by
    letI : MeasurableSpace α := generatedFiltrationSpace X sPrev
    -- Proof comment: each prefix coordinate occurs no later than the predecessor time, so every
    -- coordinate map is measurable for the predecessor history sigma-algebra.
    change Measurable prefixTuple
    refine measurable_pi_lambda _ fun i ↦ ?_
    refine Measurable.of_comap_le ?_
    simpa [prefixTimes, sPrev] using
      (past_le_generatedFiltrationSpace X
        (r := prefixTimes i) (s := sPrev)
        (htimes (Fin.castSucc_le_castSucc_iff.mpr i.le_last)))
  -- Proof comment: measurability of the whole prefix tuple pulls measurable rectangle events back
  -- to predecessor-history events.
  simpa [prefixTuple] using hprefixMeas hB

/-- Helper for Theorem 21.50: updating the last coefficient of a finite weighted sum adds the
corresponding extra multiple of the last coordinate. -/
private lemma sum_update_last_mul_nnreal
    {m : ℕ} (a z : Fin (m + 1) → NNReal) (c : NNReal) :
    (∑ i : Fin (m + 1),
        ((Function.update a (Fin.last m) (a (Fin.last m) + c)) i : ℝ) * (z i : ℝ)) =
      (∑ i : Fin (m + 1), (a i : ℝ) * (z i : ℝ)) + (c : ℝ) * (z (Fin.last m) : ℝ) := by
  -- Proof comment: split both sums into their `Fin.castSucc` prefix and last coordinate, and note
  -- that `Function.update` only changes the last term.
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp [Function.update, Fin.castSucc_ne_last]
  ring

/-- Helper for Theorem 21.50: the discrete ordered-joint Laplace functional collapses the last
coordinate into the penultimate coefficient after conditioning on the predecessor history. -/
private theorem rescaledBranchingProcessCollapseLastOrderedJointLaplace_eq
    (PZ : (n : ℕ) → ProbabilityMeasure (Ωn n))
    (Z : (n : ℕ) → ℕ → Ωn n → ℕ)
    (hZ_meas : ∀ n k : ℕ, Measurable (Z n k))
    (hCond :
      ∀ n : ℕ, ∀ s t l : NNReal,
        (PZ n : Measure (Ωn n))[fun ω ↦
          Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n (s + t) ω : ℝ))) |
            generatedFiltrationSpace (rescaledGaltonWatsonProcess (Z n) n) s] =ᵐ[
            (PZ n : Measure (Ωn n))]
          fun ω ↦
            branchingDiffusionLaplaceTransform t (rescaledGaltonWatsonProcess (Z n) n s ω) l)
    {m : ℕ} (times : Fin (m + 2) → NNReal) (htimes : Monotone times)
    (a : Fin (m + 2) → NNReal) (n : ℕ) :
    let X : NNReal → Ωn n → NNReal := rescaledGaltonWatsonProcess (Z n) n
    let prefixTimes : Fin (m + 1) → NNReal := fun i ↦ times i.castSucc
    let sPrev : NNReal := prefixTimes (Fin.last m)
    let sLast : NNReal := times (Fin.last (m + 1))
    let gap : NNReal := sLast - sPrev
    let updatedCoeff : Fin (m + 1) → NNReal :=
      Function.update (fun i ↦ a i.castSucc) (Fin.last m)
        (a (Fin.castSucc (Fin.last m)) + a (Fin.last (m + 1)) / (a (Fin.last (m + 1)) * gap + 1))
    ∫ ω, Real.exp (-∑ i : Fin (m + 2), (a i : ℝ) * (X (times i) ω : ℝ)) ∂(PZ n : Measure (Ωn n)) =
      ∫ ω, Real.exp (-∑ i : Fin (m + 1), (updatedCoeff i : ℝ) * (X (prefixTimes i) ω : ℝ)) ∂
        (PZ n : Measure (Ωn n)) := by
  let μ : Measure (Ωn n) := (PZ n : Measure (Ωn n))
  let X : NNReal → Ωn n → NNReal := rescaledGaltonWatsonProcess (Z n) n
  let prefixTimes : Fin (m + 1) → NNReal := fun i ↦ times i.castSucc
  let sPrev : NNReal := prefixTimes (Fin.last m)
  let sLast : NNReal := times (Fin.last (m + 1))
  let gap : NNReal := sLast - sPrev
  let prefixCoeff : Fin (m + 1) → NNReal := fun i ↦ a i.castSucc
  let lastCoeff : NNReal := a (Fin.last (m + 1))
  let extraCoeff : NNReal := lastCoeff / (lastCoeff * gap + 1)
  let updatedCoeff : Fin (m + 1) → NNReal :=
    Function.update prefixCoeff (Fin.last m) (prefixCoeff (Fin.last m) + extraCoeff)
  let prefixExp : Ωn n → ℝ :=
    fun ω ↦ Real.exp (-∑ i : Fin (m + 1), (prefixCoeff i : ℝ) * (X (prefixTimes i) ω : ℝ))
  let futureExp : Ωn n → ℝ :=
    fun ω ↦ Real.exp (-((lastCoeff : ℝ) * (X sLast ω : ℝ)))
  have hX_meas : ∀ t : NNReal, Measurable (X t) := by
    intro t
    -- Proof comment: every fixed-time rescaled coordinate is measurable by construction.
    simpa [X] using measurable_rescaledGaltonWatsonProcess Z hZ_meas n t
  have hhistory_le : generatedFiltrationSpace X sPrev ≤ (inferInstance : MeasurableSpace (Ωn n)) := by
    -- Proof comment: the whole predecessor filtration lives inside the ambient sigma-algebra
    -- because every rescaled coordinate is measurable.
    exact generatedFiltrationSpace_le_ambient X hX_meas sPrev
  have hsPrevLast : sPrev ≤ sLast := by
    -- Proof comment: the predecessor time is one of the earlier coordinates of the ordered tuple.
    simpa [prefixTimes, sPrev, sLast] using htimes (Fin.le_last (Fin.castSucc (Fin.last m)))
  have hgap : sPrev + gap = sLast := by
    -- Proof comment: `gap` is defined as the increment from the predecessor time to the last
    -- time.
    simpa [gap] using add_tsub_cancel_of_le hsPrevLast
  have hPrefix_sm :
      StronglyMeasurable[generatedFiltrationSpace X sPrev] prefixExp := by
    -- Proof comment: the prefix Laplace weight depends only on the predecessor history.
    simpa [prefixExp, prefixCoeff, prefixTimes, sPrev] using
      orderedJointLaplacePrefix_stronglyMeasurable X times htimes prefixCoeff
  have hPrefix_meas : Measurable prefixExp := by
    -- Proof comment: viewed in the ambient space, the prefix Laplace factor is just a finite
    -- measurable coordinate sum followed by `exp`.
    simpa [prefixExp] using
      measurable_expNegFinSum_nnreal
        (X := fun i ω ↦ X (prefixTimes i) ω)
        (hX := fun i ↦ hX_meas (prefixTimes i))
        prefixCoeff
  have hFuture_meas : Measurable futureExp := by
    -- Proof comment: the last-coordinate Laplace factor is another measurable time evaluation.
    simpa [futureExp] using
      (show Measurable (fun ω ↦ Real.exp (-((lastCoeff : ℝ) * (X sLast ω : ℝ)))) from by
        fun_prop)
  have hFuture_int : Integrable futureExp μ := by
    -- Proof comment: the future Laplace factor takes values in `[0, 1]`.
    refine Integrable.mono' (integrable_const (1 : ℝ)) hFuture_meas.aestronglyMeasurable ?_
    filter_upwards with ω
    have hnonneg : 0 ≤ futureExp ω := by
      positivity
    have hle : futureExp ω ≤ 1 := by
      simp [futureExp, Real.exp_le_one_iff]
      nlinarith [lastCoeff.2, (X sLast ω).2]
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hProd_int : Integrable (fun ω ↦ prefixExp ω * futureExp ω) μ := by
    -- Proof comment: both Laplace factors lie in `[0, 1]`, so their product is bounded by `1`.
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (hPrefix_meas.aestronglyMeasurable.mul hFuture_meas.aestronglyMeasurable) ?_
    filter_upwards with ω
    have hprefix_nonneg : 0 ≤ prefixExp ω := by
      positivity
    have hfuture_nonneg : 0 ≤ futureExp ω := by
      positivity
    have hprefix_sum_nonneg :
        0 ≤ ∑ i : Fin (m + 1), (prefixCoeff i : ℝ) * (X (prefixTimes i) ω : ℝ) := by
      refine Finset.sum_nonneg fun i _ ↦ ?_
      exact mul_nonneg (by exact_mod_cast (prefixCoeff i).2) (by exact_mod_cast (X (prefixTimes i) ω).2)
    have hprefix_le : prefixExp ω ≤ 1 := by
      simp [prefixExp, Real.exp_le_one_iff]
      linarith
    have hfuture_le : futureExp ω ≤ 1 := by
      simp [futureExp, Real.exp_le_one_iff]
      nlinarith [lastCoeff.2, (X sLast ω).2]
    have hmul_le : prefixExp ω * futureExp ω ≤ 1 := by
      nlinarith
    have hmul_abs :
        |prefixExp ω| * |futureExp ω| ≤ 1 := by
      simpa [abs_of_nonneg hprefix_nonneg, abs_of_nonneg hfuture_nonneg] using hmul_le
    simpa [Real.norm_eq_abs] using hmul_abs
  have hPull :
      μ[fun ω ↦ prefixExp ω * futureExp ω | generatedFiltrationSpace X sPrev] =ᵐ[μ]
        (fun ω ↦ prefixExp ω) * μ[futureExp | generatedFiltrationSpace X sPrev] := by
    -- Proof comment: pull the predecessor-history factor outside the predecessor-history
    -- conditional expectation.
    exact condExp_mul_of_stronglyMeasurable_left hPrefix_sm hProd_int hFuture_int
  have hFuture_cond :
      μ[futureExp | generatedFiltrationSpace X sPrev] =ᵐ[μ]
        fun ω ↦ branchingDiffusionLaplaceTransform gap (X sPrev ω) lastCoeff := by
    -- Proof comment: the standing discrete recursion identifies the conditioned last-coordinate
    -- Laplace factor with the explicit branching-diffusion transform started from the predecessor
    -- state.
    simpa [μ, X, futureExp, hgap] using hCond n sPrev gap lastCoeff
  have hsplit :
      ∀ ω,
        Real.exp (-∑ i : Fin (m + 2), (a i : ℝ) * (X (times i) ω : ℝ)) =
          prefixExp ω * futureExp ω := by
    intro ω
    simp only [prefixExp, futureExp]
    rw [sum_univ_castSucc_mul_nnreal (a := a) (z := fun i ↦ X (times i) ω)]
    rw [show
      -((∑ i : Fin (m + 1), (a i.castSucc : ℝ) * (X (times i.castSucc) ω : ℝ)) +
          (a (Fin.last (m + 1)) : ℝ) * (X (times (Fin.last (m + 1))) ω : ℝ)) =
        (-∑ i : Fin (m + 1), (a i.castSucc : ℝ) * (X (times i.castSucc) ω : ℝ)) +
          (-((a (Fin.last (m + 1)) : ℝ) * (X (times (Fin.last (m + 1))) ω : ℝ))) by ring]
    simp [prefixTimes, sLast, prefixCoeff, lastCoeff, Real.exp_add, mul_comm]
  have hcollapse :
      ∀ ω,
        prefixExp ω * branchingDiffusionLaplaceTransform gap (X sPrev ω) lastCoeff =
          Real.exp (-∑ i : Fin (m + 1), (updatedCoeff i : ℝ) * (X (prefixTimes i) ω : ℝ)) := by
    intro ω
    have hsum_update :
        (∑ i : Fin (m + 1), (updatedCoeff i : ℝ) * (X (prefixTimes i) ω : ℝ)) =
          (∑ i : Fin (m + 1), (prefixCoeff i : ℝ) * (X (prefixTimes i) ω : ℝ)) +
            (extraCoeff : ℝ) * (X sPrev ω : ℝ) := by
      simpa [updatedCoeff, prefixCoeff, extraCoeff, prefixTimes, sPrev] using
        (sum_update_last_mul_nnreal
          (a := prefixCoeff) (z := fun i ↦ X (prefixTimes i) ω) (c := extraCoeff))
    have hextra :
        (extraCoeff : ℝ) * (X sPrev ω : ℝ) =
          ((lastCoeff : ℝ) * (X sPrev ω : ℝ)) / (((lastCoeff : ℝ) * (gap : ℝ)) + 1) := by
      have hnn :
          extraCoeff * X sPrev ω = (lastCoeff * X sPrev ω) / (lastCoeff * gap + 1) := by
        -- Proof comment: in `NNReal`, collapsing the extra coefficient is just associativity of
        -- multiplication and division by the same positive denominator.
        dsimp [extraCoeff]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      exact_mod_cast hnn
    calc
      prefixExp ω * branchingDiffusionLaplaceTransform gap (X sPrev ω) lastCoeff
          = Real.exp (-∑ i : Fin (m + 1), (prefixCoeff i : ℝ) * (X (prefixTimes i) ω : ℝ)) *
              Real.exp (-((extraCoeff : ℝ) * (X sPrev ω : ℝ))) := by
                simpa [prefixExp, branchingDiffusionLaplaceTransform_apply, hextra, mul_comm]
      _ = Real.exp
            ((-∑ i : Fin (m + 1), (prefixCoeff i : ℝ) * (X (prefixTimes i) ω : ℝ)) +
              (-((extraCoeff : ℝ) * (X sPrev ω : ℝ)))) := by
                rw [← Real.exp_add]
      _ = Real.exp (-∑ i : Fin (m + 1), (updatedCoeff i : ℝ) * (X (prefixTimes i) ω : ℝ)) := by
            congr 1
            rw [hsum_update]
            ring
  calc
    ∫ ω, Real.exp (-∑ i : Fin (m + 2), (a i : ℝ) * (X (times i) ω : ℝ)) ∂μ
        = ∫ ω, prefixExp ω * futureExp ω ∂μ := by
            refine integral_congr_ae <| Filter.Eventually.of_forall hsplit
    _ = ∫ ω,
          μ[fun ω ↦ prefixExp ω * futureExp ω | generatedFiltrationSpace X sPrev] ω ∂μ := by
            symm
            exact
              integral_condExp
                (μ := μ) (m := generatedFiltrationSpace X sPrev)
                (f := fun ω ↦ prefixExp ω * futureExp ω) hhistory_le
    _ = ∫ ω, ((fun ω ↦ prefixExp ω) * μ[futureExp | generatedFiltrationSpace X sPrev]) ω ∂μ := by
          exact integral_congr_ae hPull
    _ = ∫ ω, prefixExp ω * branchingDiffusionLaplaceTransform gap (X sPrev ω) lastCoeff ∂μ := by
          exact integral_congr_ae ((Filter.EventuallyEq.refl _ _).mul hFuture_cond)
    _ = ∫ ω, Real.exp (-∑ i : Fin (m + 1), (updatedCoeff i : ℝ) * (X (prefixTimes i) ω : ℝ)) ∂μ := by
          refine integral_congr_ae <| Filter.Eventually.of_forall hcollapse

/-- Helper for Theorem 21.50: the joint law of the prefix tuple and final state of the limiting
branching diffusion is the prefix law followed by the last-state kernel row. -/
private theorem branchingDiffusionPrefixLastLaw_eq_compProd
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (x : NNReal) [IsMarkovProcessRealization κ P Y]
    {m : ℕ} (times : Fin (m + 2) → NNReal) (htimes : Monotone times) :
    let prefixTimes : Fin (m + 1) → NNReal := fun i ↦ times i.castSucc
    let prefixTuple : Ω → Fin (m + 1) → NNReal := fun ω i ↦ Y (prefixTimes i) ω
    let sPrev : NNReal := prefixTimes (Fin.last m)
    let sLast : NNReal := times (Fin.last (m + 1))
    let gap : NNReal := sLast - sPrev
    let stepKernel : Kernel (Fin (m + 1) → NNReal) NNReal :=
      Kernel.comap (κ gap) (fun z ↦ z (Fin.last m)) (by fun_prop)
    ((P x : Measure Ω).map (fun ω ↦ (prefixTuple ω, Y sLast ω))) =
      ((P x : Measure Ω).map prefixTuple) ⊗ₘ stepKernel := by
  let μ : Measure Ω := (P x : Measure Ω)
  let prefixTimes : Fin (m + 1) → NNReal := fun i ↦ times i.castSucc
  let prefixTuple : Ω → Fin (m + 1) → NNReal := fun ω i ↦ Y (prefixTimes i) ω
  let sPrev : NNReal := prefixTimes (Fin.last m)
  let sLast : NNReal := times (Fin.last (m + 1))
  let gap : NNReal := sLast - sPrev
  let lastPrefix : (Fin (m + 1) → NNReal) → NNReal := fun z ↦ z (Fin.last m)
  let stepKernel : Kernel (Fin (m + 1) → NNReal) NNReal :=
    Kernel.comap (κ gap) lastPrefix (by fun_prop)
  have hsPrevLast : sPrev ≤ sLast := by
    -- Proof comment: the predecessor time is one of the earlier coordinates of the ordered tuple.
    simpa [prefixTimes, sPrev, sLast] using
      htimes (Fin.le_last (Fin.castSucc (Fin.last m)))
  have hgap : sPrev + gap = sLast := by
    -- Proof comment: `gap` is defined as the difference between the last time and its
    -- predecessor, so adding it back recovers the terminal time.
    simpa [gap] using add_tsub_cancel_of_le hsPrevLast
  have hprefixTupleMeas : Measurable prefixTuple := by
    -- Proof comment: each prefix coordinate is one of the measurable process coordinates.
    simpa [prefixTuple] using
      (measurable_historyTuple (X := Y) (times := prefixTimes)
        (hX := IsMarkovProcessRealization.measurable_process (κ := κ) (P := P) (Y := Y)))
  have hprefixLast :
      lastPrefix ∘ prefixTuple = Y sPrev := by
    -- Proof comment: the last coordinate of the prefix tuple is exactly the predecessor state.
    funext ω
    simp [lastPrefix, prefixTuple, prefixTimes, sPrev]
  refine Measure.ext_prod ?_
  intro B A hB hA
  let prefixEvent : Set Ω := prefixTuple ⁻¹' B
  let lastEvent : Set Ω := Y sLast ⁻¹' A
  have hprefixGenerated :
      MeasurableSet[generatedFiltrationSpace Y sPrev] prefixEvent := by
    -- Proof comment: measurable prefix-tuple events depend only on the predecessor history.
    simpa [prefixEvent, prefixTuple, prefixTimes, sPrev] using
      (prefixTuple_preimage_measurable_generatedFiltration
        (X := Y) (times := times) htimes (B := B) hB)
  have hgenerated_le : generatedFiltrationSpace Y sPrev ≤ (inferInstance : MeasurableSpace Ω) := by
    -- Proof comment: every process coordinate is ambient measurable, so the generated history
    -- sigma-algebra sits inside the ambient one.
    exact
      generatedFiltrationSpace_le_ambient Y
        (IsMarkovProcessRealization.measurable_process (κ := κ) (P := P) (Y := Y)) sPrev
  have hprefixEventMeas : MeasurableSet prefixEvent := hgenerated_le _ hprefixGenerated
  have hlastEventMeas : MeasurableSet lastEvent := by
    -- Proof comment: the final-state event is the preimage of a measurable state event.
    simpa [lastEvent] using
      (IsMarkovProcessRealization.measurable_process
        (κ := κ) (P := P) (Y := Y) sLast) hA
  have hgap' : gap + sPrev = sLast := by
    -- Proof comment: the Markov-property API uses the future increment on the left.
    simpa [add_comm] using hgap
  have hmarkov :
      μ⟦lastEvent | generatedFiltrationSpace Y sPrev⟧ =ᵐ[μ]
        fun ω ↦ ((κ gap) (Y sPrev ω)).real A := by
    -- Proof comment: rewrite the terminal time as `sPrev + gap` and apply the realization-level
    -- Markov property at the last step.
    simpa [μ, lastEvent, sLast, hgap', add_comm, add_left_comm, add_assoc] using
      (IsMarkovProcessRealization.markov_property
        (κ := κ) (P := P) (Y := Y) x hA sPrev gap)
  have hIndicatorInt :
      Integrable (Set.indicator lastEvent (fun _ ↦ (1 : ℝ))) μ := by
    -- Proof comment: indicators of measurable events are integrable under the probability law.
    exact (integrable_const (1 : ℝ)).indicator hlastEventMeas
  letI : IsMarkovKernel stepKernel := by
    -- Proof comment: each row of the comapped step kernel is the realized one-time marginal
    -- started from the last prefix state.
    refine ⟨fun z ↦ ?_⟩
    rw [show stepKernel z = (κ gap) (lastPrefix z) by rfl]
    rw [← IsMarkovProcessRealization.transition_eq
      (κ := κ) (P := P) (Y := Y) (lastPrefix z) gap]
    exact
      Measure.isProbabilityMeasure_map
        (μ := (P (lastPrefix z) : Measure Ω)) (f := Y gap)
        (IsMarkovProcessRealization.measurable_process
          (κ := κ) (P := P) (Y := Y) gap).aemeasurable
  have hrealizedRect :
      (μ.map (fun ω ↦ (prefixTuple ω, Y sLast ω))).real (B ×ˢ A) =
        ∫ z in B, ((stepKernel z).real A) ∂(μ.map prefixTuple) := by
    have hrect :
        μ.real (prefixEvent ∩ lastEvent) =
          ∫ ω in prefixEvent, ((κ gap) (Y sPrev ω)).real A ∂μ := by
      -- Proof comment: integrate the last-step conditional expectation over the prefix-history
      -- event.
      calc
        μ.real (prefixEvent ∩ lastEvent)
            = ∫ ω in prefixEvent, (μ⟦lastEvent | generatedFiltrationSpace Y sPrev⟧) ω ∂μ := by
                rw [MeasureTheory.setIntegral_condExp hgenerated_le hIndicatorInt hprefixGenerated,
                  ← MeasureTheory.integral_indicator hprefixEventMeas]
                symm
                simpa [lastEvent, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
                  Set.inter_comm, smul_eq_mul] using
                  MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                    (hprefixEventMeas.inter hlastEventMeas)
        _ = ∫ ω in prefixEvent, ((κ gap) (Y sPrev ω)).real A ∂μ := by
              refine MeasureTheory.setIntegral_congr_ae hprefixEventMeas ?_
              exact hmarkov.mono fun _ hω _ ↦ hω
    have hstepInt :
        Integrable (fun z : Fin (m + 1) → NNReal ↦ (stepKernel z).real A) (μ.map prefixTuple) := by
      -- Proof comment: the comapped last-step kernel is still Markov, so its rectangle masses are
      -- integrable against the prefix law.
      simpa [stepKernel] using
        (ProbabilityTheory.Kernel.IsMarkovKernel.integrable
          (μ := μ.map prefixTuple) (κ := stepKernel) hA)
    have hpush :
        ∫ z in B, (stepKernel z).real A ∂(μ.map prefixTuple) =
          ∫ ω in prefixEvent, ((κ gap) (Y sPrev ω)).real A ∂μ := by
      -- Proof comment: push the prefix-state integral back through the measurable prefix tuple.
      rw [← MeasureTheory.integral_indicator hB]
      change
        ∫ z, Set.indicator B (fun z : Fin (m + 1) → NNReal ↦ (stepKernel z).real A) z
          ∂(μ.map prefixTuple) =
            ∫ ω in prefixEvent, ((κ gap) (Y sPrev ω)).real A ∂μ
      rw [MeasureTheory.integral_map hprefixTupleMeas.aemeasurable
        ((hstepInt.indicator hB).aestronglyMeasurable)]
      have hindicator :
          (fun ω ↦
            Set.indicator B (fun z : Fin (m + 1) → NNReal ↦ (stepKernel z).real A)
              (prefixTuple ω)) =
            Set.indicator prefixEvent (fun ω ↦ ((κ gap) (Y sPrev ω)).real A) := by
        funext ω
        by_cases hω : prefixTuple ω ∈ B
        · have hlast_eval : lastPrefix (prefixTuple ω) = Y sPrev ω := by
            simpa [Function.comp_apply] using congrFun hprefixLast ω
          simp [prefixEvent, hω, stepKernel, hlast_eval]
        · simp [prefixEvent, hω, stepKernel]
      rw [hindicator, MeasureTheory.integral_indicator hprefixEventMeas]
    have hpairMeas : Measurable (fun ω ↦ (prefixTuple ω, Y sLast ω)) := by
      -- Proof comment: the realized split map is measurable coordinatewise.
      exact hprefixTupleMeas.prodMk <|
        IsMarkovProcessRealization.measurable_process (κ := κ) (P := P) (Y := Y) sLast
    have hpre :
        (fun ω ↦ (prefixTuple ω, Y sLast ω)) ⁻¹' (B ×ˢ A) = prefixEvent ∩ lastEvent := by
      ext ω
      simp [prefixEvent, lastEvent]
    -- Proof comment: rewrite the realized rectangle as a concrete prefix/last event and then use
    -- the pushforward rectangle computation.
    calc
      (μ.map (fun ω ↦ (prefixTuple ω, Y sLast ω))).real (B ×ˢ A)
          = μ.real (prefixEvent ∩ lastEvent) := by
              rw [MeasureTheory.map_measureReal_apply hpairMeas (hB.prod hA), hpre]
      _ = ∫ ω in prefixEvent, ((κ gap) (Y sPrev ω)).real A ∂μ := hrect
      _ = ∫ z in B, (stepKernel z).real A ∂(μ.map prefixTuple) := hpush.symm
      _ = ∫ z in B, ((stepKernel z).real A) ∂((P x : Measure Ω).map prefixTuple) := by
            simp [μ]
  have hproductRect :
      (((μ.map prefixTuple) ⊗ₘ stepKernel).real (B ×ˢ A)) =
        ∫ z in B, ((stepKernel z).real A) ∂(μ.map prefixTuple) := by
    have hone :
        Integrable (fun _ : (Fin (m + 1) → NNReal) × NNReal ↦ (1 : ℝ))
          ((μ.map prefixTuple) ⊗ₘ stepKernel) := by
      simp
    calc
      (((μ.map prefixTuple) ⊗ₘ stepKernel).real (B ×ˢ A))
          = ∫ z in B ×ˢ A, (1 : ℝ) ∂((μ.map prefixTuple) ⊗ₘ stepKernel) := by
              symm
              exact MeasureTheory.setIntegral_one_eq_measureReal
      _ = ∫ z in B, ∫ y in A, (1 : ℝ) ∂(stepKernel z) ∂(μ.map prefixTuple) := by
            exact
              MeasureTheory.Measure.setIntegral_compProd hB hA hone.integrableOn
      _ = ∫ z in B, ((stepKernel z).real A) ∂(μ.map prefixTuple) := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
            simp
  have hreal :
      (μ.map (fun ω ↦ (prefixTuple ω, Y sLast ω))).real (B ×ˢ A) =
        (((μ.map prefixTuple) ⊗ₘ stepKernel).real (B ×ˢ A)) := by
    exact hrealizedRect.trans hproductRect.symm
  simpa [μ, prefixTuple, prefixTimes, sPrev, sLast, gap, stepKernel] using
    (MeasureTheory.measureReal_eq_measureReal_iff
      (μ := μ.map (fun ω ↦ (prefixTuple ω, Y sLast ω)))
      (ν := (μ.map prefixTuple) ⊗ₘ stepKernel)
      (s := B ×ˢ A) (t := B ×ˢ A)
      (measure_lt_top _ _).ne (measure_lt_top _ _).ne).mp hreal

/-- Helper for Theorem 21.50: the limiting ordered-joint Laplace functional collapses the last
coordinate into the predecessor coefficient via the branching-diffusion step kernel. -/
private theorem branchingDiffusionCollapseLastOrderedJointLaplace_eq
    {κ : NNReal → Kernel NNReal NNReal}
    {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
    (x : NNReal) [IsMarkovProcessRealization κ P Y]
    (hκ : HasBranchingDiffusionLaplaceTransform κ)
    {m : ℕ} (times : Fin (m + 2) → NNReal) (htimes : Monotone times)
    (a : Fin (m + 2) → NNReal) :
    let μ : Measure Ω := (P x : Measure Ω)
    let prefixTimes : Fin (m + 1) → NNReal := fun i ↦ times i.castSucc
    let prefixTuple : Ω → Fin (m + 1) → NNReal := fun ω i ↦ Y (prefixTimes i) ω
    let sPrev : NNReal := prefixTimes (Fin.last m)
    let sLast : NNReal := times (Fin.last (m + 1))
    let gap : NNReal := sLast - sPrev
    let prefixCoeff : Fin (m + 1) → NNReal := fun i ↦ a i.castSucc
    let updatedCoeff : Fin (m + 1) → NNReal :=
      Function.update prefixCoeff (Fin.last m)
        (prefixCoeff (Fin.last m) + a (Fin.last (m + 1)) / (a (Fin.last (m + 1)) * gap + 1))
    ∫ ω, Real.exp (-∑ i : Fin (m + 2), (a i : ℝ) * (Y (times i) ω : ℝ)) ∂μ =
      ∫ ω, Real.exp (-∑ i : Fin (m + 1), (updatedCoeff i : ℝ) * (Y (prefixTimes i) ω : ℝ)) ∂μ := by
  let μ : Measure Ω := (P x : Measure Ω)
  let prefixTimes : Fin (m + 1) → NNReal := fun i ↦ times i.castSucc
  let prefixTuple : Ω → Fin (m + 1) → NNReal := fun ω i ↦ Y (prefixTimes i) ω
  let sPrev : NNReal := prefixTimes (Fin.last m)
  let sLast : NNReal := times (Fin.last (m + 1))
  let gap : NNReal := sLast - sPrev
  let prefixCoeff : Fin (m + 1) → NNReal := fun i ↦ a i.castSucc
  let lastCoeff : NNReal := a (Fin.last (m + 1))
  let extraCoeff : NNReal := lastCoeff / (lastCoeff * gap + 1)
  let updatedCoeff : Fin (m + 1) → NNReal :=
    Function.update prefixCoeff (Fin.last m) (prefixCoeff (Fin.last m) + extraCoeff)
  let lastPrefix : (Fin (m + 1) → NNReal) → NNReal := fun z ↦ z (Fin.last m)
  let stepKernel : Kernel (Fin (m + 1) → NNReal) NNReal :=
    Kernel.comap (κ gap) lastPrefix (by fun_prop)
  let pairIntegrand : (Fin (m + 1) → NNReal) × NNReal → ℝ :=
    fun p ↦
      Real.exp (-∑ i : Fin (m + 1), (prefixCoeff i : ℝ) * (p.1 i : ℝ)) *
        Real.exp (-((lastCoeff : ℝ) * (p.2 : ℝ)))
  let updatedIntegrand : (Fin (m + 1) → NNReal) → ℝ :=
    fun z ↦ Real.exp (-∑ i : Fin (m + 1), (updatedCoeff i : ℝ) * (z i : ℝ))
  have hsPrevLast : sPrev ≤ sLast := by
    -- Proof comment: the predecessor time is one of the earlier coordinates of the ordered tuple.
    simpa [prefixTimes, sPrev, sLast] using
      htimes (Fin.le_last (Fin.castSucc (Fin.last m)))
  have hpairLaw :
      (μ.map (fun ω ↦ (prefixTuple ω, Y sLast ω))) =
        ((μ.map prefixTuple) ⊗ₘ stepKernel) := by
    -- Proof comment: the previous theorem packages the prefix/last split law as a `compProd`.
    simpa [μ, prefixTuple, prefixTimes, sPrev, sLast, gap, stepKernel] using
      (branchingDiffusionPrefixLastLaw_eq_compProd
        (κ := κ) (P := P) (Y := Y) x times htimes)
  have hprefixTupleMeas : Measurable prefixTuple := by
    -- Proof comment: every sampled prefix coordinate is a measurable process time slice.
    simpa [prefixTuple] using
      (measurable_historyTuple (X := Y) (times := prefixTimes)
        (hX := IsMarkovProcessRealization.measurable_process (κ := κ) (P := P) (Y := Y)))
  have hpairMeas : Measurable (fun ω ↦ (prefixTuple ω, Y sLast ω)) := by
    -- Proof comment: the split map is measurable coordinatewise.
    exact hprefixTupleMeas.prodMk <|
      IsMarkovProcessRealization.measurable_process (κ := κ) (P := P) (Y := Y) sLast
  letI : IsMarkovKernel stepKernel := by
    -- Proof comment: the comapped last-step kernel reads the realized one-time marginal from the
    -- last prefix state.
    refine ⟨fun z ↦ ?_⟩
    rw [show stepKernel z = (κ gap) (lastPrefix z) by rfl]
    rw [← IsMarkovProcessRealization.transition_eq
      (κ := κ) (P := P) (Y := Y) (lastPrefix z) gap]
    exact
      Measure.isProbabilityMeasure_map
        (μ := (P (lastPrefix z) : Measure Ω)) (f := Y gap)
        (IsMarkovProcessRealization.measurable_process
          (κ := κ) (P := P) (Y := Y) gap).aemeasurable
  have hpairInt :
      Integrable pairIntegrand ((μ.map prefixTuple) ⊗ₘ stepKernel) := by
    -- Proof comment: the split Laplace integrand takes values in `[0, 1]`.
    have hpairMeasurable : Measurable pairIntegrand := by
      -- Proof comment: both exponential factors are measurable on the product space.
      fun_prop
    refine Integrable.mono' (integrable_const (1 : ℝ))
      hpairMeasurable.aestronglyMeasurable ?_
    filter_upwards with p
    have hprefix_nonneg :
        0 ≤ Real.exp (-∑ i : Fin (m + 1), (prefixCoeff i : ℝ) * (p.1 i : ℝ)) := by
      positivity
    have hlast_nonneg :
        0 ≤ Real.exp (-((lastCoeff : ℝ) * (p.2 : ℝ))) := by
      positivity
    have hprefix_sum_nonneg :
        0 ≤ ∑ i : Fin (m + 1), (prefixCoeff i : ℝ) * (p.1 i : ℝ) := by
      refine Finset.sum_nonneg fun i _ ↦ ?_
      exact mul_nonneg (by exact_mod_cast (prefixCoeff i).2) (by exact_mod_cast (p.1 i).2)
    have hprefix_le :
        Real.exp (-∑ i : Fin (m + 1), (prefixCoeff i : ℝ) * (p.1 i : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have hlast_le :
        Real.exp (-((lastCoeff : ℝ) * (p.2 : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [lastCoeff.2, p.2.2]
    have hmul_le : pairIntegrand p ≤ 1 := by
      dsimp [pairIntegrand]
      nlinarith
    simpa [pairIntegrand, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hprefix_nonneg hlast_nonneg)] using hmul_le
  have hpairIntMap :
      Integrable pairIntegrand (μ.map (fun ω ↦ (prefixTuple ω, Y sLast ω))) := by
    simpa [hpairLaw] using hpairInt
  have hupdatedInt :
      Integrable updatedIntegrand (μ.map prefixTuple) := by
    -- Proof comment: the collapsed prefix Laplace integrand also takes values in `[0, 1]`.
    have hupdatedMeasurable : Measurable updatedIntegrand := by
      fun_prop
    refine Integrable.mono' (integrable_const (1 : ℝ))
      hupdatedMeasurable.aestronglyMeasurable ?_
    filter_upwards with z
    have hsum_nonneg :
        0 ≤ ∑ i : Fin (m + 1), (updatedCoeff i : ℝ) * (z i : ℝ) := by
      refine Finset.sum_nonneg fun i _ ↦ ?_
      exact mul_nonneg (by exact_mod_cast (updatedCoeff i).2) (by exact_mod_cast (z i).2)
    have hle : updatedIntegrand z ≤ 1 := by
      simp [updatedIntegrand, Real.exp_le_one_iff]
      linarith
    have hnonneg : 0 ≤ updatedIntegrand z := by
      dsimp [updatedIntegrand]
      positivity
    simpa [updatedIntegrand, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hsplit :
      ∀ ω,
        Real.exp (-∑ i : Fin (m + 2), (a i : ℝ) * (Y (times i) ω : ℝ)) =
          pairIntegrand (prefixTuple ω, Y sLast ω) := by
    intro ω
    rw [sum_univ_castSucc_mul_nnreal (a := a) (z := fun i ↦ Y (times i) ω)]
    rw [show
      -((∑ i : Fin (m + 1), (a i.castSucc : ℝ) * (Y (times i.castSucc) ω : ℝ)) +
          (a (Fin.last (m + 1)) : ℝ) * (Y (times (Fin.last (m + 1))) ω : ℝ)) =
        (-∑ i : Fin (m + 1), (a i.castSucc : ℝ) * (Y (times i.castSucc) ω : ℝ)) +
          (-((a (Fin.last (m + 1)) : ℝ) * (Y (times (Fin.last (m + 1))) ω : ℝ))) by ring]
    simp [pairIntegrand, prefixTuple, prefixTimes, sLast, prefixCoeff, lastCoeff, Real.exp_add]
  have hinner :
      ∀ z : Fin (m + 1) → NNReal,
        ∫ y, pairIntegrand (z, y) ∂stepKernel z = updatedIntegrand z := by
    intro z
    have hsum_update :
        (∑ i : Fin (m + 1), (updatedCoeff i : ℝ) * (z i : ℝ)) =
          (∑ i : Fin (m + 1), (prefixCoeff i : ℝ) * (z i : ℝ)) +
            (extraCoeff : ℝ) * (z (Fin.last m) : ℝ) := by
      simpa [updatedCoeff, prefixCoeff, extraCoeff] using
        (sum_update_last_mul_nnreal (a := prefixCoeff) (z := z) (c := extraCoeff))
    have hinner_laplace :
        ∫ y, Real.exp (-((lastCoeff : ℝ) * (y : ℝ))) ∂stepKernel z =
          branchingDiffusionLaplaceTransform gap (lastPrefix z) lastCoeff := by
      rw [show stepKernel z = (κ gap) (lastPrefix z) by rfl]
      rw [ProbabilityTheory.branchingDiffusionLaplaceTransform_apply]
      simpa [neg_div, mul_comm, mul_left_comm, mul_assoc] using hκ (lastPrefix z) gap lastCoeff
    have hcollapse :
        Real.exp (-∑ i : Fin (m + 1), (prefixCoeff i : ℝ) * (z i : ℝ)) *
            branchingDiffusionLaplaceTransform gap (lastPrefix z) lastCoeff =
          updatedIntegrand z := by
      have hextra :
          (extraCoeff : ℝ) * (z (Fin.last m) : ℝ) =
            ((lastCoeff : ℝ) * (lastPrefix z : ℝ)) / (((lastCoeff : ℝ) * (gap : ℝ)) + 1) := by
        have hnn :
            extraCoeff * z (Fin.last m) =
              (lastCoeff * lastPrefix z) / (lastCoeff * gap + 1) := by
          dsimp [extraCoeff, lastPrefix]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
        exact_mod_cast hnn
      calc
        Real.exp (-∑ i : Fin (m + 1), (prefixCoeff i : ℝ) * (z i : ℝ)) *
            branchingDiffusionLaplaceTransform gap (lastPrefix z) lastCoeff
            = Real.exp (-∑ i : Fin (m + 1), (prefixCoeff i : ℝ) * (z i : ℝ)) *
                Real.exp (-((extraCoeff : ℝ) * (z (Fin.last m) : ℝ))) := by
                  simpa [branchingDiffusionLaplaceTransform_apply, lastPrefix, hextra, mul_comm]
        _ = Real.exp
              ((-∑ i : Fin (m + 1), (prefixCoeff i : ℝ) * (z i : ℝ)) +
                (-((extraCoeff : ℝ) * (z (Fin.last m) : ℝ)))) := by
                  rw [← Real.exp_add]
        _ = updatedIntegrand z := by
              unfold updatedIntegrand
              congr 1
              rw [hsum_update]
              ring
    calc
      ∫ y, pairIntegrand (z, y) ∂stepKernel z
          = Real.exp (-∑ i : Fin (m + 1), (prefixCoeff i : ℝ) * (z i : ℝ)) *
              ∫ y, Real.exp (-((lastCoeff : ℝ) * (y : ℝ))) ∂stepKernel z := by
                change
                  ∫ y,
                      Real.exp (-∑ i : Fin (m + 1), (prefixCoeff i : ℝ) * (z i : ℝ)) *
                        Real.exp (-((lastCoeff : ℝ) * (y : ℝ))) ∂stepKernel z =
                    Real.exp (-∑ i : Fin (m + 1), (prefixCoeff i : ℝ) * (z i : ℝ)) *
                      ∫ y, Real.exp (-((lastCoeff : ℝ) * (y : ℝ))) ∂stepKernel z
                rw [MeasureTheory.integral_const_mul]
      _ = Real.exp (-∑ i : Fin (m + 1), (prefixCoeff i : ℝ) * (z i : ℝ)) *
            branchingDiffusionLaplaceTransform gap (lastPrefix z) lastCoeff := by
              rw [hinner_laplace]
      _ = updatedIntegrand z := hcollapse
  calc
    ∫ ω, Real.exp (-∑ i : Fin (m + 2), (a i : ℝ) * (Y (times i) ω : ℝ)) ∂μ
        = ∫ p, pairIntegrand p ∂(μ.map (fun ω ↦ (prefixTuple ω, Y sLast ω))) := by
            symm
            rw [MeasureTheory.integral_map hpairMeas.aemeasurable hpairIntMap.aestronglyMeasurable]
            refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ (hsplit ω).symm
    _ = ∫ p, pairIntegrand p ∂((μ.map prefixTuple) ⊗ₘ stepKernel) := by
          rw [hpairLaw]
    _ = ∫ z, ∫ y, pairIntegrand (z, y) ∂stepKernel z ∂(μ.map prefixTuple) := by
          exact ProbabilityTheory.integral_compProd hpairInt
    _ = ∫ z, updatedIntegrand z ∂(μ.map prefixTuple) := by
          refine integral_congr_ae <| Filter.Eventually.of_forall hinner
    _ = ∫ ω, updatedIntegrand (prefixTuple ω) ∂μ := by
          rw [MeasureTheory.integral_map hprefixTupleMeas.aemeasurable hupdatedInt.aestronglyMeasurable]
    _ = ∫ ω, Real.exp (-∑ i : Fin (m + 1), (updatedCoeff i : ℝ) * (Y (prefixTimes i) ω : ℝ)) ∂μ := by
          refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
          simp [updatedIntegrand, prefixTuple]

/-- Helper for Theorem 21.50: the ordered-joint Laplace functionals converge for every strictly
ordered finite tuple of times. -/
private theorem rescaledBranchingProcessOrderedJointLaplaceTendsto
    {κ : NNReal → Kernel NNReal NNReal}
    (x : NNReal)
    (PZ : (n : ℕ) → ProbabilityMeasure (Ωn n))
    (Z : (n : ℕ) → ℕ → Ωn n → ℕ)
    (hZ_meas : ∀ n k : ℕ, Measurable (Z n k))
    (P : NNReal → ProbabilityMeasure Ω)
    (Y : NNReal → Ω → NNReal)
    [IsMarkovProcessRealization κ P Y]
    (hLaplace :
      ∀ t l : NNReal,
        Tendsto
          (fun n ↦
            ∫ ω, Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n t ω : ℝ))) ∂
              (PZ n : Measure (Ωn n)))
          atTop
          (𝓝 (branchingDiffusionLaplaceTransform t x l)))
    (hCond :
      ∀ n : ℕ, ∀ s t l : NNReal,
        (PZ n : Measure (Ωn n))[fun ω ↦
          Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n (s + t) ω : ℝ))) |
            generatedFiltrationSpace (rescaledGaltonWatsonProcess (Z n) n) s] =ᵐ[
            (PZ n : Measure (Ωn n))]
          fun ω ↦
            branchingDiffusionLaplaceTransform t (rescaledGaltonWatsonProcess (Z n) n s ω) l)
    (hκ : HasBranchingDiffusionLaplaceTransform κ)
    {m : ℕ} (times : Fin (m + 1) → NNReal) (htimes : StrictMono times)
    (a : Fin (m + 1) → NNReal) :
    Tendsto
      (fun n ↦
        ∫ ω, Real.exp (-∑ i : Fin (m + 1),
          (a i : ℝ) * (rescaledGaltonWatsonProcess (Z n) n (times i) ω : ℝ)) ∂
          (PZ n : Measure (Ωn n)))
      atTop
      (𝓝
        (∫ ω, Real.exp (-∑ i : Fin (m + 1), (a i : ℝ) * (Y (times i) ω : ℝ)) ∂
          (P x : Measure Ω))) := by
  revert times htimes a
  induction m with
  | zero =>
      intro times _ a
      have hlimit :
          ∫ ω, Real.exp (-∑ i : Fin 1, (a i : ℝ) * (Y (times i) ω : ℝ)) ∂
              (P x : Measure Ω) =
            branchingDiffusionLaplaceTransform (times 0) x (a 0) := by
        -- Proof comment: for a one-point tuple, the limiting joint Laplace transform is exactly
        -- the one-time branching-diffusion Laplace transform.
        simpa [Fin.sum_univ_one] using
          (IsMarkovProcessRealization.branchingDiffusionLaplaceTransform
            (κ := κ) (P := P) (Y := Y) (hY := inferInstance) hκ x (times 0) (a 0))
      -- Proof comment: after reducing the one-point tuple to the one-time Laplace transform, the
      -- statement is exactly the standing hypothesis `hLaplace`.
      rw [hlimit]
      simpa [Fin.sum_univ_one] using hLaplace (times 0) (a 0)
  | succ m ih =>
      intro times htimes a
      let prefixTimes : Fin (m + 1) → NNReal := fun i ↦ times i.castSucc
      let gap : NNReal := times (Fin.last (m + 1)) - prefixTimes (Fin.last m)
      let updatedCoeff : Fin (m + 1) → NNReal :=
        Function.update (fun i ↦ a i.castSucc) (Fin.last m)
          (a (Fin.castSucc (Fin.last m)) + a (Fin.last (m + 1)) / (a (Fin.last (m + 1)) * gap + 1))
      have hprefixTimes : StrictMono prefixTimes := by
        -- Proof comment: the prefix tuple inherits strict ordering from the full tuple.
        intro i j hij
        exact htimes (by simpa [prefixTimes] using hij)
      have hdiscreteCollapse :
          (fun n ↦
            ∫ ω, Real.exp (-∑ i : Fin (m + 2),
              (a i : ℝ) * (rescaledGaltonWatsonProcess (Z n) n (times i) ω : ℝ)) ∂
              (PZ n : Measure (Ωn n))) =
            fun n ↦
              ∫ ω, Real.exp (-∑ i : Fin (m + 1),
                (updatedCoeff i : ℝ) *
                  (rescaledGaltonWatsonProcess (Z n) n (prefixTimes i) ω : ℝ)) ∂
                (PZ n : Measure (Ωn n)) := by
        -- Proof comment: the discrete last coordinate collapses into the predecessor coefficient
        -- by conditioning on the predecessor filtration.
        funext n
        simpa [prefixTimes, gap, updatedCoeff] using
          (rescaledBranchingProcessCollapseLastOrderedJointLaplace_eq
            (PZ := PZ) (Z := Z) (hZ_meas := hZ_meas) (hCond := hCond)
            (times := times) htimes.monotone (a := a) n)
      have hlimitCollapse :
          (∫ ω, Real.exp (-∑ i : Fin (m + 2), (a i : ℝ) * (Y (times i) ω : ℝ)) ∂
              (P x : Measure Ω)) =
            ∫ ω, Real.exp (-∑ i : Fin (m + 1), (updatedCoeff i : ℝ) * (Y (prefixTimes i) ω : ℝ)) ∂
              (P x : Measure Ω) := by
        -- Proof comment: the limiting branching diffusion satisfies the same one-step collapse
        -- after splitting off the last coordinate through the step kernel.
        simpa [prefixTimes, gap, updatedCoeff] using
          (branchingDiffusionCollapseLastOrderedJointLaplace_eq
            (κ := κ) (P := P) (Y := Y) (x := x) (hκ := hκ)
            (times := times) htimes.monotone (a := a))
      -- Proof comment: once both sides are rewritten to the collapsed prefix tuple, the induction
      -- hypothesis closes the convergence statement for the shorter ordered tuple.
      rw [hdiscreteCollapse, hlimitCollapse]
      exact ih prefixTimes hprefixTimes updatedCoeff

/-- Helper for Theorem 21.50: the ordered-joint Laplace integrand on tuple space is the bounded
continuous kernel used to test subsequential weak limits. -/
private def orderedJointLaplaceKernel {m : ℕ} (a : Fin m → NNReal) :
    (Fin m → NNReal) → ℝ :=
  fun z ↦ Real.exp (-∑ i, (a i : ℝ) * (z i : ℝ))

/-- Helper for Theorem 21.50: the tuple-space Laplace kernel is continuous because it is the
exponential of a finite weighted coordinate sum. -/
private lemma continuous_orderedJointLaplaceKernel {m : ℕ} (a : Fin m → NNReal) :
    Continuous (orderedJointLaplaceKernel a) := by
  -- Proof comment: finite coordinate sums are continuous on the finite product, and exponentials
  -- preserve continuity.
  simpa [orderedJointLaplaceKernel] using
    (show Continuous (fun z : Fin m → NNReal ↦ Real.exp (-∑ i, (a i : ℝ) * (z i : ℝ))) from by
      fun_prop)

/-- Helper for Theorem 21.50: every tuple-space Laplace kernel takes values in `[0, 1]`. -/
private lemma orderedJointLaplaceKernel_mem_Icc {m : ℕ} (a : Fin m → NNReal)
    (z : Fin m → NNReal) :
    orderedJointLaplaceKernel a z ∈ Set.Icc (0 : ℝ) 1 := by
  -- Proof comment: the exponent is the negative of a nonnegative weighted sum, so the resulting
  -- exponential is positive and at most `1`.
  refine ⟨Real.exp_pos _ |>.le, ?_⟩
  rw [orderedJointLaplaceKernel, Real.exp_le_one_iff]
  refine neg_nonpos.mpr <| Finset.sum_nonneg fun i _ ↦ ?_
  exact mul_nonneg (by exact_mod_cast (a i).2) (by exact_mod_cast (z i).2)

/-- Helper for Theorem 21.50: the tuple-space Laplace kernels are uniformly bounded, so they
define bounded continuous test functions. -/
private lemma orderedJointLaplaceKernel_dist_le_one {m : ℕ} (a : Fin m → NNReal) :
    ∀ z w : Fin m → NNReal,
      dist (orderedJointLaplaceKernel a z) (orderedJointLaplaceKernel a w) ≤ 1 := by
  intro z w
  have hz := orderedJointLaplaceKernel_mem_Icc a z
  have hw := orderedJointLaplaceKernel_mem_Icc a w
  exact Real.dist_le_of_mem_Icc_01 hz hw

/-- Helper for Theorem 21.50: package the tuple-space Laplace kernel as a bounded continuous
function for the weak-convergence test-function API. -/
private def orderedJointLaplaceKernelBCF {m : ℕ} (a : Fin m → NNReal) :
    BoundedContinuousFunction (Fin m → NNReal) ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨orderedJointLaplaceKernel a, continuous_orderedJointLaplaceKernel a⟩
    1
    (orderedJointLaplaceKernel_dist_le_one a)

/-- Helper for Theorem 21.50: the ordered tuple laws are tight because the finitely many
coordinate tails are controlled by one-time Laplace bounds, and only finitely many initial laws
need separate compact witnesses. -/
private theorem orderedTupleLawEventually_boxEscape_le
    (x : NNReal)
    (PZ : (n : ℕ) → ProbabilityMeasure (Ωn n))
    (Z : (n : ℕ) → ℕ → Ωn n → ℕ)
    (hZ_meas : ∀ n k : ℕ, Measurable (Z n k))
    (hLaplace :
      ∀ t l : NNReal,
        Tendsto
          (fun n ↦
            ∫ ω, Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n t ω : ℝ))) ∂
              (PZ n : Measure (Ωn n)))
          atTop
          (𝓝 (branchingDiffusionLaplaceTransform t x l)))
    (J : Finset NNReal) :
    let orderedTimes : Fin J.card → NNReal := fun i ↦ J.orderEmbOfFin rfl i
    let νn : ℕ → ProbabilityMeasure (Fin J.card → NNReal) := fun n ↦
      ProbabilityMeasure.map
        (PZ n)
        ((measurable_pi_lambda _ fun i : Fin J.card ↦
            measurable_rescaledGaltonWatsonProcess Z hZ_meas n (orderedTimes i)).aemeasurable)
    ∀ ε : NNReal, 0 < ε →
      ∃ R : NNReal, 0 < R ∧ ∃ N : ℕ, ∀ n ≥ N,
        ((νn n : Measure (Fin J.card → NNReal)).real
          ((Set.pi Set.univ (fun _ : Fin J.card ↦ Set.Icc (0 : NNReal) R))ᶜ)) ≤ ε := by
  classical
  intro orderedTimes νn ε hε
  let c : ℝ := 1 - Real.exp (-1)
  have hc : 0 < c := by
    have hexp_lt : Real.exp (-1 : ℝ) < 1 := by
      simpa using (Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0))
    dsimp [c]
    linarith
  let δ : ℝ := (ε : ℝ) * c / (4 * (J.card + 1 : ℝ))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let l : NNReal := ⟨min 1 (δ / ((x : ℝ) + 1)), by positivity⟩
  have hl : 0 < l := by
    show 0 < min 1 (δ / ((x : ℝ) + 1))
    refine lt_min (by norm_num) ?_
    positivity
  let R : NNReal := 1 / l
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hmulR_real : (l : ℝ) * (R : ℝ) = 1 := by
    have hmul : l * R = 1 := by
      simp [R, hl.ne']
    exact_mod_cast hmul
  have hl_mul_bound : (x : ℝ) * (l : ℝ) ≤ δ := by
    have hl_le : (l : ℝ) ≤ δ / ((x : ℝ) + 1) := by
      simp [l]
    have hx_nonneg : 0 ≤ (x : ℝ) := by exact_mod_cast x.2
    have hden_pos : 0 < (x : ℝ) + 1 := by positivity
    have hmul_le :
        (x : ℝ) * (l : ℝ) ≤ (x : ℝ) * (δ / ((x : ℝ) + 1)) := by
      exact mul_le_mul_of_nonneg_left hl_le hx_nonneg
    have hfrac_le : (x : ℝ) * (δ / ((x : ℝ) + 1)) ≤ δ := by
      have hx_le_den : (x : ℝ) ≤ (x : ℝ) + 1 := by
        nlinarith
      have hdiv_le : (x : ℝ) / ((x : ℝ) + 1) ≤ 1 := by
        exact (div_le_one hden_pos).2 hx_le_den
      calc
        (x : ℝ) * (δ / ((x : ℝ) + 1))
            = δ * ((x : ℝ) / ((x : ℝ) + 1)) := by
                field_simp [hden_pos.ne']
        _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hdiv_le hδ.le
        _ = δ := by ring
    exact hmul_le.trans hfrac_le
  have hcoordEventual :
      ∀ i : Fin J.card, ∃ Nᵢ : ℕ, ∀ n ≥ Nᵢ,
        ((νn n : Measure (Fin J.card → NNReal)).real {z | R < z i}) ≤
          (ε : ℝ) / (2 * (J.card + 1 : ℝ)) := by
    intro i
    let tailSet : Set (Fin J.card → NNReal) := {z | R < z i}
    have htailSetMeas : MeasurableSet tailSet := by
      dsimp [tailSet]
      simpa [Set.Ioi] using (continuous_apply i).measurable measurableSet_Ioi
    have hlimit_small :
        1 - branchingDiffusionLaplaceTransform (orderedTimes i) x l ≤ δ := by
      have hfrac_le :
          ((x : ℝ) * (l : ℝ)) / (((l : ℝ) * (orderedTimes i : ℝ)) + 1) ≤
            (x : ℝ) * (l : ℝ) := by
        have hnum_nonneg : 0 ≤ (x : ℝ) * (l : ℝ) := by positivity
        have hden_pos : 0 < ((l : ℝ) * (orderedTimes i : ℝ)) + 1 := by positivity
        have hden_ge_one : 1 ≤ ((l : ℝ) * (orderedTimes i : ℝ)) + 1 := by
          nlinarith [l.2, (orderedTimes i).2]
        refine (div_le_iff₀ hden_pos).2 ?_
        nlinarith
      have hexp_le :
          Real.exp (-((x : ℝ) * (l : ℝ))) ≤
            branchingDiffusionLaplaceTransform (orderedTimes i) x l := by
        rw [ProbabilityTheory.branchingDiffusionLaplaceTransform_apply]
        refine Real.exp_le_exp.mpr ?_
        nlinarith [hfrac_le]
      have hnum_exp :
          1 - branchingDiffusionLaplaceTransform (orderedTimes i) x l ≤
            1 - Real.exp (-((x : ℝ) * (l : ℝ))) := by
        linarith
      have hnum_linear :
          1 - Real.exp (-((x : ℝ) * (l : ℝ))) ≤ (x : ℝ) * (l : ℝ) := by
        have hone : 1 - ((x : ℝ) * (l : ℝ)) ≤ Real.exp (-((x : ℝ) * (l : ℝ))) :=
          Real.one_sub_le_exp_neg ((x : ℝ) * (l : ℝ))
        linarith
      exact hnum_exp.trans (hnum_linear.trans hl_mul_bound)
    have hclose :
        ∀ᶠ n in atTop,
          dist
            (∫ ω, Real.exp (-((l : ℝ) *
                (rescaledGaltonWatsonProcess (Z n) n (orderedTimes i) ω : ℝ))) ∂
                (PZ n : Measure (Ωn n)))
            (branchingDiffusionLaplaceTransform (orderedTimes i) x l) < δ :=
      hLaplace (orderedTimes i) l (Metric.ball_mem_nhds _ hδ)
    rw [Filter.eventually_atTop] at hclose
    rcases hclose with ⟨Nᵢ, hNᵢ⟩
    refine ⟨Nᵢ, ?_⟩
    intro n hn
    let approx : ℝ :=
      ∫ ω, Real.exp (-((l : ℝ) *
        (rescaledGaltonWatsonProcess (Z n) n (orderedTimes i) ω : ℝ))) ∂
          (PZ n : Measure (Ωn n))
    let limit : ℝ := branchingDiffusionLaplaceTransform (orderedTimes i) x l
    have hdist_lt := hNᵢ n hn
    have hnum_le :
        1 - approx ≤
          2 * δ := by
      have hdist_abs :
          |approx - limit| < δ := by
        rwa [Real.dist_eq] at hdist_lt
      have hdist_upper : limit - approx < δ := by
        linarith [(abs_lt.mp hdist_abs).1]
      nlinarith [hlimit_small, hdist_upper]
    have htail_real :
        ((νn n : Measure (Fin J.card → NNReal)).real tailSet) ≤
          (1 -
              approx) / c := by
      calc
        ((νn n : Measure (Fin J.card → NNReal)).real tailSet)
            = ((PZ n : Measure (Ωn n)).real
                {ω | R < rescaledGaltonWatsonProcess (Z n) n (orderedTimes i) ω}) := by
                  calc
                    ((νn n : Measure (Fin J.card → NNReal)).real tailSet) = (νn n) tailSet := by
                      simpa [tailSet] using
                        (ProbabilityMeasure.measureReal_eq_coe_coeFn (ν := νn n) tailSet)
                    _ = (PZ n)
                        {ω | R < rescaledGaltonWatsonProcess (Z n) n (orderedTimes i) ω} := by
                          simpa [νn, orderedTimes, tailSet, Set.preimage] using
                            (ProbabilityMeasure.map_apply_of_aemeasurable
                              (ν := PZ n)
                              ((measurable_pi_lambda _ fun j : Fin J.card ↦
                                  measurable_rescaledGaltonWatsonProcess Z hZ_meas n
                                    (orderedTimes j)).aemeasurable)
                              (A := tailSet) htailSetMeas)
                    _ = ((PZ n : Measure (Ωn n)).real
                        {ω | R < rescaledGaltonWatsonProcess (Z n) n (orderedTimes i) ω}) := by
                          symm
                          simpa [tailSet] using
                            (ProbabilityMeasure.measureReal_eq_coe_coeFn
                              (ν := PZ n)
                              {ω | R < rescaledGaltonWatsonProcess (Z n) n (orderedTimes i) ω})
        _ ≤
            (1 -
                approx) /
              (1 - Real.exp (-((l : ℝ) * (R : ℝ)))) := by
              exact
                measureReal_gt_le_laplaceGap
                  (μ := (PZ n : Measure (Ωn n)))
                  (X := rescaledGaltonWatsonProcess (Z n) n (orderedTimes i))
                  (measurable_rescaledGaltonWatsonProcess Z hZ_meas n (orderedTimes i))
                  hl hR
        _ = (1 - approx) / c := by
              simp [approx, c, hmulR_real]
    refine htail_real.trans ?_
    have hdiv_le :
        (1 - approx) / c ≤
          (2 * δ) / c := by
      exact div_le_div_of_nonneg_right hnum_le hc.le
    have hdelta_eval : (2 * δ) / c = (ε : ℝ) / (2 * (J.card + 1 : ℝ)) := by
      dsimp [δ]
      field_simp [hc.ne']
      ring
    simpa [hdelta_eval] using hdiv_le
  choose Ncoord hNcoord using hcoordEventual
  let N : ℕ := Finset.univ.sup Ncoord
  let K : Set (Fin J.card → NNReal) := Set.pi Set.univ (fun _ : Fin J.card ↦ Set.Icc (0 : NNReal) R)
  have hKcompl :
      Kᶜ = ⋃ i : Fin J.card, {z : Fin J.card → NNReal | R < z i} := by
    ext z
    constructor
    · intro hz
      have hz_not : ¬ z ≤ fun _ : Fin J.card ↦ R := by
        intro hzle
        exact hz <| by
          simp [K, Pi.le_def, hzle]
      simpa [Pi.le_def, not_forall] using hz_not
    · intro hzUnion hz
      rcases Set.mem_iUnion.mp hzUnion with ⟨i, hi⟩
      have hz' : z ≤ fun _ : Fin J.card ↦ R := by
        simpa [K, Pi.le_def] using hz
      exact not_lt_of_ge (hz' i) hi
  refine ⟨R, hR, N, ?_⟩
  intro n hn
  have hbox_le :
      ((νn n : Measure (Fin J.card → NNReal)).real Kᶜ) ≤
        ∑ i : Fin J.card, ((νn n : Measure (Fin J.card → NNReal)).real {z | R < z i}) := by
    rw [hKcompl]
    simpa using
      (MeasureTheory.measureReal_iUnion_fintype_le
        (μ := (νn n : Measure (Fin J.card → NNReal)))
        (f := fun i : Fin J.card ↦ {z : Fin J.card → NNReal | R < z i}))
  have hsum_le :
      ∑ i : Fin J.card, ((νn n : Measure (Fin J.card → NNReal)).real {z | R < z i}) ≤ ε := by
    calc
      ∑ i : Fin J.card, ((νn n : Measure (Fin J.card → NNReal)).real {z | R < z i})
          ≤ ∑ i : Fin J.card, (ε : ℝ) / (2 * (J.card + 1 : ℝ)) := by
              refine Finset.sum_le_sum fun i _ ↦ ?_
              exact hNcoord i n (le_trans (Finset.le_sup (Finset.mem_univ i)) hn)
      _ = (J.card : ℝ) * ((ε : ℝ) / (2 * (J.card + 1 : ℝ))) := by
            simp [mul_comm, mul_left_comm, mul_assoc]
      _ ≤ ε := by
            have hε_nonneg : 0 ≤ (ε : ℝ) := by exact_mod_cast ε.2
            have hden_pos : 0 < (2 * (J.card + 1 : ℝ)) := by positivity
            have hratio_le : (J.card : ℝ) / (2 * (J.card + 1 : ℝ)) ≤ 1 := by
              refine (div_le_iff₀ hden_pos).2 ?_
              nlinarith
            have hfactor :
                (J.card : ℝ) * ((ε : ℝ) / (2 * (J.card + 1 : ℝ))) =
                  (ε : ℝ) * ((J.card : ℝ) / (2 * (J.card + 1 : ℝ))) := by
              ring
            rw [hfactor]
            have hmul_le :
                (ε : ℝ) * ((J.card : ℝ) / (2 * (J.card + 1 : ℝ))) ≤
                  (ε : ℝ) * 1 := by
              exact mul_le_mul_of_nonneg_left hratio_le hε_nonneg
            nlinarith
  exact hbox_le.trans hsum_le

/-- Helper for Theorem 21.50: the ordered tuple laws are tight because the finitely many
coordinate tails are controlled by one-time Laplace bounds, and only finitely many initial laws
need separate compact witnesses. -/
private theorem orderedTupleLawTight
    (x : NNReal)
    (PZ : (n : ℕ) → ProbabilityMeasure (Ωn n))
    (Z : (n : ℕ) → ℕ → Ωn n → ℕ)
    (hZ_meas : ∀ n k : ℕ, Measurable (Z n k))
    (hLaplace :
      ∀ t l : NNReal,
        Tendsto
          (fun n ↦
            ∫ ω, Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n t ω : ℝ))) ∂
              (PZ n : Measure (Ωn n)))
          atTop
          (𝓝 (branchingDiffusionLaplaceTransform t x l)))
    (J : Finset NNReal) :
    let orderedTimes : Fin J.card → NNReal := fun i ↦ J.orderEmbOfFin rfl i
    let νn : ℕ → ProbabilityMeasure (Fin J.card → NNReal) := fun n ↦
      ProbabilityMeasure.map
        (PZ n)
        ((measurable_pi_lambda _ fun i : Fin J.card ↦
            measurable_rescaledGaltonWatsonProcess Z hZ_meas n (orderedTimes i)).aemeasurable)
    IsTightMeasureSet (Set.range fun n ↦ (νn n : Measure (Fin J.card → NNReal))) := by
  classical
  intro orderedTimes νn
  -- Proof comment: use one common compact box for the tail family `n ≥ N`, then adjoin the
  -- finitely many singleton compact witnesses for the initial segment `n < N`.
  rw [MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hεTop : ε = ⊤
  · refine ⟨∅, isCompact_empty, ?_⟩
    intro μ hμ
    simp [hεTop]
  lift ε to NNReal using hεTop with ε'
  have hε' : 0 < ε' := by
    exact_mod_cast hε
  obtain ⟨R, hR, N, hN⟩ :=
    orderedTupleLawEventually_boxEscape_le x PZ Z hZ_meas hLaplace J ε' hε'
  let Ktail : Set (Fin J.card → NNReal) :=
    Set.pi Set.univ (fun _ : Fin J.card ↦ Set.Icc (0 : NNReal) R)
  have hsingle :
      ∀ n : Fin N,
        ∃ Kinit : Set (Fin J.card → NNReal),
          IsCompact Kinit ∧
            ∀ μ ∈ ({((νn n : ProbabilityMeasure (Fin J.card → NNReal)) :
                Measure (Fin J.card → NNReal))} : Set (Measure (Fin J.card → NNReal))),
              μ Kinitᶜ ≤ ε' := by
    intro n
    exact
      (MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
          (MeasureTheory.isTightMeasureSet_singleton
            (μ := ((νn n : ProbabilityMeasure (Fin J.card → NNReal)) :
              Measure (Fin J.card → NNReal)))))
        (ε' : ENNReal) (by exact_mod_cast hε')
  choose Kinit hKinitCompact hKinitBound using hsingle
  let K : Set (Fin J.card → NNReal) := Ktail ∪ ⋃ n : Fin N, Kinit n
  refine ⟨K, ?_, ?_⟩
  · exact (isCompact_orderedTupleBox _ R).union (isCompact_iUnion fun n ↦ hKinitCompact n)
  · intro μ hμ
    rcases hμ with ⟨n, rfl⟩
    by_cases hn : n < N
    · let nFin : Fin N := ⟨n, hn⟩
      have hsubset : Kᶜ ⊆ (Kinit nFin)ᶜ := by
        intro z hz
        simp [K, Ktail, nFin] at hz ⊢
        exact hz.2 nFin
      exact
        (measure_mono hsubset).trans
          (hKinitBound nFin _ (by simp [nFin]))
    · have hsubset : Kᶜ ⊆ Ktailᶜ := by
        intro z hz
        simp [K, Ktail] at hz ⊢
        exact hz.1
      have htail_real : ((νn n : Measure (Fin J.card → NNReal)).real Ktailᶜ) ≤ ε' :=
        hN n (Nat.le_of_not_gt hn)
      have htail_meas : ((νn n : Measure (Fin J.card → NNReal)) Ktailᶜ) ≤ ε' := by
        have htail_prob : (νn n) Ktailᶜ ≤ ε' := by
          simpa [ProbabilityMeasure.measureReal_eq_coe_coeFn] using htail_real
        rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure (ν := νn n) Ktailᶜ]
        exact ENNReal.coe_le_coe.mpr htail_prob
      have hmono :
          ((fun n ↦ (νn n : Measure (Fin J.card → NNReal))) n) Kᶜ ≤
            ((νn n : Measure (Fin J.card → NNReal)) Ktailᶜ) := by
        exact measure_mono hsubset
      exact hmono.trans htail_meas

/-- Helper for Theorem 21.50: every cluster point of the ordered tuple laws is forced by the
common ordered-joint Laplace limits, so it equals the branching-diffusion tuple law. -/
private theorem mapClusterPt_orderedJointLaplace_eq
    {κ : NNReal → Kernel NNReal NNReal}
    (x : NNReal)
    (PZ : (n : ℕ) → ProbabilityMeasure (Ωn n))
    (Z : (n : ℕ) → ℕ → Ωn n → ℕ)
    (hZ_meas : ∀ n k : ℕ, Measurable (Z n k))
    (P : NNReal → ProbabilityMeasure Ω)
    (Y : NNReal → Ω → NNReal)
    [IsMarkovProcessRealization κ P Y]
    (hLaplace :
      ∀ t l : NNReal,
        Tendsto
          (fun n ↦
            ∫ ω, Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n t ω : ℝ))) ∂
              (PZ n : Measure (Ωn n)))
          atTop
          (𝓝 (branchingDiffusionLaplaceTransform t x l)))
    (hCond :
      ∀ n : ℕ, ∀ s t l : NNReal,
        (PZ n : Measure (Ωn n))[fun ω ↦
          Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n (s + t) ω : ℝ))) |
            generatedFiltrationSpace (rescaledGaltonWatsonProcess (Z n) n) s] =ᵐ[
            (PZ n : Measure (Ωn n))]
          fun ω ↦
            branchingDiffusionLaplaceTransform t (rescaledGaltonWatsonProcess (Z n) n s ω) l)
    (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (J : Finset NNReal)
    {Q : ProbabilityMeasure (Fin J.card → NNReal)}
    (hQ : MapClusterPt Q atTop
      (fun n ↦
        ProbabilityMeasure.map
          (PZ n)
          ((measurable_pi_lambda _ fun i : Fin J.card ↦
              measurable_rescaledGaltonWatsonProcess Z hZ_meas n (J.orderEmbOfFin rfl i)).aemeasurable)))
    (a : Fin J.card → NNReal) :
    ∫ z, orderedJointLaplaceKernel a z ∂(Q : Measure (Fin J.card → NNReal)) =
      ∫ ω, Real.exp (-∑ i : Fin J.card, (a i : ℝ) * (Y (J.orderEmbOfFin rfl i) ω : ℝ)) ∂
        (P x : Measure Ω) := by
  classical
  let orderedTimes : Fin J.card → NNReal := fun i ↦ J.orderEmbOfFin rfl i
  let νn : ℕ → ProbabilityMeasure (Fin J.card → NNReal) := fun n ↦
    ProbabilityMeasure.map
      (PZ n)
      ((measurable_pi_lambda _ fun i : Fin J.card ↦
          measurable_rescaledGaltonWatsonProcess Z hZ_meas n (orderedTimes i)).aemeasurable)
  let νY : ProbabilityMeasure (Fin J.card → NNReal) := ProbabilityMeasure.map
    (P x)
    ((measurable_pi_lambda _ fun i : Fin J.card ↦
        IsMarkovProcessRealization.measurable_process
          (κ := κ) (P := P) (Y := Y) (orderedTimes i)).aemeasurable)
  by_cases hJ0 : J.card = 0
  · -- Proof comment: in the empty tuple case both Laplace kernels are the constant function `1`.
    letI : IsEmpty (Fin J.card) := by
      rw [hJ0]
      infer_instance
    simp [orderedJointLaplaceKernel]
  · obtain ⟨ψ, hψmono, hψtendsto⟩ :=
      TopologicalSpace.FirstCountableTopology.tendsto_subseq hQ
    have hQtest :
        Tendsto
          (fun k ↦
            ∫ z, orderedJointLaplaceKernel a z ∂((νn (ψ k) : ProbabilityMeasure _) : Measure _))
          atTop
          (𝓝 (∫ z, orderedJointLaplaceKernel a z ∂(Q : Measure (Fin J.card → NNReal)))) := by
      exact
        (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hψtendsto)
          (orderedJointLaplaceKernelBCF a)
    let m : ℕ := J.card - 1
    have hm : m + 1 = J.card := by
      dsimp [m]
      exact Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hJ0)
    let times : Fin (m + 1) → NNReal := fun i ↦ orderedTimes (Fin.cast hm i)
    let coeff : Fin (m + 1) → NNReal := fun i ↦ a (Fin.cast hm i)
    have htimes : StrictMono times := by
      intro i j hij
      exact (J.orderEmbOfFin rfl).strictMono (by simpa [times, hm] using hij)
    have hνn_eq :
        ∀ n : ℕ,
          ∫ z, orderedJointLaplaceKernel a z ∂((νn n : ProbabilityMeasure _) : Measure _) =
            ∫ ω, Real.exp (-∑ i : Fin (m + 1), (coeff i : ℝ) *
              (rescaledGaltonWatsonProcess (Z n) n (times i) ω : ℝ)) ∂
              (PZ n : Measure (Ωn n)) := by
      intro n
      calc
        ∫ z, orderedJointLaplaceKernel a z ∂((νn n : ProbabilityMeasure _) : Measure _) =
            ∫ ω, Real.exp (-∑ i : Fin J.card, (a i : ℝ) *
              (rescaledGaltonWatsonProcess (Z n) n (orderedTimes i) ω : ℝ)) ∂
                (PZ n : Measure (Ωn n)) := by
                  simpa [νn, orderedJointLaplaceKernel, orderedTimes] using
                    (MeasureTheory.integral_map
                      ((measurable_pi_lambda _ fun i : Fin J.card ↦
                          measurable_rescaledGaltonWatsonProcess Z hZ_meas n
                            (orderedTimes i)).aemeasurable)
                      (continuous_orderedJointLaplaceKernel a).measurable.aestronglyMeasurable)
        _ = ∫ ω, Real.exp (-∑ i : Fin (m + 1), (coeff i : ℝ) *
              (rescaledGaltonWatsonProcess (Z n) n (times i) ω : ℝ)) ∂
                (PZ n : Measure (Ωn n)) := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
              have hsum :=
                (Equiv.sum_comp (finCongr hm)
                  (fun i : Fin J.card ↦
                    (a i : ℝ) *
                      (rescaledGaltonWatsonProcess (Z n) n (orderedTimes i) ω : ℝ)))
              congr 1
              simpa [times, coeff] using hsum.symm
    have hνY_eq :
        ∫ z, orderedJointLaplaceKernel a z ∂((νY : ProbabilityMeasure _) : Measure _) =
          ∫ ω, Real.exp (-∑ i : Fin (m + 1), (coeff i : ℝ) * (Y (times i) ω : ℝ)) ∂
            (P x : Measure Ω) := by
      calc
        ∫ z, orderedJointLaplaceKernel a z ∂((νY : ProbabilityMeasure _) : Measure _) =
            ∫ ω, Real.exp (-∑ i : Fin J.card, (a i : ℝ) * (Y (orderedTimes i) ω : ℝ)) ∂
              (P x : Measure Ω) := by
                simpa [νY, orderedJointLaplaceKernel, orderedTimes] using
                  (MeasureTheory.integral_map
                    ((measurable_pi_lambda _ fun i : Fin J.card ↦
                        IsMarkovProcessRealization.measurable_process
                          (κ := κ) (P := P) (Y := Y) (orderedTimes i)).aemeasurable)
                    (continuous_orderedJointLaplaceKernel a).measurable.aestronglyMeasurable)
        _ = ∫ ω, Real.exp (-∑ i : Fin (m + 1), (coeff i : ℝ) * (Y (times i) ω : ℝ)) ∂
              (P x : Measure Ω) := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
              have hsum :=
                (Equiv.sum_comp (finCongr hm)
                  (fun i : Fin J.card ↦ (a i : ℝ) * (Y (orderedTimes i) ω : ℝ)))
              congr 1
              simpa [times, coeff] using hsum.symm
    have hJoint :
        Tendsto
          (fun n ↦
            ∫ z, orderedJointLaplaceKernel a z ∂((νn n : ProbabilityMeasure _) : Measure _))
          atTop
          (𝓝 (∫ z, orderedJointLaplaceKernel a z ∂((νY : ProbabilityMeasure _) : Measure _))) := by
      have hbase :=
        rescaledBranchingProcessOrderedJointLaplaceTendsto
          (κ := κ) x PZ Z hZ_meas P Y hLaplace hCond hκ times htimes coeff
      simpa [hνn_eq, hνY_eq] using hbase
    have hJointSubseq :
        Tendsto
          (fun k ↦
            ∫ z, orderedJointLaplaceKernel a z ∂((νn (ψ k) : ProbabilityMeasure _) : Measure _))
          atTop
          (𝓝 (∫ z, orderedJointLaplaceKernel a z ∂((νY : ProbabilityMeasure _) : Measure _))) :=
      hJoint.comp hψmono.tendsto_atTop
    have hkernel_eq :
        ∫ z, orderedJointLaplaceKernel a z ∂(Q : Measure (Fin J.card → NNReal)) =
          ∫ z, orderedJointLaplaceKernel a z ∂((νY : ProbabilityMeasure _) : Measure _) :=
      tendsto_nhds_unique hQtest hJointSubseq
    calc
      ∫ z, orderedJointLaplaceKernel a z ∂(Q : Measure (Fin J.card → NNReal)) =
          ∫ z, orderedJointLaplaceKernel a z ∂((νY : ProbabilityMeasure _) : Measure _) :=
            hkernel_eq
      _ = ∫ ω, Real.exp (-∑ i : Fin (m + 1), (coeff i : ℝ) * (Y (times i) ω : ℝ)) ∂
            (P x : Measure Ω) := hνY_eq
      _ = ∫ ω, Real.exp (-∑ i : Fin J.card, (a i : ℝ) * (Y (orderedTimes i) ω : ℝ)) ∂
            (P x : Measure Ω) := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
              have hsum :=
                (Equiv.sum_comp (finCongr hm)
                  (fun i : Fin J.card ↦ (a i : ℝ) * (Y (orderedTimes i) ω : ℝ)))
              congr 1
              simpa [times, coeff] using hsum

/-- Helper for Theorem 21.50: every cluster point of the ordered tuple laws is forced by the
common ordered-joint Laplace limits, so it equals the branching-diffusion tuple law. -/
private theorem mapClusterPt_eq_ofOrderedTupleLawLaplace
    {κ : NNReal → Kernel NNReal NNReal}
    (x : NNReal)
    (PZ : (n : ℕ) → ProbabilityMeasure (Ωn n))
    (Z : (n : ℕ) → ℕ → Ωn n → ℕ)
    (hZ_meas : ∀ n k : ℕ, Measurable (Z n k))
    (P : NNReal → ProbabilityMeasure Ω)
    (Y : NNReal → Ω → NNReal)
    [IsMarkovProcessRealization κ P Y]
    (hLaplace :
      ∀ t l : NNReal,
        Tendsto
          (fun n ↦
            ∫ ω, Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n t ω : ℝ))) ∂
              (PZ n : Measure (Ωn n)))
          atTop
          (𝓝 (branchingDiffusionLaplaceTransform t x l)))
    (hCond :
      ∀ n : ℕ, ∀ s t l : NNReal,
        (PZ n : Measure (Ωn n))[fun ω ↦
          Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n (s + t) ω : ℝ))) |
            generatedFiltrationSpace (rescaledGaltonWatsonProcess (Z n) n) s] =ᵐ[
            (PZ n : Measure (Ωn n))]
          fun ω ↦
            branchingDiffusionLaplaceTransform t (rescaledGaltonWatsonProcess (Z n) n s ω) l)
    (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (J : Finset NNReal)
    {Q : ProbabilityMeasure (Fin J.card → NNReal)}
    (hQ : MapClusterPt Q atTop
      (fun n ↦
        ProbabilityMeasure.map
          (PZ n)
          ((measurable_pi_lambda _ fun i : Fin J.card ↦
              measurable_rescaledGaltonWatsonProcess Z hZ_meas n (J.orderEmbOfFin rfl i)).aemeasurable))) :
    Q =
      ProbabilityMeasure.map
        (P x)
        ((measurable_pi_lambda _ fun i : Fin J.card ↦
            IsMarkovProcessRealization.measurable_process
              (κ := κ) (P := P) (Y := Y) (J.orderEmbOfFin rfl i)).aemeasurable) := by
  let νY : ProbabilityMeasure (Fin J.card → NNReal) := ProbabilityMeasure.map
    (P x)
    ((measurable_pi_lambda _ fun i : Fin J.card ↦
        IsMarkovProcessRealization.measurable_process
          (κ := κ) (P := P) (Y := Y) (J.orderEmbOfFin rfl i)).aemeasurable)
  let μQ : Measure (EuclideanSpace ℝ (Fin J.card)) :=
    Measure.map (orderedTupleToEuclidean J.card) (Q : Measure (Fin J.card → NNReal))
  let μY : Measure (EuclideanSpace ℝ (Fin J.card)) :=
    Measure.map (orderedTupleToEuclidean J.card) (νY : Measure (Fin J.card → NNReal))
  have hmgf :
      ∀ t : EuclideanSpace ℝ (Fin J.card),
        (∀ i, 0 ≤ t i) →
          ProbabilityTheory.mgf (fun x ↦ -inner ℝ t x) μQ 1 =
            ProbabilityTheory.mgf (fun x ↦ -inner ℝ t x) μY 1 := by
    intro t ht
    have hkernel :=
      mapClusterPt_orderedJointLaplace_eq
        (κ := κ) x PZ Z hZ_meas P Y hLaplace hCond hκ J hQ
        (fun i ↦ Real.toNNReal (t i))
    have hνY_integral :
        ∫ z, Real.exp (-∑ i : Fin J.card, t i * (z i : ℝ)) ∂(νY : Measure (Fin J.card → NNReal)) =
          ∫ ω, Real.exp (-∑ i : Fin J.card, (t i) * (Y (J.orderEmbOfFin rfl i) ω : ℝ)) ∂
            (P x : Measure Ω) := by
      have hkernelAEMeas :
          AEStronglyMeasurable
            (orderedJointLaplaceKernel (fun i ↦ Real.toNNReal (t i)))
            (νY : Measure (Fin J.card → NNReal)) := by
        have hkernelMeas :
            Measurable (orderedJointLaplaceKernel (fun i ↦ Real.toNNReal (t i))) := by
          exact (continuous_orderedJointLaplaceKernel (fun i ↦ Real.toNNReal (t i))).measurable
        exact
          hkernelMeas.aestronglyMeasurable
      simpa [νY, orderedJointLaplaceKernel, Real.toNNReal_of_nonneg, ht] using
        (MeasureTheory.integral_map
          ((measurable_pi_lambda _ fun i : Fin J.card ↦
              IsMarkovProcessRealization.measurable_process
                (κ := κ) (P := P) (Y := Y) (J.orderEmbOfFin rfl i)).aemeasurable)
          hkernelAEMeas)
    calc
      ProbabilityTheory.mgf (fun x ↦ -inner ℝ t x) μQ 1 =
          ∫ z, Real.exp (-∑ i, t i * (z i : ℝ)) ∂(Q : Measure (Fin J.card → NNReal)) := by
            simpa [μQ, Real.toNNReal_of_nonneg, ht] using
              mgf_orderedTupleToEuclidean_map_eq J.card
                (Q : Measure (Fin J.card → NNReal)) t
      _ =
          ∫ ω, Real.exp (-∑ i : Fin J.card, (t i) * (Y (J.orderEmbOfFin rfl i) ω : ℝ)) ∂
            (P x : Measure Ω) := by
              simpa [orderedJointLaplaceKernel, Real.toNNReal_of_nonneg, ht] using hkernel
      _ = ∫ z, Real.exp (-∑ i : Fin J.card, t i * (z i : ℝ)) ∂(νY : Measure (Fin J.card → NNReal)) := by
            symm
            exact hνY_integral
      _ = ProbabilityTheory.mgf (fun x ↦ -inner ℝ t x) μY 1 := by
            symm
            simpa [μY, Real.toNNReal_of_nonneg, ht] using
              mgf_orderedTupleToEuclidean_map_eq J.card
                (νY : Measure (Fin J.card → NNReal)) t
  have hmeas_eq :
      (Q : Measure (Fin J.card → NNReal)) = (νY : Measure (Fin J.card → NNReal)) := by
    have hpush_eq :
        μQ = μY := by
      exact
        eq_of_laplaceTransform_eq_on_nonnegativeOrthant
          (d := J.card)
          (μ := μQ) (ν := μY)
          (ae_nonneg_orderedTupleToEuclidean_map J.card (Q : Measure (Fin J.card → NNReal)))
          (ae_nonneg_orderedTupleToEuclidean_map J.card (νY : Measure (Fin J.card → NNReal)))
          hmgf
    exact map_orderedTupleToEuclidean_injective J.card hpush_eq
  exact ProbabilityMeasure.toMeasure_injective hmeas_eq

/-- Helper for Theorem 21.50: after the reindexing bridge is fixed, it remains to prove weak
convergence of the ordered tuple laws on the deduplicated finite time set `J`. -/
private theorem orderedTupleLawTendstoOnFinset
    {κ : NNReal → Kernel NNReal NNReal}
    (x : NNReal)
    (PZ : (n : ℕ) → ProbabilityMeasure (Ωn n))
    (Z : (n : ℕ) → ℕ → Ωn n → ℕ)
    (hZ_meas : ∀ n k : ℕ, Measurable (Z n k))
    (P : NNReal → ProbabilityMeasure Ω)
    (Y : NNReal → Ω → NNReal)
    [IsMarkovProcessRealization κ P Y]
    (hLaplace :
      ∀ t l : NNReal,
        Tendsto
          (fun n ↦
            ∫ ω, Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n t ω : ℝ))) ∂
              (PZ n : Measure (Ωn n)))
          atTop
          (𝓝 (branchingDiffusionLaplaceTransform t x l)))
    (hCond :
      ∀ n : ℕ, ∀ s t l : NNReal,
        (PZ n : Measure (Ωn n))[fun ω ↦
          Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n (s + t) ω : ℝ))) |
            generatedFiltrationSpace (rescaledGaltonWatsonProcess (Z n) n) s] =ᵐ[
            (PZ n : Measure (Ωn n))]
          fun ω ↦
            branchingDiffusionLaplaceTransform t (rescaledGaltonWatsonProcess (Z n) n s ω) l)
    (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (J : Finset NNReal) :
    let orderedTimes : Fin J.card → NNReal := fun i ↦ J.orderEmbOfFin rfl i
    Tendsto
      (fun n ↦
        ProbabilityMeasure.map
          (PZ n)
          ((measurable_pi_lambda _ fun i : Fin J.card ↦
              measurable_rescaledGaltonWatsonProcess Z hZ_meas n (orderedTimes i)).aemeasurable))
      atTop
      (𝓝 (ProbabilityMeasure.map
        (P x)
        ((measurable_pi_lambda _ fun i : Fin J.card ↦
            IsMarkovProcessRealization.measurable_process
              (κ := κ) (P := P) (Y := Y) (orderedTimes i)).aemeasurable))) := by
  let orderedTimes : Fin J.card → NNReal := fun i ↦ J.orderEmbOfFin rfl i
  let νn : ℕ → ProbabilityMeasure (Fin J.card → NNReal) := fun n ↦
    ProbabilityMeasure.map
      (PZ n)
      ((measurable_pi_lambda _ fun i : Fin J.card ↦
          measurable_rescaledGaltonWatsonProcess Z hZ_meas n (orderedTimes i)).aemeasurable)
  let νY : ProbabilityMeasure (Fin J.card → NNReal) := ProbabilityMeasure.map
    (P x)
    ((measurable_pi_lambda _ fun i : Fin J.card ↦
        IsMarkovProcessRealization.measurable_process
          (κ := κ) (P := P) (Y := Y) (orderedTimes i)).aemeasurable)
  have htightRange :
      IsTightMeasureSet
        {((μ : ProbabilityMeasure (Fin J.card → NNReal)) : Measure (Fin J.card → NNReal)) |
          μ ∈ Set.range νn} := by
    have hset :
        {((μ : ProbabilityMeasure (Fin J.card → NNReal)) : Measure (Fin J.card → NNReal)) |
            μ ∈ Set.range νn} =
          Set.range fun n ↦ (νn n : Measure (Fin J.card → NNReal)) := by
      ext μ
      constructor
      · rintro ⟨ρ, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨νn n, ⟨n, rfl⟩, rfl⟩
    simpa [hset] using orderedTupleLawTight x PZ Z hZ_meas hLaplace J
  have hcompact : IsCompact (closure (Set.range νn)) :=
    isCompact_closure_of_isTightMeasureSet (S := Set.range νn) htightRange
  have hνn :
      Tendsto νn atTop (𝓝 νY) := by
    refine hcompact.tendsto_nhds_of_unique_mapClusterPt ?_ ?_
    · exact Filter.Eventually.of_forall fun n ↦ subset_closure ⟨n, rfl⟩
    · intro Q _hQmem hQcluster
      exact
        mapClusterPt_eq_ofOrderedTupleLawLaplace
          (κ := κ) x PZ Z hZ_meas P Y hLaplace hCond hκ J (Q := Q)
          (by simpa [νn, orderedTimes] using hQcluster)
  simpa [orderedTimes, νn, νY] using hνn

/-- Helper for Theorem 21.50: once the ordered joint Laplace recursion is upgraded to the
canonical restriction laws on `Finset.univ.image times`, those restriction laws converge weakly to
the corresponding branching-diffusion restriction law. -/
private theorem restrictLawTendstoOfJointLaplace
    {κ : NNReal → Kernel NNReal NNReal}
    (x : NNReal)
    (PZ : (n : ℕ) → ProbabilityMeasure (Ωn n))
    (Z : (n : ℕ) → ℕ → Ωn n → ℕ)
    (hZ_meas : ∀ n k : ℕ, Measurable (Z n k))
    (P : NNReal → ProbabilityMeasure Ω)
    (Y : NNReal → Ω → NNReal)
    [IsMarkovProcessRealization κ P Y]
    (hLaplace :
      ∀ t l : NNReal,
        Tendsto
          (fun n ↦
            ∫ ω, Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n t ω : ℝ))) ∂
              (PZ n : Measure (Ωn n)))
          atTop
          (𝓝 (branchingDiffusionLaplaceTransform t x l)))
    (hCond :
      ∀ n : ℕ, ∀ s t l : NNReal,
        (PZ n : Measure (Ωn n))[fun ω ↦
          Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n (s + t) ω : ℝ))) |
            generatedFiltrationSpace (rescaledGaltonWatsonProcess (Z n) n) s] =ᵐ[
            (PZ n : Measure (Ωn n))]
          fun ω ↦
            branchingDiffusionLaplaceTransform t (rescaledGaltonWatsonProcess (Z n) n s ω) l)
    (hκ : HasBranchingDiffusionLaplaceTransform κ)
    {k : ℕ} (times : Fin k → NNReal) :
    Tendsto
      (fun n ↦
        ProbabilityMeasure.map
          (PZ n)
          ((measurable_pi_lambda _ fun t : ↥(Finset.univ.image times) ↦
              measurable_rescaledGaltonWatsonProcess Z hZ_meas n (t : NNReal)).aemeasurable))
      atTop
      (𝓝 (ProbabilityMeasure.map
        (P x)
        ((measurable_pi_lambda _ fun t : ↥(Finset.univ.image times) ↦
            IsMarkovProcessRealization.measurable_process
              (κ := κ) (P := P) (Y := Y) (t : NNReal)).aemeasurable))) := by
  -- Route correction: keep the proof on the finite subtype `↥(Finset.univ.image times)` and
  -- identify the weak limit there before transporting back to ordered tuples.
  let J : Finset NNReal := Finset.univ.image times
  have hXn_meas :
      ∀ n : ℕ, ∀ t : NNReal,
        Measurable (rescaledGaltonWatsonProcess (Z n) n t) := by
    -- Proof comment: every discrete coordinate is measurable by the standing setup, so the
    -- rescaled process is measurable at each fixed time.
    intro n t
    exact measurable_rescaledGaltonWatsonProcess Z hZ_meas n t
  have hY_meas : ∀ t : NNReal, Measurable (Y t) := by
    -- Proof comment: the branching-diffusion realization is coordinatewise measurable by the
    -- realization typeclass.
    intro t
    exact IsMarkovProcessRealization.measurable_process (κ := κ) (P := P) (Y := Y) t
  refine
    restrictLawTendsto_of_orderedTupleTendsto
      PZ (P x) (fun n ↦ rescaledGaltonWatsonProcess (Z n) n) Y hXn_meas hY_meas J ?_
  -- Proof comment: after the reindexing bridge, the remaining helper step is weak convergence of
  -- the ordered tuple laws on the deduplicated time set `J`.
  exact orderedTupleLawTendstoOnFinset x PZ Z hZ_meas P Y hLaplace hCond hκ J

/-- Auxiliary implication for Theorem 21.50: the Chapter 21 Laplace-transform setup implies the
finite-dimensional convergence of the rescaled branching-process laws to the branching-diffusion
laws. -/
-- Route correction: the real obstruction is now statement-level rather than tuple transport.
-- `⟶[fdd]` is built from `TendstoInDistribution`, so the discrete side now carries the explicit
-- coordinate-measurability hypothesis `hZ_meas`, while the limit-side measurability still comes
-- from `IsMarkovProcessRealization`. What remains is tuple-law convergence, not another statement
-- repair.
theorem rescaled_branching_process_laws_tendsto_branchingDiffusion_of_laplace_setup
    {κ : NNReal → Kernel NNReal NNReal}
    (x : NNReal)
    (PZ : (n : ℕ) → ProbabilityMeasure (Ωn n))
    (Z : (n : ℕ) → ℕ → Ωn n → ℕ)
    (hZ_meas : ∀ n k : ℕ, Measurable (Z n k))
    (P : NNReal → ProbabilityMeasure Ω)
    (Y : NNReal → Ω → NNReal)
    [IsMarkovProcessRealization κ P Y]
    (hLaplace :
      ∀ t l : NNReal,
        Tendsto
          (fun n ↦
            ∫ ω, Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n t ω : ℝ))) ∂
              (PZ n : Measure (Ωn n)))
          atTop
          (𝓝 (branchingDiffusionLaplaceTransform t x l)))
    (hCond :
      ∀ n : ℕ, ∀ s t l : NNReal,
        (PZ n : Measure (Ωn n))[fun ω ↦
          Real.exp (-((l : ℝ) * (rescaledGaltonWatsonProcess (Z n) n (s + t) ω : ℝ))) |
            generatedFiltrationSpace (rescaledGaltonWatsonProcess (Z n) n) s] =ᵐ[
            (PZ n : Measure (Ωn n))]
          fun ω ↦
            branchingDiffusionLaplaceTransform t (rescaledGaltonWatsonProcess (Z n) n s ω) l)
    (hκ : HasBranchingDiffusionLaplaceTransform κ) :
    (PZ, fun n ↦ rescaledGaltonWatsonProcess (Z n) n) ⟶[fdd] (P x, Y) := by
  -- Source-faithful repair note: `hZ_meas` restores the missing stochastic-process side condition
  -- on the discrete Galton--Watson coordinates; the limit process measurability still comes from
  -- `IsMarkovProcessRealization`. The remaining proof work is to turn those measurable coordinates
  -- together with the Laplace recursion into finite-dimensional convergence.
  intro k times
  have hXn_meas :
      ∀ n : ℕ, ∀ t : NNReal,
        Measurable (rescaledGaltonWatsonProcess (Z n) n t) := by
    intro n t
    exact measurable_rescaledGaltonWatsonProcess Z hZ_meas n t
  have hY_meas : ∀ t : NNReal, Measurable (Y t) := by
    -- Proof comment: the realized branching diffusion is coordinatewise measurable by the
    -- realization typeclass.
    intro t
    exact IsMarkovProcessRealization.measurable_process (κ := κ) (P := P) (Y := Y) t
  refine
    finiteDimensionalEvaluation_tendsto_of_restrictLaw
      PZ (P x) (fun n ↦ rescaledGaltonWatsonProcess (Z n) n) Y
      hXn_meas hY_meas times ?_
  -- Proof comment: the remaining owner-level task is exactly the weak convergence of the
  -- canonical restriction laws on the finite time set `Finset.univ.image times`.
  exact restrictLawTendstoOfJointLaplace x PZ Z hZ_meas P Y hLaplace hCond hκ times

/-- Theorem 21.50: we have `ℒ_x[\tilde Z^n] ⟶ ℒ_x[Y]`. -/
theorem orderedTupleLawTendsto
    {κ : NNReal → Kernel NNReal NNReal}
    (x : NNReal)
    (PZ : (n : ℕ) → ProbabilityMeasure (Ωn n))
    (Z : (n : ℕ) → ℕ → Ωn n → ℕ)
    (P : NNReal → ProbabilityMeasure Ω)
    (Y : NNReal → Ω → NNReal)
    [IsMarkovProcessRealization κ P Y]
    (hSetup : HasRescaledBranchingProcessLaplaceSetup x PZ Z)
    (hκ : HasBranchingDiffusionLaplaceTransform κ) :
    (PZ, fun n ↦ rescaledGaltonWatsonProcess (Z n) n) ⟶[fdd] (P x, Y) := by
  -- Proof comment: the theorem-level setup is exactly the triple of hypotheses required by the
  -- auxiliary implication, so the wrapper just unpacks `hSetup`.
  rcases hSetup with ⟨hZ_meas, hLaplace, hCond⟩
  exact
    rescaled_branching_process_laws_tendsto_branchingDiffusion_of_laplace_setup
      x PZ Z hZ_meas P Y hLaplace hCond hκ

/-- Helper for Theorem 21.50: restate `orderedTupleLawTendsto` under the chapter-specific theorem
name used elsewhere in the file. -/
theorem rescaled_branching_process_laws_tendsto_branchingDiffusion
    {κ : NNReal → Kernel NNReal NNReal}
    (x : NNReal)
    (PZ : (n : ℕ) → ProbabilityMeasure (Ωn n))
    (Z : (n : ℕ) → ℕ → Ωn n → ℕ)
    (P : NNReal → ProbabilityMeasure Ω)
    (Y : NNReal → Ω → NNReal)
    [IsMarkovProcessRealization κ P Y]
    (hSetup : HasRescaledBranchingProcessLaplaceSetup x PZ Z)
    (hκ : HasBranchingDiffusionLaplaceTransform κ) :
    (PZ, fun n ↦ rescaledGaltonWatsonProcess (Z n) n) ⟶[fdd] (P x, Y) := by
  -- Proof comment: this wrapper preserves the previous exported theorem name while delegating the
  -- actual label-bearing result to `orderedTupleLawTendsto`.
  exact orderedTupleLawTendsto x PZ Z P Y hSetup hκ

end ProbabilityTheory
