/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_14

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [mE : MeasurableSpace E]

/-- Helper for Theorem 20.29: the finite prefix of a discrete-time process up to time `k`. -/
def pastPath (X : ℕ → Ω → E) (k : ℕ) : Ω → Fin (k + 1) → E :=
  fun ω i ↦ X i ω

/-- Helper for Theorem 20.29: the shifted future path of a discrete-time process after time `k`.
-/
def shiftedPath (X : ℕ → Ω → E) (k : ℕ) : Ω → ℕ → E :=
  fun ω n ↦ X (n + k) ω

/-- Helper for Theorem 20.29: the ordered future coordinates of a shifted discrete-time path. -/
def shiftedPathCoordinates {n : ℕ} (X : ℕ → Ω → E) (k : ℕ) (t : Fin n → ℕ) :
    Ω → Fin n → E :=
  fun ω i ↦ X (t i + k) ω

/-- Helper for Theorem 20.29: evaluating `shiftedPath X k` at time `n` reads off `X (n + k)`. -/
theorem shiftedPath_apply
    (X : ℕ → Ω → E) (k : ℕ) (ω : Ω) (n : ℕ) :
    shiftedPath X k ω n = X (n + k) ω := by
  rfl

/-- Helper for Theorem 20.29: evaluating the past path at `i` reads off the coordinate `X i`. -/
theorem pastPath_apply
    (X : ℕ → Ω → E) (k : ℕ) (ω : Ω) (i : Fin (k + 1)) :
    pastPath X k ω i = X i ω := rfl

/-- Helper for Theorem 20.29: the finite-history map `pastPath X k` is measurable once each
coordinate of `X` is measurable. -/
lemma measurable_pastPath
    (X : ℕ → Ω → E) (hX_meas : ∀ n, Measurable (X n)) (k : ℕ) :
    Measurable (pastPath X k) := by
  -- Proof comment: measurability on the finite product is coordinatewise.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [pastPath] using hX_meas i

/-- Helper for Theorem 20.29: the shifted future-path map is measurable once each process
coordinate is measurable. -/
lemma measurable_shiftedPath
    (X : ℕ → Ω → E) (hX_meas : ∀ n, Measurable (X n)) (k : ℕ) :
    Measurable (shiftedPath X k) := by
  -- Proof comment: each shifted coordinate is the measurable slice `X (n + k)`.
  refine measurable_pi_lambda _ fun n ↦ ?_
  simpa [shiftedPath, add_comm] using hX_meas (n + k)

/-- Helper for Theorem 20.29: finite ordered coordinates of the shifted path are measurable. -/
lemma measurable_shiftedPathCoordinates {n : ℕ}
    (X : ℕ → Ω → E) (hX_meas : ∀ n, Measurable (X n)) (k : ℕ) (t : Fin n → ℕ) :
    Measurable (shiftedPathCoordinates X k t) := by
  -- Proof comment: each tuple coordinate is the measurable slice `X (t i + k)`.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [shiftedPathCoordinates, add_comm] using hX_meas (t i + k)

/-- Helper for Theorem 20.29: the time-`k` generated filtration is the pullback sigma-algebra of
the finite-history map `pastPath X k`. -/
lemma generatedFiltrationSpace_eq_pastPath_comap
    (X : ℕ → Ω → E) (k : ℕ) :
    generatedFiltrationSpace X k = MeasurableSpace.comap (pastPath X k) inferInstance := by
  have hleft :
      MeasurableSpace.comap (pastPath X k) inferInstance ≤ generatedFiltrationSpace X k := by
    have hPastMeas :
        Measurable[generatedFiltrationSpace X k] (fun ω ↦ fun i : Fin (k + 1) ↦ X i ω) := by
      -- Proof comment: every coordinate of the finite history is already measurable at time `k`.
      rw [@measurable_pi_iff]
      intro i
      refine Measurable.of_comap_le ?_
      exact
        le_iSup_of_le i <|
          le_iSup_of_le (show (i : ℕ) ≤ k from Nat.le_of_lt_succ i.2) le_rfl
    exact hPastMeas.comap_le
  have hright :
      generatedFiltrationSpace X k ≤ MeasurableSpace.comap (pastPath X k) inferInstance := by
    rw [generatedFiltrationSpace]
    refine iSup₂_le fun t ht ↦ ?_
    let i : Fin (k + 1) := ⟨t, Nat.lt_succ_of_le ht⟩
    have hCoord :
        Measurable[MeasurableSpace.comap (pastPath X k) inferInstance]
          (fun ω ↦ pastPath X k ω i) := by
      exact (measurable_pi_apply i).comp (comap_measurable (pastPath X k))
    simpa [pastPath, i] using hCoord.comap_le
  exact le_antisymm hright hleft

/-- Helper for Theorem 20.29: every Nat-indexed path measure is the projective limit of its finite
restriction marginals. -/
lemma natPathMeasure_isProjectiveLimit_restrictions
    (ν : Measure (ℕ → E)) :
    MeasureTheory.IsProjectiveLimit ν (fun J : Finset ℕ ↦ ν.map J.restrict) := by
  -- Proof comment: the defining property of a projective limit is exactly the prescribed finite
  -- restriction pushforward.
  intro J
  rfl

/-- Helper for Theorem 20.29: reindexing along `J.orderEmbOfFin` matches the usual finite
restriction `J.restrict`. -/
lemma piCongrLeft_orderEmbOfFin_eq_restrict
    (J : Finset ℕ) (y : ℕ → E) :
    let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
    let t : Fin J.card → ℕ := J.orderEmbOfFin rfl
    (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) (fun i ↦ y (t i)) = J.restrict y := by
  -- Proof comment: the order isomorphism turns the ordered tuple back into the ordinary
  -- restriction map.
  dsimp
  ext j
  have hindex :
      J.orderEmbOfFin rfl ((J.orderIsoOfFin rfl).symm j) = j.1 := by
    exact congrArg Subtype.val ((J.orderIsoOfFin rfl).apply_symm_apply j)
  change
    ((Equiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
        (fun i ↦ y (J.orderEmbOfFin rfl i)) j) =
      J.restrict y j
  rw [Equiv.piCongrLeft_apply]
  simp [hindex]

/-- Helper for Theorem 20.29: evaluating a composed kernel against a restricted pushforward is
the same as integrating the row masses over the source event. -/
lemma kernelCompRestrictMapRealEqSetIntegral
    {F : Type*} [MeasurableSpace F]
    (κ : Kernel E F) [IsMarkovKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] {Y : Ω → E} (hY : Measurable Y)
    {B : Set Ω} (_hB : MeasurableSet B) {A : Set F} (hA : MeasurableSet A) :
    ((κ ∘ₘ ((μ.restrict B).map Y)).real A) = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
  let ν : Measure E := ((μ.restrict B).map Y)
  have hkernel_int :
      Integrable (fun y : E ↦ (κ y).real A) ν := by
    simpa [ν] using
      (ProbabilityTheory.Kernel.IsMarkovKernel.integrable
        (μ := ν) (κ := κ) hA)
  have hkernel_nonneg :
      0 ≤ᵐ[ν] fun y : E ↦ (κ y).real A :=
    Filter.Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg
  have hcomp_real :
      ((κ ∘ₘ ν).real A) = ∫ y, (κ y).real A ∂ν := by
    rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.bind_apply hA
      (ProbabilityTheory.Kernel.aemeasurable _)]
    have hlintegral :
        ∫⁻ y, κ y A ∂ν = ENNReal.ofReal (∫ y, (κ y).real A ∂ν) := by
      calc
        ∫⁻ y, κ y A ∂ν = ∫⁻ y, ENNReal.ofReal ((κ y).real A) ∂ν := by
            refine lintegral_congr_ae ?_
            filter_upwards with y
            rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal]
            exact measure_ne_top _ _
        _ = ENNReal.ofReal (∫ y, (κ y).real A ∂ν) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hkernel_int hkernel_nonneg
    rw [hlintegral, ENNReal.toReal_ofReal]
    exact integral_nonneg_of_ae hkernel_nonneg
  have hmap_real :
      ∫ y, (κ y).real A ∂ν = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
    change ∫ y, (κ y).real A ∂((μ.restrict B).map Y) = ∫ ω, (κ (Y ω)).real A ∂(μ.restrict B)
    rw [MeasureTheory.integral_map hY.aemeasurable hkernel_int.aestronglyMeasurable]
  calc
    ((κ ∘ₘ ((μ.restrict B).map Y)).real A) = ∫ y, (κ y).real A ∂ν := by
      simpa [ν] using hcomp_real
    _ = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
      simpa [ν] using hmap_real

/-- Helper for Theorem 20.29: Theorem 17.9 gives the conditional law of every finite future
restriction on history events. -/
lemma futurePathRestrictionIndicator_condExp
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) (J : Finset ℕ) {A : Set (J → E)} (hA : MeasurableSet A) :
    ((P x : Measure Ω)[fun ω ↦ Set.indicator A (fun _ ↦ (1 : ℝ))
        (J.restrict (shiftedPath X k ω)) | generatedFiltrationSpace X k]) =ᵐ[
      (P x : Measure Ω)] fun ω ↦ (((κ (X k ω)).map J.restrict).real A) := by
  let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
  let t : Fin J.card → ℕ := J.orderEmbOfFin rfl
  let A' : Set (Fin J.card → E) :=
    (fun z ↦ (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) z) ⁻¹' A
  have hA'_meas : MeasurableSet A' := by
    exact hA.preimage ((MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e).measurable)
  have hIndicator_meas :
      Measurable (Set.indicator A' fun _ : Fin J.card → E ↦ (1 : ℝ)) := by
    exact Measurable.indicator measurable_const hA'_meas
  have hIndicator_bdd :
      Bornology.IsBounded (Set.range (Set.indicator A' fun _ : Fin J.card → E ↦ (1 : ℝ))) := by
    have h01 :
        Set.range (Set.indicator A' fun _ : Fin J.card → E ↦ (1 : ℝ)) ⊆
          ({(0 : ℝ)} ∪ ({(1 : ℝ)} : Set ℝ)) := by
      intro r hr
      rcases hr with ⟨y, rfl⟩
      by_cases hy : y ∈ A'
      · right
        simp [hy]
      · left
        simp [hy]
    have hBound01 :
        Bornology.IsBounded (({(0 : ℝ)} : Set ℝ) ∪ ({(1 : ℝ)} : Set ℝ)) := by
      exact Bornology.IsBounded.union
        Bornology.isBounded_singleton Bornology.isBounded_singleton
    exact hBound01.subset h01
  have hFinite :
      HasFuturePathConditionalExpectationFormula X P κ := by
    -- Proof comment: Theorem 17.9 is already the owner theorem for deterministic-time future-path
    -- conditional expectations, so we instantiate it before translating from ordered coordinates
    -- to restriction maps.
    exact
      (isTimeHomogeneousMarkovProcess_iff_hasFuturePathConditionalExpectationFormula_of_fixedPathKernel
        X P κ hX_meas hX0 hpath).mp hMarkov
  have hFiniteIndicator :
      (P x : Measure Ω)[fun ω ↦ Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ))
          (shiftedPathCoordinates X k t ω) | generatedFiltrationSpace X k] =ᵐ[
            (P x : Measure Ω)] fun ω ↦
              ∫ y, Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ)) (fun i ↦ y (t i))
                ∂κ (X k ω) := by
    -- Proof comment: this is exactly the finite-coordinate specialization of the owner future-path
    -- formula at the ordered family `J.orderEmbOfFin rfl`.
    simpa [shiftedPathCoordinates, t] using
      hFinite hIndicator_meas hIndicator_bdd
        (show Monotone t by simpa [t] using (J.orderEmbOfFin rfl).monotone)
        k x (show 0 ≤ k by simp)
  have hleft_fun :
      (fun ω ↦ Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ))
          (shiftedPathCoordinates X k t ω)) =
        fun ω ↦ Set.indicator A (fun _ : J → E ↦ (1 : ℝ))
          (J.restrict (shiftedPath X k ω)) := by
    funext ω
    have hEq :
        (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) (shiftedPathCoordinates X k t ω) =
          J.restrict (shiftedPath X k ω) := by
      calc
        (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) (shiftedPathCoordinates X k t ω)
            = (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e)
                (fun i ↦ shiftedPath X k ω (t i)) := by
                  rfl
        _ = J.restrict (shiftedPath X k ω) := by
              simpa [e, t] using
                piCongrLeft_orderEmbOfFin_eq_restrict (J := J) (y := shiftedPath X k ω)
    have hfuture_mem :
        shiftedPathCoordinates X k t ω ∈ A' ↔ J.restrict (shiftedPath X k ω) ∈ A := by
      simpa [A'] using show
        (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) (shiftedPathCoordinates X k t ω) ∈ A ↔
          J.restrict (shiftedPath X k ω) ∈ A from by rw [hEq]
    by_cases hmem : J.restrict (shiftedPath X k ω) ∈ A
    · have hmem' : shiftedPathCoordinates X k t ω ∈ A' := hfuture_mem.mpr hmem
      simp [hmem, hmem']
    · have hmem' : shiftedPathCoordinates X k t ω ∉ A' := by
        intro hmem'
        exact hmem (hfuture_mem.mp hmem')
      simp [hmem, hmem']
  have hFiniteIndicator' :
      (P x : Measure Ω)[fun ω ↦ Set.indicator A (fun _ : J → E ↦ (1 : ℝ))
          (J.restrict (shiftedPath X k ω)) | generatedFiltrationSpace X k] =ᵐ[
            (P x : Measure Ω)] fun ω ↦
              ∫ y, Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ)) (fun i ↦ y (t i))
                ∂κ (X k ω) := by
    simpa [hleft_fun] using hFiniteIndicator
  filter_upwards [hFiniteIndicator'] with ω hω
  have hright :
      (∫ y, Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ)) (fun i ↦ y (t i)) ∂κ (X k ω)) =
        (((κ (X k ω)).map J.restrict).real A) := by
    calc
      ∫ y, Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ)) (fun i ↦ y (t i)) ∂κ (X k ω)
          = ∫ y, Set.indicator (J.restrict ⁻¹' A) (fun _ : ℕ → E ↦ (1 : ℝ)) y ∂κ (X k ω) := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
              have hEq := piCongrLeft_orderEmbOfFin_eq_restrict (J := J) (y := y)
              have hmem :
                  (fun i ↦ y (t i)) ∈ A' ↔ y ∈ J.restrict ⁻¹' A := by
                simpa [A', e, t] using show
                  ((MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) (fun i ↦ y (t i)) ∈ A ↔
                    J.restrict y ∈ A) from by rw [hEq]
              by_cases hy : y ∈ J.restrict ⁻¹' A
              · have hy' : (fun i ↦ y (t i)) ∈ A' := hmem.mpr hy
                simp [hy, hy']
              · have hy' : (fun i ↦ y (t i)) ∉ A' := by
                  intro hy'
                  exact hy (hmem.mp hy')
                simp [hy, hy']
      _ = (κ (X k ω)).real (J.restrict ⁻¹' A) := by
            simpa using
              (MeasureTheory.integral_indicator_one (μ := κ (X k ω))
                (s := J.restrict ⁻¹' A)
                ((Finset.measurable_restrict J) hA))
      _ = (((κ (X k ω)).map J.restrict).real A) := by
            simpa using
              (MeasureTheory.map_measureReal_apply (μ := κ (X k ω)) (f := J.restrict)
                (Finset.measurable_restrict J) hA).symm
  simpa [hright] using hω

/-- Helper for Theorem 20.29: on each history event, the restricted future-path law agrees with
the path kernel mixed against the present-state law. -/
lemma restrictedFuturePathLaw_eq_mixedPathLaw_on_history
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) {B : Set Ω} (hB : MeasurableSet[generatedFiltrationSpace X k] B) :
    let μ : Measure Ω := (P x : Measure Ω)
    let νB : Measure (ℕ → E) := (μ.restrict B).map (shiftedPath X k)
    let ρB : Measure (ℕ → E) := κ ∘ₘ ((μ.restrict B).map (X k))
    νB = ρB := by
  let μ : Measure Ω := (P x : Measure Ω)
  let νB : Measure (ℕ → E) := (μ.restrict B).map (shiftedPath X k)
  let ρB : Measure (ℕ → E) := κ ∘ₘ ((μ.restrict B).map (X k))
  have hgenerated_le : generatedFiltrationSpace X k ≤ ‹MeasurableSpace Ω› := by
    rw [generatedFiltrationSpace_eq_pastPath_comap X k]
    exact (measurable_pastPath X hX_meas k).comap_le
  have hPathMap_meas : Measurable (fun ω ↦ fun n : ℕ ↦ X n ω) := by
    refine measurable_pi_lambda _ fun n ↦ ?_
    simpa using hX_meas n
  letI : IsMarkovKernel κ := by
    refine ⟨fun y : E ↦ ?_⟩
    rw [hpath y]
    exact Measure.isProbabilityMeasure_map hPathMap_meas.aemeasurable
  have hB_ambient : MeasurableSet B := hgenerated_le B hB
  have hJ :
      ∀ J : Finset ℕ, νB.map J.restrict = ρB.map J.restrict := by
    intro J
    let κJ : Kernel E (J → E) := κ.map J.restrict
    letI : IsMarkovKernel κJ := by
      let hmeasRestrict : Measurable (J.restrict : (ℕ → E) → J → E) :=
        Finset.measurable_restrict J
      refine ⟨fun y : E ↦ ?_⟩
      have hrow : κJ y = (κ y).map J.restrict := by
        simpa [κJ] using Kernel.map_apply κ hmeasRestrict y
      rw [hrow]
      simpa using Measure.isProbabilityMeasure_map (μ := κ y) hmeasRestrict.aemeasurable
    refine Measure.ext fun A hA ↦ ?_
    let futureEvent : Set Ω := (fun ω ↦ J.restrict (shiftedPath X k ω)) ⁻¹' A
    have hfuture_meas : MeasurableSet futureEvent := by
      simpa [futureEvent] using
        ((Finset.measurable_restrict J).comp (measurable_shiftedPath X hX_meas k)) hA
    have hIndicatorInt :
        Integrable (Set.indicator futureEvent (fun _ ↦ (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hfuture_meas
    have hmarkov :
        μ⟦futureEvent | generatedFiltrationSpace X k⟧ =ᵐ[μ]
          fun ω ↦ (((κ (X k ω)).map J.restrict).real A) := by
      -- Proof comment: the finite-restriction conditional-law formula gives the event mass on
      -- each history event.
      simpa [futureEvent] using
        futurePathRestrictionIndicator_condExp X P κ hX_meas hX0 hpath x k J hA
    have hleft_real :
        (((νB.map J.restrict).real A)) = ∫ ω in B, (((κ (X k ω)).map J.restrict).real A) ∂μ := by
      have hmass :
          μ.real (B ∩ futureEvent) =
            ∫ ω in B, (((κ (X k ω)).map J.restrict).real A) ∂μ := by
        calc
          μ.real (B ∩ futureEvent)
              = ∫ ω in B, (μ⟦futureEvent | generatedFiltrationSpace X k⟧) ω ∂μ := by
                  rw [MeasureTheory.setIntegral_condExp hgenerated_le hIndicatorInt hB,
                    ← MeasureTheory.integral_indicator hB_ambient]
                  simpa [futureEvent, Set.indicator_indicator, Set.inter_assoc,
                    Set.inter_left_comm, Set.inter_comm, smul_eq_mul] using
                    (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                      (hB_ambient.inter hfuture_meas)).symm
          _ = ∫ ω in B, (((κ (X k ω)).map J.restrict).real A) ∂μ := by
                exact MeasureTheory.integral_congr_ae hmarkov.restrict
      have hmapJ :
          νB.map J.restrict = (μ.restrict B).map (fun ω ↦ J.restrict (shiftedPath X k ω)) := by
        dsimp [νB]
        rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict J).aemeasurable]
        · rfl
        · exact (measurable_shiftedPath X hX_meas k).aemeasurable
      calc
        (((νB.map J.restrict).real A))
            = ((((μ.restrict B).map (fun ω ↦ J.restrict (shiftedPath X k ω))).real A)) := by
                rw [hmapJ]
        _ = (μ.restrict B).real futureEvent := by
              simpa [futureEvent] using
                (MeasureTheory.map_measureReal_apply
                  (μ := (μ.restrict B)) (f := fun ω ↦ J.restrict (shiftedPath X k ω))
                  ((Finset.measurable_restrict J).comp (measurable_shiftedPath X hX_meas k)) hA)
        _ = μ.real (futureEvent ∩ B) := by
              simpa [futureEvent] using
                (MeasureTheory.measureReal_restrict_apply (μ := μ) (s := B) (t := futureEvent)
                  hfuture_meas)
        _ = ∫ ω in B, (((κ (X k ω)).map J.restrict).real A) ∂μ := by
              simpa [Set.inter_comm] using hmass
    have hright_real :
        (((ρB.map J.restrict).real A)) = ∫ ω in B, (((κ (X k ω)).map J.restrict).real A) ∂μ := by
      let κJ : Kernel E (J → E) := κ.map J.restrict
      have hmap :
          ρB.map J.restrict = κJ ∘ₘ ((μ.restrict B).map (X k)) := by
        dsimp [ρB, κJ]
        simpa using Measure.map_comp (((μ.restrict B).map (X k))) κ (Finset.measurable_restrict J)
      haveI : IsMarkovKernel κJ := by
        let hmeasRestrict : Measurable (J.restrict : (ℕ → E) → J → E) :=
          Finset.measurable_restrict J
        refine ⟨fun y : E ↦ ?_⟩
        have hrow : κJ y = (κ y).map J.restrict := by
          simpa [κJ] using Kernel.map_apply κ hmeasRestrict y
        rw [hrow]
        simpa using Measure.isProbabilityMeasure_map (μ := κ y) hmeasRestrict.aemeasurable
      rw [hmap]
      calc
        ((κJ ∘ₘ ((μ.restrict B).map (X k))).real A)
            = ∫ ω in B, (κJ (X k ω)).real A ∂μ := by
                simpa [κJ] using
                  (kernelCompRestrictMapRealEqSetIntegral
                    (κ := κ.map J.restrict) (μ := μ) (Y := X k) (hY := hX_meas k)
                    (B := B) hB_ambient (A := A) hA)
        _ = ∫ ω in B, (((κ (X k ω)).map J.restrict).real A) ∂μ := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
              have hrow : κJ (X k ω) = (κ (X k ω)).map J.restrict := by
                simpa [κJ] using Kernel.map_apply κ (Finset.measurable_restrict J) (X k ω)
              exact congrArg (fun ν : Measure (J → E) ↦ ν.real A) hrow
    have hleft_ne_top : (νB.map J.restrict) A ≠ ⊤ := by
      simpa using measure_lt_top (νB.map J.restrict) A
    have hright_ne_top : (ρB.map J.restrict) A ≠ ⊤ := by
      simpa using measure_lt_top (ρB.map J.restrict) A
    exact
      (MeasureTheory.measureReal_eq_measureReal_iff
        (μ := νB.map J.restrict) (ν := ρB.map J.restrict)
        (s := A) (t := A) hleft_ne_top hright_ne_top).mp
        (hleft_real.trans hright_real.symm)
  have hν :
      MeasureTheory.IsProjectiveLimit νB (fun J : Finset ℕ ↦ νB.map J.restrict) := by
    simpa [νB] using natPathMeasure_isProjectiveLimit_restrictions νB
  have hρ :
      MeasureTheory.IsProjectiveLimit ρB (fun J : Finset ℕ ↦ ρB.map J.restrict) := by
    simpa [ρB] using natPathMeasure_isProjectiveLimit_restrictions ρB
  have hρ' :
      MeasureTheory.IsProjectiveLimit ρB (fun J : Finset ℕ ↦ νB.map J.restrict) := by
    intro J
    exact (hJ J).symm
  haveI : ∀ J : Finset ℕ, IsFiniteMeasure (νB.map J.restrict) := fun _ ↦ inferInstance
  -- Proof comment: equality of all finite restrictions identifies the full path measures by
  -- projective-limit uniqueness.
  exact MeasureTheory.IsProjectiveLimit.unique hν hρ'

/-- Helper for Theorem 20.29: the discrete-time Markov owner gives the full future-path
conditional-expectation formula for bounded measurable path functionals. -/
lemma futurePathCondExp_of_markovProcessNat
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) (g : (ℕ → E) → ℝ) (hg_meas : Measurable g)
    (hg_bdd : Bornology.IsBounded (Set.range g)) :
    ((P x : Measure Ω)[fun ω ↦ g (shiftedPath X k ω) | generatedFiltrationSpace X k]) =ᵐ[
      (P x : Measure Ω)] fun ω ↦ ∫ y, g y ∂κ (X k ω) := by
  have hPathMap_meas : Measurable (fun ω ↦ fun n : ℕ ↦ X n ω) := by
    refine measurable_pi_lambda _ fun n ↦ ?_
    simpa using hX_meas n
  letI : IsMarkovKernel κ := by
    refine ⟨fun y : E ↦ ?_⟩
    rw [hpath y]
    exact Measure.isProbabilityMeasure_map hPathMap_meas.aemeasurable
  let μ : Measure Ω := (P x : Measure Ω)
  have hgenerated_le : generatedFiltrationSpace X k ≤ ‹MeasurableSpace Ω› := by
    rw [generatedFiltrationSpace_eq_pastPath_comap X k]
    exact (measurable_pastPath X hX_meas k).comap_le
  have hfuture_meas : Measurable (shiftedPath X k) := measurable_shiftedPath X hX_meas k
  have hg_int :
      Integrable (fun ω ↦ g (shiftedPath X k ω)) μ := by
    obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range g) hg_bdd
    -- Proof comment: bounded measurable path test functions are integrable under the start law.
    refine Integrable.of_bound (hg_meas.comp hfuture_meas).aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun ω ↦ hC _ ⟨shiftedPath X k ω, rfl⟩
  have hXk_generated : Measurable[generatedFiltrationSpace X k] (X k) := by
    -- Proof comment: the present state is the last coordinate of the finite history.
    rw [generatedFiltrationSpace_eq_pastPath_comap X k]
    have hCoord :
        Measurable[MeasurableSpace.comap (pastPath X k) inferInstance]
          (fun ω ↦ pastPath X k ω (Fin.last k)) := by
      exact (measurable_pi_apply (Fin.last k)).comp (comap_measurable (pastPath X k))
    simpa [pastPath] using hCoord
  have hKernelIntegral_meas :
      Measurable fun z : E ↦ ∫ y, g y ∂κ z := by
    -- Proof comment: integrating a measurable real-valued path functional against the kernel is
    -- measurable in the starting state.
    exact
      (hg_meas.stronglyMeasurable.integral_kernel :
        StronglyMeasurable fun z : E ↦ ∫ y, g y ∂κ z).measurable
  have hKernelIntegral_meas_generated :
      Measurable[generatedFiltrationSpace X k] fun ω ↦ ∫ y, g y ∂κ (X k ω) := by
    -- Proof comment: compose the measurable kernel integral with the history-measurable present
    -- state.
    exact hKernelIntegral_meas.comp hXk_generated
  have hKernelIntegral_meas_ambient :
      Measurable fun ω ↦ ∫ y, g y ∂κ (X k ω) := by
    exact hKernelIntegral_meas.comp (hX_meas k)
  obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range g) hg_bdd
  have hCondExp :
      (fun ω ↦ ∫ y, g y ∂κ (X k ω)) =ᵐ[μ]
        μ[fun ω ↦ g (shiftedPath X k ω) | generatedFiltrationSpace X k] := by
    exact MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hgenerated_le hg_int
      (fun s hs hμs ↦ by
        -- Proof comment: the kernel-integral candidate is bounded on every finite history event.
        refine IntegrableOn.of_bound hμs hKernelIntegral_meas_ambient.aestronglyMeasurable C ?_
        refine Filter.Eventually.of_forall fun ω ↦ ?_
        have hbound_row :
            ‖∫ y, g y ∂κ (X k ω)‖ ≤ C := by
          have hgC : ∀ᵐ y ∂κ (X k ω), ‖g y‖ ≤ C := by
            exact Filter.Eventually.of_forall fun y ↦ hC _ ⟨y, rfl⟩
          simpa using
            (MeasureTheory.norm_integral_le_of_norm_le_const (μ := κ (X k ω)) hgC)
        exact hbound_row)
      (fun s hs hμs ↦ by
        -- Proof comment: on each history event, identify the restricted future-path law with the
        -- mixed path-kernel law and then integrate `g` against that common path measure.
        let νB : Measure (ℕ → E) := (μ.restrict s).map (shiftedPath X k)
        let ρB : Measure (ℕ → E) := κ ∘ₘ ((μ.restrict s).map (X k))
        have hs_history : MeasurableSet[generatedFiltrationSpace X k] s := hs
        have hlaw : νB = ρB := by
          simpa [μ, νB, ρB] using
            restrictedFuturePathLaw_eq_mixedPathLaw_on_history X P κ hX_meas hX0 hpath x k
              hs_history
        haveI : IsFiniteMeasure νB := by
          dsimp [νB]
          infer_instance
        have hg_νB_int : Integrable g νB := by
          refine Integrable.of_bound hg_meas.aestronglyMeasurable C ?_
          exact Filter.Eventually.of_forall fun y ↦ hC _ ⟨y, rfl⟩
        have hg_ρB_int : Integrable g ρB := by
          rw [← hlaw]
          exact hg_νB_int
        have hleft :
            ∫ ω in s, g (shiftedPath X k ω) ∂μ = ∫ y, g y ∂νB := by
          change ∫ ω, g (shiftedPath X k ω) ∂(μ.restrict s) = ∫ y, g y ∂νB
          rw [show νB = (μ.restrict s).map (shiftedPath X k) by rfl]
          exact
            (MeasureTheory.integral_map hfuture_meas.aemeasurable
              hg_meas.aestronglyMeasurable).symm
        have hright :
            ∫ y, g y ∂ρB = ∫ ω in s, ∫ y, g y ∂κ (X k ω) ∂μ := by
          let κ₀ : Kernel Unit E := Kernel.const Unit ((μ.restrict s).map (X k))
          have hcomp :
              (κ ∘ₖ κ₀) () = ρB := by
            simp [κ₀, ρB]
          calc
            ∫ y, g y ∂ρB = ∫ y, g y ∂((κ ∘ₖ κ₀) ()) := by rw [← hcomp]
            _ = ∫ z, ∫ y, g y ∂κ z ∂κ₀ () := by
                  simpa using
                    (ProbabilityTheory.Kernel.integral_comp (η := κ) (κ := κ₀) (a := ())
                      hg_ρB_int)
            _ = ∫ z, ∫ y, g y ∂κ z ∂((μ.restrict s).map (X k)) := by
                  simp [κ₀]
            _ = ∫ ω in s, ∫ y, g y ∂κ (X k ω) ∂μ := by
                  simpa using
                    (MeasureTheory.integral_map (hX_meas k).aemeasurable
                      hKernelIntegral_meas.aestronglyMeasurable)
        exact (hleft.trans (hlaw ▸ hright)).symm)
      hKernelIntegral_meas_generated.aestronglyMeasurable
  exact hCondExp.symm

end ProbabilityTheory
