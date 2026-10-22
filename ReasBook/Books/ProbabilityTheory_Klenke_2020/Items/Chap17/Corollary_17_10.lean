/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_14

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [mE : MeasurableSpace E]

/-- The finite prefix of a discrete-time process up to time `k`. -/
def pastPath (X : ℕ → Ω → E) (k : ℕ) : Ω → Fin (k + 1) → E :=
  fun ω i ↦ X i ω

/-- The shifted future path of a discrete-time process after time `k`. -/
def futurePathNat (X : ℕ → Ω → E) (k : ℕ) : Ω → ℕ → E :=
  fun ω n ↦ X (n + k) ω

/-- The ordered coordinates of a shifted discrete-time path. -/
def futurePathCoordinatesNat {n : ℕ} (X : ℕ → Ω → E) (k : ℕ) (t : Fin n → ℕ) :
    Ω → Fin n → E :=
  fun ω i ↦ X (t i + k) ω

-- Proof sketch: unfold `futurePathNat`; it is the shifted coordinate map of the process.
/-- Evaluating the future path at time `n` reads off the coordinate `X (n + k)`. -/
theorem futurePath_apply {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
    (X : ℕ → Ω → E) (k : ℕ) (ω : Ω) (n : ℕ) :
    futurePathNat X k ω n = X (n + k) ω := rfl

/-- The shifted future path is measurable when every coordinate of the process is measurable. -/
lemma measurable_futurePathNat
    (X : ℕ → Ω → E) (hX_meas : ∀ n, Measurable (X n)) (k : ℕ) :
    Measurable (futurePathNat X k) := by
  refine measurable_pi_lambda _ fun n ↦ ?_
  simpa [futurePathNat] using hX_meas (n + k)

-- Proof sketch: unfold `pastPath`; it packages the coordinates `X 0, ..., X k` into one finite
-- history map.
/-- Evaluating the past path at index `i` reads off the coordinate `X i`. -/
theorem pastPath_apply {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
    (X : ℕ → Ω → E) (k : ℕ) (ω : Ω) (i : Fin (k + 1)) :
    pastPath X k ω i = X i ω := rfl

/-- Helper for Corollary 17.10: the finite-history map `pastPath X k` is measurable when the
process is coordinatewise measurable. -/
lemma measurable_pastPath
    (X : ℕ → Ω → E) (hX_meas : ∀ n, Measurable (X n)) (k : ℕ) :
    Measurable (pastPath X k) := by
  -- Proof comment: each coordinate of `pastPath X k` is the measurable slice `X i`.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [pastPath] using hX_meas i

/-- Helper for Corollary 17.10: the natural filtration up to time `k` is exactly the pullback
σ-algebra of the finite-history map `pastPath X k`. -/
lemma generatedFiltrationSpace_eq_pastPath_comap
    (X : ℕ → Ω → E) (k : ℕ) :
    generatedFiltrationSpace X k = MeasurableSpace.comap (pastPath X k) inferInstance := by
  have hleft :
      MeasurableSpace.comap (pastPath X k) inferInstance ≤ generatedFiltrationSpace X k := by
    have hPastMeas :
        Measurable[generatedFiltrationSpace X k] (fun ω ↦ fun i : Fin (k + 1) ↦ X i ω) := by
      -- Proof comment: every coordinate of the finite history already belongs to the generated
      -- history filtration up to time `k`.
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

/-- Helper for Corollary 17.10: `historyPathKernel κ k` reads the future-path kernel `κ` from the
last state of a finite history of length `k + 1`. -/
def historyPathKernel (κ : Kernel E (ℕ → E)) (k : ℕ) :
    Kernel (Fin (k + 1) → E) (ℕ → E) :=
  κ.comap (fun h : Fin (k + 1) → E ↦ h (Fin.last k)) (measurable_pi_apply (Fin.last k))

omit [MeasurableSpace Ω] in
/-- Helper for Corollary 17.10: evaluating `historyPathKernel κ k` on `pastPath X k ω` recovers
the path law started from the current state `X k ω`. -/
lemma historyPathKernel_apply_pastPath
    (X : ℕ → Ω → E) (κ : Kernel E (ℕ → E)) (k : ℕ) (ω : Ω) :
    historyPathKernel κ k (pastPath X k ω) = κ (X k ω) := by
  -- Proof comment: `historyPathKernel` only reads the last coordinate of the finite history.
  rw [historyPathKernel, Kernel.comap_apply]
  simp [pastPath_apply]

variable [StandardBorelSpace E] [Nonempty E]

omit [StandardBorelSpace E] [Nonempty E] in
/-- Helper for Corollary 17.10: every path measure is the projective limit of its finite
restriction marginals. -/
lemma pathMeasureNat_isProjectiveLimit_restrictions
    (ν : Measure (ℕ → E)) :
    MeasureTheory.IsProjectiveLimit ν (fun J : Finset ℕ ↦ ν.map J.restrict) := by
  -- Proof comment: the defining property of a projective limit is exactly that each finite
  -- restriction marginal is the prescribed pushforward.
  intro J
  rfl

/-- Helper for Corollary 17.10: reindexing the ordered tuple attached to `J.orderEmbOfFin`
recovers the ordinary finite restriction map on path space. -/
lemma piCongrLeft_orderEmbOfFin_eq_restrict
    (J : Finset ℕ) (y : ℕ → E) :
    let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
    let t : Fin J.card → ℕ := J.orderEmbOfFin rfl
    (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) (fun i ↦ y (t i)) = J.restrict y := by
  -- Proof comment: the order isomorphism `Fin J.card ≃ J` turns the sorted tuple coordinates back
  -- into the usual finite restriction map.
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

/-- Helper for Corollary 17.10: evaluating a composed kernel against a restricted pushforward is
the same as integrating the row masses over the source event. -/
lemma kernelComp_restrictMap_real_eq_setIntegral
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

/-- Helper for Corollary 17.10: Theorem 17.9 gives the conditional law of every finite future
restriction on history events. -/
lemma futurePathRestrictionIndicator_condExp
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) (J : Finset ℕ) {A : Set (J → E)} (hA : MeasurableSet A) :
    ((P x : Measure Ω)[fun ω ↦ Set.indicator A (fun _ ↦ (1 : ℝ))
        (J.restrict (futurePathNat X k ω)) | generatedFiltrationSpace X k]) =ᵐ[
      (P x : Measure Ω)] fun ω ↦ (((κ (X k ω)).map J.restrict).real A) := by
  sorry

/-- Helper for Corollary 17.10: on each history event, the restricted future-path law agrees with
the path kernel mixed against the present-state law. -/
lemma restrictedFuturePathLaw_eq_mixedPathLaw_on_history
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) {B : Set Ω} (hB : MeasurableSet[generatedFiltrationSpace X k] B) :
    let μ : Measure Ω := (P x : Measure Ω)
    let νB : Measure (ℕ → E) := (μ.restrict B).map (futurePathNat X k)
    let ρB : Measure (ℕ → E) := κ ∘ₘ ((μ.restrict B).map (X k))
    νB = ρB := by
  let μ : Measure Ω := (P x : Measure Ω)
  let νB : Measure (ℕ → E) := (μ.restrict B).map (futurePathNat X k)
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
    let futureEvent : Set Ω := (fun ω ↦ J.restrict (futurePathNat X k ω)) ⁻¹' A
    have hfuture_meas : MeasurableSet futureEvent := by
      simpa [futureEvent] using ((Finset.measurable_restrict J).comp (measurable_futurePathNat X hX_meas k)) hA
    have hIndicatorInt :
        Integrable (Set.indicator futureEvent (fun _ ↦ (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hfuture_meas
    have hmarkov :
        μ⟦futureEvent | generatedFiltrationSpace X k⟧ =ᵐ[μ]
          fun ω ↦ (((κ (X k ω)).map J.restrict).real A) := by
      -- Proof comment: the finite-restriction conditional-law formula gives the needed event mass
      -- identity on the history sigma-algebra.
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
          νB.map J.restrict = (μ.restrict B).map (fun ω ↦ J.restrict (futurePathNat X k ω)) := by
        dsimp [νB]
        rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict J).aemeasurable]
        · rfl
        · exact (measurable_futurePathNat X hX_meas k).aemeasurable
      calc
        (((νB.map J.restrict).real A))
            = ((((μ.restrict B).map (fun ω ↦ J.restrict (futurePathNat X k ω))).real A)) := by
                rw [hmapJ]
        _ = (μ.restrict B).real futureEvent := by
              simpa [futureEvent] using
                (MeasureTheory.map_measureReal_apply
                  (μ := μ.restrict B)
                  (f := fun ω ↦ J.restrict (futurePathNat X k ω))
                  ((Finset.measurable_restrict J).comp (measurable_futurePathNat X hX_meas k))
                  hA)
        _ = μ.real (futureEvent ∩ B) := by
              simpa [futureEvent] using
                (MeasureTheory.measureReal_restrict_apply (μ := μ) (s := B)
                  (t := futureEvent) hfuture_meas)
        _ = ∫ ω in B, (((κ (X k ω)).map J.restrict).real A) ∂μ := by
              simpa [futureEvent, Set.inter_comm] using hmass
    have hright_real :
        (((ρB.map J.restrict).real A)) = ∫ ω in B, (((κ (X k ω)).map J.restrict).real A) ∂μ := by
      have hmapJ :
          ρB.map J.restrict = κJ ∘ₘ ((μ.restrict B).map (X k)) := by
        dsimp [ρB, κJ]
        simpa using Measure.map_comp (((μ.restrict B).map (X k))) κ (Finset.measurable_restrict J)
      calc
        (((ρB.map J.restrict).real A))
            = ((κJ ∘ₘ ((μ.restrict B).map (X k))).real A) := by rw [hmapJ]
        _ = ∫ ω in B, (κJ (X k ω)).real A ∂μ := by
              simpa [κJ] using
                (kernelComp_restrictMap_real_eq_setIntegral
                  (κ := κJ) (μ := μ) (hY := hX_meas k) hB_ambient hA)
        _ = ∫ ω in B, (((κ (X k ω)).map J.restrict).real A) ∂μ := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
              have hrow : κJ (X k ω) = (κ (X k ω)).map J.restrict := by
                simpa [κJ] using Kernel.map_apply κ (Finset.measurable_restrict J) (X k ω)
              exact congrArg (fun ν : Measure (J → E) ↦ ν.real A) hrow
    exact
      (MeasureTheory.measureReal_eq_measureReal_iff
        (μ := νB.map J.restrict) (ν := ρB.map J.restrict) (s := A) (t := A)).mp
        (hleft_real.trans hright_real.symm)
  have hν :
      MeasureTheory.IsProjectiveLimit νB (fun J : Finset ℕ ↦ νB.map J.restrict) := by
    simpa [νB] using pathMeasureNat_isProjectiveLimit_restrictions νB
  have hρ :
      MeasureTheory.IsProjectiveLimit ρB (fun J : Finset ℕ ↦ ρB.map J.restrict) := by
    simpa [ρB] using pathMeasureNat_isProjectiveLimit_restrictions ρB
  have hρ' :
      MeasureTheory.IsProjectiveLimit ρB (fun J : Finset ℕ ↦ νB.map J.restrict) := by
    intro J
    exact (hJ J).symm
  haveI : ∀ J : Finset ℕ, IsFiniteMeasure (νB.map J.restrict) := fun _ ↦ inferInstance
  exact MeasureTheory.IsProjectiveLimit.unique hν hρ'

/-- Helper for Corollary 17.10: the discrete-time Markov owner gives the full future-path
conditional-expectation formula for bounded measurable path functionals. -/
lemma futurePathCondExp_of_markovProcessNat
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) (g : (ℕ → E) → ℝ) (hg_meas : Measurable g)
    (hg_bdd : Bornology.IsBounded (Set.range g)) :
    ((P x : Measure Ω)[fun ω ↦ g (futurePathNat X k ω) | generatedFiltrationSpace X k]) =ᵐ[
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
  have hfuture_meas : Measurable (futurePathNat X k) := measurable_futurePathNat X hX_meas k
  have hg_int :
      Integrable (fun ω ↦ g (futurePathNat X k ω)) μ := by
    obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range g) hg_bdd
    -- Proof comment: bounded measurable path test functions are integrable under the start law.
    refine Integrable.of_bound (hg_meas.comp hfuture_meas).aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun ω ↦ hC _ ⟨futurePathNat X k ω, rfl⟩
  have hXk_generated : Measurable[generatedFiltrationSpace X k] (X k) := by
    -- Proof comment: the present state is the last coordinate of the finite history map.
    rw [generatedFiltrationSpace_eq_pastPath_comap X k]
    have hCoord :
        Measurable[MeasurableSpace.comap (pastPath X k) inferInstance]
          (fun ω ↦ pastPath X k ω (Fin.last k)) := by
      exact (measurable_pi_apply (Fin.last k)).comp (comap_measurable (pastPath X k))
    simpa [pastPath] using hCoord
  have hKernelIntegral_meas :
      Measurable fun z : E ↦ ∫ y, g y ∂κ z := by
    -- Proof comment: integrating a measurable real-valued path functional against a Markov kernel
    -- is measurable in the starting state.
    exact
      (hg_meas.stronglyMeasurable.integral_kernel :
        StronglyMeasurable fun z : E ↦ ∫ y, g y ∂κ z).measurable
  have hKernelIntegral_meas_generated :
      Measurable[generatedFiltrationSpace X k] fun ω ↦ ∫ y, g y ∂κ (X k ω) := by
    -- Proof comment: compose the measurable kernel integral with the present-state map, which is
    -- already history-measurable.
    exact hKernelIntegral_meas.comp hXk_generated
  have hKernelIntegral_meas_ambient :
      Measurable fun ω ↦ ∫ y, g y ∂κ (X k ω) := by
    -- Proof comment: the same kernel integral is also ambient measurable after composing with the
    -- measurable present-state map.
    exact hKernelIntegral_meas.comp (hX_meas k)
  obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range g) hg_bdd
  have hCondExp :
      (fun ω ↦ ∫ y, g y ∂κ (X k ω)) =ᵐ[μ]
        μ[fun ω ↦ g (futurePathNat X k ω) | generatedFiltrationSpace X k] := by
    exact MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hgenerated_le hg_int
      (fun s hs hμs ↦ by
        -- Proof comment: the kernel-integral candidate is bounded on every finite history event,
        -- so it is integrable there.
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
        -- Proof comment: on each history event `s`, identify the two restricted future-path laws
        -- and then rewrite both sides as integrals of `g` against the same path measure.
        let νB : Measure (ℕ → E) := (μ.restrict s).map (futurePathNat X k)
        let ρB : Measure (ℕ → E) := κ ∘ₘ ((μ.restrict s).map (X k))
        have hs_history : MeasurableSet[generatedFiltrationSpace X k] s := hs
        have hlaw : νB = ρB := by
          simpa [μ, νB, ρB] using
            restrictedFuturePathLaw_eq_mixedPathLaw_on_history X P κ hX_meas hX0 hpath x k hs_history
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
            ∫ ω in s, g (futurePathNat X k ω) ∂μ = ∫ y, g y ∂νB := by
          change ∫ ω, g (futurePathNat X k ω) ∂(μ.restrict s) = ∫ y, g y ∂νB
          rw [show νB = (μ.restrict s).map (futurePathNat X k) by rfl]
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


/-- Helper for Corollary 17.10: the rectangle mass of the joint law of `(pastPath X k, futurePathNat
X k)` is the history integral of the row kernel obtained from the current state. -/
lemma jointLawPastFuture_realProd_eq_historyIntegral
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) {hs : Set (Fin (k + 1) → E)} {t : Set (ℕ → E)}
    (hs_meas : MeasurableSet hs) (ht_meas : MeasurableSet t) :
    let μ : Measure Ω := (P x : Measure Ω)
    let H : Ω → Fin (k + 1) → E := pastPath X k
    let Y : Ω → ℕ → E := futurePathNat X k
    let ηk : Kernel (Fin (k + 1) → E) (ℕ → E) := historyPathKernel κ k
    (μ.map (fun ω ↦ (H ω, Y ω))).real (hs ×ˢ t) =
      ∫ ω in H ⁻¹' hs, (ηk (H ω)).real t ∂μ := by
  set μ : Measure Ω := (P x : Measure Ω)
  set H : Ω → Fin (k + 1) → E := pastPath X k
  set Y : Ω → ℕ → E := futurePathNat X k
  set ηk : Kernel (Fin (k + 1) → E) (ℕ → E) := historyPathKernel κ k
  have hH_meas : Measurable H := by
    -- Proof comment: the past path is measurable because each coordinate `X i` is measurable.
    simpa [H] using measurable_pastPath X hX_meas k
  have hY_meas : Measurable Y := by
    -- Proof comment: the future path is measurable by the coordinatewise measurability of `X`.
    simpa [Y] using measurable_futurePathNat X hX_meas k
  have hPair_meas : Measurable (fun ω ↦ (H ω, Y ω)) := by
    -- Proof comment: the joint map of past and future paths is measurable coordinatewise.
    exact Measurable.prodMk hH_meas hY_meas
  have hPathMap_meas : Measurable (fun ω ↦ fun n : ℕ ↦ X n ω) := by
    refine measurable_pi_lambda _ fun n ↦ ?_
    simpa using hX_meas n
  letI : IsMarkovKernel κ := by
    refine ⟨fun y : E ↦ ?_⟩
    rw [hpath y]
    exact Measure.isProbabilityMeasure_map hPathMap_meas.aemeasurable
  let g : (ℕ → E) → ℝ := Set.indicator t fun _ ↦ (1 : ℝ)
  have hg_meas : Measurable g := by
    -- Proof comment: the rectangle test function is the measurable indicator of `t`.
    exact Measurable.indicator measurable_const ht_meas
  have hg_bdd : Bornology.IsBounded (Set.range g) := by
    have h01 : Set.range g ⊆ ({(0 : ℝ)} ∪ ({(1 : ℝ)} : Set ℝ)) := by
      intro r hr
      rcases hr with ⟨y, rfl⟩
      by_cases hy : y ∈ t
      · right
        simp [g, hy]
      · left
        simp [g, hy]
    have hBound01 : Bornology.IsBounded (({(0 : ℝ)} : Set ℝ) ∪ ({(1 : ℝ)} : Set ℝ)) :=
      Bornology.IsBounded.union Bornology.isBounded_singleton Bornology.isBounded_singleton
    exact hBound01.subset h01
  have hg_int : Integrable (fun ω ↦ g (Y ω)) μ := by
    -- Proof comment: the indicator test is bounded by `1`, so it is integrable under the
    -- finite start law `μ`.
    refine Integrable.of_bound (hg_meas.comp hY_meas).aestronglyMeasurable 1 ?_
    exact ae_of_all _ fun ω ↦ by
      by_cases hω : Y ω ∈ t <;> simp [g, hω]
  have hFiltration_le : generatedFiltrationSpace X k ≤ ‹MeasurableSpace Ω› := by
    rw [generatedFiltrationSpace_eq_pastPath_comap X k]
    exact (measurable_pastPath X hX_meas k).comap_le
  have hHistory_meas :
      MeasurableSet[generatedFiltrationSpace X k] (H ⁻¹' hs) := by
    -- Proof comment: history rectangles are measurable in the generated filtration because that
    -- filtration is the pullback sigma-algebra of `pastPath`.
    rw [generatedFiltrationSpace_eq_pastPath_comap X k]
    exact hs_meas.preimage (comap_measurable H)
  have hFuture :
      μ[fun ω ↦ g (Y ω) | generatedFiltrationSpace X k] =ᵐ[μ]
        fun ω ↦ ∫ y, g y ∂κ (X k ω) := by
    -- Proof comment: the forward branch now delegates the full-path conditional expectation to
    -- the local discrete-time helper built from Theorem 17.9.
    simpa [μ, Y] using
      futurePathCondExp_of_markovProcessNat X P κ hX_meas hX0 hpath x k g hg_meas hg_bdd
  -- Proof comment: test the future-path conditional-expectation formula on the indicator of `t`
  -- and rewrite both sides as real masses of measurable rectangles.
  calc
    (μ.map (fun ω ↦ (H ω, Y ω))).real (hs ×ˢ t)
        = μ.real ((fun ω ↦ (H ω, Y ω)) ⁻¹' (hs ×ˢ t)) := by
          simpa using
            (MeasureTheory.map_measureReal_apply
              (μ := μ) (f := fun ω ↦ (H ω, Y ω)) hPair_meas (hs_meas.prod ht_meas))
    _ = μ.real (H ⁻¹' hs ∩ Y ⁻¹' t) := by
      rfl
    _ = ∫ ω in H ⁻¹' hs, g (Y ω) ∂μ := by
      symm
      calc
        ∫ ω in H ⁻¹' hs, g (Y ω) ∂μ = ∫ ω, g (Y ω) ∂μ.restrict (H ⁻¹' hs) := rfl
        _ = ∫ ω, Set.indicator (Y ⁻¹' t) (fun _ ↦ (1 : ℝ)) ω ∂μ.restrict (H ⁻¹' hs) := by
          refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
          by_cases hω : Y ω ∈ t <;> simp [g, hω]
        _ = (μ.restrict (H ⁻¹' hs)).real (Y ⁻¹' t) := by
          simpa using
            (MeasureTheory.integral_indicator_one
              (μ := μ.restrict (H ⁻¹' hs)) (s := Y ⁻¹' t) (hY_meas ht_meas))
        _ = μ.real (Y ⁻¹' t ∩ H ⁻¹' hs) := by
          rw [MeasureTheory.measureReal_restrict_apply
            (μ := μ) (s := H ⁻¹' hs) (t := Y ⁻¹' t) (hY_meas ht_meas)]
        _ = μ.real (H ⁻¹' hs ∩ Y ⁻¹' t) := by
          rw [Set.inter_comm]
    _ = ∫ ω in H ⁻¹' hs, ∫ y, g y ∂κ (X k ω) ∂μ := by
      calc
        ∫ ω in H ⁻¹' hs, g (Y ω) ∂μ
            = ∫ ω in H ⁻¹' hs,
                (μ[fun ω ↦ g (Y ω) | generatedFiltrationSpace X k]) ω ∂μ := by
                  symm
                  exact MeasureTheory.setIntegral_condExp hFiltration_le hg_int hHistory_meas
        _ = ∫ ω in H ⁻¹' hs, ∫ y, g y ∂κ (X k ω) ∂μ := by
          refine integral_congr_ae ?_
          exact ae_restrict_of_ae hFuture
    _ = ∫ ω in H ⁻¹' hs, (ηk (H ω)).real t ∂μ := by
      refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
      calc
        ∫ y, g y ∂κ (X k ω) = (κ (X k ω)).real t := by
          simpa [g] using
            (MeasureTheory.integral_indicator_one (μ := κ (X k ω)) (s := t) ht_meas)
        _ = (ηk (H ω)).real t := by
          have hη_eval : ηk (H ω) = κ (X k ω) := by
            simpa [ηk, H] using historyPathKernel_apply_pastPath X κ k ω
          rw [hη_eval]

omit [StandardBorelSpace E] [Nonempty E] in
/-- Helper for Corollary 17.10: the rectangle mass of the composition product
`μ.map (pastPath X k) ⊗ₘ ηk` is the same history integral as on the joint-law side. -/
lemma compProdHistoryKernel_realProd_eq_historyIntegral
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    (x : E) (k : ℕ) {hs : Set (Fin (k + 1) → E)} {t : Set (ℕ → E)}
    (hs_meas : MeasurableSet hs) (ht_meas : MeasurableSet t) :
    let μ : Measure Ω := (P x : Measure Ω)
    let H : Ω → Fin (k + 1) → E := pastPath X k
    let ηk : Kernel (Fin (k + 1) → E) (ℕ → E) := historyPathKernel κ k
    (μ.map H ⊗ₘ ηk).real (hs ×ˢ t) =
      ∫ ω in H ⁻¹' hs, (ηk (H ω)).real t ∂μ := by
  set μ : Measure Ω := (P x : Measure Ω)
  set H : Ω → Fin (k + 1) → E := pastPath X k
  set ηk : Kernel (Fin (k + 1) → E) (ℕ → E) := historyPathKernel κ k
  have hH_meas : Measurable H := by
    -- Proof comment: the history map is measurable by the coordinatewise measurability of `X`.
    simpa [H] using measurable_pastPath X hX_meas k
  have hPathMap_meas : Measurable (fun ω ↦ fun n : ℕ ↦ X n ω) := by
    refine measurable_pi_lambda _ fun n ↦ ?_
    simpa using hX_meas n
  letI : IsMarkovKernel κ := by
    refine ⟨fun y : E ↦ ?_⟩
    rw [hpath y]
    exact Measure.isProbabilityMeasure_map hPathMap_meas.aemeasurable
  letI : IsMarkovKernel ηk := by
    dsimp [ηk, historyPathKernel]
    infer_instance
  letI : IsFiniteKernel ηk := inferInstance
  have hrow_meas : Measurable fun h ↦ (ηk h).real t := by
    -- Proof comment: row masses on a measurable set vary measurably with the history parameter.
    exact (ηk.measurable_coe ht_meas).ennreal_toReal
  -- Proof comment: compute the rectangle mass of the composition product by Fubini and then pull
  -- the outer history integral back along `H`.
  calc
    (μ.map H ⊗ₘ ηk).real (hs ×ˢ t)
        = ∫ z in hs ×ˢ t, (1 : ℝ) ∂(μ.map H ⊗ₘ ηk) := by
          symm
          exact MeasureTheory.setIntegral_one_eq_measureReal
    _ = ∫ h in hs, ∫ y in t, (1 : ℝ) ∂ηk h ∂(μ.map H) := by
          have hone : Integrable (fun _ : (Fin (k + 1) → E) × (ℕ → E) ↦ (1 : ℝ))
              (μ.map H ⊗ₘ ηk) := by
            simp
          exact MeasureTheory.Measure.setIntegral_compProd hs_meas ht_meas hone.integrableOn
    _ = ∫ h in hs, (ηk h).real t ∂(μ.map H) := by
          refine integral_congr_ae <| Filter.Eventually.of_forall fun h ↦ ?_
          simp
    _ = ∫ ω in H ⁻¹' hs, (ηk (H ω)).real t ∂μ := by
          exact MeasureTheory.setIntegral_map hs_meas hrow_meas.aestronglyMeasurable
            hH_meas.aemeasurable

lemma map_pastFuture_eq_map_past_compProd_pathKernel
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ] :
    ∀ x k,
      let μ : Measure Ω := (P x : Measure Ω)
      let H : Ω → Fin (k + 1) → E := pastPath X k
      let Y : Ω → ℕ → E := futurePathNat X k
      let ηk : Kernel (Fin (k + 1) → E) (ℕ → E) := historyPathKernel κ k
      μ.map (fun ω ↦ (H ω, Y ω)) = μ.map H ⊗ₘ ηk := by
  intro x k
  -- Proof comment: compare both measures on measurable rectangles and invoke product-measure
  -- extensionality once the rectangle masses are identified with the same history integral.
  have hPathMap_meas : Measurable (fun ω ↦ fun n : ℕ ↦ X n ω) := by
    refine measurable_pi_lambda _ fun n ↦ ?_
    simpa using hX_meas n
  letI : IsMarkovKernel κ := by
    refine ⟨fun y : E ↦ ?_⟩
    rw [hpath y]
    exact Measure.isProbabilityMeasure_map hPathMap_meas.aemeasurable
  letI : IsMarkovKernel (historyPathKernel κ k) := by
    dsimp [historyPathKernel]
    infer_instance
  letI : IsFiniteKernel (historyPathKernel κ k) := inferInstance
  refine Measure.ext_prod ?_
  intro hs t hs_meas ht_meas
  have hreal :
      ((P x : Measure Ω).map (fun ω ↦ (pastPath X k ω, futurePathNat X k ω))).real (hs ×ˢ t) =
        (((P x : Measure Ω).map (pastPath X k) ⊗ₘ historyPathKernel κ k).real (hs ×ˢ t)) := by
    calc
      ((P x : Measure Ω).map (fun ω ↦ (pastPath X k ω, futurePathNat X k ω))).real (hs ×ˢ t)
          = ∫ ω in (pastPath X k) ⁻¹' hs,
              ((historyPathKernel κ k (pastPath X k ω)).real t) ∂(P x : Measure Ω) := by
                simpa using
                  (jointLawPastFuture_realProd_eq_historyIntegral X P κ hX_meas hX0 hpath x k
                    hs_meas ht_meas)
      _ = (((P x : Measure Ω).map (pastPath X k) ⊗ₘ historyPathKernel κ k).real (hs ×ˢ t)) := by
            symm
            simpa using
              (compProdHistoryKernel_realProd_eq_historyIntegral X P κ hX_meas hpath x k hs_meas
                ht_meas)
  exact
    (measureReal_eq_measureReal_iff
      (μ := (P x : Measure Ω).map (fun ω ↦ (pastPath X k ω, futurePathNat X k ω)))
      (ν := (P x : Measure Ω).map (pastPath X k) ⊗ₘ historyPathKernel κ k)
      (s := hs ×ˢ t) (t := hs ×ˢ t)).mp hreal

/-- Helper for Corollary 17.10: once the future-path conditional-expectation formula is known,
`condDistrib` uniqueness identifies the future-path conditional law with the path kernel started at
the current state. -/
lemma condDistrib_futurePath_eq_pathKernel_of_isTimeHomogeneousMarkovProcess
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ] :
    ∀ x k,
      (fun ω ↦ condDistrib (futurePathNat X k) (pastPath X k) (P x : Measure Ω)
        (pastPath X k ω)) =ᵐ[(P x : Measure Ω)] fun ω ↦ κ (X k ω) := by
  intro x k
  set μ : Measure Ω := (P x : Measure Ω)
  set H : Ω → Fin (k + 1) → E := pastPath X k
  set Y : Ω → ℕ → E := futurePathNat X k
  set ηk : Kernel (Fin (k + 1) → E) (ℕ → E) := historyPathKernel κ k
  have hH_meas : Measurable H := by
    -- Proof comment: the conditioning map is the measurable finite history.
    simpa [H] using measurable_pastPath X hX_meas k
  have hY_meas : Measurable Y := by
    -- Proof comment: the response variable is the measurable future path.
    simpa [Y] using measurable_futurePathNat X hX_meas k
  letI : IsMarkovKernel κ := by
    have hPathMap_meas : Measurable (fun ω ↦ fun n : ℕ ↦ X n ω) := by
      refine measurable_pi_lambda _ fun n ↦ ?_
      simpa using hX_meas n
    refine ⟨fun y : E ↦ ?_⟩
    rw [hpath y]
    exact Measure.isProbabilityMeasure_map hPathMap_meas.aemeasurable
  letI : IsMarkovKernel ηk := by
    dsimp [ηk, historyPathKernel]
    infer_instance
  letI : IsFiniteKernel ηk := inferInstance
  have hcond :
      condDistrib Y H μ =ᵐ[μ.map H] ηk := by
    -- Proof comment: the joint-law factorization identifies `ηk` as the conditional law of the
    -- future path given the past path.
    have hfactorization :
        μ.map (fun ω ↦ (H ω, Y ω)) = μ.map H ⊗ₘ ηk := by
      simpa [μ, H, Y, ηk] using
        (map_pastFuture_eq_map_past_compProd_pathKernel X P κ hX_meas hX0 hpath x k)
    exact
      ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
        hH_meas hY_meas hfactorization
  have hpull :
      (fun ω ↦ condDistrib Y H μ (H ω)) =ᵐ[μ] fun ω ↦ ηk (H ω) :=
    MeasureTheory.ae_eq_comp hH_meas.aemeasurable hcond
  -- Proof comment: pull the a.e. equality back from history space to `Ω`, then collapse the
  -- deterministic history kernel to the current-state path law.
  filter_upwards [hpull] with ω hω
  have hη_eval : ηk (H ω) = κ (X k ω) := by
    simpa [ηk, H] using historyPathKernel_apply_pastPath X κ k ω
  simpa [μ, H, Y, hη_eval] using hω

/-- Helper for Corollary 17.10: the path-level conditional-distribution identity implies the
owner Markov property via Theorem 17.9. -/
lemma isTimeHomogeneousMarkovProcess_of_condDistrib_futurePath_eq_pathKernel
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    (hCond :
      ∀ x k,
        (fun ω ↦ condDistrib (futurePathNat X k) (pastPath X k) (P x : Measure Ω)
          (pastPath X k ω)) =ᵐ[(P x : Measure Ω)] fun ω ↦ κ (X k ω)) :
    IsTimeHomogeneousMarkovProcess X P κ := by
  sorry

-- Proof sketch: the forward direction upgrades the coordinate-wise Markov property to equality of
-- regular conditional distributions on path space by testing cylinder sets; the converse tests the
-- equality of conditional path laws on one-coordinate cylinders.
/-- Corollary 17.10: under the canonical path-law kernel
`κ x = 𝓛_x[(X_n)_{n \in \mathbb{N}_0}]`, a discrete-time process is a Markov chain if and only if
for every `k` the regular conditional law of its future path `(X_{n+k})_n` given the finite
history `(X_0, \ldots, X_k)` agrees almost surely with the path law started from the present state
`X_k`. -/
theorem isTimeHomogeneousMarkovProcess_iff_condDistrib_futurePath_eq_pathKernel
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω)) :
    IsTimeHomogeneousMarkovProcess X P κ ↔
      ∀ x k,
        (fun ω ↦ condDistrib (futurePathNat X k) (pastPath X k) (P x : Measure Ω)
          (pastPath X k ω)) =ᵐ[(P x : Measure Ω)] fun ω ↦ κ (X k ω) := by
  constructor
  · intro hMarkov
    letI : IsTimeHomogeneousMarkovProcess X P κ := hMarkov
    -- Route correction: the forward implication now routes through a local discrete-time
    -- full-path helper, not the mismatched add-submonoid theorem from Theorem 17.14.
    exact
      condDistrib_futurePath_eq_pathKernel_of_isTimeHomogeneousMarkovProcess
        X P κ hX_meas hX0 hpath
  · intro hCond
    -- Proof comment: the assumed path-kernel identity is stronger than Theorem 17.9's
    -- conditional-expectation hypothesis, so the existing implication yields the owner property.
    exact isTimeHomogeneousMarkovProcess_of_condDistrib_futurePath_eq_pathKernel
      X P κ hX_meas hX0 hpath hCond

end ProbabilityTheory
