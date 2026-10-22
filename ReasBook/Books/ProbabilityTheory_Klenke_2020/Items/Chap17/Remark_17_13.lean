/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Lemma_9_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_9

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Helper for Remark 17.13: for a measurable discrete-time process, the ambient-history
filtration `processFiltration X` collapses to the generated filtration `generatedFiltration X hX`.
-/
lemma processFiltration_eq_generatedFiltration
    (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n)) :
    processFiltration X = generatedFiltration X hX := by
  apply Filtration.ext
  funext n
  -- Proof comment: measurability of each coordinate shows that the ambient infimum in
  -- `processFiltration` is redundant.
  simpa [processFiltration, generatedFiltration_apply] using
    inf_eq_right.mpr ((generatedFiltration X hX).le n)

/-- Helper for Remark 17.13: a measurable process is adapted to its own generated filtration. -/
lemma adapted_generatedFiltration_of_measurable
    (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n)) :
    Adapted (generatedFiltration X hX) X := by
  intro n
  -- Proof comment: the time-`n` coordinate is one of the generators of the time-`n`
  -- generated filtration.
  refine Measurable.of_comap_le ?_
  rw [generatedFiltration_apply]
  exact le_iSup_of_le n <| le_iSup_of_le le_rfl le_rfl

-- Proof sketch: specialize Definition 17.12 to the `ℕ`-valued stopping time
-- `fun ω ↦ (τ ω : WithTop ℕ)` and use that this stopping time never takes the value `⊤`.
/-- For an `ℕ`-valued stopping time, the canonical future path after stopping from
Definition 17.12 is the explicit shifted path `n ↦ X (τ + n)`. -/
theorem futurePathAfterStoppingTime_coe_apply
    (X : ℕ → Ω → E) (τ : Ω → ℕ) (ω : Ω) (n : ℕ) :
    futurePathAfterStoppingTime X (fun ω ↦ (τ ω : WithTop ℕ)) ω n = X (τ ω + n) ω := by
  -- Proof comment: the coerced stopping time is never `⊤`, so the generic stopped-future formula
  -- reduces to the explicit discrete-time shift.
  simpa using
    futurePathAfterStoppingTime_apply_of_ne_top X (fun ω ↦ (τ ω : WithTop ℕ)) ω n
      (by simp)

/-- Helper for Remark 17.13: for an `ℕ`-valued stopping time, the stopped state is the present
process value `X (τ ω) ω`. -/
lemma stoppedValue_coe_eq
    (X : ℕ → Ω → E) (τ : Ω → ℕ) (ω : Ω) :
    stoppedValue X (fun ω ↦ (τ ω : WithTop ℕ)) ω = X (τ ω) ω := by
  -- Proof comment: after unfolding `stoppedValue`, the finite stopping time value is read off
  -- directly from the coercion `ℕ → WithTop ℕ`.
  have hne : ((τ ω : WithTop ℕ)) ≠ ⊤ := by simp
  have huntop : ((τ ω : WithTop ℕ)).untop hne = τ ω := by
    exact WithTop.coe_inj.mp (WithTop.coe_untop (x := (τ ω : WithTop ℕ)) hne)
  rw [stoppedValue, WithTop.untopA_eq_untop hne, huntop]

/-- Helper for Remark 17.13: the post-stopping path of a measurable discrete-time process is an
ambient measurable path-valued map. -/
lemma measurable_futurePathAfterStoppingTime_coe
    (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n)) (τ : Ω → ℕ)
    (hτ : IsStoppingTime (generatedFiltration X hX) fun ω ↦ (τ ω : WithTop ℕ)) :
    Measurable (futurePathAfterStoppingTime X (fun ω ↦ (τ ω : WithTop ℕ))) := by
  refine measurable_pi_lambda _ fun n ↦ ?_
  let lifted : Ω × ℕ → E := fun p ↦ X (p.2 + n) p.1
  have hlifted : Measurable lifted := by
    -- Proof comment: every fixed-time slice of the lifted map is one of the measurable process
    -- coordinates.
    refine measurable_from_prod_countable_left fun i ↦ ?_
    simpa [lifted] using hX (i + n)
  have hτ_meas : Measurable τ := by
    refine measurable_to_countable' fun i ↦ ?_
    have hpre :
        (fun ω ↦ (τ ω : WithTop ℕ)) ⁻¹' ({(i : WithTop ℕ)} : Set (WithTop ℕ)) =
          τ ⁻¹' ({i} : Set ℕ) := by
      ext ω
      simp
    simpa [hpre] using
      (measurableSet_singleton (x := (i : WithTop ℕ))).preimage hτ.measurable'
  have hgraph : Measurable (fun ω ↦ (ω, τ ω)) := Measurable.prodMk measurable_id hτ_meas
  have hcoord : Measurable (fun ω ↦ X (τ ω + n) ω) := by
    simpa [lifted] using hlifted.comp hgraph
  -- Proof comment: each coordinate of the stopped future path is the corresponding shifted
  -- process value.
  simpa [futurePathAfterStoppingTime_coe_apply] using hcoord

/-- Helper for Remark 17.13: on the slice `{τ = s}`, the stopped future path agrees with the
deterministic shifted path `futurePath X s`. -/
lemma futurePathAfterStoppingTime_eq_futurePath_on_timeSlice
    (X : ℕ → Ω → E) (τ : Ω → WithTop ℕ) {s : ℕ} {ω : Ω}
    (hτω : τ ω = (s : WithTop ℕ)) :
    futurePathAfterStoppingTime X τ ω = futurePath X s ω := by
  -- Proof comment: once the stopping time is fixed to the value `s`, the generic stopped-future
  -- definition is exactly the deterministic shift by `s`.
  funext t
  have hτ_ne_top : τ ω ≠ ⊤ := by
    simpa [hτω]
  have hτ_untop : (τ ω).untop hτ_ne_top = s := by
    apply WithTop.coe_injective
    simpa [hτω] using (WithTop.coe_untop (x := τ ω) hτ_ne_top)
  calc
    futurePathAfterStoppingTime X τ ω t = X ((τ ω).untop hτ_ne_top + t) ω := by
      exact futurePathAfterStoppingTime_apply_of_ne_top X τ ω t hτ_ne_top
    _ = X (s + t) ω := by
      rw [hτ_untop]
    _ = futurePath X s ω t := by
      simp [futurePath, add_comm]

/-- Helper for Remark 17.13: on the slice `{τ = s}`, the stopped present state is `X s`. -/
lemma stoppedValue_eq_on_timeSlice
    (X : ℕ → Ω → E) (τ : Ω → WithTop ℕ) {s : ℕ} {ω : Ω}
    (hτω : τ ω = (s : WithTop ℕ)) :
    stoppedValue X τ ω = X s ω := by
  -- Proof comment: after rewriting `τ ω` to the finite time `s`, `stoppedValue` becomes the
  -- ordinary process value at time `s`.
  have hτ_ne_top : τ ω ≠ ⊤ := by
    simpa [hτω]
  have hτ_untop : (τ ω).untop hτ_ne_top = s := by
    apply WithTop.coe_injective
    simpa [hτω] using (WithTop.coe_untop (x := τ ω) hτ_ne_top)
  rw [stoppedValue, WithTop.untopA_eq_untop hτ_ne_top, hτ_untop]

/-- Helper for Remark 17.13: bounded measurable path functionals remain measurable after
composition with the stopped future path of a measurable discrete-time process. -/
lemma measurable_stoppedFutureFunctional
    (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n))
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime (processFiltration X) τ)
    (f : (ℕ → E) → ℝ) (hf_meas : Measurable f) :
    Measurable (fun ω ↦ f (futurePathAfterStoppingTime X τ ω)) := by
  let lifted : Ω × ℕ → ℝ := fun p ↦ f (fun t ↦ X (p.2 + t) p.1)
  have hlifted_meas : Measurable lifted := by
    -- Proof comment: the stopped-time value ranges over a countable time index, so measurability
    -- reduces to the measurable deterministic slices `ω ↦ f (futurePath X n ω)`.
    refine measurable_from_prod_countable_left fun n ↦ ?_
    have hslice :
        (fun ω ↦ lifted (ω, n)) = f ∘ futurePath X n := by
      funext ω
      change f (fun t ↦ X (n + t) ω) = f (futurePath X n ω)
      congr
      funext t
      simp [futurePath, add_comm]
    rw [hslice]
    exact hf_meas.comp (measurable_futurePath X hX n)
  have hτ_untopA_meas : Measurable fun ω ↦ (τ ω).untopA := by
    exact (measurable_of_countable fun t : WithTop ℕ ↦ t.untopA).comp hτ.measurable'
  have hgraph_meas : Measurable fun ω ↦ (ω, (τ ω).untopA) := by
    exact Measurable.prodMk measurable_id hτ_untopA_meas
  -- Proof comment: compose the measurable slice family with the measurable graph
  -- `ω ↦ (ω, (τ ω).untopA)`.
  simpa [lifted, futurePathAfterStoppingTime, stoppedValue] using hlifted_meas.comp hgraph_meas

/-- Helper for Remark 17.13: bounded measurable functionals of the stopped future path are
integrable under each start law `P x`. -/
lemma integrable_stoppedFutureFunctional
    (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n))
    (P : E → ProbabilityMeasure Ω) (x : E)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime (processFiltration X) τ)
    (f : (ℕ → E) → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ C : ℝ, ∀ y, |f y| ≤ C) :
    Integrable (fun ω ↦ f (futurePathAfterStoppingTime X τ ω)) (P x : Measure Ω) := by
  rcases hf_bdd with ⟨C, hC⟩
  -- Proof comment: the stopped-future functional is measurable, and the uniform bound coming
  -- from `f` gives the required `L¹` estimate on the probability space `(Ω, P x)`.
  refine Integrable.of_bound
    (measurable_stoppedFutureFunctional X hX τ hτ f hf_meas).aestronglyMeasurable C ?_
  exact Filter.Eventually.of_forall fun ω ↦ by
    simpa using hC (futurePathAfterStoppingTime X τ ω)

/-- Helper for Remark 17.13: evaluating a kernel composition against a restricted pushforward is
the same as integrating the corresponding row masses over the restricting set. -/
lemma kernelComp_restrictMap_real_eq_setIntegral_local
    {F : Type*} [MeasurableSpace F]
    (κ : Kernel E F) [IsMarkovKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] {Y : Ω → E} (hY : Measurable Y)
    {B : Set Ω} (_hB : MeasurableSet B) {A : Set F} (hA : MeasurableSet A) :
    ((κ ∘ₘ ((μ.restrict B).map Y)).real A) = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
  let ν : Measure E := (μ.restrict B).map Y
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

/-- Helper for Remark 17.13: every stopping-time slice `{τ = s}` is measurable for the
deterministic-time history `processFiltration X s`. -/
lemma measurableSet_timeSlice_processFiltration
    (X : ℕ → Ω → E) (τ : Ω → WithTop ℕ)
    (hτ : IsStoppingTime (processFiltration X) τ) (s : ℕ) :
    MeasurableSet[processFiltration X s] {ω | τ ω = s} := by
  have hslice_hτ :
      MeasurableSet[hτ.measurableSpace] (Set.univ ∩ {ω | τ ω = s}) := by
    simpa using hτ.measurableSet_eq_of_countable' s
  simpa using (hτ.measurableSet_inter_eq_iff Set.univ s).mp hslice_hτ

-- Proof sketch: as in Corollary 17.10, pass between the stopping-time conditional probabilities
-- of one-coordinate cylinder events and the conditional probabilities of arbitrary measurable path
-- events for the shifted process `(X_{τ+t})_t`.
/-- Remark 17.13: for a discrete-time process, with “almost surely finite” stopping times encoded
by maps `τ : Ω → ℕ`, the strong Markov property is equivalent to saying that for every stopping
time `τ` the conditional law of the post-`τ` path given the stopping-time σ-algebra agrees almost
surely with the path kernel started from the present state `X_τ`. -/
theorem hasStrongMarkovProperty_iff_conditionalFuturePathLaw_eq_pathKernel
    [StandardBorelSpace E] [Nonempty E] (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n))
    (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E)) [IsMarkovKernel κ] :
    HasStrongMarkovProperty P X κ ↔
      ∀ x (τ : Ω → ℕ),
        ∀ (hτ : IsStoppingTime (generatedFiltration X hX) fun ω ↦ (τ ω : WithTop ℕ)),
          ∀ ⦃A : Set (ℕ → E)⦄, MeasurableSet A →
            (P x)⟦futurePathAfterStoppingTime X (fun ω ↦ (τ ω : WithTop ℕ)) ⁻¹' A
              | hτ.measurableSpace⟧ =ᵐ[(P x : Measure Ω)] fun ω ↦ (κ (X (τ ω) ω)).real A := by
  constructor
  · intro hStrong x τ hτ A hA
    have hτ_process : IsStoppingTime (processFiltration X) fun ω ↦ (τ ω : WithTop ℕ) := by
      -- Proof comment: for a measurable process, `processFiltration X` and
      -- `generatedFiltration X hX` agree pointwise.
      simpa [processFiltration_eq_generatedFiltration (X := X) hX] using hτ
    have hfinite :
        ∀ᵐ ω ∂(P x : Measure Ω), (fun ω ↦ (τ ω : WithTop ℕ)) ω ≠ ⊤ := by
      -- Proof comment: an `ℕ`-valued stopping time is automatically finite.
      exact Filter.Eventually.of_forall fun ω ↦ by simp
    let f : (ℕ → E) → ℝ := Set.indicator A fun _ ↦ (1 : ℝ)
    have hf_meas : Measurable f := by
      -- Proof comment: the test functional is the measurable indicator of the measurable path
      -- event `A`.
      exact Measurable.indicator measurable_const hA
    have hf_bdd : ∃ C : ℝ, ∀ y, |f y| ≤ C := by
      -- Proof comment: the indicator test functional only takes the values `0` and `1`.
      refine ⟨1, ?_⟩
      intro y
      by_cases hy : y ∈ A
      · simp [f, hy]
      · simp [f, hy]
    have hcond :
        (P x : Measure Ω)[fun ω ↦ f (futurePathAfterStoppingTime X (fun ω ↦ (τ ω : WithTop ℕ)) ω)
            | hτ_process.measurableSpace] =ᵐ[(P x : Measure Ω)]
          fun ω ↦ ∫ y, f y ∂κ (stoppedValue X (fun ω ↦ (τ ω : WithTop ℕ)) ω) := by
      -- Proof comment: this is Definition 17.12 specialized to the indicator of `A`.
      exact (hasStrongMarkovProperty_iff P X κ).mp hStrong x _ hτ_process hfinite f hf_meas hf_bdd
    have hleft :
        (fun ω ↦ f (futurePathAfterStoppingTime X (fun ω ↦ (τ ω : WithTop ℕ)) ω)) =
          Set.indicator (futurePathAfterStoppingTime X (fun ω ↦ (τ ω : WithTop ℕ)) ⁻¹' A)
            (fun _ ↦ (1 : ℝ)) := by
      funext ω
      by_cases hω : futurePathAfterStoppingTime X (fun ω ↦ (τ ω : WithTop ℕ)) ω ∈ A
      · simp [f, hω]
      · simp [f, hω]
    have hright :
        (fun ω ↦ ∫ y, f y ∂κ (stoppedValue X (fun ω ↦ (τ ω : WithTop ℕ)) ω)) =
          fun ω ↦ (κ (X (τ ω) ω)).real A := by
      funext ω
      rw [stoppedValue_coe_eq]
      -- Proof comment: integrating the indicator of `A` against the path kernel returns the
      -- probability mass of `A`.
      simpa [f] using
        (MeasureTheory.integral_indicator_one (μ := κ (X (τ ω) ω)) hA)
    have hspace_eq : hτ_process.measurableSpace = hτ.measurableSpace := by
      simpa [processFiltration_eq_generatedFiltration (X := X) hX] using
        MeasureTheory.IsStoppingTime.measurableSpace.congr_simp
          (e_f := processFiltration_eq_generatedFiltration (X := X) hX) (e_τ := rfl) hτ_process
    -- Proof comment: after rewriting the test functional and the stopped state, the conditional
    -- expectation identity is exactly the desired conditional-law formula.
    rw [← hspace_eq]
    simpa [hleft, hright] using hcond
  · intro hLaw
    -- Route correction: the earlier direct converse route tried to turn an a.s.-finite
    -- `WithTop ℕ` stopping time into an `ℕ`-valued stopping time. The stable route is instead to
    -- extract the deterministic-time future-path conditional-expectation formula from `hLaw`
    -- using constant stopping times, and then glue the arbitrary stopping-time statement over the
    -- countable partition `{τ = s}`.
    have hFixedTime :
        ∀ x (s : ℕ) (f : (ℕ → E) → ℝ),
          Measurable f →
          (∃ C : ℝ, ∀ y, |f y| ≤ C) →
          ((P x : Measure Ω)[fun ω ↦ f (futurePath X s ω) | processFiltration X s]) =ᵐ[
            (P x : Measure Ω)] fun ω ↦ ∫ y, f y ∂κ (X s ω) := by
      intro x s f hf_meas hf_bdd
      let μ : Measure Ω := (P x : Measure Ω)
      let τs : Ω → ℕ := fun _ ↦ s
      have hτs :
          IsStoppingTime (generatedFiltration X hX) fun ω ↦ (τs ω : WithTop ℕ) := by
        simpa [τs] using isStoppingTime_const (generatedFiltration X hX) s
      have hspace_eq : hτs.measurableSpace = generatedFiltration X hX s := by
        simpa [τs] using MeasureTheory.IsStoppingTime.measurableSpace_const
          (generatedFiltration X hX) s
      have hfuture_eq :
          futurePathAfterStoppingTime X (fun ω ↦ (τs ω : WithTop ℕ)) = futurePath X s := by
        funext ω
        funext n
        simp [futurePathAfterStoppingTime_coe_apply, futurePath, τs, add_comm]
      have hLawConst :
          ∀ ⦃A : Set (ℕ → E)⦄, MeasurableSet A →
            μ⟦futurePath X s ⁻¹' A | generatedFiltration X hX s⟧ =ᵐ[μ]
              fun ω ↦ (κ (X s ω)).real A := by
        intro A hA
        simpa [μ, hspace_eq, hfuture_eq] using hLaw x τs hτs hA
      have hgenerated_le : generatedFiltration X hX s ≤ ‹MeasurableSpace Ω› :=
        (generatedFiltration X hX).le s
      have hfuture_meas : Measurable (futurePath X s) := measurable_futurePath X hX s
      obtain ⟨C, hC⟩ := hf_bdd
      have hf_int : Integrable (fun ω ↦ f (futurePath X s ω)) μ := by
        -- Proof comment: bounded measurable path functionals are integrable under the start law.
        refine Integrable.of_bound (hf_meas.comp hfuture_meas).aestronglyMeasurable C ?_
        exact Filter.Eventually.of_forall fun ω ↦ hC (futurePath X s ω)
      have hXs_generated : Measurable[generatedFiltration X hX s] (X s) :=
        adapted_generatedFiltration_of_measurable X hX s
      have hKernelIntegral_meas : Measurable fun z : E ↦ ∫ y, f y ∂κ z := by
        -- Proof comment: kernel integration of a measurable real-valued path functional is
        -- measurable in the starting state.
        exact
          (hf_meas.stronglyMeasurable.integral_kernel :
            StronglyMeasurable fun z : E ↦ ∫ y, f y ∂κ z).measurable
      have hKernelIntegral_meas_generated :
          Measurable[generatedFiltration X hX s] fun ω ↦ ∫ y, f y ∂κ (X s ω) := by
        -- Proof comment: compose the measurable kernel integral with the present-state map `X s`,
        -- which is measurable for the time-`s` history sigma-algebra.
        exact hKernelIntegral_meas.comp hXs_generated
      have hKernelIntegral_meas_ambient :
          Measurable fun ω ↦ ∫ y, f y ∂κ (X s ω) := by
        exact hKernelIntegral_meas.comp (hX s)
      have hRestrictedLaw :
          ∀ ⦃B : Set Ω⦄, MeasurableSet[generatedFiltration X hX s] B →
            ((μ.restrict B).map (futurePath X s)) = κ ∘ₘ ((μ.restrict B).map (X s)) := by
        intro B hB
        have hB_ambient : MeasurableSet B := hgenerated_le B hB
        refine Measure.ext fun A hA ↦ ?_
        have hfutureEvent_meas : MeasurableSet ((futurePath X s) ⁻¹' A) :=
          hfuture_meas hA
        have hindicator_int :
            Integrable (fun ω ↦ Set.indicator A (fun _ ↦ (1 : ℝ)) (futurePath X s ω)) μ := by
          refine Integrable.of_bound
            ((Measurable.indicator measurable_const hA).comp hfuture_meas).aestronglyMeasurable 1
            ?_
          exact Filter.Eventually.of_forall fun ω ↦ by
            by_cases hω : futurePath X s ω ∈ A
            · simp [hω]
            · simp [hω]
        have hmass :
            μ.real ((futurePath X s) ⁻¹' A ∩ B) =
              ∫ ω in B, (κ (X s ω)).real A ∂μ := by
          calc
            μ.real ((futurePath X s) ⁻¹' A ∩ B)
                = ∫ ω in B, Set.indicator A (fun _ ↦ (1 : ℝ)) (futurePath X s ω) ∂μ := by
                    symm
                    calc
                      ∫ ω in B, Set.indicator A (fun _ ↦ (1 : ℝ)) (futurePath X s ω) ∂μ
                          = ∫ ω in B,
                              Set.indicator ((futurePath X s) ⁻¹' A) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
                                refine MeasureTheory.integral_congr_ae <|
                                  Filter.Eventually.of_forall fun ω ↦ ?_
                                by_cases hω : futurePath X s ω ∈ A
                                · simp [hω]
                                · simp [hω]
                      _ = (μ.restrict B).real ((futurePath X s) ⁻¹' A) := by
                            calc
                              ∫ ω in B,
                                  Set.indicator ((futurePath X s) ⁻¹' A) (fun _ ↦ (1 : ℝ)) ω ∂μ
                                  =
                                    ∫ ω,
                                      Set.indicator ((futurePath X s) ⁻¹' A) (fun _ ↦ (1 : ℝ)) ω
                                        ∂(μ.restrict B) := by
                                          rfl
                              _ = (μ.restrict B).real ((futurePath X s) ⁻¹' A) := by
                                    simpa using
                                      (MeasureTheory.integral_indicator_one
                                        (μ := μ.restrict B)
                                        (s := (futurePath X s) ⁻¹' A) hfutureEvent_meas)
                      _ = μ.real ((futurePath X s) ⁻¹' A ∩ B) := by
                            simpa using
                              (MeasureTheory.measureReal_restrict_apply
                                (μ := μ) (s := B) (t := (futurePath X s) ⁻¹' A)
                                hfutureEvent_meas)
            _ = ∫ ω in B,
                (μ[fun ω ↦ Set.indicator A (fun _ ↦ (1 : ℝ)) (futurePath X s ω)
                  | generatedFiltration X hX s]) ω ∂μ := by
                    symm
                    exact
                      MeasureTheory.setIntegral_condExp hgenerated_le hindicator_int hB
            _ = ∫ ω in B, (κ (X s ω)).real A ∂μ := by
                  exact MeasureTheory.integral_congr_ae (ae_restrict_of_ae (hLawConst hA))
        have hleft_real :
            ((((μ.restrict B).map (futurePath X s)).real A)) =
              ∫ ω in B, (κ (X s ω)).real A ∂μ := by
          calc
            (((μ.restrict B).map (futurePath X s)).real A)
                = (μ.restrict B).real ((futurePath X s) ⁻¹' A) := by
                    simpa using
                      (MeasureTheory.map_measureReal_apply
                        (μ := μ.restrict B) (f := futurePath X s) hfuture_meas hA)
            _ = μ.real ((futurePath X s) ⁻¹' A ∩ B) := by
                  simpa using
                    (MeasureTheory.measureReal_restrict_apply
                      (μ := μ) (s := B) (t := (futurePath X s) ⁻¹' A) hfutureEvent_meas)
            _ = ∫ ω in B, (κ (X s ω)).real A ∂μ := by
                  exact hmass
        have hright_real :
            (((κ ∘ₘ ((μ.restrict B).map (X s))).real A)) =
              ∫ ω in B, (κ (X s ω)).real A ∂μ := by
          simpa using
            (kernelComp_restrictMap_real_eq_setIntegral_local
              (κ := κ) (μ := μ) (hY := hX s) hB_ambient hA)
        exact
          (MeasureTheory.measureReal_eq_measureReal_iff
            (μ := (μ.restrict B).map (futurePath X s))
            (ν := κ ∘ₘ ((μ.restrict B).map (X s))) (s := A) (t := A)).mp
            (hleft_real.trans hright_real.symm)
      have hCondExp :
          (fun ω ↦ ∫ y, f y ∂κ (X s ω)) =ᵐ[μ]
            μ[fun ω ↦ f (futurePath X s ω) | generatedFiltration X hX s] := by
        exact
          MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hgenerated_le hf_int
            (fun B hB hμB ↦ by
              -- Proof comment: the kernel-integral candidate is uniformly bounded on each
              -- history event, so it is integrable there.
              refine IntegrableOn.of_bound hμB
                hKernelIntegral_meas_ambient.aestronglyMeasurable C ?_
              refine Filter.Eventually.of_forall fun ω ↦ ?_
              have hbound_row :
                  ‖∫ y, f y ∂κ (X s ω)‖ ≤ C := by
                have hfC :
                    ∀ᵐ y ∂κ (X s ω), ‖f y‖ ≤ C :=
                  Filter.Eventually.of_forall fun y ↦ by simpa using hC y
                simpa using
                  (MeasureTheory.norm_integral_le_of_norm_le_const
                    (μ := κ (X s ω)) hfC)
              exact hbound_row)
            (fun B hB hμB ↦ by
              -- Proof comment: on each history event `B`, identify the restricted future-path
              -- law with the mixed path kernel and then integrate `f` against the common measure.
              let νB : Measure (ℕ → E) := (μ.restrict B).map (futurePath X s)
              let ρB : Measure (ℕ → E) := κ ∘ₘ ((μ.restrict B).map (X s))
              have hlaw : νB = ρB := by
                simpa [νB, ρB] using hRestrictedLaw hB
              haveI : IsFiniteMeasure νB := by
                dsimp [νB]
                infer_instance
              have hf_νB_int : Integrable f νB := by
                refine Integrable.of_bound hf_meas.aestronglyMeasurable C ?_
                exact Filter.Eventually.of_forall fun y ↦ hC y
              have hf_ρB_int : Integrable f ρB := by
                rw [← hlaw]
                exact hf_νB_int
              have hleft :
                  ∫ ω in B, f (futurePath X s ω) ∂μ = ∫ y, f y ∂νB := by
                change ∫ ω, f (futurePath X s ω) ∂(μ.restrict B) = ∫ y, f y ∂νB
                rw [show νB = (μ.restrict B).map (futurePath X s) by rfl]
                exact
                  (MeasureTheory.integral_map hfuture_meas.aemeasurable
                    hf_meas.aestronglyMeasurable).symm
              have hright :
                  ∫ y, f y ∂ρB = ∫ ω in B, ∫ y, f y ∂κ (X s ω) ∂μ := by
                let κ₀ : Kernel Unit E := Kernel.const Unit ((μ.restrict B).map (X s))
                have hcomp :
                    (κ ∘ₖ κ₀) () = ρB := by
                  simp [κ₀, ρB]
                calc
                  ∫ y, f y ∂ρB = ∫ y, f y ∂((κ ∘ₖ κ₀) ()) := by
                    rw [← hcomp]
                  _ = ∫ z, ∫ y, f y ∂κ z ∂κ₀ () := by
                        simpa using
                          (ProbabilityTheory.Kernel.integral_comp
                            (η := κ) (κ := κ₀) (a := ()) hf_ρB_int)
                  _ = ∫ z, ∫ y, f y ∂κ z ∂((μ.restrict B).map (X s)) := by
                        simp [κ₀]
                  _ = ∫ ω in B, ∫ y, f y ∂κ (X s ω) ∂μ := by
                        simpa using
                          (MeasureTheory.integral_map (hX s).aemeasurable
                            hKernelIntegral_meas.aestronglyMeasurable)
              exact (hleft.trans (hlaw ▸ hright)).symm)
            hKernelIntegral_meas_generated.aestronglyMeasurable
      simpa [μ, processFiltration_eq_generatedFiltration (X := X) hX] using hCondExp.symm
    refine (hasStrongMarkovProperty_iff P X κ).2 ?_
    intro x τ hτ hτfinite f hf_meas hf_bdd
    let μ : Measure Ω := (P x : Measure Ω)
    let lhs : Ω → ℝ :=
      μ[fun ω ↦ f (futurePathAfterStoppingTime X τ ω) | hτ.measurableSpace]
    let rhs : Ω → ℝ := fun ω ↦ ∫ y, f y ∂κ (stoppedValue X τ ω)
    have hSlice :
        ∀ s : ℕ, lhs =ᵐ[μ.restrict {ω | τ ω = s}] rhs := by
      intro s
      let slice : Set Ω := {ω | τ ω = s}
      have hRestrict :
          μ[fun ω ↦ f (futurePathAfterStoppingTime X τ ω) | hτ.measurableSpace] =ᵐ[
            μ.restrict slice]
            μ[fun ω ↦ f (futurePathAfterStoppingTime X τ ω) | processFiltration X s] := by
        -- Proof comment: first replace the stopping-time conditioning sigma-algebra by the
        -- deterministic-time sigma-algebra on the slice `{τ = s}`.
        simpa [μ, slice] using
          (MeasureTheory.condExp_stopping_time_ae_eq_restrict_eq_of_countable
            (μ := μ) (ℱ := processFiltration X)
            (f := fun ω ↦ f (futurePathAfterStoppingTime X τ ω)) hτ s)
      have hFixedTime_process :
          μ[fun ω ↦ f (futurePath X s ω) | processFiltration X s] =ᵐ[μ]
            fun ω ↦ ∫ y, f y ∂κ (X s ω) := by
        -- Proof comment: this is the deterministic-time future-path formula extracted above from
        -- the constant-stopping-time special case of `hLaw`.
        simpa [μ] using hFixedTime x s f hf_meas hf_bdd
      let gStopped : Ω → ℝ := fun ω ↦ f (futurePathAfterStoppingTime X τ ω)
      let gFixed : Ω → ℝ := fun ω ↦ f (futurePath X s ω)
      have hslice_proc : MeasurableSet[processFiltration X s] slice := by
        simpa [slice] using measurableSet_timeSlice_processFiltration X τ hτ s
      have hslice_ambient : MeasurableSet slice := by
        exact (processFiltration X).le s _ hslice_proc
      have hgStopped_int : Integrable gStopped μ := by
        -- Proof comment: the stopped future functional is integrable by boundedness and the
        -- measurable stopped-future reduction.
        simpa [gStopped, μ] using
          integrable_stoppedFutureFunctional X hX P x τ hτ f hf_meas hf_bdd
      have hgFixed_meas : Measurable gFixed := by
        simpa [gFixed] using hf_meas.comp (measurable_futurePath X hX s)
      have hgFixed_int : Integrable gFixed μ := by
        rcases hf_bdd with ⟨C, hC⟩
        -- Proof comment: the same uniform bound also integrates the deterministic shifted future.
        refine Integrable.of_bound hgFixed_meas.aestronglyMeasurable C ?_
        exact Filter.Eventually.of_forall fun ω ↦ hC (futurePath X s ω)
      have hIndicatorInput :
          slice.indicator gStopped =ᵐ[μ] slice.indicator gFixed := by
        -- Proof comment: inside the slice `{τ = s}`, the stopped future path is exactly the
        -- deterministic shifted future path.
        refine Filter.EventuallyEq.of_eq ?_
        funext ω
        by_cases hω : ω ∈ slice
        · have hτω : τ ω = (s : WithTop ℕ) := by
            simpa [slice] using hω
          rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
          exact congrArg f <|
            futurePathAfterStoppingTime_eq_futurePath_on_timeSlice (X := X) (τ := τ) (hτω := hτω)
        · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
      have hStoppedIndicator :
          μ[slice.indicator gStopped | processFiltration X s] =ᵐ[μ]
            slice.indicator (μ[gStopped | processFiltration X s]) := by
        -- Proof comment: conditioning commutes with multiplying by the slice indicator because
        -- the slice belongs to the fixed-time filtration.
        exact MeasureTheory.condExp_indicator (μ := μ) (m := processFiltration X s)
          hgStopped_int hslice_proc
      have hFixedIndicator :
          μ[slice.indicator gFixed | processFiltration X s] =ᵐ[μ]
            slice.indicator (μ[gFixed | processFiltration X s]) := by
        -- Proof comment: the same indicator transport applies to the deterministic shifted future.
        exact MeasureTheory.condExp_indicator (μ := μ) (m := processFiltration X s)
          hgFixed_int hslice_proc
      have hCondEqOnSlice :
          μ[gStopped | processFiltration X s] =ᵐ[μ.restrict slice]
            μ[gFixed | processFiltration X s] := by
        -- Proof comment: compare the two fixed-time conditional expectations through their slice
        -- indicators and then convert back to a restricted almost-everywhere statement.
        rw [ae_eq_restrict_iff_indicator_ae_eq hslice_ambient]
        exact hStoppedIndicator.symm.trans <|
          (MeasureTheory.condExp_congr_ae
            (μ := μ) (m := processFiltration X s) hIndicatorInput).trans hFixedIndicator
      have hKernelOnSlice :
          μ[gStopped | processFiltration X s] =ᵐ[μ.restrict slice]
            fun ω ↦ ∫ y, f y ∂κ (X s ω) := by
        -- Proof comment: after transporting to the deterministic shifted future, only the fixed
        -- time kernel formula remains.
        exact hCondEqOnSlice.trans (ae_restrict_of_ae hFixedTime_process)
      have hStoppedValueEq :
          (fun ω ↦ ∫ y, f y ∂κ (X s ω)) =ᵐ[μ.restrict slice]
            fun ω ↦ ∫ y, f y ∂κ (stoppedValue X τ ω) := by
        -- Proof comment: on `{τ = s}`, the stopped present state is exactly `X s`.
        rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hslice_ambient]
        exact Filter.Eventually.of_forall fun ω hω ↦ by
          have hτω : τ ω = (s : WithTop ℕ) := by
            simpa [slice] using hω
          rw [stoppedValue_eq_on_timeSlice (X := X) (τ := τ) (hτω := hτω)]
      exact hRestrict.trans (hKernelOnSlice.trans hStoppedValueEq)
    have hNotTopUnion : {ω | τ ω ≠ ⊤} = ⋃ s : ℕ, {ω | τ ω = s} := by
      ext ω
      constructor
      · intro hω
        obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hω
        exact Set.mem_iUnion.2 ⟨s, by simpa [Set.mem_setOf_eq] using hs.symm⟩
      · intro hω
        rcases Set.mem_iUnion.mp hω with ⟨s, hs⟩
        intro htop
        simpa [Set.mem_setOf_eq, htop] using hs
    have hOnFinite : lhs =ᵐ[μ.restrict {ω | τ ω ≠ ⊤}] rhs := by
      -- Proof comment: glue the slicewise identities over the countable partition of the finite
      -- stopping-time event.
      rw [hNotTopUnion, MeasureTheory.ae_eq_restrict_iUnion_iff]
      intro s
      exact hSlice s
    have hTopNull : μ {ω | τ ω = ⊤} = 0 := by
      -- Proof comment: the almost-sure finiteness hypothesis kills the exceptional top slice.
      rw [MeasureTheory.ae_iff] at hτfinite
      simpa [μ, not_ne_iff] using hτfinite
    have hOnTop : lhs =ᵐ[μ.restrict {ω | τ ω = ⊤}] rhs := by
      rw [Measure.restrict_eq_zero.2 hTopNull]
      simpa [Filter.EventuallyEq, Filter.Eventually]
    let pieces : Bool → Set Ω :=
      fun b ↦ if b then {ω | τ ω ≠ ⊤} else {ω | τ ω = ⊤}
    have hPiecesUniv : (⋃ b, pieces b) = Set.univ := by
      ext ω
      by_cases hω : τ ω = ⊤
      · simp [pieces, hω]
      · simp [pieces, hω]
    have hGlobal : lhs =ᵐ[μ] rhs := by
      -- Proof comment: combine the finite-time region with the null top slice to recover the
      -- global almost-everywhere identity.
      have hGlobalRestrict : lhs =ᵐ[μ.restrict (⋃ b, pieces b)] rhs := by
        rw [MeasureTheory.ae_eq_restrict_iUnion_iff]
        intro b
        cases b
        · simpa [pieces] using hOnTop
        · simpa [pieces] using hOnFinite
      simpa [hPiecesUniv] using hGlobalRestrict
    simpa [lhs, rhs, μ] using hGlobal

end ProbabilityTheory
