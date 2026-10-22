/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_9

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {I : Type u} [AddCommMonoid I]
variable {Ω : Type v} [mΩ : MeasurableSpace Ω]
variable {E : Type w} [mE : MeasurableSpace E]

/-- Helper for Theorem 17.14: on the slice `{τ = s}`, the stopped future path agrees with the
deterministic shifted path `t ↦ X (s + t)`. -/
lemma futurePathAfterStoppingTime_eq_on_timeSlice
    [Preorder I]
    (X : I → Ω → E) (τ : Ω → WithTop I) {s : I} {ω : Ω}
    (hτω : τ ω = (s : WithTop I)) :
    futurePathAfterStoppingTime X τ ω = fun t ↦ X (s + t) ω := by
  -- Proof comment: on the slice `τ ω = s`, the `WithTop` stopping-time evaluation becomes the
  -- deterministic shift by `s`.
  funext t
  have hτ_ne_top : τ ω ≠ ⊤ := by
    simpa [hτω]
  have hτ_untop : (τ ω).untop hτ_ne_top = s := by
    apply WithTop.coe_injective
    rw [WithTop.coe_untop, hτω]
  calc
    futurePathAfterStoppingTime X τ ω t = X ((τ ω).untop hτ_ne_top + t) ω := by
      exact futurePathAfterStoppingTime_apply_of_ne_top X τ ω t hτ_ne_top
    _ = X (s + t) ω := by
      rw [hτ_untop]

/-- Helper for Theorem 17.14: on the slice `{τ = s}`, the stopped present state is `X s`. -/
lemma stoppedValue_eq_on_timeSlice
    (X : I → Ω → E) (τ : Ω → WithTop I) {s : I} {ω : Ω}
    (hτω : τ ω = (s : WithTop I)) :
    stoppedValue X τ ω = X s ω := by
  -- Proof comment: after rewriting `τ ω` to the finite time `s`, `stoppedValue` reduces by
  -- unfolding to the ordinary process value at time `s`.
  simpa [stoppedValue, hτω]

section

variable {I : AddSubmonoid NNReal}

/-- Helper for Theorem 17.14: the natural process filtration collapses to
`generatedFiltrationSpace X s` for a time-homogeneous Markov process. -/
lemma processFiltration_eq_generatedFiltrationSpace_of_markovProcess
    [Countable I]
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    [IsTimeHomogeneousMarkovProcess X P κ] (s : I) :
    processFiltration X s = generatedFiltrationSpace X s := by
  have hgenerated_le : generatedFiltrationSpace X s ≤ mΩ := by
    exact
      IsTimeHomogeneousMarkovProcess.generatedFiltrationSpace_le_ambient
        (X := X) (P := P) (κ := κ) s
  -- Proof comment: the only extra term in `processFiltration` is the ambient infimum with `mΩ`.
  simpa [processFiltration, generatedFiltrationSpace] using inf_eq_right.mpr hgenerated_le

/-- Helper for Theorem 17.14: on the slice `{τ = s}`, the stopped future path is the deterministic
future path `futurePath X s`. -/
lemma futurePathAfterStoppingTime_eq_futurePath_on_timeSlice
    (X : I → Ω → E) (τ : Ω → WithTop I) {s : I} {ω : Ω}
    (hτω : τ ω = (s : WithTop I)) :
    futurePathAfterStoppingTime X τ ω = futurePath X s ω := by
  -- Proof comment: this is the existing slice formula, rewritten into the exact `futurePath`
  -- interface used by Theorem 17.9.
  funext t
  simpa [futurePath, add_comm] using
    congrFun
      (futurePathAfterStoppingTime_eq_on_timeSlice (X := X) (τ := τ) (hτω := hτω)) t

/-- Helper for Theorem 17.14: a uniform absolute bound on a real-valued path functional gives a
bounded range in the sense required by Theorem 17.9. -/
lemma isBounded_range_of_abs_le {α : Type*} (f : α → ℝ)
    (hC : ∃ C : ℝ, ∀ y, |f y| ≤ C) :
    Bornology.IsBounded (Set.range f) := by
  rcases hC with ⟨C, hC⟩
  refine isBounded_iff_forall_norm_le.mpr ⟨max C 0, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact le_trans (by simpa using hC y) (le_max_left _ _)

/-- Helper for Theorem 17.14: every stopping-time slice `{τ = s}` is measurable for the
deterministic-time filtration `processFiltration X s`. -/
lemma measurableSet_timeSlice_processFiltration
    [Countable I]
    (X : I → Ω → E) (τ : Ω → WithTop I)
    (hτ : IsStoppingTime (processFiltration X) τ) (s : I) :
    MeasurableSet[processFiltration X s] {ω | τ ω = s} := by
  -- Proof comment: on the slice `{τ = s}`, the stopping-time sigma-algebra and the time-`s`
  -- filtration agree by the standard stopping-time restriction theorem.
  have hslice_hτ :
      MeasurableSet[hτ.measurableSpace] (Set.univ ∩ {ω | τ ω = s}) := by
    simpa using hτ.measurableSet_eq_of_countable' s
  simpa using (hτ.measurableSet_inter_eq_iff Set.univ s).mp hslice_hτ

/-- Helper for Theorem 17.14: restricting `𝓕_τ` to the slice `{τ = s}` turns the stopped-future
conditional expectation into the deterministic-time conditional expectation at time `s`. -/
lemma stoppedFutureCondExp_eq_restrict_eq_fixedTimeCondExp
    [Countable I]
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    [IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (τ : Ω → WithTop I) (hτ : IsStoppingTime (processFiltration X) τ)
    (f : (I → E) → ℝ) (s : I) :
    ((P x : Measure Ω)[fun ω ↦ f (futurePathAfterStoppingTime X τ ω) | hτ.measurableSpace]) =ᵐ[
      (P x : Measure Ω).restrict {ω | τ ω = s}]
      (P x : Measure Ω)[fun ω ↦ f (futurePathAfterStoppingTime X τ ω) | processFiltration X s] := by
  -- Proof comment: this is the standard stopping-time restriction identity on the slice `{τ = s}`.
  simpa using
    (MeasureTheory.condExp_stopping_time_ae_eq_restrict_eq_of_countable
      (μ := (P x : Measure Ω)) (ℱ := processFiltration X) (hτ := hτ)
      (f := fun ω ↦ f (futurePathAfterStoppingTime X τ ω)) s)

/-- Helper for Theorem 17.14: Theorem 17.9 already upgrades a time-homogeneous Markov process on
an additive submonoid of `NNReal` to the full deterministic-time future-path conditional
expectation formula. -/
lemma markovProcessHasFuturePathFormulaAddSubmonoid
    [Countable I]
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    (hsub : ∀ ⦃s t : I⦄, s ≤ t → t.1 - s.1 ∈ I)
    [IsTimeHomogeneousMarkovProcess X P κ] :
    HasFuturePathConditionalExpectationFormula X P κ := by
  -- Proof comment: Theorem 17.9 packages the measurable-process, initial-state, and path-law
  -- fields of the Markov-process owner into the full future-path conditional-expectation API.
  exact
    (isTimeHomogeneousMarkovProcess_iff_hasFuturePathConditionalExpectationFormula_of_fixedPathKernel
      X P κ
      (fun t ↦
        IsTimeHomogeneousMarkovProcess.measurable_process
          (X := X) (P := P) (κ := κ) t)
      (fun x ↦
        IsTimeHomogeneousMarkovProcess.initial_state
          (X := X) (P := P) (κ := κ) x)
      (fun x ↦
        IsTimeHomogeneousMarkovProcess.path_law
          (X := X) (P := P) (κ := κ) x)
      hsub).mp inferInstance

/-- Helper for Theorem 17.14: the missing deterministic-time bridge packages bounded measurable
future-path functionals at a fixed time `s`. -/
lemma futurePathCondExp_of_markovProcess_addSubmonoid
    [Countable I]
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    (hsub : ∀ ⦃s t : I⦄, s ≤ t → t.1 - s.1 ∈ I)
    [IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (f : (I → E) → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ C : ℝ, ∀ y, |f y| ≤ C) (s : I) :
    ((P x : Measure Ω)[fun ω ↦ f (futurePath X s ω) | generatedFiltrationSpace X s]) =ᵐ[
      (P x : Measure Ω)] fun ω ↦ ∫ y, f y ∂κ (X s ω) := by
  have hFuture : HasFuturePathConditionalExpectationFormula X P κ := by
    -- Proof comment: reuse the Theorem 17.9 bridge instead of rebuilding the deterministic-time
    -- future-path formula from finite-dimensional cylinders inside this file.
    exact markovProcessHasFuturePathFormulaAddSubmonoid (X := X) (P := P) (κ := κ) hsub
  have hBdd : Bornology.IsBounded (Set.range f) := by
    -- Proof comment: the textbook absolute-value bound is exactly the bounded-range hypothesis
    -- expected by the future-path conditional-expectation formula.
    exact isBounded_range_of_abs_le f hf_bdd
  have hs_nonneg : (0 : I) ≤ s := by
    -- Proof comment: `I` is a subtype of `NNReal`, so every time parameter is nonnegative.
    show (0 : NNReal) ≤ (s : NNReal)
    exact zero_le _
  -- Proof comment: specialize the deterministic-time future-path formula at the chosen function,
  -- time, and start state.
  simpa using hFuture hf_meas hBdd s x hs_nonneg

/-- Helper for Theorem 17.14: bounded measurable path functionals remain measurable after
composition with the stopped future path. -/
lemma measurable_stoppedFutureFunctional
    [Countable I]
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    [IsTimeHomogeneousMarkovProcess X P κ]
    (τ : Ω → WithTop I) (hτ : IsStoppingTime (processFiltration X) τ)
    (f : (I → E) → ℝ) (hf_meas : Measurable f) :
    Measurable (fun ω ↦ f (futurePathAfterStoppingTime X τ ω)) := by
  let lifted : Ω × I → ℝ :=
    fun p ↦ f (fun t ↦ X (p.2 + t) p.1)
  have hlifted_meas : Measurable lifted := by
    -- Proof comment: the stopping time value ranges over a countable time set, so measurability
    -- reduces to the measurable fixed-time slices `ω ↦ f (futurePath X s ω)`.
    refine measurable_from_prod_countable_left ?_
    intro i
    have hEq : (fun x ↦ lifted (x, i)) = f ∘ futurePath X i := by
      funext x
      change f (fun t ↦ X (i + t) x) = f (futurePath X i x)
      congr
      funext t
      simp [futurePath, add_comm]
    rw [hEq]
    exact
      hf_meas.comp
        (measurable_futurePath
          (X := X)
          (hX_meas := fun t ↦
            IsTimeHomogeneousMarkovProcess.measurable_process
              (X := X) (P := P) (κ := κ) t)
          i)
  have hτ_top_meas : MeasurableSet {ω | τ ω = (⊤ : WithTop I)} := by
    have hEq :
        {ω | τ ω = (⊤ : WithTop I)} =
          (⋃ i : I, {ω | τ ω = (i : WithTop I)})ᶜ := by
      ext ω
      constructor
      · intro hω
        have hωtop : τ ω = (⊤ : WithTop I) := by
          simpa using hω
        simp [hωtop]
      · intro hω
        by_cases htop : τ ω = ⊤
        · exact htop
        · exfalso
          apply hω
          exact Set.mem_iUnion.2 ⟨(τ ω).untop htop, by simp [WithTop.coe_untop, htop]⟩
    rw [hEq]
    refine MeasurableSet.iUnion ?_ |>.compl
    intro i
    exact hτ.measurableSpace_le _ (hτ.measurableSet_eq_of_countable' i)
  have hτ_untopA_meas : Measurable (fun ω ↦ (τ ω).untopA) := by
    refine measurable_to_countable' ?_
    intro i
    by_cases hi : ((⊤ : WithTop I).untopA : I) = i
    · have hEq :
          {ω | (τ ω).untopA = i} = {ω | τ ω = (i : WithTop I)} ∪ {ω | τ ω = ⊤} := by
        ext ω
        cases hτω : τ ω with
        | top =>
            simp [hτω, hi]
        | coe j =>
            simp [hτω]
      change MeasurableSet {ω | (τ ω).untopA = i}
      rw [hEq]
      exact (hτ.measurableSpace_le _ (hτ.measurableSet_eq_of_countable' i)).union
        hτ_top_meas
    · have hEq :
          {ω | (τ ω).untopA = i} = {ω | τ ω = (i : WithTop I)} := by
        ext ω
        cases hτω : τ ω with
        | top =>
            simpa [hτω] using hi
        | coe j =>
            simp [hτω]
      change MeasurableSet {ω | (τ ω).untopA = i}
      rw [hEq]
      exact hτ.measurableSpace_le _ (hτ.measurableSet_eq_of_countable' i)
  have hgraph_meas : Measurable (fun ω ↦ (ω, (τ ω).untopA)) := by
    fun_prop
  -- Proof comment: compose the measurable slice family with the measurable graph
  -- `ω ↦ (ω, (τ ω).untopA)`.
  simpa [lifted, futurePathAfterStoppingTime, stoppedValue] using
    hlifted_meas.comp hgraph_meas

/-- Helper for Theorem 17.14: bounded measurable path functionals of the stopped future path are
integrable under each `P x`. -/
lemma integrable_stoppedFutureFunctional
    [Countable I]
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    [IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (τ : Ω → WithTop I) (hτ : IsStoppingTime (processFiltration X) τ)
    (f : (I → E) → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ C : ℝ, ∀ y, |f y| ≤ C) :
    Integrable (fun ω ↦ f (futurePathAfterStoppingTime X τ ω)) (P x : Measure Ω) := by
  rcases hf_bdd with ⟨C, hC⟩
  -- Proof comment: after the measurable stopped-future reduction, the uniform bound from `f`
  -- gives an `L¹` bound on the probability space `(Ω, P x)`.
  refine Integrable.of_bound
    (measurable_stoppedFutureFunctional
      (X := X) (P := P) (κ := κ) (τ := τ) hτ f hf_meas).aestronglyMeasurable C ?_
  exact Filter.Eventually.of_forall fun ω ↦ by
    simpa using hC (futurePathAfterStoppingTime X τ ω)

/-- Helper for Theorem 17.14: on each slice `{τ = s}`, the stopped-future conditional expectation
should collapse to the deterministic-time kernel formula from Theorem 17.9. -/
lemma stoppedFutureCondExp_eq_kernel_on_timeSlice
    [Countable I]
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    (hsub : ∀ ⦃s t : I⦄, s ≤ t → t.1 - s.1 ∈ I)
    [IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (τ : Ω → WithTop I) (hτ : IsStoppingTime (processFiltration X) τ)
    (f : (I → E) → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ C : ℝ, ∀ y, |f y| ≤ C) (s : I) :
    ((P x : Measure Ω)[fun ω ↦ f (futurePathAfterStoppingTime X τ ω) | hτ.measurableSpace]) =ᵐ[
      (P x : Measure Ω).restrict {ω | τ ω = s}]
      fun ω ↦ ∫ y, f y ∂κ (stoppedValue X τ ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let slice : Set Ω := {ω | τ ω = s}
  have hRestrict :
      μ[fun ω ↦ f (futurePathAfterStoppingTime X τ ω) | hτ.measurableSpace] =ᵐ[μ.restrict slice]
        μ[fun ω ↦ f (futurePathAfterStoppingTime X τ ω) | processFiltration X s] := by
    -- Proof comment: first replace the stopped-time conditioning sigma-algebra by the fixed-time
    -- sigma-algebra on the slice `{τ = s}`.
    simpa [μ, slice] using
      stoppedFutureCondExp_eq_restrict_eq_fixedTimeCondExp
        (X := X) (P := P) (κ := κ) x τ hτ f s
  have hFixedTime :
      μ[fun ω ↦ f (futurePath X s ω) | generatedFiltrationSpace X s] =ᵐ[μ]
        fun ω ↦ ∫ y, f y ∂κ (X s ω) := by
    -- Proof comment: this is the only remaining conceptual gap, namely the deterministic-time
    -- future-path conditional-expectation theorem for additive submonoids of `NNReal`.
    simpa [μ] using
      futurePathCondExp_of_markovProcess_addSubmonoid
        (X := X) (P := P) (κ := κ) (hsub := hsub) x f hf_meas hf_bdd s
  let gStopped : Ω → ℝ := fun ω ↦ f (futurePathAfterStoppingTime X τ ω)
  let gFixed : Ω → ℝ := fun ω ↦ f (futurePath X s ω)
  have hslice_proc : MeasurableSet[processFiltration X s] slice := by
    -- Proof comment: the time slice `{τ = s}` is measurable for the deterministic-time history.
    simpa [slice, μ] using measurableSet_timeSlice_processFiltration (X := X) (τ := τ) hτ s
  have hslice_ambient : MeasurableSet slice := by
    exact (processFiltration X).le s _ hslice_proc
  have hgStopped_int : Integrable gStopped μ := by
    -- Proof comment: boundedness and the measurable stopped-future helper give integrability of
    -- the stopped future functional needed for the indicator transport below.
    simpa [gStopped, μ] using
      integrable_stoppedFutureFunctional
        (X := X) (P := P) (κ := κ) x τ hτ f hf_meas hf_bdd
  have hgFixed_meas : Measurable gFixed := by
    -- Proof comment: the deterministic shifted path is measurable coordinatewise by the
    -- underlying Markov-process measurability.
    simpa [gFixed] using
      hf_meas.comp
        (measurable_futurePath
          (X := X)
          (hX_meas := fun t ↦
            IsTimeHomogeneousMarkovProcess.measurable_process
              (X := X) (P := P) (κ := κ) t)
          s)
  have hgFixed_int : Integrable gFixed μ := by
    rcases hf_bdd with ⟨C, hC⟩
    -- Proof comment: the same uniform bound integrates the fixed-time future functional.
    refine Integrable.of_bound hgFixed_meas.aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa [gFixed] using hC (futurePath X s ω)
  have hIndicatorInput :
      slice.indicator gStopped =ᵐ[μ] slice.indicator gFixed := by
    -- Proof comment: inside the slice `{τ = s}`, the stopped future path is exactly the
    -- deterministic shifted future path.
    refine Filter.EventuallyEq.of_eq ?_
    funext ω
    by_cases hω : ω ∈ slice
    · have hτω : τ ω = (s : WithTop I) := by
        simpa [slice] using hω
      rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      exact congrArg f <|
        futurePathAfterStoppingTime_eq_futurePath_on_timeSlice
          (X := X) (τ := τ) (hτω := hτω)
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
  have hStoppedIndicator :
      μ[slice.indicator gStopped | processFiltration X s] =ᵐ[μ]
        slice.indicator (μ[gStopped | processFiltration X s]) := by
    -- Proof comment: conditioning commutes with multiplying by the slice indicator because the
    -- slice belongs to the fixed-time filtration.
    exact MeasureTheory.condExp_indicator (μ := μ) (m := processFiltration X s)
      hgStopped_int hslice_proc
  have hFixedIndicator :
      μ[slice.indicator gFixed | processFiltration X s] =ᵐ[μ]
        slice.indicator (μ[gFixed | processFiltration X s]) := by
    -- Proof comment: the same indicator transport applies to the deterministic shifted future.
    exact MeasureTheory.condExp_indicator (μ := μ) (m := processFiltration X s)
      hgFixed_int hslice_proc
  have hFixedTime_process :
      μ[gFixed | processFiltration X s] =ᵐ[μ]
        fun ω ↦ ∫ y, f y ∂κ (X s ω) := by
    -- Proof comment: rewrite the deterministic-time bridge onto `processFiltration`, which
    -- coincides with `generatedFiltrationSpace` for a Markov process.
    simpa [gFixed,
      processFiltration_eq_generatedFiltrationSpace_of_markovProcess
        (X := X) (P := P) (κ := κ) s] using hFixedTime
  have hCondEqOnSlice :
      μ[gStopped | processFiltration X s] =ᵐ[μ.restrict slice]
        μ[gFixed | processFiltration X s] := by
    -- Proof comment: compare the two fixed-time conditional expectations via their slice
    -- indicators, then convert back to a restricted almost-everywhere statement.
    rw [ae_eq_restrict_iff_indicator_ae_eq hslice_ambient]
    exact hStoppedIndicator.symm.trans <|
      (MeasureTheory.condExp_congr_ae (μ := μ) (m := processFiltration X s) hIndicatorInput).trans
        hFixedIndicator
  have hKernelOnSlice :
      μ[gStopped | processFiltration X s] =ᵐ[μ.restrict slice]
        fun ω ↦ ∫ y, f y ∂κ (X s ω) := by
    -- Proof comment: after the slice transport, only the deterministic-time kernel formula
    -- remains.
    exact hCondEqOnSlice.trans (ae_restrict_of_ae hFixedTime_process)
  have hStoppedValueEq :
      (fun ω ↦ ∫ y, f y ∂κ (X s ω)) =ᵐ[μ.restrict slice]
        fun ω ↦ ∫ y, f y ∂κ (stoppedValue X τ ω) := by
    -- Proof comment: on `{τ = s}`, the stopped present state is exactly `X s`.
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hslice_ambient]
    exact Filter.Eventually.of_forall fun ω hω ↦ by
      have hτω : τ ω = (s : WithTop I) := by
        simpa [slice] using hω
      rw [stoppedValue_eq_on_timeSlice (X := X) (τ := τ) (hτω := hτω)]
  -- Proof comment: combine the stopping-time restriction, the fixed-time kernel identity on the
  -- slice, and the stopped-state rewrite.
  exact hRestrict.trans (hKernelOnSlice.trans hStoppedValueEq)

-- Semantic recall: `MeasureTheory.condExp_stopping_time_ae_eq_restrict_eq_of_countable` also
-- uses a countable linearly ordered stopping-time index, matching the countable ordered subtype
-- of `NNReal` used here.
-- Proof sketch: on a countable ordered additive time set modeling a countable subset of
-- `[0, ∞)` closed under addition, reduce bounded measurable future-path functionals to the
-- deterministic-time future-path formula from Theorem 17.9 and sum over the countable partition
-- `{τ = s}`.
/-- Theorem 17.14: for a countable additive time set `I ⊆ [0, ∞)` represented by an additive
submonoid of `NNReal`, every Markov process with laws `P x` satisfies the strong Markov property
with respect to its natural history filtration. -/
theorem isTimeHomogeneousMarkovProcess_hasStrongMarkovProperty
    [Countable I]
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    (hsub : ∀ ⦃s t : I⦄, s ≤ t → t.1 - s.1 ∈ I)
    [IsTimeHomogeneousMarkovProcess X P κ] :
    HasStrongMarkovProperty P X κ := by
  intro x τ hτ hτfinite f hf_meas hf_bdd
  let μ : Measure Ω := (P x : Measure Ω)
  let lhs : Ω → ℝ :=
    μ[fun ω ↦ f (futurePathAfterStoppingTime X τ ω) | hτ.measurableSpace]
  let rhs : Ω → ℝ := fun ω ↦ ∫ y, f y ∂κ (stoppedValue X τ ω)
  have hSlice :
      ∀ s : I, lhs =ᵐ[μ.restrict {ω | τ ω = s}] rhs := by
    intro s
    -- Proof comment: this is the slicewise strong-Markov identity produced by the helper above.
    simpa [lhs, rhs, μ] using
      stoppedFutureCondExp_eq_kernel_on_timeSlice
        (X := X) (P := P) (κ := κ) hsub x τ hτ f hf_meas hf_bdd s
  have hNotTopUnion : {ω | τ ω ≠ ⊤} = ⋃ s : I, {ω | τ ω = s} := by
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
  have hFiniteMeas : MeasurableSet {ω | τ ω ≠ ⊤} := by
    -- Proof comment: the finite-time event is the countable union of the measurable slices
    -- `{τ = s}`.
    rw [hNotTopUnion]
    refine MeasurableSet.iUnion fun s ↦ ?_
    exact
      (processFiltration X).le s _ <|
        measurableSet_timeSlice_processFiltration (X := X) (τ := τ) hτ s
  have hOnFiniteGlobal :
      ∀ᵐ ω ∂μ, ω ∈ {ω | τ ω ≠ ⊤} → lhs ω = rhs ω :=
    (MeasureTheory.ae_restrict_iff' hFiniteMeas).1 hOnFinite
  have hFiniteAe : ∀ᵐ ω ∂μ, ω ∈ {ω | τ ω ≠ ⊤} := by
    -- Proof comment: the strong-Markov assumption is only required on the almost-surely finite
    -- stopping-time event.
    simpa
  -- Proof comment: combine the finite-time region and the almost-sure finiteness hypothesis to
  -- recover the global almost-everywhere equality.
  have hGlobal : lhs =ᵐ[μ] rhs := by
    rw [Filter.EventuallyEq]
    filter_upwards [hFiniteAe, hOnFiniteGlobal] with ω hωfinite hωeq
    exact hωeq hωfinite
  simpa [lhs, rhs, μ] using hGlobal

end

end ProbabilityTheory
