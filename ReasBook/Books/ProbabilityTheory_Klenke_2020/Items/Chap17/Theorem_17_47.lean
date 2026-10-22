/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_11

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/- Layering for Theorem 17.47:
- `returnCycleOccupationMass` and `returnCycleOccupationMeasure` are the source-facing excursion
  objects attached to the textbook statement.
- The singleton-mass lemma is derived API from that primitive data.
- The invariance conclusion is a `core/canonical` owner property, so the main theorem should use
  `Kernel.Invariant` rather than a raw measure-kernel composition equality. -/

/-- The occupation mass of the state `y` during the excursion from `x` up to the first positive
return to `x`, written as the sum of the probabilities of the events
`{ω | X n ω = y ∧ n < τ_x^1(ω)}`. This is the textbook quantity
`𝔼_x [∑_{n=0}^{τ_x^1 - 1} 1_{ {X_n = y} }]`. -/
def returnCycleOccupationMass
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x y : E) : ℝ≥0∞ :=
  ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}

/-- The measure on the discrete state space whose singleton masses are the excursion occupation
mass before the first positive return to `x`. -/
def returnCycleOccupationMeasure
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x : E) : Measure E :=
  Measure.count.withDensity (returnCycleOccupationMass P X x)

notation "μ[" P ", " X "]" => returnCycleOccupationMeasure P X

-- Proof sketch: unfold `returnCycleOccupationMeasure`, evaluate the `withDensity` of
-- `Measure.count` on the singleton `{y}`, and use `Measure.count_singleton` to identify the value
-- with the density at `y`, which is `returnCycleOccupationMass P X x y`.
/-- The singleton mass formula for the return-cycle occupation measure `(μ[P, X]) x`. -/
theorem returnCycleOccupationMeasure_apply_singleton
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x y : E) :
    (μ[P, X] x) {y} = returnCycleOccupationMass P X x y := by
  -- Proof comment: evaluate the weighted counting measure on the singleton `{y}` and identify the
  -- resulting count integral with the density value at `y`.
  simp [returnCycleOccupationMeasure, withDensity_apply, lintegral_count]

section

variable {κ : ℕ → Kernel E E}
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization κ P X]
variable [Countable E]

-- Source alignment: Theorem 17.47 belongs to the countable-state regime of Chapter 17, and the
-- excursion-measure identities below use countable singleton decompositions accordingly.

/-- Helper for Theorem 17.47: the event `{ω | (τ_[X, x]^1) ω ≤ n}` is exactly the occurrence of
`x` at some time between `1` and `n`. -/
private lemma firstReturnTime_le_iff
    (x : E) (n : ℕ) (ω : Ω) :
    (τ_[X, x]^1) ω ≤ n ↔ ∃ j ∈ Set.Icc 1 n, X j ω = x := by
  -- Proof comment: specialize the bounded-hitting-time characterization of `hittingAfter` to the
  -- singleton set `{x}` and rewrite the membership condition.
  have h :
      MeasureTheory.hittingAfter X ({x} : Set E) 1 ω ≤ n ↔
        ∃ j ∈ Set.Icc 1 n, X j ω ∈ ({x} : Set E) :=
    hittingAfter_le_iff
  simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using h

/-- Helper for Theorem 17.47: the bounded first-return event is measurable with respect to the
time-`n` generated filtration. -/
private lemma measurableSet_firstReturnTimeLeInFiltration
    (x : E) (n : ℕ) :
    MeasurableSet[generatedFiltrationSpace X n] {ω | (τ_[X, x]^1) ω ≤ n} := by
  -- Proof comment: rewrite the bounded event as a finite union of singleton fibers of the
  -- coordinates `X j` for `j ≤ n`, each of which already belongs to the time-`n` history
  -- sigma-algebra.
  have hEq :
      {ω | (τ_[X, x]^1) ω ≤ n} =
        ⋃ j ∈ ((Finset.Icc 1 n : Finset ℕ) : Set ℕ), X j ⁻¹' ({x} : Set E) := by
    ext ω
    simp [firstReturnTime_le_iff]
  rw [hEq]
  refine MeasurableSet.biUnion (Set.to_countable _) ?_
  intro j hj
  have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
  have hle : MeasurableSpace.comap (X j) ‹MeasurableSpace E› ≤ generatedFiltrationSpace X n := by
    exact le_iSup₂_of_le j hjn le_rfl
  have hmeas : Measurable[generatedFiltrationSpace X n] (X j) :=
    Measurable.of_comap_le hle
  exact hmeas (measurableSet_singleton x)

/-- Helper for Theorem 17.47: the before-return tail event `{ω | n < τ_[X, x]^1(ω)}` is already
measurable at time `n`. -/
private lemma measurableSet_firstReturnTimeTailInFiltration
    (x : E) (n : ℕ) :
    MeasurableSet[generatedFiltrationSpace X n] {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  -- Proof comment: `n < τ_x^1` is the complement of the bounded-horizon return event
  -- `τ_x^1 ≤ n`, so filtration measurability follows from the previous lemma.
  have hEq :
      {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} = {ω | (τ_[X, x]^1) ω ≤ n}ᶜ := by
    ext ω
    simp
  rw [hEq]
  exact (measurableSet_firstReturnTimeLeInFiltration x n).compl

/-- Helper for Theorem 17.47: the before-return tail event is measurable on the ambient
measurable space. -/
private lemma measurableSet_firstReturnTimeTail
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω}
    [IsMarkovProcessRealization κ P X]
    (x : E) (n : ℕ) :
    MeasurableSet {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  -- Proof comment: the history sigma-algebra up to time `n` sits inside the ambient measurable
  -- space, so the filtration-measurable tail event is ambient measurable as well.
  exact
    (generatedFiltrationSpace_le_ambient X hReal.measurable_process n) _
      (measurableSet_firstReturnTimeTailInFiltration x n)

/-- Helper for Theorem 17.47: the deterministic-time Markov factorization is most stable in
real-valued form before transporting back to `ℝ≥0∞`, and it works for any measurable one-step
target set. -/
private lemma measure_inter_beforeReturn_step_mem_eq_mulReal
    (x y : E) {s : Set E} (hs : MeasurableSet s) (n : ℕ) :
    (P x : Measure Ω).real {ω |
        X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω ∈ s} =
      ((κ 1) y s).toReal *
        (P x : Measure Ω).real {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  let μ : Measure Ω := P x
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let A : Set Ω := {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}
  let B : Set Ω := X (n + 1) ⁻¹' s
  have hXn_measF : Measurable[generatedFiltrationSpace X n] (X n) := by
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le n <| le_iSup_of_le le_rfl le_rfl
  have hA_measFiltration : MeasurableSet[generatedFiltrationSpace X n] A := by
    have hState :
        MeasurableSet[generatedFiltrationSpace X n] (X n ⁻¹' ({y} : Set E)) := by
      simpa using hXn_measF (MeasurableSet.singleton y)
    have hEq :
        A = (X n ⁻¹' ({y} : Set E)) ∩ {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
      ext ω
      simp [A]
    rw [hEq]
    exact hState.inter (measurableSet_firstReturnTimeTailInFiltration x n)
  have hA_sub : A ⊆ {ω | X n ω = y} := by
    intro ω hω
    exact hω.1
  have hA_meas : MeasurableSet A := by
    exact (generatedFiltrationSpace_le_ambient X hReal.measurable_process n) _
      hA_measFiltration
  have hB_meas : MeasurableSet B := by
    simpa [B] using (hReal.measurable_process (n + 1)) hs
  have hMarkovGenerated :
      μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
        fun ω ↦ ((κ 1) (X n ω)).real s := by
    simpa [μ, B, add_comm] using
      hReal.markov_property x hs n 1
  have hIndicatorIntegrable : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB_meas
  -- Proof comment: integrate the deterministic-time Markov identity over the before-return
  -- history event and freeze the transition row at `y` because `A` already forces `X n = y`.
  calc
    μ.real {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω ∈ s}
        = ∫ ω in A, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂ μ := by
            have hInterEq :
                A ∩ B = {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω ∈ s} := by
              ext ω
              simp [A, B, and_left_comm, and_assoc]
            rw [setIntegral_condExp
              (generatedFiltrationSpace_le_ambient X hReal.measurable_process n)
              hIndicatorIntegrable hA_measFiltration, ← integral_indicator hA_meas]
            symm
            rw [← hInterEq]
            simpa [A, B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
              Set.inter_comm, smul_eq_mul] using
              integral_indicator_const (1 : ℝ) (hA_meas.inter hB_meas)
    _ = ∫ ω in A, ((κ 1) (X n ω)).real s ∂ μ := by
          exact integral_congr_ae hMarkovGenerated.restrict
    _ = ∫ _ in A, ((κ 1) y s).toReal ∂ μ := by
          refine integral_congr_ae ?_
          filter_upwards [self_mem_ae_restrict hA_meas] with ω hω
          have hω' : X n ω = y := hA_sub hω
          rw [hω']
          simp [Measure.real_def]
    _ = ((κ 1) y s).toReal * μ.real A := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- Helper for Theorem 17.47: the singleton-target deterministic-time Markov factorization is the
special case of the measurable-target bridge above. -/
private lemma measure_inter_beforeReturn_step_eq_mulReal
    (x y z : E) (n : ℕ) :
    (P x : Measure Ω).real {ω |
        X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω = z} =
      ((κ 1) y ({z} : Set E)).toReal *
        (P x : Measure Ω).real {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  -- Proof comment: specialize the measurable-target identity to the singleton target `{z}`.
  let s : Set E := {z}
  have h :
      (P x : Measure Ω).real {ω |
          X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω ∈ s} =
        ((κ 1) y s).toReal *
          (P x : Measure Ω).real {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} :=
    measure_inter_beforeReturn_step_mem_eq_mulReal x y (by
      simpa [s] using measurableSet_singleton z) n
  simpa [s, Set.mem_singleton_iff] using h

/-- Helper for Theorem 17.47: the measurable-target version of the deterministic-time Markov law
in `ℝ≥0∞`. -/
private lemma measure_inter_beforeReturn_step_mem_eq_mul
    (x y : E) {s : Set E} (hs : MeasurableSet s) (n : ℕ) :
    (P x : Measure Ω) {ω |
        X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω ∈ s} =
      ((κ 1) y s) *
        (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  have hstep :
      (P x : Measure Ω).real {ω |
          X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω ∈ s} =
        ((κ 1) y s).toReal *
          (P x : Measure Ω).real {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} :=
    measure_inter_beforeReturn_step_mem_eq_mulReal x y hs n
  have hleft_ne_top :
      (P x : Measure Ω) {ω |
          X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω ∈ s} ≠ ⊤ :=
    measure_ne_top _ _
  have hright_ne_top :
      ((κ 1) y s) *
          (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} ≠ ⊤ := by
    let _ : IsMarkovKernel (κ 1) :=
      (inferInstance : IsMarkovProcessRealization κ P X).semigroup.isMarkovKernel 1
    have hkernel_ne_top : ((κ 1) y s) ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt prob_le_one ENNReal.one_lt_top)
    exact ENNReal.mul_ne_top hkernel_ne_top (measure_ne_top _ _)
  -- Proof comment: finiteness of both event masses lets us transfer the real-valued identity back
  -- to `ℝ≥0∞`.
  exact (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top).mp <| by
    simpa [Measure.real_def, ENNReal.toReal_mul, measure_ne_top _ _, measure_ne_top _ _] using
      (measure_inter_beforeReturn_step_mem_eq_mulReal x y hs n)

/-- Helper for Theorem 17.47: if a time-`n` slice already pins down `X n = y`, then intersecting
it with the one-step future singleton event factors through the deterministic-time Markov law. -/
private lemma measure_inter_beforeReturn_step_eq_mul
    (x y z : E) (n : ℕ) :
    (P x : Measure Ω) {ω |
        X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω = z} =
      ((κ 1) y ({z} : Set E)) *
        (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  -- Proof comment: specialize the measurable-target `ℝ≥0∞` factorization to the singleton set
  -- `{z}`.
  let s : Set E := {z}
  have h :
      (P x : Measure Ω) {ω |
          X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω ∈ s} =
        ((κ 1) y s) *
          (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} :=
    measure_inter_beforeReturn_step_mem_eq_mul x y (by
      simpa [s] using measurableSet_singleton z) n
  simpa [s, Set.mem_singleton_iff] using h

/-- Helper for Theorem 17.47: at fixed time `n`, summing the state slices that flow into `z` in
one step recovers the probability of being at `z` at time `n + 1` before the return to `x`. -/
private lemma tsum_stateSliceStepProbabilities_eq
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (x z : E) (n : ℕ) :
    ∑' y : E, (P x : Measure Ω) {ω |
        X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω = z} =
      (P x : Measure Ω) {ω | X (n + 1) ω = z ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let A : E → Set Ω := fun y ↦ {ω |
    X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω = z}
  have hPairwise : Pairwise fun y₁ y₂ ↦ Disjoint (A y₁) (A y₂) := by
    intro y₁ y₂ hy
    refine Set.disjoint_left.2 ?_
    intro ω hω₁ hω₂
    exact hy (hω₁.1.symm.trans hω₂.1)
  have hMeas : ∀ y : E, MeasurableSet (A y) := by
    intro y
    have hXn : MeasurableSet (X n ⁻¹' ({y} : Set E)) := by
      simpa using hReal.measurable_process n (measurableSet_singleton y)
    have hTail : MeasurableSet {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} :=
      measurableSet_firstReturnTimeTail (κ := κ) (P := P) (X := X) x n
    have hNext : MeasurableSet (X (n + 1) ⁻¹' ({z} : Set E)) := by
      simpa using hReal.measurable_process (n + 1) (measurableSet_singleton z)
    have hEq :
        A y =
          (X n ⁻¹' ({y} : Set E)) ∩
            ({ω | (n : ℕ∞) < (τ_[X, x]^1) ω} ∩ X (n + 1) ⁻¹' ({z} : Set E)) := by
      ext ω
      simp [A, and_assoc]
    rw [hEq]
    exact hXn.inter (hTail.inter hNext)
  have hUnion :
      (⋃ y : E, A y) = {ω | X (n + 1) ω = z ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨y, hy⟩
      exact ⟨hy.2.2, hy.2.1⟩
    · intro hω
      refine Set.mem_iUnion.2 ⟨X n ω, ?_⟩
      exact ⟨rfl, hω.2, hω.1⟩
  -- Proof comment: the current-state slices are pairwise disjoint and cover the target event.
  rw [← hUnion]
  symm
  exact measure_iUnion hPairwise hMeas

/-- Helper for Theorem 17.47: at fixed time `n`, summing the state slices whose next step lands
in a measurable set `s` recovers the before-return probability of hitting `s` at time `n + 1`.
-/
private lemma tsum_stateSliceStepProbabilities_mem_eq
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (x : E) {s : Set E} (hs : MeasurableSet s) (n : ℕ) :
    ∑' y : E, (P x : Measure Ω) {ω |
        X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω ∈ s} =
      (P x : Measure Ω) {ω | X (n + 1) ω ∈ s ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let A : E → Set Ω := fun y ↦ {ω |
    X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω ∈ s}
  have hPairwise : Pairwise fun y₁ y₂ ↦ Disjoint (A y₁) (A y₂) := by
    intro y₁ y₂ hy
    refine Set.disjoint_left.2 ?_
    intro ω hω₁ hω₂
    exact hy (hω₁.1.symm.trans hω₂.1)
  have hMeas : ∀ y : E, MeasurableSet (A y) := by
    intro y
    have hXn : MeasurableSet (X n ⁻¹' ({y} : Set E)) := by
      simpa using hReal.measurable_process n (measurableSet_singleton y)
    have hTail : MeasurableSet {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} :=
      measurableSet_firstReturnTimeTail (κ := κ) (P := P) (X := X) x n
    have hNext : MeasurableSet (X (n + 1) ⁻¹' s) := by
      simpa using hReal.measurable_process (n + 1) hs
    have hEq :
        A y =
          (X n ⁻¹' ({y} : Set E)) ∩
            ({ω | (n : ℕ∞) < (τ_[X, x]^1) ω} ∩ X (n + 1) ⁻¹' s) := by
      ext ω
      simp [A, and_assoc]
    rw [hEq]
    exact hXn.inter (hTail.inter hNext)
  have hUnion :
      (⋃ y : E, A y) = {ω | X (n + 1) ω ∈ s ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨y, hy⟩
      exact ⟨hy.2.2, hy.2.1⟩
    · intro hω
      refine Set.mem_iUnion.2 ⟨X n ω, ?_⟩
      exact ⟨rfl, hω.2, hω.1⟩
  -- Proof comment: the state slices are pairwise disjoint and their union is the target event.
  rw [← hUnion]
  symm
  exact measure_iUnion hPairwise hMeas

/-- Helper for Theorem 17.47: summing the time-`n` state slices over a measurable set `s`
recovers the probability of being in `s` at time `n` before the return to `x`. -/
private lemma tsum_stateSliceProbabilities_mem_eq
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (x : E) {s : Set E} (hs : MeasurableSet s) (n : ℕ) :
    ∑' y : E,
      Set.indicator s
        (fun y ↦ (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}) y =
      (P x : Measure Ω) {ω | X n ω ∈ s ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  classical
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let A : s → Set Ω := fun y ↦ {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}
  have hPairwise : Pairwise fun y₁ y₂ ↦ Disjoint (A y₁) (A y₂) := by
    intro y₁ y₂ hy
    refine Set.disjoint_left.2 ?_
    intro ω hω₁ hω₂
    exact hy <| Subtype.ext (hω₁.1.symm.trans hω₂.1)
  have hMeas : ∀ y : s, MeasurableSet (A y) := by
    intro y
    have hState : MeasurableSet (X n ⁻¹' ({(y : E)} : Set E)) := by
      simpa using hReal.measurable_process n (MeasurableSet.singleton (y : E))
    have hTail : MeasurableSet {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} :=
      measurableSet_firstReturnTimeTail (κ := κ) (P := P) (X := X) x n
    rw [show A y = (X n ⁻¹' ({(y : E)} : Set E)) ∩ {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} by
      ext ω
      simp [A]]
    exact hState.inter hTail
  have hUnion :
      (⋃ y : s, A y) = {ω | X n ω ∈ s ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨y, hy⟩
      have hstate : X n ω = y := hy.1
      exact ⟨by simpa [hstate] using y.property, hy.2⟩
    · intro hω
      refine Set.mem_iUnion.2 ⟨⟨X n ω, hω.1⟩, ?_⟩
      exact ⟨rfl, hω.2⟩
  -- Proof comment: the set event is the disjoint union of the singleton state slices over the
  -- subtype `s`; convert that subtype sum back to the ambient indicator series with `tsum_subtype`.
  calc
    ∑' y : E,
        Set.indicator s
          (fun y ↦ (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}) y
      = ∑' y : s, (P x : Measure Ω) (A y) := by
          symm
          simpa [A, Set.indicator_apply] using
            (tsum_subtype (s := s)
              (f := fun y : E ↦
                (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}))
    _ = (P x : Measure Ω) (⋃ y : s, A y) := (measure_iUnion hPairwise hMeas).symm
    _ = (P x : Measure Ω) {ω | X n ω ∈ s ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by rw [hUnion]

/-- Helper for Theorem 17.47: evaluating `μ_x` on a measurable set rewrites the weighted counting
measure as the before-return state series over that set. -/
private lemma returnCycleOccupationMeasure_apply
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (x : E) {s : Set E} (hs : MeasurableSet s) :
    (μ[P, X] x) s =
      ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω ∈ s ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  classical
  -- Proof comment: evaluate `μ_x` as a weighted counting measure, commute the count integral with
  -- the time series, and collapse each fixed-time state sum to the set event `X n ∈ s`.
  calc
    (μ[P, X] x) s
      = ∫⁻ y, Set.indicator s (returnCycleOccupationMass P X x) y ∂Measure.count := by
          rw [returnCycleOccupationMeasure, withDensity_apply _ hs]
          simp [hs]
    _ = ∫⁻ y, ∑' n : ℕ,
          Set.indicator s
            (fun y ↦ (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}) y
          ∂Measure.count := by
          refine lintegral_congr_ae ?_
          filter_upwards [] with y
          by_cases hy : y ∈ s
          · simp [returnCycleOccupationMass, Set.indicator_apply, hy]
          · simp [returnCycleOccupationMass, Set.indicator_apply, hy]
    _ = ∑' n : ℕ,
          ∫⁻ y,
            Set.indicator s
              (fun y ↦ (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}) y
            ∂Measure.count := by
          rw [lintegral_tsum fun n ↦
            (Measurable.of_discrete :
              Measurable fun y : E ↦
                Set.indicator s
                  (fun y ↦
                    (P x : Measure Ω)
                      {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}) y).aemeasurable]
    _ = ∑' n : ℕ,
          ∑' y : E,
            Set.indicator s
              (fun y ↦ (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}) y := by
          refine tsum_congr fun n ↦ ?_
          rw [lintegral_count]
    _ = ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω ∈ s ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
          refine tsum_congr fun n ↦ ?_
          exact tsum_stateSliceProbabilities_mem_eq (κ := κ) (P := P) (X := X) x hs n

/-- Helper for Theorem 17.47: evaluating the composed measure `μ_x.bind (κ 1)` on a measurable
set rewrites it as the shifted before-return series. -/
private lemma comp_returnCycleOccupationMeasure_apply
    (x : E) {s : Set E} (hs : MeasurableSet s) :
    (((μ[P, X] x).bind (κ 1)) s) =
      ∑' n : ℕ, (P x : Measure Ω) {ω |
        X (n + 1) ω ∈ s ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  classical
  -- Route correction: expand the composed measure on the countable discrete state space first,
  -- then insert the deterministic-time Markov factorization before commuting the time/state sums.
  change (((κ 1) ∘ₘ (μ[P, X] x)) s) = _
  rw [Measure.comp_eq_sum_of_countable, Measure.sum_apply _ hs]
  calc
    ∑' y : E, (μ[P, X] x) {y} * (κ 1) y s
      = ∑' y : E, returnCycleOccupationMass P X x y * (κ 1) y s := by
          refine tsum_congr fun y ↦ ?_
          rw [returnCycleOccupationMeasure_apply_singleton]
    _ = ∑' y : E, ∑' n : ℕ,
          (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} * (κ 1) y s := by
          refine tsum_congr fun y ↦ ?_
          rw [returnCycleOccupationMass, ENNReal.tsum_mul_right]
    _ = ∑' n : ℕ, ∑' y : E,
          (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} * (κ 1) y s := by
          exact ENNReal.tsum_comm
    _ = ∑' n : ℕ, ∑' y : E,
          (P x : Measure Ω) {ω |
            X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ∧ X (n + 1) ω ∈ s} := by
          refine tsum_congr fun n ↦ ?_
          refine tsum_congr fun y ↦ ?_
          simpa [mul_comm] using
            (measure_inter_beforeReturn_step_mem_eq_mul (P := P) (X := X) (κ := κ) x y hs n).symm
    _ = ∑' n : ℕ, (P x : Measure Ω) {ω |
          X (n + 1) ω ∈ s ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
          refine tsum_congr fun n ↦ ?_
          exact tsum_stateSliceStepProbabilities_mem_eq (P := P) (X := X) (κ := κ) x hs n

/-- Helper for Theorem 17.47: the singleton mass of the composed measure
`(μ[P, X] x).bind (κ 1)` is the one-step before-return series. -/
private lemma comp_returnCycleOccupationMeasure_apply_singleton_eq_tsum_nextStepBeforeReturn
    (x z : E) :
    (((μ[P, X] x).bind (κ 1)) {z}) =
      ∑' n : ℕ, (P x : Measure Ω) {ω |
        X (n + 1) ω = z ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  -- Proof comment: specialize the measurable-set owner formula to the singleton `{z}`.
  simpa [Set.mem_singleton_iff] using
    comp_returnCycleOccupationMeasure_apply (P := P) (X := X) (κ := κ) x
      (measurableSet_singleton z)

/-- Helper for Theorem 17.47: before the first positive return to `x`, the path only contributes
to the occupation mass of `x` at time `0`. -/
private lemma returnCycleOccupationMass_self_eq_one
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (x : E) :
    returnCycleOccupationMass P X x x = 1 := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  have hinit :
      (P x : Measure Ω) {ω | X 0 ω = x} = 1 := by
    have hpreimage : {ω | X 0 ω = x} = X 0 ⁻¹' ({x} : Set E) := by
      ext ω
      simp
    rw [hpreimage, ← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton x)]
    rw [hReal.initial_eq x]
    simp
  have hterm0 :
      (P x : Measure Ω) {ω | X 0 ω = x ∧ (0 : ℕ∞) < (τ_[X, x]^1) ω} = 1 := by
    have hτpos : ∀ ω : Ω, (0 : ℕ∞) < (τ_[X, x]^1) ω := by
      intro ω
      have hτge1 : (1 : ℕ∞) ≤ (τ_[X, x]^1) ω := by
        have h : (1 : ℕ) ≤ MeasureTheory.hittingAfter X ({x} : Set E) 1 ω := le_hittingAfter ω
        simpa [iteratedEntranceTime_one] using h
      exact lt_of_lt_of_le (by simp) hτge1
    have hEq :
        {ω | X 0 ω = x ∧ (0 : ℕ∞) < (τ_[X, x]^1) ω} = {ω | X 0 ω = x} := by
      ext ω
      constructor
      · intro hω
        exact hω.1
      · intro hω
        exact ⟨hω, hτpos ω⟩
    rw [hEq]
    exact hinit
  have htailZero :
      ∀ m : ℕ,
        ite (m = 0) 0
            ((P x : Measure Ω) {ω | X m ω = x ∧ (m : ℕ∞) < (τ_[X, x]^1) ω}) = 0 := by
    intro m
    by_cases hm : m = 0
    · simp [hm]
    · rcases Nat.exists_eq_succ_of_ne_zero hm with ⟨n, rfl⟩
      have hempty :
          {ω | X (n + 1) ω = x ∧ (((n + 1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} = ∅ := by
        ext ω
        constructor
        · intro hω
          have hle : (τ_[X, x]^1) ω ≤ n + 1 := by
            have h :
                MeasureTheory.hittingAfter X ({x} : Set E) 1 ω ≤ n + 1 :=
              hittingAfter_le_of_mem (by simp) (by simpa [Set.mem_singleton_iff] using hω.1)
            simpa [iteratedEntranceTime_one] using h
          exact False.elim <| (not_lt_of_ge hle) hω.2
        · simp
      rw [hempty]
      simp
  have htailTsum :
      (∑' m : ℕ,
        ite (m = 0) 0 ((P x : Measure Ω) {ω | X m ω = x ∧ (m : ℕ∞) < (τ_[X, x]^1) ω})) = 0 := by
    exact ENNReal.tsum_eq_zero.2 htailZero
  have hterm0' :
      (P x : Measure Ω) {ω | X 0 ω = x ∧ ((0 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} = 1 := by
    simpa using hterm0
  have htailTsum' :
      (∑' i : ℕ,
        if i = 0 then 0 else (P x : Measure Ω) {ω | X i ω = x ∧ (i : ℕ∞) < (τ_[X, x]^1) ω}) = 0 := by
    simpa using htailTsum
  -- Proof comment: the initial time contributes mass `1`, and every later diagonal slice is
  -- empty because a return at time `m > 0` would contradict `m < τ_x^1`.
  rw [returnCycleOccupationMass, ENNReal.tsum_eq_add_tsum_ite 0, hterm0']
  have hsum1 :
      1 + (∑' i : ℕ,
        if i = 0 then 0 else (P x : Measure Ω) {ω | X i ω = x ∧ (i : ℕ∞) < (τ_[X, x]^1) ω}) =
          1 + 0 := congrArg (fun t : ℝ≥0∞ ↦ 1 + t) htailTsum'
  simpa using hsum1

/-- Helper for Theorem 17.47: the event `{ω | X (n + 1) ω = x ∧ n < τ_x^1(ω)}` is exactly the
exact first-return slice `{ω | τ_x^1(ω) = n + 1}`. -/
private lemma step_beforeReturn_self_iff_firstReturn_eq
    (x : E) (n : ℕ) (ω : Ω) :
    X (n + 1) ω = x ∧ (n : ℕ∞) < (τ_[X, x]^1) ω ↔ (τ_[X, x]^1) ω = n + 1 := by
  constructor
  · rintro ⟨hstate, htail⟩
    have hle : (τ_[X, x]^1) ω ≤ n + 1 := by
      have h : MeasureTheory.hittingAfter X ({x} : Set E) 1 ω ≤ n + 1 :=
        hittingAfter_le_of_mem (by simp) (by simpa [Set.mem_singleton_iff] using hstate)
      simpa [iteratedEntranceTime_one] using h
    have hlt_top : (τ_[X, x]^1) ω < ⊤ :=
      lt_of_le_of_lt hle (by simp)
    let m := ENat.lift ((τ_[X, x]^1) ω) hlt_top
    have hm_eq : (m : ℕ∞) = (τ_[X, x]^1) ω :=
      ENat.coe_lift ((τ_[X, x]^1) ω) hlt_top
    have hm_le : m ≤ n + 1 := by
      simpa [m, hm_eq] using hle
    have hn_lt_m : n < m := by
      simpa [m, hm_eq] using htail
    have hm : m = n + 1 := Nat.le_antisymm hm_le (Nat.succ_le_of_lt hn_lt_m)
    calc
      (τ_[X, x]^1) ω = (m : ℕ∞) := hm_eq.symm
      _ = n + 1 := by simpa [hm]
  · intro hτ
    have hcoene : ((n + 1 : ℕ) : ℕ∞) ≠ ⊤ := by
      exact ENat.coe_ne_top (n + 1)
    have hne_top : (τ_[X, x]^1) ω ≠ ⊤ := by
      simpa [hτ] using hcoene
    have hmem :
        X (((τ_[X, x]^1) ω).untopA) ω = x := by
      have h :
          X (MeasureTheory.hittingAfter X ({x} : Set E) 1 ω).untopA ω ∈ ({x} : Set E) :=
        hittingAfter_mem_set_of_ne_top (by simpa [iteratedEntranceTime_one] using hne_top)
      simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using h
    have huntop : ((τ_[X, x]^1) ω).untopA = n + 1 := by
      rw [WithTop.untopA_eq_untop hne_top]
      simpa [ENat.lift, hτ] using (ENat.lift_coe (n + 1))
    have hstate : X (n + 1) ω = x := by
      simpa [huntop] using hmem
    have htail : (n : ℕ∞) < (τ_[X, x]^1) ω := by
      simpa [hτ] using (show (n : ℕ∞) < n + 1 by exact_mod_cast Nat.lt_succ_self n)
    exact ⟨hstate, htail⟩

/-- Helper for Theorem 17.47: if `z ≠ x`, then reaching `z` at time `n + 1` before the return to
`x` is equivalent to still being before the return at time `n + 1`. -/
private lemma nextStepBeforeReturn_eq_succTail_of_ne
    (x z : E) (hz : z ≠ x) (n : ℕ) :
    {ω | X (n + 1) ω = z ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} =
      {ω | X (n + 1) ω = z ∧ ((n + 1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} := by
  ext ω
  constructor
  · rintro ⟨hstate, htail⟩
    have hstate_ne : X (n + 1) ω ≠ x := by
      intro hx
      exact hz (hstate.symm.trans hx)
    have hsuccTail : (((n + 1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω) := by
      by_contra hnot
      have hle : (τ_[X, x]^1) ω ≤ n + 1 := le_of_not_gt hnot
      have hlt_top : (τ_[X, x]^1) ω < ⊤ := lt_of_le_of_lt hle (by simp)
      let m := ENat.lift ((τ_[X, x]^1) ω) hlt_top
      have hm_eq : (m : ℕ∞) = (τ_[X, x]^1) ω :=
        ENat.coe_lift ((τ_[X, x]^1) ω) hlt_top
      have hm_le : m ≤ n + 1 := by
        simpa [m, hm_eq] using hle
      have hn_lt_m : n < m := by
        simpa [m, hm_eq] using htail
      have hm : m = n + 1 := Nat.le_antisymm hm_le (Nat.succ_le_of_lt hn_lt_m)
      have hτeq : (τ_[X, x]^1) ω = n + 1 := by
        calc
          (τ_[X, x]^1) ω = (m : ℕ∞) := hm_eq.symm
          _ = n + 1 := by simpa [hm]
      have hx :
          X (n + 1) ω = x :=
        (step_beforeReturn_self_iff_firstReturn_eq x n ω).2 hτeq |>.1
      exact hstate_ne hx
    exact ⟨hstate, hsuccTail⟩
  · rintro ⟨hstate, htail⟩
    exact ⟨hstate, lt_trans (by exact_mod_cast Nat.lt_succ_self n) htail⟩

/-- Helper for Theorem 17.47: the exact first-return probabilities sum to `1` when `x` is
recurrent. -/
private lemma tsum_firstReturnProbabilities_eq_one
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (x : E) (hx : IsRecurrentState P X x) :
    ∑' n : ℕ, (P x : Measure Ω) {ω | (τ_[X, x]^1) ω = n + 1} = 1 := by
  let μ : Measure Ω := P x
  let A : ℕ → Set Ω := fun n ↦ {ω | (τ_[X, x]^1) ω = n + 1}
  have hPairwise : Pairwise fun m n ↦ Disjoint (A m) (A n) := by
    intro m n hmn
    refine Set.disjoint_left.2 ?_
    intro ω hωm hωn
    have hm : (τ_[X, x]^1) ω = m + 1 := by
      simpa [A] using hωm
    have hn : (τ_[X, x]^1) ω = n + 1 := by
      simpa [A] using hωn
    have hsuc : m + 1 = n + 1 := ENat.coe_inj.mp (hm.symm.trans hn)
    exact hmn (Nat.succ.inj hsuc)
  have hMeas : ∀ n : ℕ, MeasurableSet (A n) := by
    intro n
    have hEq :
        A n = {ω | X (n + 1) ω = x ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
      ext ω
      simpa [A] using (step_beforeReturn_self_iff_firstReturn_eq x n ω).symm
    rw [hEq]
    have hState : MeasurableSet (X (n + 1) ⁻¹' ({x} : Set E)) := by
      simpa using
        (inferInstance : IsMarkovProcessRealization κ P X).measurable_process (n + 1)
          (measurableSet_singleton x)
    have hTail : MeasurableSet {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} :=
      measurableSet_firstReturnTimeTail (κ := κ) (P := P) (X := X) x n
    rw [show {ω | X (n + 1) ω = x ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} =
      (X (n + 1) ⁻¹' ({x} : Set E)) ∩ {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} by
      ext ω
      simp]
    exact hState.inter hTail
  have hUnion :
      (⋃ n : ℕ, A n) = {ω | (τ_[X, x]^1) ω < ⊤} := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      simp [A] at hn
      simpa [hn]
    · intro hω
      let m := ENat.lift ((τ_[X, x]^1) ω) hω
      have hm_eq : (m : ℕ∞) = (τ_[X, x]^1) ω :=
        ENat.coe_lift ((τ_[X, x]^1) ω) hω
      have hτge1 : (1 : ℕ∞) ≤ (τ_[X, x]^1) ω := by
        have h : (1 : ℕ) ≤ MeasureTheory.hittingAfter X ({x} : Set E) 1 ω := le_hittingAfter ω
        simpa [iteratedEntranceTime_one] using h
      have hm_pos : 0 < m := by
        have hm_ge1 : 1 ≤ m := by
          simpa [m, hm_eq] using hτge1
        exact lt_of_lt_of_le (by simp) hm_ge1
      rcases Nat.exists_eq_succ_of_ne_zero hm_pos.ne' with ⟨n, hm⟩
      refine Set.mem_iUnion.2 ⟨n, ?_⟩
      calc
        (τ_[X, x]^1) ω = (m : ℕ∞) := hm_eq.symm
        _ = n + 1 := by simpa [hm]
  have hhit :
      μ {ω | (τ_[X, x]^1) ω < ⊤} = 1 := by
    have hEq :
        {ω | (τ_[X, x]^1) ω < ⊤} = {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} := by
      ext ω
      simpa [iteratedEntranceTime_one] using (hittingAfter_singleton_lt_top_iff X x ω)
    have hrec :
        μ.real {ω | (τ_[X, x]^1) ω < ⊤} = 1 := by
      simpa [μ, IsRecurrentState, everHitsProbability_def, hEq] using hx
    exact (ENNReal.toReal_eq_one_iff _).mp hrec
  -- Proof comment: the finite return event decomposes into pairwise disjoint exact-return slices,
  -- and recurrence makes the total mass of that union equal to `1`.
  calc
    ∑' n : ℕ, μ (A n) = μ (⋃ n : ℕ, A n) := (measure_iUnion hPairwise hMeas).symm
    _ = μ {ω | (τ_[X, x]^1) ω < ⊤} := by rw [hUnion]
    _ = 1 := hhit

/-- Helper for Theorem 17.47: if the measurable set `s` does not contain `x`, then reaching `s`
at time `n + 1` before the return to `x` is equivalent to still being before the return at time
`n + 1`. -/
private lemma nextStepBeforeReturn_mem_eq_succTail_of_not_mem
    (x : E) {s : Set E} (hx : x ∉ s) (n : ℕ) :
    {ω | X (n + 1) ω ∈ s ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} =
      {ω | X (n + 1) ω ∈ s ∧ ((n + 1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} := by
  ext ω
  constructor
  · rintro ⟨hstate, htail⟩
    have hsuccTail : (((n + 1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω) := by
      by_contra hnot
      have hle : (τ_[X, x]^1) ω ≤ n + 1 := le_of_not_gt hnot
      have hlt_top : (τ_[X, x]^1) ω < ⊤ := lt_of_le_of_lt hle (by simp)
      let m := ENat.lift ((τ_[X, x]^1) ω) hlt_top
      have hm_eq : (m : ℕ∞) = (τ_[X, x]^1) ω :=
        ENat.coe_lift ((τ_[X, x]^1) ω) hlt_top
      have hm_le : m ≤ n + 1 := by
        simpa [m, hm_eq] using hle
      have hn_lt_m : n < m := by
        simpa [m, hm_eq] using htail
      have hm : m = n + 1 := Nat.le_antisymm hm_le (Nat.succ_le_of_lt hn_lt_m)
      have hτeq : (τ_[X, x]^1) ω = n + 1 := by
        calc
          (τ_[X, x]^1) ω = (m : ℕ∞) := hm_eq.symm
          _ = n + 1 := by simpa [hm]
      have hxstate :
          X (n + 1) ω = x :=
        (step_beforeReturn_self_iff_firstReturn_eq x n ω).2 hτeq |>.1
      exact hx (by simpa [hxstate] using hstate)
    exact ⟨hstate, hsuccTail⟩
  · rintro ⟨hstate, htail⟩
    exact ⟨hstate, lt_trans (by exact_mod_cast Nat.lt_succ_self n) htail⟩

/-- Helper for Theorem 17.47: on a measurable set avoiding `x`, the composed excursion measure
already agrees with `μ_x`. -/
private lemma comp_returnCycleOccupationMeasure_apply_eq_of_not_mem
    (x : E) {s : Set E} (hs : MeasurableSet s) (hx : x ∉ s) :
    (((μ[P, X] x).bind (κ 1)) s) = (μ[P, X] x) s := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let f : ℕ → ℝ≥0∞ := fun n ↦
    (P x : Measure Ω) {ω | X n ω ∈ s ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}
  have hτpos : ∀ ω : Ω, ((0 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω := by
    intro ω
    have hτge1 : (1 : ℕ∞) ≤ (τ_[X, x]^1) ω := by
      have h : (1 : ℕ) ≤ MeasureTheory.hittingAfter X ({x} : Set E) 1 ω := le_hittingAfter ω
      simpa [iteratedEntranceTime_one] using h
    exact lt_of_lt_of_le (by simp) hτge1
  have hzero : f 0 = 0 := by
    have hEq :
        {ω | X 0 ω ∈ s ∧ (((0 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} = X 0 ⁻¹' s := by
      ext ω
      constructor
      · intro hω
        exact hω.1
      · intro hω
        exact ⟨hω, hτpos ω⟩
    -- Proof comment: the initial law is concentrated at `x`, so the initial term vanishes when
    -- `s` avoids `x`.
    dsimp [f]
    rw [hEq, ← Measure.map_apply (hReal.measurable_process 0) hs, hReal.initial_eq x]
    exact (dirac_eq_zero_iff_not_mem hs).2 hx
  have hshift :
      (∑' n : ℕ, (P x : Measure Ω) {ω |
          X (n + 1) ω ∈ s ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}) =
        ∑' n : ℕ, f (n + 1) := by
    -- Proof comment: off the diagonal `x ∉ s`, the next-step event is the shifted tail event.
    refine tsum_congr fun n ↦ ?_
    exact congrArg (fun t : Set Ω ↦ (P x : Measure Ω) t)
      (nextStepBeforeReturn_mem_eq_succTail_of_not_mem (x := x) (s := s) hx n)
  have htail :
      ∑' n : ℕ, f (n + 1) = ∑' n : ℕ, f n := by
    -- Proof comment: split the nonnegative series into its initial term and tail, then remove the
    -- zero initial term.
    calc
      ∑' n : ℕ, f (n + 1) = f 0 + ∑' n : ℕ, f (n + 1) := by simp [hzero]
      _ = ∑' n : ℕ, f n := by
            symm
            simpa using (tsum_eq_zero_add' (f := f) ENNReal.summable)
  -- Proof comment: the owner-level set formulas reduce the whole statement to the shifted-series
  -- identity proved above.
  calc
    (((μ[P, X] x).bind (κ 1)) s)
      = ∑' n : ℕ, (P x : Measure Ω) {ω |
          X (n + 1) ω ∈ s ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} :=
        comp_returnCycleOccupationMeasure_apply (P := P) (X := X) (κ := κ) x hs
    _ = ∑' n : ℕ, f (n + 1) := hshift
    _ = ∑' n : ℕ, f n := htail
    _ = (μ[P, X] x) s := by
          symm
          exact returnCycleOccupationMeasure_apply (P := P) (X := X) (κ := κ) x hs

-- Proof sketch: use the strong Markov property at the first positive return time `τ_x^1` and the
-- decomposition of one-step transitions by whether the next state is `x` or not. The singleton
-- masses still control the self branch, but the final equality is now proved on arbitrary
-- measurable sets to avoid an unavailable singleton-extensionality theorem on a possibly
-- uncountable discrete state space.
/- The source-facing invariant-measure statement is repaired to the chapter's countable-state
setting, matching the singleton-sum formulas used throughout this file. -/
/-- Theorem 17.47: on a countable discrete state space, if `x` is recurrent, then the measure
`(μ[P, X]) x`, whose singleton masses count the expected visits to each state before the first
positive return to `x`, is invariant under the one-step kernel `κ 1`. -/
theorem recurrentState_returnCycleOccupationMeasure_comp_eq
    {x : E} (hx : IsRecurrentState P X x) :
    Kernel.Invariant (κ 1) ((μ[P, X]) x) := by
  rw [Kernel.Invariant]
  ext s hs
  by_cases hxs : x ∈ s
  · let t : Set E := s \ {x}
    have ht : MeasurableSet t := hs.diff (measurableSet_singleton x)
    have hxt : x ∉ t := by
      simp [t]
    have hdisj : Disjoint ({x} : Set E) t := by
      refine Set.disjoint_left.2 ?_
      intro y hy1 hy2
      exact hy2.2 hy1
    have hsplit : ({x} : Set E) ∪ t = s := by
      ext y
      by_cases hy : y = x
      · subst hy
        simp [t, hxs]
      · simp [t, hy]
    have hsingletonComp : (((μ[P, X] x).bind (κ 1)) {x}) = 1 := by
      -- Proof comment: the singleton `{x}` branch is exactly the exact first-return partition.
      calc
        (((μ[P, X] x).bind (κ 1)) {x})
          = ∑' n : ℕ, (P x : Measure Ω) {ω |
              X (n + 1) ω = x ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} :=
            comp_returnCycleOccupationMeasure_apply_singleton_eq_tsum_nextStepBeforeReturn
              (P := P) (X := X) (κ := κ) x x
        _ = ∑' n : ℕ, (P x : Measure Ω) {ω | (τ_[X, x]^1) ω = n + 1} := by
              refine tsum_congr fun n ↦ ?_
              exact congrArg (fun t : Set Ω ↦ (P x : Measure Ω) t) <| by
                ext ω
                simpa using (step_beforeReturn_self_iff_firstReturn_eq (X := X) x n ω)
        _ = 1 := tsum_firstReturnProbabilities_eq_one (P := P) (X := X) (κ := κ) x hx
    have hsingletonMass : (μ[P, X] x) {x} = 1 := by
      -- Proof comment: the excursion mass at `x` is the unique initial visit before the first
      -- positive return.
      rw [returnCycleOccupationMeasure_apply_singleton]
      exact returnCycleOccupationMass_self_eq_one (P := P) (X := X) (κ := κ) x
    -- Proof comment: split `s` into `{x}` and the off-diagonal remainder `s \ {x}`, prove
    -- invariance on each piece, and reassemble by disjoint additivity.
    calc
      (((μ[P, X] x).bind (κ 1)) s)
        = (((μ[P, X] x).bind (κ 1)) (({x} : Set E) ∪ t)) := by rw [hsplit.symm]
      _ = (((μ[P, X] x).bind (κ 1)) {x}) + (((μ[P, X] x).bind (κ 1)) t) := by
            rw [measure_union hdisj ht]
      _ = 1 + (μ[P, X] x) t := by
            rw [hsingletonComp,
              comp_returnCycleOccupationMeasure_apply_eq_of_not_mem
                (P := P) (X := X) (κ := κ) x ht hxt]
      _ = (μ[P, X] x) {x} + (μ[P, X] x) t := by rw [hsingletonMass]
      _ = (μ[P, X] x) (({x} : Set E) ∪ t) := by
            symm
            exact measure_union hdisj ht
      _ = (μ[P, X] x) s := by rw [hsplit]
  · -- Proof comment: away from `x`, the shifted before-return series reindexes directly.
    exact comp_returnCycleOccupationMeasure_apply_eq_of_not_mem
      (P := P) (X := X) (κ := κ) x hs hxs

end

end ProbabilityTheory
