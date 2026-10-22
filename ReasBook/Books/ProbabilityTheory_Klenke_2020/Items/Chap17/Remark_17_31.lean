/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Exercise_17_4_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_37
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

namespace DiscreteMarkovChain

universe u

/-- Local owner copy for Remark 17.31: a realization of a discrete-time Markov semigroup by a
process `X` started from laws `P`. This keeps the item independent of the broken Chapter 17
import chain through `Theorem_17_8`. -/
class IsMarkovProcessRealization {Ω : Type u} [MeasurableSpace Ω] {E : Type*}
    [MeasurableSpace E] (κ : ℕ → Kernel E E)
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) : Prop where
  /-- The prescribed transition family is a Markov semigroup. -/
  semigroup : IsMarkovSemigroup κ
  /-- Each time slice of the realization is measurable. -/
  measurable_process : ∀ t : ℕ, Measurable (X t)
  /-- The realization starts from the deterministic initial state. -/
  initial_eq : ∀ x : E, (P x : Measure Ω).map (X 0) = Measure.dirac x
  /-- The one-time marginal at time `t` is the kernel row `κ t x`. -/
  transition_eq : ∀ x : E, ∀ t : ℕ, (P x : Measure Ω).map (X t) = κ t x
  /-- Conditioning on the history up to time `s` yields the time-homogeneous transition law
  at increment `t`. -/
  markov_property :
    ∀ x ⦃A : Set E⦄, MeasurableSet A → ∀ s t : ℕ,
      (P x)⟦X (t + s) ⁻¹' A | generatedFiltrationSpace X s⟧ =ᵐ[(P x : Measure Ω)]
        fun ω ↦ ((κ t) (X s ω)).real A

/-- Helper for Remark 17.31: the local owner copy of a discrete-time Markov realization carries
the shared Chapter 17 owner realization structure as well. -/
private theorem ownerIsMarkovProcessRealization
    {Ω : Type u} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization κ P X] :
    ProbabilityTheory.IsMarkovProcessRealization κ P X := by
  let hLocal : IsMarkovProcessRealization κ P X := inferInstance
  -- Proof comment: the local record was copied verbatim from the owner Chapter 17 class, so the
  -- bridge is just field-by-field reuse.
  exact
    { semigroup := hLocal.semigroup
      measurable_process := hLocal.measurable_process
      initial_eq := hLocal.initial_eq
      transition_eq := hLocal.transition_eq
      markov_property := hLocal.markov_property }

/-- Helper for Remark 17.31: register the bridge from the local owner-copy realization to the
shared Chapter 17 realization class. -/
private instance
    {Ω : Type u} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization κ P X] :
    ProbabilityTheory.IsMarkovProcessRealization κ P X :=
  ownerIsMarkovProcessRealization

/-- Local owner copy for Remark 17.31: the expected first return time `𝔼_x[τ_x^1]`. -/
def expectedFirstReturnTime {Ω : Type u} [MeasurableSpace Ω] {E : Type*}
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x : E) : ℝ≥0∞ :=
  ∫⁻ ω, ((τ_[X, x]^1) ω : ℝ≥0∞) ∂(P x : Measure Ω)

/-- Local owner copy for Remark 17.31: a state is recurrent when its positive-time return
probability is `1`. -/
def IsRecurrentState {Ω : Type u} [MeasurableSpace Ω] {E : Type*}
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x : E) : Prop :=
  (F[P, X]) x x = 1

/-- Local owner copy for Remark 17.31: a state is positive recurrent when its expected first
return time is finite. -/
def IsPositiveRecurrentState {Ω : Type u} [MeasurableSpace Ω] {E : Type*}
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x : E) : Prop :=
  expectedFirstReturnTime P X x < ⊤

/-- Local owner copy for Remark 17.31: a state is null recurrent when it is recurrent but not
positive recurrent. -/
def IsNullRecurrentState {Ω : Type u} [MeasurableSpace Ω] {E : Type*}
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x : E) : Prop :=
  IsRecurrentState P X x ∧ ¬ IsPositiveRecurrentState P X x

/-- Local owner copy for Remark 17.31: a state is transient when its return probability is
strictly smaller than `1`. -/
def IsTransientState {Ω : Type u} [MeasurableSpace Ω] {E : Type*}
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x : E) : Prop :=
  (F[P, X]) x x < 1

/-- Local owner copy for Remark 17.31: a one-step transition-matrix state is absorbing when it
stays fixed with probability `1`. -/
def IsAbsorbingState {E : Type*} (p : E → E → ℝ≥0∞) (x : E) : Prop :=
  p x x = 1

/-- Local owner copy for Remark 17.31: a chain is positive recurrent when every state is positive
recurrent. -/
def IsPositiveRecurrentMarkovChain {Ω : Type u} [MeasurableSpace Ω] {E : Type*}
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ x : E, IsPositiveRecurrentState P X x

/-- Local owner copy for Remark 17.31: a chain is null recurrent when every state is null
recurrent. -/
def IsNullRecurrentMarkovChain {Ω : Type u} [MeasurableSpace Ω] {E : Type*}
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ x : E, IsNullRecurrentState P X x

/-- The eight states of the Markov chain drawn in Fig. 17.1. -/
inductive Figure17_1State
  | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8
  deriving DecidableEq, Fintype

open Figure17_1State

/-- The finite state space of Fig. 17.1 carries the discrete measurable structure. -/
instance instMeasurableSpaceFigure17_1State : MeasurableSpace Figure17_1State := ⊤

/-- The transition matrix encoded by Fig. 17.1. -/
def figure17_1TransitionMatrix : Figure17_1State → Figure17_1State → ENNReal
  | s1, s2 => 1 / 2
  | s1, s3 => 1 / 3
  | s1, s4 => 1 / 6
  | s2, s2 => 1
  | s3, s4 => 1 / 2
  | s3, s5 => 1 / 2
  | s4, s3 => 1 / 2
  | s4, s5 => 1 / 2
  | s5, s3 => 3 / 4
  | s5, s6 => 1 / 4
  | s6, s7 => 1 / 4
  | s6, s8 => 3 / 4
  | s7, s8 => 1
  | s8, s6 => 1 / 2
  | s8, s7 => 1 / 2
  | _, _ => 0

/-- Helper for Remark 17.31: the singleton mass of the discrete kernel for Fig. 17.1 is exactly
the corresponding matrix entry. -/
private theorem figure17_1_discreteMatrixKernel_apply_singleton
    (x y : Figure17_1State) :
    discreteMatrixKernel figure17_1TransitionMatrix x ({y} : Set Figure17_1State) =
      figure17_1TransitionMatrix x y := by
  -- Proof comment: unfold the discrete kernel and isolate the only summand that contributes to
  -- the singleton `{y}`.
  rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
  simpa using
    (Measure.sum_smul_dirac_singleton
      (f := fun z : Figure17_1State ↦ figure17_1TransitionMatrix x z) (a := y))

/-- The nearest-neighbor transition matrix encoded by Fig. 17.2, with parameter `r ∈ [0,1]`,
deterministic jump `0 → 1`, and, for `n + 1`, left jump probability `1 - r` and right jump
probability `r`. -/
def figure17_2TransitionMatrix (r : Set.Icc (0 : ENNReal) 1) : ℕ → ℕ → ENNReal
  | 0, 1 => 1
  | 0, _ => 0
  | n + 1, m =>
      if m = n then 1 - (r : ENNReal) else if m = n + 2 then (r : ENNReal) else 0

/-- Helper for Remark 17.31: subclaim (1) says that in Fig. 17.1,
state `2` is absorbing. -/
theorem figure17_1_state2_isAbsorbing :
    IsAbsorbingState figure17_1TransitionMatrix s2 := by
  -- The absorbing-state predicate is exactly the one-step self-transition being `1`.
  simp [IsAbsorbingState, figure17_1TransitionMatrix]

section Figure17_1

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Figure17_1State → ProbabilityMeasure Ω} {X : ℕ → Ω → Figure17_1State}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ n) P X]

/-- Helper for Remark 17.31: the positive-time hit event of a fixed state is measurable. -/
private theorem figure17_1_measurableSet_exists_positiveEq
    (hX_meas : ∀ n : ℕ, Measurable (X n)) (x : Figure17_1State) :
    MeasurableSet {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} := by
  have hUnion :
      {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = ⋃ n : ℕ, {ω | 0 < n ∧ X n ω = x} := by
    ext ω
    simp
  rw [hUnion]
  refine MeasurableSet.iUnion fun n ↦ ?_
  by_cases hn : 0 < n
  · have hset : {ω | 0 < n ∧ X n ω = x} = X n ⁻¹' ({x} : Set Figure17_1State) := by
      ext ω
      simp [hn]
    rw [hset]
    exact (hX_meas n) (measurableSet_singleton x)
  · have hset : {ω | 0 < n ∧ X n ω = x} = (∅ : Set Ω) := by
      ext ω
      simp [hn]
    rw [hset]
    simp

/-- Helper for Remark 17.31: every generated history filtration of the realized chain is
contained in the ambient measurable space. -/
private theorem figure17_1_generatedFiltrationSpace_le_ambient
    (hX_meas : ∀ n : ℕ, Measurable (X n)) (n : ℕ) :
    generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
  -- Proof comment: each coordinate sigma-algebra in the generated filtration is ambient because
  -- every time slice of the realization is measurable.
  refine iSup_le fun j ↦ iSup_le fun hj ↦ ?_
  exact (hX_meas j).comap_le

/-- Helper for Remark 17.31: a state-membership event at time `j ≤ n` is measurable for the
generated filtration at time `n`. -/
private theorem figure17_1_measurableSet_mem_of_le_generatedFiltration
    {j n : ℕ} (hjn : j ≤ n) (A : Set Figure17_1State) :
    MeasurableSet[generatedFiltrationSpace X n] {ω | X j ω ∈ A} := by
  have hXj_meas : Measurable[generatedFiltrationSpace X n] (X j) := by
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le j <| le_iSup_of_le hjn le_rfl
  simpa [Set.preimage, Set.mem_setOf_eq] using hXj_meas MeasurableSet.of_discrete

/-- Helper for Remark 17.31: a countable union of real-null events is again real-null. -/
private theorem figure17_1_measureReal_iUnion_null
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : ℕ → Set Ω)
    (hA_zero : ∀ n : ℕ, μ.real (A n) = 0) :
    μ.real (⋃ n : ℕ, A n) = 0 := by
  have hA_zero_ennreal : ∀ n : ℕ, μ (A n) = 0 := by
    intro n
    rcases (ENNReal.toReal_eq_zero_iff (μ (A n))).mp (by simpa [Measure.real_def] using hA_zero n) with
      hzero | htop
    · exact hzero
    · exact False.elim (measure_ne_top μ (A n) htop)
  have hUnion_zero : μ (⋃ n : ℕ, A n) = 0 := measure_iUnion_null hA_zero_ennreal
  simpa [Measure.real_def, hUnion_zero]

/-- Helper for Remark 17.31: integrating the Markov property over a history event that already
fixes `X n = y` factors the future singleton mass through the `m`-step row from `y`. -/
private theorem figure17_1_measureInter_stateEvent_eq_mul_singletonMass
    (x y z : Figure17_1State) (n m : ℕ) {A : Set Ω}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z}) =
      ((((discreteMatrixKernel figure17_1TransitionMatrix ^ m) y) ({z} : Set Figure17_1State)).toReal) *
        (P x : Measure Ω).real A := by
  let μ : Measure Ω := P x
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ k) P X := inferInstance
  let B : Set Ω := X (n + m) ⁻¹' ({z} : Set Figure17_1State)
  have hB_meas : MeasurableSet B := by
    simpa [B] using (hReal.measurable_process (n + m)) (measurableSet_singleton z)
  have hA_measAmbient : MeasurableSet A := by
    have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› :=
      figure17_1_generatedFiltrationSpace_le_ambient (X := X) hReal.measurable_process n
    dsimp [LE.le] at hFiltration_le
    exact hFiltration_le (s := A) hA_meas
  have hMarkovGenerated :
      μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
        fun ω ↦ (((discreteMatrixKernel figure17_1TransitionMatrix ^ m) (X n ω))
          ({z} : Set Figure17_1State)).toReal := by
    simpa [μ, B, add_comm] using
      hReal.markov_property x (A := ({z} : Set Figure17_1State)) (measurableSet_singleton z) n m
  have hIndicatorIntegrable : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB_meas
  -- Proof comment: integrate the one-step Markov identity over the history event `A`, then use
  -- that `A` already determines the time-`n` state.
  calc
    μ.real (A ∩ {ω | X (n + m) ω = z}) =
        ∫ ω in A, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂μ := by
          rw [setIntegral_condExp
              (figure17_1_generatedFiltrationSpace_le_ambient (X := X) hReal.measurable_process n)
              hIndicatorIntegrable hA_meas,
            ← integral_indicator hA_measAmbient]
          symm
          simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
            Set.inter_comm, smul_eq_mul] using
            integral_indicator_const (1 : ℝ) (hA_measAmbient.inter hB_meas)
    _ = ∫ ω in A,
          (((discreteMatrixKernel figure17_1TransitionMatrix ^ m) (X n ω))
            ({z} : Set Figure17_1State)).toReal ∂μ := by
          exact integral_congr_ae hMarkovGenerated.restrict
    _ = ∫ _ in A,
          ((((discreteMatrixKernel figure17_1TransitionMatrix ^ m) y)
            ({z} : Set Figure17_1State)).toReal) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [self_mem_ae_restrict (μ := μ) (s := A) hA_measAmbient] with ω hω
          have hω : X n ω = y := hA_sub hω
          rw [hω]
    _ = ((((discreteMatrixKernel figure17_1TransitionMatrix ^ m) y)
          ({z} : Set Figure17_1State)).toReal) * μ.real A := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- Helper for Remark 17.31: the probability of a one-step state slice is exactly the
corresponding matrix entry of Fig. 17.1. -/
private theorem figure17_1_timeOne_stateEvent
    (x y : Figure17_1State) :
    (P x : Measure Ω) {ω | X 1 ω = y} = figure17_1TransitionMatrix x y := by
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ k) P X := inferInstance
  have hTransition :
      ((P x : Measure Ω).map (X 1)) ({y} : Set Figure17_1State) =
        ((discreteMatrixKernel figure17_1TransitionMatrix ^ 1) x) ({y} : Set Figure17_1State) :=
    congrArg (fun μ : Measure Figure17_1State ↦ μ ({y} : Set Figure17_1State))
      (hReal.transition_eq x 1)
  rw [pow_one, figure17_1_discreteMatrixKernel_apply_singleton] at hTransition
  -- Proof comment: evaluate the time-one marginal on the singleton `{y}` and identify it with
  -- the corresponding discrete matrix entry.
  simpa [Measure.map_apply, hReal.measurable_process 1] using hTransition

/-- Helper for Remark 17.31: the probability of a one-step state slice is exactly the
corresponding matrix entry of Fig. 17.1. -/
private theorem figure17_1_timeOne_stateEvent_real
    (x y : Figure17_1State) :
    (P x : Measure Ω).real {ω | X 1 ω = y} = (figure17_1TransitionMatrix x y).toReal := by
  -- Proof comment: convert the one-time marginal identity to a singleton probability statement.
  simpa [Measure.real_def] using
    congrArg ENNReal.toReal (figure17_1_timeOne_stateEvent (P := P) (X := X) x y)

/-- Helper for Remark 17.31: finite-horizon no-hit events in Fig. 17.1 are measurable. -/
private theorem figure17_1_measurableSet_noHitHorizon
    (hX_meas : ∀ n : ℕ, Measurable (X n)) (x : Figure17_1State) (n M : ℕ) :
    MeasurableSet (noHitHorizonLocal X x n M) := by
  classical
  have hEq :
      noHitHorizonLocal X x n M =
        ⋂ m ∈ (Finset.Icc 1 M : Finset ℕ),
          {ω | X (n + m) ω ≠ x} := by
    ext ω
    simp [noHitHorizonLocal, Finset.mem_Icc]
  rw [hEq]
  refine MeasurableSet.biInter (Set.to_countable _) ?_
  intro m hm
  exact (hX_meas (n + m)) (measurableSet_singleton x).compl

/-- Helper for Remark 17.31: `figure17_1_futurePrefixEvent X n f` fixes the finite path segment
`X n, X (n + 1), ..., X (n + M)` to the values prescribed by `f`. -/
private def figure17_1_futurePrefixEvent (Y : ℕ → Ω → Figure17_1State) (n : ℕ) {M : ℕ}
    (f : Fin (M + 1) → Figure17_1State) : Set Ω :=
  {ω | ∀ i : Fin (M + 1), Y (n + (i : ℕ)) ω = f i}

/-- Helper for Remark 17.31: exact finite future-prefix events in Fig. 17.1 are measurable. -/
private theorem figure17_1_measurableSet_futurePrefixEvent
    (hX_meas : ∀ n : ℕ, Measurable (X n)) (n : ℕ) {M : ℕ}
    (f : Fin (M + 1) → Figure17_1State) :
    MeasurableSet (figure17_1_futurePrefixEvent X n f) := by
  have hEq :
      figure17_1_futurePrefixEvent X n f =
        ⋂ i : Fin (M + 1), {ω | X (n + (i : ℕ)) ω = f i} := by
    ext ω
    simp [figure17_1_futurePrefixEvent]
  rw [hEq]
  refine MeasurableSet.iInter fun i ↦ ?_
  exact hX_meas (n + (i : ℕ)) (measurableSet_singleton (f i))

/-- Helper for Remark 17.31: exact finite future-prefix events are already measurable with
respect to the deterministic history up to their terminal time. -/
private theorem figure17_1_measurableSet_futurePrefixEvent_generated
    (n : ℕ) {M : ℕ} (f : Fin (M + 1) → Figure17_1State) :
    MeasurableSet[generatedFiltrationSpace X (n + M)] (figure17_1_futurePrefixEvent X n f) := by
  have hEq :
      figure17_1_futurePrefixEvent X n f =
        ⋂ i : Fin (M + 1), {ω | X (n + (i : ℕ)) ω = f i} := by
    ext ω
    simp [figure17_1_futurePrefixEvent]
  rw [hEq]
  refine MeasurableSet.iInter fun i ↦ ?_
  exact figure17_1_measurableSet_mem_of_le_generatedFiltration
    (X := X) (j := n + (i : ℕ)) (n := n + M)
    (Nat.add_le_add_left (Nat.le_of_lt_succ i.2) n) ({f i} : Set Figure17_1State)

/-- Helper for Remark 17.31: at horizon `0`, an exact future-prefix event is just the state event
at the current deterministic time. -/
private theorem figure17_1_futurePrefixEvent_zero_eq_stateEvent
    (Y : ℕ → Ω → Figure17_1State) (n : ℕ) (f : Fin 1 → Figure17_1State) :
    figure17_1_futurePrefixEvent Y n f = {ω | Y n ω = f 0} := by
  ext ω
  simp [figure17_1_futurePrefixEvent]

/-- Helper for Remark 17.31: a longer exact future-prefix event splits into its shorter prefix
and terminal one-step event. -/
private theorem figure17_1_futurePrefixEvent_succ_eq
    (Y : ℕ → Ω → Figure17_1State) {M n : ℕ} (f : Fin (M + 2) → Figure17_1State) :
    figure17_1_futurePrefixEvent Y n f =
      figure17_1_futurePrefixEvent Y n (fun i : Fin (M + 1) ↦ f i.castSucc) ∩
        {ω | Y (n + (M + 1)) ω = f (Fin.last (M + 1))} := by
  ext ω
  constructor
  · intro hω
    refine ⟨?_, ?_⟩
    · intro i
      simpa [figure17_1_futurePrefixEvent] using hω i.castSucc
    · simpa [figure17_1_futurePrefixEvent] using hω (Fin.last (M + 1))
  · rintro ⟨hωPrefix, hωLast⟩
    intro i
    by_cases hi : i = Fin.last (M + 1)
    · subst hi
      simpa [figure17_1_futurePrefixEvent] using hωLast
    · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      simpa [figure17_1_futurePrefixEvent] using hωPrefix j

/-- Helper for Remark 17.31: an exact future-prefix event determines its terminal state. -/
private theorem figure17_1_futurePrefixEvent_terminal_subset
    (Y : ℕ → Ω → Figure17_1State) {M n : ℕ} (f : Fin (M + 1) → Figure17_1State) :
    figure17_1_futurePrefixEvent Y n f ⊆ {ω | Y (n + M) ω = f (Fin.last M)} := by
  intro ω hω
  simpa [figure17_1_futurePrefixEvent] using hω (Fin.last M)

/-- Helper for Remark 17.31: the deterministic-time state-slice factorization is convenient in
raw `Measure` (`ℝ≥0∞`) form as well. -/
private theorem figure17_1_measureInter_stateEvent_eq_mul_singletonMass_ennreal
    (x y z : Figure17_1State) (n m : ℕ) {A : Set Ω}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) =
      (((discreteMatrixKernel figure17_1TransitionMatrix ^ m) y) ({z} : Set Figure17_1State)) *
        (P x : Measure Ω) A := by
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ k) P X := inferInstance
  let _ : IsMarkovKernel (discreteMatrixKernel figure17_1TransitionMatrix ^ m) :=
    hReal.semigroup.isMarkovKernel m
  have hstep :
      (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z}) =
        ((((discreteMatrixKernel figure17_1TransitionMatrix ^ m) y)
          ({z} : Set Figure17_1State)).toReal) *
          (P x : Measure Ω).real A :=
    figure17_1_measureInter_stateEvent_eq_mul_singletonMass
      (P := P) (X := X) x y z n m hA_meas hA_sub
  have hleft_ne_top :
      (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) ≠ ⊤ := measure_ne_top _ _
  have hkernel_ne_top :
      (((discreteMatrixKernel figure17_1TransitionMatrix ^ m) y)
        ({z} : Set Figure17_1State)) ≠ ⊤ := measure_ne_top _ _
  have hA_ne_top : (P x : Measure Ω) A ≠ ⊤ := measure_ne_top _ _
  -- Proof comment: convert the real-valued Markov slice identity back to ENNReal masses.
  calc
    (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) =
        ENNReal.ofReal ((P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z})) := by
          symm
          exact ENNReal.ofReal_toReal hleft_ne_top
    _ =
        ENNReal.ofReal
          ((((discreteMatrixKernel figure17_1TransitionMatrix ^ m) y)
            ({z} : Set Figure17_1State)).toReal *
            (P x : Measure Ω).real A) := by
          rw [hstep]
    _ =
        (((discreteMatrixKernel figure17_1TransitionMatrix ^ m) y)
          ({z} : Set Figure17_1State)) *
          (P x : Measure Ω) A := by
          rw [ENNReal.ofReal_mul]
          · rw [ENNReal.ofReal_toReal hkernel_ne_top]
            change
              (((discreteMatrixKernel figure17_1TransitionMatrix ^ m) y)
                ({z} : Set Figure17_1State)) *
                  ENNReal.ofReal (((P x : Measure Ω) A).toReal) =
                (((discreteMatrixKernel figure17_1TransitionMatrix ^ m) y)
                  ({z} : Set Figure17_1State)) *
                  (P x : Measure Ω) A
            rw [ENNReal.ofReal_toReal hA_ne_top]
          · positivity

/-- Helper for Remark 17.31: once a history event pins down the state at time `n`, intersecting
it with an exact future path factors through the path law started from that pinned state. -/
private theorem figure17_1_measureInter_futurePrefixEvent_eq_mul
    {start current : Figure17_1State} {A : Set Ω} {n M : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = current})
    (f : Fin (M + 1) → Figure17_1State) :
    (P start : Measure Ω) (A ∩ figure17_1_futurePrefixEvent X n f) =
      (P current : Measure Ω) (figure17_1_futurePrefixEvent X 0 f) * (P start : Measure Ω) A := by
  induction M generalizing n A current with
  | zero =>
      let hReal :
          IsMarkovProcessRealization
            (fun k : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ k) P X := inferInstance
      have hright_eval :
          (P current : Measure Ω) (figure17_1_futurePrefixEvent X 0 f) =
            if f 0 = current then 1 else 0 := by
        rw [figure17_1_futurePrefixEvent_zero_eq_stateEvent (Y := X) (n := 0) f]
        have hpreimage : {ω | X 0 ω = f 0} = X 0 ⁻¹' ({f 0} : Set Figure17_1State) := by
          ext ω
          simp
        rw [hpreimage]
        rw [← Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton (f 0))]
        rw [hReal.initial_eq current]
        by_cases hf0 : f 0 = current <;> simp [hf0]
      by_cases hf0 : f 0 = current
      · have hleft_eq :
          A ∩ figure17_1_futurePrefixEvent X n f = A := by
            ext ω
            constructor
            · intro hω
              exact hω.1
            · intro hω
              refine ⟨hω, ?_⟩
              rw [figure17_1_futurePrefixEvent_zero_eq_stateEvent (Y := X) (n := n) f]
              simpa [hf0] using hA_sub hω
        -- Proof comment: at horizon zero the future-prefix event only asks for the pinned current
        -- state, so it contributes the indicator `if f 0 = current then 1 else 0`.
        calc
          (P start : Measure Ω) (A ∩ figure17_1_futurePrefixEvent X n f) =
              (P start : Measure Ω) A := by
                rw [hleft_eq]
          _ = 1 * (P start : Measure Ω) A := by rw [one_mul]
          _ = (P current : Measure Ω) (figure17_1_futurePrefixEvent X 0 f) *
                (P start : Measure Ω) A := by
                rw [hright_eval, if_pos hf0]
      · have hleft_eq :
          A ∩ figure17_1_futurePrefixEvent X n f = ∅ := by
            ext ω
            constructor
            · rintro ⟨hωA, hωf⟩
              rw [figure17_1_futurePrefixEvent_zero_eq_stateEvent (Y := X) (n := n) f] at hωf
              exact hf0 (hωf.symm.trans (hA_sub hωA))
            · intro hω
              exact False.elim (by simpa using hω)
        calc
          (P start : Measure Ω) (A ∩ figure17_1_futurePrefixEvent X n f) = 0 := by
            simp [hleft_eq]
          _ = (P current : Measure Ω) (figure17_1_futurePrefixEvent X 0 f) *
                (P start : Measure Ω) A := by
                rw [hright_eval, if_neg hf0]
                simp
  | succ M ih =>
      let g : Fin (M + 1) → Figure17_1State := fun i ↦ f i.castSucc
      let B : Set Ω := A ∩ figure17_1_futurePrefixEvent X n g
      have hA_meas_big : MeasurableSet[generatedFiltrationSpace X (n + M)] A := by
        have hmono : generatedFiltrationSpace X n ≤ generatedFiltrationSpace X (n + M) := by
          refine iSup₂_le fun r hr ↦ ?_
          exact le_iSup_of_le r <| le_iSup_of_le (hr.trans (Nat.le_add_right n M)) le_rfl
        exact hmono (s := A) hA_meas
      have hB_meas : MeasurableSet[generatedFiltrationSpace X (n + M)] B := by
        exact hA_meas_big.inter
          (figure17_1_measurableSet_futurePrefixEvent_generated (X := X) (n := n) g)
      have hB_sub : B ⊆ {ω | X (n + M) ω = g (Fin.last M)} := by
        intro ω hω
        exact figure17_1_futurePrefixEvent_terminal_subset (Y := X) (n := n) g hω.2
      have hleft_step :
          (P start : Measure Ω) (A ∩ figure17_1_futurePrefixEvent X n f) =
            (((discreteMatrixKernel figure17_1TransitionMatrix ^ 1) (g (Fin.last M)))
              ({f (Fin.last (M + 1))} : Set Figure17_1State)) *
              (P start : Measure Ω) B := by
        calc
          (P start : Measure Ω) (A ∩ figure17_1_futurePrefixEvent X n f) =
              (P start : Measure Ω)
                (B ∩ {ω | X ((n + M) + 1) ω = f (Fin.last (M + 1))}) := by
                  simp [B, g, figure17_1_futurePrefixEvent_succ_eq, Nat.add_assoc,
                    Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
          _ =
              (((discreteMatrixKernel figure17_1TransitionMatrix ^ 1) (g (Fin.last M)))
                ({f (Fin.last (M + 1))} : Set Figure17_1State)) *
                (P start : Measure Ω) B := by
                  simpa [B] using
                    figure17_1_measureInter_stateEvent_eq_mul_singletonMass_ennreal
                      (P := P) (X := X) start (g (Fin.last M)) (f (Fin.last (M + 1)))
                      (n + M) 1 hB_meas hB_sub
      have hg_meas :
          MeasurableSet[generatedFiltrationSpace X M] (figure17_1_futurePrefixEvent X 0 g) := by
        have htmp :
            MeasurableSet[generatedFiltrationSpace X (0 + M)] (figure17_1_futurePrefixEvent X 0 g) :=
          figure17_1_measurableSet_futurePrefixEvent_generated (X := X) (n := 0) g
        convert htmp using 1 <;> simp [zero_add]
      have hg_sub :
          figure17_1_futurePrefixEvent X 0 g ⊆ {ω | X M ω = g (Fin.last M)} := by
        have htmp :
            figure17_1_futurePrefixEvent X 0 g ⊆ {ω | X (0 + M) ω = g (Fin.last M)} :=
          figure17_1_futurePrefixEvent_terminal_subset (Y := X) (n := 0) g
        simpa [zero_add] using htmp
      have hright_step :
          (P current : Measure Ω) (figure17_1_futurePrefixEvent X 0 f) =
            (((discreteMatrixKernel figure17_1TransitionMatrix ^ 1) (g (Fin.last M)))
              ({f (Fin.last (M + 1))} : Set Figure17_1State)) *
              (P current : Measure Ω) (figure17_1_futurePrefixEvent X 0 g) := by
        calc
          (P current : Measure Ω) (figure17_1_futurePrefixEvent X 0 f) =
              (P current : Measure Ω)
                (figure17_1_futurePrefixEvent X 0 g ∩
                  {ω | X (M + 1) ω = f (Fin.last (M + 1))}) := by
                  simp [g, figure17_1_futurePrefixEvent_succ_eq, Nat.add_assoc,
                    Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
          _ =
              (((discreteMatrixKernel figure17_1TransitionMatrix ^ 1) (g (Fin.last M)))
                ({f (Fin.last (M + 1))} : Set Figure17_1State)) *
                (P current : Measure Ω) (figure17_1_futurePrefixEvent X 0 g) := by
                  simpa using
                    figure17_1_measureInter_stateEvent_eq_mul_singletonMass_ennreal
                      (P := P) (X := X) current (g (Fin.last M)) (f (Fin.last (M + 1))) M 1
                      hg_meas hg_sub
      -- Proof comment: split off the last coordinate of the finite path and reuse the induction
      -- hypothesis on the shorter prefix.
      calc
        (P start : Measure Ω) (A ∩ figure17_1_futurePrefixEvent X n f) =
            (((discreteMatrixKernel figure17_1TransitionMatrix ^ 1) (g (Fin.last M)))
              ({f (Fin.last (M + 1))} : Set Figure17_1State)) *
              (P start : Measure Ω) B := hleft_step
        _ =
            (((discreteMatrixKernel figure17_1TransitionMatrix ^ 1) (g (Fin.last M)))
              ({f (Fin.last (M + 1))} : Set Figure17_1State)) *
              ((P current : Measure Ω) (figure17_1_futurePrefixEvent X 0 g) *
                (P start : Measure Ω) A) := by
                rw [ih hA_meas hA_sub g]
        _ =
            ((((discreteMatrixKernel figure17_1TransitionMatrix ^ 1) (g (Fin.last M)))
              ({f (Fin.last (M + 1))} : Set Figure17_1State)) *
              (P current : Measure Ω) (figure17_1_futurePrefixEvent X 0 g)) *
              (P start : Measure Ω) A := by
                rw [mul_assoc]
        _ = (P current : Measure Ω) (figure17_1_futurePrefixEvent X 0 f) *
              (P start : Measure Ω) A := by
              rw [hright_step]

/-- Helper for Remark 17.31: a one-step decomposition of a finite no-hit horizon in Fig. 17.1
splits according to the time-one state. -/
private theorem figure17_1_noHitHorizon_step_decomposition
    (start target : Figure17_1State) (M : ℕ) :
    (P start : Measure Ω) (noHitHorizonLocal X target 0 (M + 1)) =
      Finset.sum (Finset.univ.erase target : Finset Figure17_1State) fun z ↦
        (P z : Measure Ω) (noHitHorizonLocal X target 0 M) *
          figure17_1TransitionMatrix start z := by
  classical
  let A : Figure17_1State → Set Ω := fun z ↦ {ω | X 1 ω = z}
  let T : Type := {f : Fin (M + 1) → Figure17_1State // ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ target}
  have hsplit :
      noHitHorizonLocal X target 0 (M + 1) =
        ⋃ z ∈ (Finset.univ.erase target : Finset Figure17_1State), A z ∩ noHitHorizonLocal X target 1 M := by
    ext ω
    constructor
    · intro hω
      refine Set.mem_iUnion.2 ⟨X 1 ω, ?_⟩
      have hneq : X 1 ω ≠ target := by
        simpa using hω 1 (by simp) (by omega)
      refine Set.mem_iUnion.2 ⟨by simp [A, hneq], ?_⟩
      refine ⟨rfl, ?_⟩
      intro m hm1 hmM
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hω (m + 1) (by omega) (by omega)
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨z, hzω⟩
      rcases Set.mem_iUnion.1 hzω with ⟨hz, hωz⟩
      rcases hωz with ⟨hz1, htail⟩
      intro m hm1 hmM
      cases m with
      | zero =>
          omega
      | succ m =>
          cases m with
          | zero =>
              have hz_ne_target : z ≠ target := (Finset.mem_erase.mp hz).1
              have hstep : X 1 ω ≠ target := by
                intro hEq
                exact hz_ne_target (hz1.symm.trans hEq)
              simpa using hstep
          | succ k =>
              have htail' : X (1 + (k + 1)) ω ≠ target := htail (k + 1) (by simp) (by omega)
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.succ_eq_add_one] using
                htail'
  have hslices :
      ∀ z ∈ (Finset.univ.erase target : Finset Figure17_1State),
        (P start : Measure Ω) (A z ∩ noHitHorizonLocal X target 1 M) =
          (P z : Measure Ω) (noHitHorizonLocal X target 0 M) * (P start : Measure Ω) (A z) := by
    intro z hz
    have hA_meas : MeasurableSet[generatedFiltrationSpace X 1] (A z) := by
      simpa [A] using
        figure17_1_measurableSet_mem_of_le_generatedFiltration
          (X := X) (j := 1) (n := 1) le_rfl ({z} : Set Figure17_1State)
    have hA_sub : A z ⊆ {ω | X 1 ω = z} := by
      intro ω hω
      exact hω
    have hleft_union :
        A z ∩ noHitHorizonLocal X target 1 M =
          ⋃ f : T, A z ∩ figure17_1_futurePrefixEvent X 1 f.1 := by
      ext ω
      constructor
      · rintro ⟨hωA, hωNoHit⟩
        let f : Fin (M + 1) → Figure17_1State := fun i ↦ X (1 + (i : ℕ)) ω
        have hf : ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ target := by
          intro i hi
          simpa [f, Nat.add_assoc] using hωNoHit (i : ℕ) hi (Nat.le_of_lt_succ i.2)
        refine Set.mem_iUnion.2 ?_
        refine ⟨⟨f, hf⟩, ?_⟩
        refine ⟨hωA, ?_⟩
        intro i
        rfl
      · intro hω
        rcases Set.mem_iUnion.1 hω with ⟨f, hωf⟩
        refine ⟨hωf.1, ?_⟩
        intro m hm hmM
        let i : Fin (M + 1) := ⟨m, Nat.lt_succ_of_le hmM⟩
        have hpath : X (1 + m) ω = f.1 i := by
          simpa [figure17_1_futurePrefixEvent, i] using hωf.2 i
        exact hpath.trans_ne (f.2 i hm)
    have hright_union :
        noHitHorizonLocal X target 0 M = ⋃ f : T, figure17_1_futurePrefixEvent X 0 f.1 := by
      ext ω
      constructor
      · intro hωNoHit
        let f : Fin (M + 1) → Figure17_1State := fun i ↦ X (i : ℕ) ω
        have hf : ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ target := by
          intro i hi
          simpa [f, zero_add] using hωNoHit (i : ℕ) hi (Nat.le_of_lt_succ i.2)
        refine Set.mem_iUnion.2 ?_
        refine ⟨⟨f, hf⟩, ?_⟩
        intro i
        simp [f, zero_add]
      · intro hω
        rcases Set.mem_iUnion.1 hω with ⟨f, hωf⟩
        intro m hm hmM
        let i : Fin (M + 1) := ⟨m, Nat.lt_succ_of_le hmM⟩
        have hpath : X (0 + m) ω = f.1 i := by
          simpa [figure17_1_futurePrefixEvent, i, zero_add] using hωf i
        exact hpath.trans_ne (f.2 i hm)
    have hpairwise_left :
        Pairwise (fun f g : T ↦ Disjoint (A z ∩ figure17_1_futurePrefixEvent X 1 f.1)
          (A z ∩ figure17_1_futurePrefixEvent X 1 g.1)) := by
      intro f g hfg
      refine Set.disjoint_left.2 ?_
      intro ω hωf hωg
      have hEq : f.1 = g.1 := by
        funext i
        exact (hωf.2 i).symm.trans (hωg.2 i)
      exact hfg (Subtype.ext hEq)
    have hpairwise_right :
        Pairwise (fun f g : T ↦ Disjoint (figure17_1_futurePrefixEvent X 0 f.1)
          (figure17_1_futurePrefixEvent X 0 g.1)) := by
      intro f g hfg
      refine Set.disjoint_left.2 ?_
      intro ω hωf hωg
      have hEq : f.1 = g.1 := by
        funext i
        exact (hωf i).symm.trans (hωg i)
      exact hfg (Subtype.ext hEq)
    have hleft_sum :
        (P start : Measure Ω) (A z ∩ noHitHorizonLocal X target 1 M) =
          ∑' f : T, (P start : Measure Ω) (A z ∩ figure17_1_futurePrefixEvent X 1 f.1) := by
      rw [hleft_union, measure_iUnion hpairwise_left]
      intro f
      exact (((inferInstance : IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ k) P X).measurable_process 1
          (measurableSet_singleton z))).inter
        (figure17_1_measurableSet_futurePrefixEvent
          (X := X)
          ((inferInstance : IsMarkovProcessRealization
            (fun k : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ k) P X).measurable_process)
          (n := 1) f.1)
    have hright_sum :
        (P z : Measure Ω) (noHitHorizonLocal X target 0 M) =
          ∑' f : T, (P z : Measure Ω) (figure17_1_futurePrefixEvent X 0 f.1) := by
      rw [hright_union, measure_iUnion hpairwise_right]
      intro f
      exact figure17_1_measurableSet_futurePrefixEvent
        (X := X)
        ((inferInstance : IsMarkovProcessRealization
          (fun k : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ k) P X).measurable_process)
        (n := 0) f.1
    -- Proof comment: partition the future no-hit block by exact path segments, factor each exact
    -- path through the Markov property at time `1`, and sum over all such finite paths.
    calc
      (P start : Measure Ω) (A z ∩ noHitHorizonLocal X target 1 M) =
          ∑' f : T, (P start : Measure Ω) (A z ∩ figure17_1_futurePrefixEvent X 1 f.1) := hleft_sum
      _ =
          ∑' f : T, (P z : Measure Ω) (figure17_1_futurePrefixEvent X 0 f.1) *
            (P start : Measure Ω) (A z) := by
              refine tsum_congr fun f ↦ ?_
              exact figure17_1_measureInter_futurePrefixEvent_eq_mul
                (P := P) (X := X) hA_meas hA_sub f.1
      _ =
          (∑' f : T, (P z : Measure Ω) (figure17_1_futurePrefixEvent X 0 f.1)) *
            (P start : Measure Ω) (A z) := by
              rw [ENNReal.tsum_mul_right]
      _ = (P z : Measure Ω) (noHitHorizonLocal X target 0 M) * (P start : Measure Ω) (A z) := by
            rw [← hright_sum]
  have hdisj :
      Set.PairwiseDisjoint (↑(Finset.univ.erase target : Finset Figure17_1State))
        (fun z ↦ A z ∩ noHitHorizonLocal X target 1 M) := by
    intro z hz w hw hzw
    refine Set.disjoint_left.2 ?_
    intro ω hωz hωw
    have : z = w := hωz.1.symm.trans hωw.1
    exact hzw this
  have hmeas :
      ∀ z ∈ (Finset.univ.erase target : Finset Figure17_1State),
        MeasurableSet (A z ∩ noHitHorizonLocal X target 1 M) := by
    intro z hz
    let hReal :
        IsMarkovProcessRealization
          (fun k : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ k) P X := inferInstance
    exact (hReal.measurable_process 1 (measurableSet_singleton z)).inter
      (figure17_1_measurableSet_noHitHorizon (X := X) hReal.measurable_process target 1 M)
  calc
    (P start : Measure Ω) (noHitHorizonLocal X target 0 (M + 1)) =
        (P start : Measure Ω)
          (⋃ z ∈ (Finset.univ.erase target : Finset Figure17_1State),
            A z ∩ noHitHorizonLocal X target 1 M) := by
              rw [hsplit]
    _ =
        ∑ z ∈ (Finset.univ.erase target : Finset Figure17_1State),
          (P start : Measure Ω) (A z ∩ noHitHorizonLocal X target 1 M) := by
            rw [measure_biUnion_finset hdisj hmeas]
    _ =
        ∑ z ∈ (Finset.univ.erase target : Finset Figure17_1State),
          (P z : Measure Ω) (noHitHorizonLocal X target 0 M) * (P start : Measure Ω) (A z) := by
            refine Finset.sum_congr rfl ?_
            intro z hz
            exact hslices z hz
    _ =
        Finset.sum (Finset.univ.erase target : Finset Figure17_1State) fun z ↦
          (P z : Measure Ω) (noHitHorizonLocal X target 0 M) *
            figure17_1TransitionMatrix start z := by
              refine Finset.sum_congr rfl ?_
              intro z hz
              rw [figure17_1_timeOne_stateEvent (P := P) (X := X) start z]

/-- Helper for Remark 17.31: the generated history filtration is monotone in deterministic time.
-/
private theorem figure17_1_generatedFiltrationSpace_monoNat
    {m n : ℕ} (hmn : m ≤ n) :
    generatedFiltrationSpace X m ≤ generatedFiltrationSpace X n := by
  -- Proof comment: every coordinate visible by time `m` is still visible by the larger history
  -- sigma-algebra at time `n`.
  refine iSup₂_le fun r hr ↦ ?_
  exact le_iSup_of_le r <| le_iSup_of_le (hr.trans hmn) le_rfl

/-- Helper for Remark 17.31: the first positive entrance time is bounded by `n` exactly when the
path visits the target state between times `1` and `n`. -/
private theorem figure17_1_firstReturnTime_le_iff
    (x : Figure17_1State) (n : ℕ) (ω : Ω) :
    (τ_[X, x]^1) ω ≤ n ↔ ∃ j ∈ Set.Icc 1 n, X j ω = x := by
  -- Proof comment: specialize the finite-prefix description of `hittingAfter` to the singleton
  -- target `{x}`.
  simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using
    (hittingAfter_le_iff (u := X) (s := ({x} : Set Figure17_1State)) (n := 1) (ω := ω) (i := n))

/-- Helper for Remark 17.31: the bounded first-return event is measurable with respect to the
history up to that deterministic horizon. -/
private theorem figure17_1_measurableSet_firstReturnTimeLe
    (x : Figure17_1State) (n : ℕ) :
    MeasurableSet[generatedFiltrationSpace X n] {ω | (τ_[X, x]^1) ω ≤ n} := by
  -- Proof comment: rewrite the event as a finite union of singleton fibers of the coordinates
  -- `X j` with `j ≤ n`.
  have hEq :
      {ω | (τ_[X, x]^1) ω ≤ n} =
        ⋃ j ∈ ((Finset.Icc 1 n : Finset ℕ) : Set ℕ), X j ⁻¹' ({x} : Set Figure17_1State) := by
    ext ω
    simp [figure17_1_firstReturnTime_le_iff, Finset.mem_Icc]
  rw [hEq]
  refine MeasurableSet.biUnion (Set.to_countable _) ?_
  intro j hj
  have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
  exact figure17_1_measurableSet_mem_of_le_generatedFiltration
    (X := X) (j := j) (n := n) hjn ({x} : Set Figure17_1State)

/-- Helper for Remark 17.31: the counting measure of the initial segment below `t : ℕ∞`
recovers `t` itself. -/
private theorem figure17_1_count_lt_enat_eq (t : ℕ∞) :
    Measure.count {n : ℕ | (n : ℕ∞) < t} = t := by
  -- Proof comment: split into the infinite and finite cases and identify the finite tail set with
  -- an initial range.
  by_cases ht : t = ⊤
  · subst ht
    simpa [Measure.count_univ, ENat.card_eq_top_of_infinite] using
      (Measure.count_univ : Measure.count (Set.univ : Set ℕ) = ENat.card ℕ)
  · lift t to ℕ using ht with m hm
    subst hm
    have hEq : {n : ℕ | (n : ℕ∞) < (m : ℕ∞)} = (Finset.range m : Set ℕ) := by
      ext n
      simp
    rw [hEq, Measure.count_apply_finset]
    simp

/-- Helper for Remark 17.31: the pointwise tail-indicator series is the counting measure of the
tail set `{n | n < τ_[X, x]^1(ω)}`. -/
private theorem figure17_1_tsum_tailIndicators_eq_countTailMass
    (x : Figure17_1State) (ω : Ω) :
    (∑' n : ℕ,
      Set.indicator {ω' | (n : ℕ∞) < (τ_[X, x]^1) ω'} (fun _ ↦ (1 : ℝ≥0∞)) ω) =
      Measure.count {n : ℕ | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  -- Proof comment: rewrite the series as the sum over the subtype of admissible indices and then
  -- identify it with counting measure.
  rw [Measure.count_apply MeasurableSet.of_discrete]
  calc
    ∑' n : ℕ,
        Set.indicator {ω' | (n : ℕ∞) < (τ_[X, x]^1) ω'} (fun _ ↦ (1 : ℝ≥0∞)) ω
      = ∑' _ : {n : ℕ | (n : ℕ∞) < (τ_[X, x]^1) ω}, (1 : ℝ≥0∞) := by
          simpa [Set.indicator_apply] using
            (tsum_subtype {n : ℕ | (n : ℕ∞) < (τ_[X, x]^1) ω}
              (fun _ : ℕ ↦ (1 : ℝ≥0∞))).symm
    _ = ENat.card {n : ℕ | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
          simpa using
            (ENNReal.tsum_one :
              ∑' _ : {n : ℕ | (n : ℕ∞) < (τ_[X, x]^1) ω}, (1 : ℝ≥0∞) =
                ENat.card {n : ℕ | (n : ℕ∞) < (τ_[X, x]^1) ω})
    _ = ({n : ℕ | (n : ℕ∞) < (τ_[X, x]^1) ω}).encard := by
          rw [ENat.card_coe_set_eq]

/-- Helper for Remark 17.31: the first return time is the tail-indicator series of the events
`{ω | n < τ_[X, x]^1(ω)}`. -/
private theorem figure17_1_firstReturnTime_eq_tsum_tailIndicators
    (x : Figure17_1State) (ω : Ω) :
    ((τ_[X, x]^1) ω : ℝ≥0∞) =
      ∑' n : ℕ,
        Set.indicator {ω' | (n : ℕ∞) < (τ_[X, x]^1) ω'} (fun _ ↦ (1 : ℝ≥0∞)) ω := by
  -- Proof comment: rewrite the series as a counting measure of the tail set and then collapse
  -- that counting measure back to the entrance time.
  calc
    ((τ_[X, x]^1) ω : ℝ≥0∞)
      = Measure.count {n : ℕ | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
          symm
          exact figure17_1_count_lt_enat_eq ((τ_[X, x]^1) ω)
    _ = ∑' n : ℕ,
          Set.indicator
            {ω' | (n : ℕ∞) < (τ_[X, x]^1) ω'} (fun _ ↦ (1 : ℝ≥0∞)) ω := by
          symm
          exact figure17_1_tsum_tailIndicators_eq_countTailMass (X := X) x ω

/-- Helper for Remark 17.31: the tail event `{ω | n < τ_[X, x]^1(ω)}` is measurable already at
time `n`. -/
private theorem figure17_1_measurableSet_firstReturnTimeTail
    (x : Figure17_1State) (n : ℕ) :
    MeasurableSet[generatedFiltrationSpace X n] {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  -- Proof comment: the strict tail is the complement of the measurable bounded-horizon hit event
  -- inside the same history sigma-algebra.
  have hEq :
      {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} = {ω | (τ_[X, x]^1) ω ≤ n}ᶜ := by
    ext ω
    simp
  rw [hEq]
  exact (figure17_1_measurableSet_firstReturnTimeLe (X := X) x n).compl

/-- Helper for Remark 17.31: the expected first return time is the tail-probability series of the
first return event. -/
private theorem figure17_1_expectedFirstReturnTime_eq_tsum_tailProbabilities
    (x : Figure17_1State) :
    expectedFirstReturnTime P X x =
      ∑' n : ℕ, (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  -- Proof comment: rewrite the entrance time pointwise as the tail-indicator series, commute the
  -- countable sum with the integral, and evaluate each indicator integral as a tail probability.
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ k) P X := inferInstance
  rw [expectedFirstReturnTime]
  calc
    ∫⁻ ω, ((τ_[X, x]^1) ω : ℝ≥0∞) ∂(P x : Measure Ω)
      = ∫⁻ ω,
          ∑' n : ℕ,
            Set.indicator {ω' | (n : ℕ∞) < (τ_[X, x]^1) ω'} (fun _ ↦ (1 : ℝ≥0∞)) ω
          ∂(P x : Measure Ω) := by
            refine lintegral_congr_ae ?_
            filter_upwards [] with ω
            rw [figure17_1_firstReturnTime_eq_tsum_tailIndicators (X := X) x ω]
    _ = ∑' n : ℕ,
          ∫⁻ ω,
            Set.indicator {ω' | (n : ℕ∞) < (τ_[X, x]^1) ω'} (fun _ ↦ (1 : ℝ≥0∞)) ω
          ∂(P x : Measure Ω) := by
            rw [lintegral_tsum]
            intro n
            have hTailAmbient :
                MeasurableSet {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
              have hFiltration_le :
                  generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› :=
                figure17_1_generatedFiltrationSpace_le_ambient
                  (X := X) hReal.measurable_process n
              dsimp [LE.le] at hFiltration_le
              exact hFiltration_le
                (s := {ω | (n : ℕ∞) < (τ_[X, x]^1) ω})
                (figure17_1_measurableSet_firstReturnTimeTail (X := X) x n)
            exact (measurable_const.indicator hTailAmbient).aemeasurable
    _ = ∑' n : ℕ, (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
          refine tsum_congr fun n ↦ ?_
          have hTailAmbient :
              MeasurableSet {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
            have hFiltration_le :
                generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› :=
              figure17_1_generatedFiltrationSpace_le_ambient
                (X := X) hReal.measurable_process n
            dsimp [LE.le] at hFiltration_le
            exact hFiltration_le
              (s := {ω | (n : ℕ∞) < (τ_[X, x]^1) ω})
              (figure17_1_measurableSet_firstReturnTimeTail (X := X) x n)
          simpa using
            (lintegral_indicator_one (μ := (P x : Measure Ω))
              (s := {ω | (n : ℕ∞) < (τ_[X, x]^1) ω})
              hTailAmbient)

/-- Helper for Remark 17.31: the positive-time first-return event is measurable on the ambient
space. -/
private theorem figure17_1_measurableSet_firstReturnTimeFinite
    (hX_meas : ∀ n : ℕ, Measurable (X n)) (x : Figure17_1State) :
    MeasurableSet {ω | (τ_[X, x]^1) ω < ⊤} := by
  have hEq :
      {ω | (τ_[X, x]^1) ω < ⊤} = ⋃ n : ℕ, X n.succ ⁻¹' ({x} : Set Figure17_1State) := by
    ext ω
    constructor
    · intro hω
      rcases (hittingAfter_singleton_lt_top_iff X x ω).1 (by
        simpa [iteratedEntranceTime_one] using hω) with ⟨n, hn, hnx⟩
      rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨m, rfl⟩
      exact Set.mem_iUnion.2 ⟨m, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hnx⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      exact (hittingAfter_singleton_lt_top_iff X x ω).2
        ⟨n.succ, Nat.succ_pos _, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hn⟩
  rw [hEq]
  refine MeasurableSet.iUnion fun n ↦ ?_
  -- Proof comment: each successor-time singleton slice is measurable because the realization is
  -- measurable at every deterministic time.
  exact (hX_meas n.succ) (measurableSet_singleton x)

/-- Helper for Remark 17.31: finite expected first return time forces recurrence for the local
Fig. 17.1 realization. -/
private theorem figure17_1_positiveRecurrentState_isRecurrentState
    (x : Figure17_1State) (hx : IsPositiveRecurrentState P X x) :
    IsRecurrentState P X x := by
  let A : Set Ω := {ω | (τ_[X, x]^1) ω < ⊤}
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ k) P X := inferInstance
  have hA_meas : MeasurableSet A :=
    figure17_1_measurableSet_firstReturnTimeFinite (X := X) hReal.measurable_process x
  have hAc_zero : (P x : Measure Ω) Aᶜ = 0 := by
    by_contra hAc_zero
    have hindicator_top :
        ∫⁻ ω, Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞)) ω ∂(P x : Measure Ω) = ∞ := by
      have hmeas :
          AEMeasurable (Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞))) (P x : Measure Ω) :=
        (measurable_const.indicator hA_meas.compl).aemeasurable
      have hset :
          (P x : Measure Ω)
            {ω | Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞)) ω = ∞} ≠ 0 := by
        have hEq :
            {ω | Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞)) ω = ∞} = Aᶜ := by
          ext ω
          by_cases hω : ω ∈ Aᶜ
          · have hnotA : ω ∉ A := hω
            simp [Set.indicator, hω, hnotA]
          · have hA : ω ∈ A := by simpa using hω
            simp [Set.indicator, hω, hA]
        simpa [hEq] using hAc_zero
      exact lintegral_eq_top_of_measure_eq_top_ne_zero hmeas hset
    have hdom :
        ∫⁻ ω, Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞)) ω ∂(P x : Measure Ω) ≤
          expectedFirstReturnTime P X x := by
      rw [expectedFirstReturnTime]
      refine lintegral_mono fun ω ↦ ?_
      by_cases hω : ω ∈ Aᶜ
      · have hτ : (τ_[X, x]^1) ω = ⊤ := by
          simpa [A, Set.mem_setOf_eq, lt_top_iff_ne_top] using hω
        simp [Set.indicator, hω, hτ]
      · simp [Set.indicator, hω]
    have htop : expectedFirstReturnTime P X x = ∞ := by
      simpa [hindicator_top] using hdom
    exact (ne_of_lt hx) htop
  have hA_prob : (P x : Measure Ω) A = 1 := by
    have hA_le : (P x : Measure Ω) A ≤ 1 := by
      have hA_le_univ : (P x : Measure Ω) A ≤ (P x : Measure Ω) Set.univ :=
        measure_mono (show A ⊆ Set.univ by intro ω _; simp)
      simpa using hA_le_univ
    have hA_ge : 1 ≤ (P x : Measure Ω) A := by
      have hunion : A ∪ Aᶜ = Set.univ := by
        ext ω
        simp [A]
      calc
        1 = (P x : Measure Ω) Set.univ := by simp
        _ ≤ (P x : Measure Ω) A + (P x : Measure Ω) Aᶜ := by
              have hUnion_le :
                  (P x : Measure Ω) (A ∪ Aᶜ) ≤ (P x : Measure Ω) A + (P x : Measure Ω) Aᶜ :=
                measure_union_le A Aᶜ
              simpa [hunion] using hUnion_le
        _ = (P x : Measure Ω) A := by rw [hAc_zero, add_zero]
    exact le_antisymm hA_le hA_ge
  have hhit :
      (P x : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = 1 := by
    have hEq : {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = A := by
      ext ω
      simpa [A, iteratedEntranceTime_one] using (hittingAfter_singleton_lt_top_iff X x ω).symm
    rw [hEq]
    exact hA_prob
  rw [IsRecurrentState, everHitsProbability_def]
  exact (ENNReal.toReal_eq_one_iff _).2 hhit

/-- Helper for Remark 17.31: the occupation-mass series of the return-cycle measure collapses to
the first-return tail probabilities on the finite state space of Fig. 17.1. -/
private theorem figure17_1_tsum_returnCycleOccupationMass_eq_tsum_tailProbabilities
    (x : Figure17_1State) :
    ∑' y : Figure17_1State, ProbabilityTheory.returnCycleOccupationMass P X x y =
      ∑' n : ℕ, (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
  calc
    ∑' y : Figure17_1State, ProbabilityTheory.returnCycleOccupationMass P X x y
      = ∫⁻ y, ProbabilityTheory.returnCycleOccupationMass P X x y ∂Measure.count := by
          rw [lintegral_count]
    _ = ∫⁻ y, ∑' n : ℕ,
          (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}
          ∂Measure.count := by
          rfl
    _ = ∑' n : ℕ,
          ∫⁻ y, (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}
          ∂Measure.count := by
          rw [lintegral_tsum]
          intro n
          exact (Measurable.of_discrete :
            Measurable fun y : Figure17_1State ↦
              (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}).aemeasurable
    _ = ∑' n : ℕ, (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
          refine tsum_congr fun n ↦ ?_
          rw [lintegral_count, tsum_fintype]
          have hpairwise :
              Set.PairwiseDisjoint (↑(Finset.univ : Finset Figure17_1State))
                (fun y ↦ {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}) := by
            intro y hy z hz hyz
            refine Set.disjoint_left.2 ?_
            intro ω hωy hωz
            exact hyz (hωy.1.symm.trans hωz.1)
          have hmeas :
              ∀ y ∈ (Finset.univ : Finset Figure17_1State),
                MeasurableSet {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} := by
            intro y hy
            let hReal :
                IsMarkovProcessRealization
                  (fun k : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ k) P X :=
              inferInstance
            have htailAmbient :
                MeasurableSet {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
              have hFiltration_le :
                  generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› :=
                figure17_1_generatedFiltrationSpace_le_ambient
                  (X := X) hReal.measurable_process n
              dsimp [LE.le] at hFiltration_le
              exact hFiltration_le
                (s := {ω | (n : ℕ∞) < (τ_[X, x]^1) ω})
                (figure17_1_measurableSet_firstReturnTimeTail (X := X) x n)
            exact (hReal.measurable_process n (measurableSet_singleton y)).inter htailAmbient
          have hUnion :
              (⋃ y ∈ (Finset.univ : Finset Figure17_1State),
                {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}) =
                  {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
            ext ω
            constructor
            · intro hω
              rcases Set.mem_iUnion.1 hω with ⟨y, hyω⟩
              rcases Set.mem_iUnion.1 hyω with ⟨hy, hyω'⟩
              exact hyω'.2
            · intro hω
              exact Set.mem_iUnion.2 ⟨X n ω, Set.mem_iUnion.2 ⟨by simp, ⟨rfl, hω⟩⟩⟩
          symm
          rw [← hUnion, measure_biUnion_finset hpairwise hmeas]

/-- Helper for Remark 17.31: the total mass of the return-cycle occupation measure is the
expected first return time. -/
private theorem figure17_1_returnCycleOccupationMeasure_univ_eq_expectedFirstReturnTime
    (x : Figure17_1State) :
    (μ[P, X] x : Measure Figure17_1State) Set.univ = expectedFirstReturnTime P X x := by
  calc
    (μ[P, X] x : Measure Figure17_1State) Set.univ
      = ∫⁻ y, ProbabilityTheory.returnCycleOccupationMass P X x y ∂Measure.count := by
          rw [ProbabilityTheory.returnCycleOccupationMeasure, withDensity_apply _ MeasurableSet.univ,
            Measure.restrict_univ]
    _ = ∑' y : Figure17_1State, ProbabilityTheory.returnCycleOccupationMass P X x y := by
          rw [lintegral_count]
    _ = ∑' n : ℕ, (P x : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, x]^1) ω} := by
          exact figure17_1_tsum_returnCycleOccupationMass_eq_tsum_tailProbabilities
            (P := P) (X := X) x
    _ = expectedFirstReturnTime P X x := by
          symm
          exact figure17_1_expectedFirstReturnTime_eq_tsum_tailProbabilities
            (P := P) (X := X) x

/-- Helper for Remark 17.31: a positive-probability event whose intersection with the
positive-time return event is null forces transience. -/
private theorem figure17_1_transient_of_escapeEvent
    (x : Figure17_1State) {A : Set Ω}
    (hA_pos : 0 < (P x : Measure Ω).real A)
    (hA_hit_zero :
      (P x : Measure Ω).real (A ∩ {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x}) = 0) :
    IsTransientState P X x := by
  let μ : Measure Ω := P x
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ k) P X := inferInstance
  let hitEvent : Set Ω := {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x}
  have hhit_meas : MeasurableSet hitEvent :=
    figure17_1_measurableSet_exists_positiveEq (X := X) hReal.measurable_process x
  have hA_le_compl : μ.real A ≤ μ.real hitEventᶜ := by
    -- Proof comment: removing a null intersection with the return event leaves the same mass
    -- inside the complement of that return event.
    calc
      μ.real A = μ.real (A \ hitEvent) := by
        symm
        exact measureReal_diff_null' (μ := μ) (s₁ := A) (s₂ := hitEvent) hA_hit_zero
      _ ≤ μ.real hitEventᶜ := by
        refine measureReal_mono ?_
        intro ω hω
        exact hω.2
  have hhit_le : μ.real hitEvent ≤ 1 - μ.real A := by
    have hcompl : μ.real hitEventᶜ = 1 - μ.real hitEvent :=
      probReal_compl_eq_one_sub (μ := μ) hhit_meas
    linarith
  -- Proof comment: the return event misses at least the positive mass of `A`, so its
  -- probability is strictly smaller than `1`.
  rw [IsTransientState, everHitsProbability_def]
  linarith

/-- Helper for Remark 17.31: every power of the Fig. 17.1 kernel started from `s2` is the
Dirac mass at `s2`. -/
private theorem figure17_1_absorbingState_pow_dirac (n : ℕ) :
    (discreteMatrixKernel figure17_1TransitionMatrix ^ n) s2 = Measure.dirac s2 := by
  induction n with
  | zero =>
      -- Proof comment: the zero-step kernel is the identity kernel, hence gives the initial
      -- Dirac law.
      rw [Measure.ext_iff_singleton]
      intro y
      change (Kernel.id s2) ({y} : Set Figure17_1State) = (Measure.dirac s2) ({y} : Set Figure17_1State)
      rw [Kernel.id_apply]
  | succ n hn =>
      -- Proof comment: one more step from `s2` still stays at `s2`, so the Dirac law is
      -- preserved by Chapman-Kolmogorov.
      rw [Measure.ext_iff_singleton]
      intro y
      rw [Kernel.pow_succ_apply_eq_lintegral _ n s2 (measurableSet_singleton y)]
      simp_rw [figure17_1_discreteMatrixKernel_apply_singleton]
      rw [hn]
      rw [MeasureTheory.lintegral_fintype]
      fin_cases y <;> simp [figure17_1TransitionMatrix, Pi.single_apply]

/-- Helper for Remark 17.31: once the chain enters the absorbing state `s2`, it cannot hit
`s1` again at any later deterministic time. -/
private theorem figure17_1_state2_pow_singleton_eq_zero (n : ℕ) :
    (((discreteMatrixKernel figure17_1TransitionMatrix ^ n) s2)
      ({s1} : Set Figure17_1State)) = 0 := by
  -- Proof comment: after normalizing the whole `n`-step law to `δ_{s2}`, the singleton mass at
  -- `s1` vanishes immediately.
  rw [figure17_1_absorbingState_pow_dirac]
  simp

/-- Helper for Remark 17.31: every power of the Fig. 17.1 kernel started in the closed class
`{s6, s7, s8}` assigns zero mass to the states outside that class. -/
private theorem figure17_1_closedClass_pow_outside_eq_zero
    {y : Figure17_1State} (hy : y = s6 ∨ y = s7 ∨ y = s8) (n : ℕ) :
    (((discreteMatrixKernel figure17_1TransitionMatrix ^ n) y)
      ({s1} : Set Figure17_1State)) = 0 ∧
      (((discreteMatrixKernel figure17_1TransitionMatrix ^ n) y)
        ({s2} : Set Figure17_1State)) = 0 ∧
      (((discreteMatrixKernel figure17_1TransitionMatrix ^ n) y)
        ({s3} : Set Figure17_1State)) = 0 ∧
      (((discreteMatrixKernel figure17_1TransitionMatrix ^ n) y)
        ({s4} : Set Figure17_1State)) = 0 ∧
      (((discreteMatrixKernel figure17_1TransitionMatrix ^ n) y)
        ({s5} : Set Figure17_1State)) = 0 := by
  induction n with
  | zero =>
      -- Proof comment: the zero-step kernel is the identity, and none of `s6`, `s7`, `s8`
      -- equals an outside state.
      rcases hy with rfl | rfl | rfl
      all_goals
        repeat' constructor
        all_goals
          change (Kernel.id _) _ = _
          rw [Kernel.id_apply]
          simp [Pi.single_apply]
  | succ n hn =>
      rcases hn with ⟨hs1, hs2, hs3, hs4, hs5⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- Proof comment: no one-step successor of any state in Fig. 17.1 lands in `s1`.
        rw [Kernel.pow_succ_apply_eq_lintegral _ n y (measurableSet_singleton s1)]
        simp_rw [figure17_1_discreteMatrixKernel_apply_singleton]
        rw [MeasureTheory.lintegral_fintype]
        refine Finset.sum_eq_zero ?_
        intro i hi
        fin_cases i <;> simp [figure17_1TransitionMatrix]
      · -- Proof comment: the closed class has no one-step transition into the absorbing state
        -- `s2`.
        rw [Kernel.pow_succ_apply_eq_lintegral _ n y (measurableSet_singleton s2)]
        simp_rw [figure17_1_discreteMatrixKernel_apply_singleton]
        rw [MeasureTheory.lintegral_fintype]
        refine Finset.sum_eq_zero ?_
        intro i hi
        fin_cases i <;> simp [figure17_1TransitionMatrix, hs1, hs2]
      · -- Proof comment: the only predecessors of `s3` are `s1`, `s4`, and `s5`, which already
        -- have zero `n`-step mass by the induction hypothesis.
        rw [Kernel.pow_succ_apply_eq_lintegral _ n y (measurableSet_singleton s3)]
        simp_rw [figure17_1_discreteMatrixKernel_apply_singleton]
        rw [MeasureTheory.lintegral_fintype]
        refine Finset.sum_eq_zero ?_
        intro i hi
        fin_cases i <;> simp [figure17_1TransitionMatrix, hs1, hs4, hs5]
      · -- Proof comment: the only predecessors of `s4` are `s1` and `s3`, both outside the
        -- closed class.
        rw [Kernel.pow_succ_apply_eq_lintegral _ n y (measurableSet_singleton s4)]
        simp_rw [figure17_1_discreteMatrixKernel_apply_singleton]
        rw [MeasureTheory.lintegral_fintype]
        refine Finset.sum_eq_zero ?_
        intro i hi
        fin_cases i <;> simp [figure17_1TransitionMatrix, hs1, hs3]
      · -- Proof comment: the only predecessors of `s5` are `s3` and `s4`, which already carry
        -- zero mass after `n` steps.
        rw [Kernel.pow_succ_apply_eq_lintegral _ n y (measurableSet_singleton s5)]
        simp_rw [figure17_1_discreteMatrixKernel_apply_singleton]
        rw [MeasureTheory.lintegral_fintype]
        refine Finset.sum_eq_zero ?_
        intro i hi
        fin_cases i <;> simp [figure17_1TransitionMatrix, hs3, hs4]

/-- Helper for Remark 17.31: the closed class `{s6, s7, s8}` never reaches the transient states
`s3`, `s4`, or `s5` at any deterministic time. -/
private theorem figure17_1_closedClass_pow_singleton_eq_zero
    {y x : Figure17_1State} (hy : y = s6 ∨ y = s7 ∨ y = s8)
    (hx : x = s3 ∨ x = s4 ∨ x = s5) (n : ℕ) :
    (((discreteMatrixKernel figure17_1TransitionMatrix ^ n) y)
      ({x} : Set Figure17_1State)) = 0 := by
  -- Proof comment: the stronger closed-class support lemma already records that every outside
  -- singleton has zero mass.
  rcases figure17_1_closedClass_pow_outside_eq_zero hy n with ⟨_, _, hs3, hs4, hs5⟩
  rcases hx with rfl | rfl | rfl
  · exact hs3
  · exact hs4
  · exact hs5

/-- Helper for Remark 17.31: the zero-based no-hit horizon is exactly the strict tail event of
the first positive entrance time. -/
private theorem figure17_1_noHitHorizon_zero_eq_firstReturnTail
    (y : Figure17_1State) (M : ℕ) :
    noHitHorizonLocal X y 0 M = {ω | (M : ℕ∞) < (τ_[X, y]^1) ω} := by
  -- Proof comment: avoiding `y` during the first `M` positive times is equivalent to saying
  -- that the first positive entrance time into `{y}` is strictly larger than `M`.
  ext ω
  constructor
  · intro hω
    change (M : ℕ∞) < (τ_[X, y]^1) ω
    by_contra hle
    have hτle : (τ_[X, y]^1) ω ≤ M := le_of_not_gt hle
    rcases (figure17_1_firstReturnTime_le_iff (X := X) y M ω).1 hτle with ⟨m, hm, hmEq⟩
    exact hω m hm.1 hm.2 (by simpa [zero_add] using hmEq)
  · intro hω
    intro m hm1 hmM hmEq
    have hτle : (τ_[X, y]^1) ω ≤ M :=
      (figure17_1_firstReturnTime_le_iff (X := X) y M ω).2
        ⟨m, ⟨hm1, hmM⟩, by simpa [zero_add] using hmEq⟩
    exact not_le_of_gt hω hτle

/-- Helper for Remark 17.31: subclaim (2) says that in any realization of the
Markov chain of Fig. 17.1, the states `1`, `3`, `4`, and `5` are transient. -/
theorem figure17_1_states1345_transient :
    {x | x = s1 ∨ x = s3 ∨ x = s4 ∨ x = s5} ⊆ {x | IsTransientState P X x} := by
  -- Route correction: the blocker here is no longer the malformed `opaque` declaration shape but
  -- the missing local first-step return-probability calculation for the transient states.
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl
  · let A : Set Ω := {ω | X 1 ω = s2}
    have hA_pos : 0 < (P s1 : Measure Ω).real A := by
      -- Proof comment: the one-step jump `s1 → s2` has probability `1 / 2`.
      rw [figure17_1_timeOne_stateEvent_real (P := P) (X := X) s1 s2]
      norm_num [A, figure17_1TransitionMatrix]
    have hSliceZero :
        ∀ m : ℕ, (P s1 : Measure Ω).real (A ∩ {ω | X (m + 1) ω = s1}) = 0 := by
      intro m
      have hA_meas : MeasurableSet[generatedFiltrationSpace X 1] A := by
        simpa [A] using
          figure17_1_measurableSet_mem_of_le_generatedFiltration
            (X := X) (j := 1) (n := 1) le_rfl ({s2} : Set Figure17_1State)
      have hA_sub : A ⊆ {ω | X 1 ω = s2} := by
        intro ω hω
        exact hω
      -- Proof comment: after the first-step slice `X 1 = s2`, every later mass at `s1`
      -- vanishes because `s2` is absorbing.
      simpa [A, Nat.add_comm, figure17_1_state2_pow_singleton_eq_zero (n := m)] using
        figure17_1_measureInter_stateEvent_eq_mul_singletonMass
          (P := P) (X := X) (x := s1) (y := s2) (z := s1) (n := 1) (m := m)
          hA_meas hA_sub
    have hA_hit_zero :
        (P s1 : Measure Ω).real (A ∩ {ω | ∃ n : ℕ, 0 < n ∧ X n ω = s1}) = 0 := by
      have hUnion :
          A ∩ {ω | ∃ n : ℕ, 0 < n ∧ X n ω = s1} =
            ⋃ m : ℕ, A ∩ {ω | X (m + 1) ω = s1} := by
        ext ω
        constructor
        · intro hω
          rcases hω.2 with ⟨n, hn, hnω⟩
          cases n with
          | zero =>
              cases Nat.lt_asymm hn hn
          | succ m =>
              refine Set.mem_iUnion.2 ⟨m, ?_⟩
              simpa [Nat.succ_eq_add_one] using ⟨hω.1, hnω⟩
        · intro hω
          rcases Set.mem_iUnion.1 hω with ⟨m, hmω⟩
          exact ⟨hmω.1, ⟨m + 1, Nat.succ_pos _, by simpa [Nat.succ_eq_add_one] using hmω.2⟩⟩
      -- Proof comment: the return event is the countable union of those later singleton slices.
      simpa [hUnion] using
        figure17_1_measureReal_iUnion_null
          (μ := (P s1 : Measure Ω)) (A := fun m : ℕ ↦ A ∩ {ω | X (m + 1) ω = s1}) hSliceZero
    exact figure17_1_transient_of_escapeEvent (P := P) (X := X) s1 hA_pos hA_hit_zero
  · let B : Set Ω := {ω | X 1 ω = s5} ∩ {ω | X 2 ω = s6}
    have hStep1 :
        (P s3 : Measure Ω).real {ω | X 1 ω = s5} = 1 / 2 := by
      -- Proof comment: the branch `s3 → s5` has probability `1 / 2`.
      simpa [figure17_1TransitionMatrix] using
        figure17_1_timeOne_stateEvent_real (P := P) (X := X) s3 s5
    have hSlice1_meas : MeasurableSet[generatedFiltrationSpace X 1] {ω | X 1 ω = s5} := by
      simpa using
        figure17_1_measurableSet_mem_of_le_generatedFiltration
          (X := X) (j := 1) (n := 1) le_rfl ({s5} : Set Figure17_1State)
    have hSlice1_sub : {ω | X 1 ω = s5} ⊆ {ω | X 1 ω = s5} := by intro ω hω; exact hω
    have hB_eq :
        (P s3 : Measure Ω).real B =
          (figure17_1TransitionMatrix s5 s6).toReal * (P s3 : Measure Ω).real {ω | X 1 ω = s5} := by
      -- Proof comment: condition on the first jump to `s5`, then use the one-step mass
      -- `s5 → s6 = 1 / 4`.
      calc
        (P s3 : Measure Ω).real B =
            ((((discreteMatrixKernel figure17_1TransitionMatrix ^ 1) s5)
              ({s6} : Set Figure17_1State)).toReal) *
              (P s3 : Measure Ω).real {ω | X 1 ω = s5} := by
              simpa [B] using
                figure17_1_measureInter_stateEvent_eq_mul_singletonMass
                  (P := P) (X := X) (x := s3) (y := s5) (z := s6) (n := 1) (m := 1)
                  hSlice1_meas hSlice1_sub
        _ = (figure17_1TransitionMatrix s5 s6).toReal * (P s3 : Measure Ω).real {ω | X 1 ω = s5} := by
              rw [pow_one, figure17_1_discreteMatrixKernel_apply_singleton]
    have hB_pos : 0 < (P s3 : Measure Ω).real B := by
      rw [hB_eq, hStep1]
      norm_num [figure17_1TransitionMatrix]
    have hB_meas : MeasurableSet[generatedFiltrationSpace X 2] B := by
      have h15 : MeasurableSet[generatedFiltrationSpace X 2] {ω | X 1 ω = s5} := by
        simpa using
          figure17_1_measurableSet_mem_of_le_generatedFiltration
            (X := X) (j := 1) (n := 2) (by omega) ({s5} : Set Figure17_1State)
      have h26 : MeasurableSet[generatedFiltrationSpace X 2] {ω | X 2 ω = s6} := by
        simpa using
          figure17_1_measurableSet_mem_of_le_generatedFiltration
            (X := X) (j := 2) (n := 2) le_rfl ({s6} : Set Figure17_1State)
      simpa [B] using h15.inter h26
    have hB_sub : B ⊆ {ω | X 2 ω = s6} := by
      intro ω hω
      exact hω.2
    have hTailZero :
        ∀ m : ℕ, (P s3 : Measure Ω).real (B ∩ {ω | X (m + 2) ω = s3}) = 0 := by
      intro m
      -- Proof comment: once the path has reached `s6` at time `2`, the closed class
      -- `{s6, s7, s8}` excludes every later visit to `s3`.
      simpa [B, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
        figure17_1_closedClass_pow_singleton_eq_zero
          (hy := Or.inl rfl) (hx := Or.inl rfl) (n := m)] using
        figure17_1_measureInter_stateEvent_eq_mul_singletonMass
          (P := P) (X := X) (x := s3) (y := s6) (z := s3) (n := 2) (m := m)
          hB_meas hB_sub
    have hB_hit_zero :
        (P s3 : Measure Ω).real (B ∩ {ω | ∃ n : ℕ, 0 < n ∧ X n ω = s3}) = 0 := by
      have hTailUnionZero :
          (P s3 : Measure Ω).real (⋃ m : ℕ, B ∩ {ω | X (m + 2) ω = s3}) = 0 := by
        simpa using
          figure17_1_measureReal_iUnion_null
            (μ := (P s3 : Measure Ω)) (A := fun m : ℕ ↦ B ∩ {ω | X (m + 2) ω = s3}) hTailZero
      have hFirstZero : (P s3 : Measure Ω).real (B ∩ {ω | X 1 ω = s3}) = 0 := by
        have hEmpty : B ∩ {ω | X 1 ω = s3} = (∅ : Set Ω) := by
          ext ω
          constructor
          · intro hω
            rcases hω with ⟨⟨h15, _h26⟩, h13⟩
            have : s5 = s3 := h15.symm.trans h13
            cases this
          · intro hω
            cases hω
        simpa [hEmpty]
      have hUnion :
          B ∩ {ω | ∃ n : ℕ, 0 < n ∧ X n ω = s3} =
            (B ∩ {ω | X 1 ω = s3}) ∪ ⋃ m : ℕ, B ∩ {ω | X (m + 2) ω = s3} := by
        ext ω
        constructor
        · intro hω
          rcases hω.2 with ⟨n, hn, hnω⟩
          cases n with
          | zero =>
              cases Nat.lt_asymm hn hn
          | succ n =>
              cases n with
              | zero =>
                  exact Or.inl <| by simpa [B] using ⟨hω.1, hnω⟩
              | succ m =>
                  refine Or.inr <| Set.mem_iUnion.2 ?_
                  refine ⟨m, ?_⟩
                  simpa [Nat.succ_eq_add_one, Nat.add_assoc, B] using ⟨hω.1, hnω⟩
        · intro hω
          rcases hω with hω | hω
          · exact ⟨hω.1, ⟨1, by norm_num, hω.2⟩⟩
          · rcases Set.mem_iUnion.1 hω with ⟨m, hmω⟩
            exact ⟨hmω.1, ⟨m + 2, by omega, by simpa using hmω.2⟩⟩
      have hUpper :
          (P s3 : Measure Ω).real
              ((B ∩ {ω | X 1 ω = s3}) ∪ ⋃ m : ℕ, B ∩ {ω | X (m + 2) ω = s3}) ≤ 0 := by
        simpa [hFirstZero, hTailUnionZero] using
          (measureReal_union_le (μ := (P s3 : Measure Ω))
            (B ∩ {ω | X 1 ω = s3}) (⋃ m : ℕ, B ∩ {ω | X (m + 2) ω = s3}))
      rw [hUnion]
      exact le_antisymm hUpper measureReal_nonneg
    exact figure17_1_transient_of_escapeEvent (P := P) (X := X) s3 hB_pos hB_hit_zero
  · let B : Set Ω := {ω | X 1 ω = s5} ∩ {ω | X 2 ω = s6}
    have hStep1 :
        (P s4 : Measure Ω).real {ω | X 1 ω = s5} = 1 / 2 := by
      -- Proof comment: the branch `s4 → s5` also has probability `1 / 2`.
      simpa [figure17_1TransitionMatrix] using
        figure17_1_timeOne_stateEvent_real (P := P) (X := X) s4 s5
    have hSlice1_meas : MeasurableSet[generatedFiltrationSpace X 1] {ω | X 1 ω = s5} := by
      simpa using
        figure17_1_measurableSet_mem_of_le_generatedFiltration
          (X := X) (j := 1) (n := 1) le_rfl ({s5} : Set Figure17_1State)
    have hSlice1_sub : {ω | X 1 ω = s5} ⊆ {ω | X 1 ω = s5} := by intro ω hω; exact hω
    have hB_eq :
        (P s4 : Measure Ω).real B =
          (figure17_1TransitionMatrix s5 s6).toReal * (P s4 : Measure Ω).real {ω | X 1 ω = s5} := by
      -- Proof comment: after the first jump to `s5`, the same `s5 → s6` branch provides the
      -- escape cylinder.
      calc
        (P s4 : Measure Ω).real B =
            ((((discreteMatrixKernel figure17_1TransitionMatrix ^ 1) s5)
              ({s6} : Set Figure17_1State)).toReal) *
              (P s4 : Measure Ω).real {ω | X 1 ω = s5} := by
              simpa [B] using
                figure17_1_measureInter_stateEvent_eq_mul_singletonMass
                  (P := P) (X := X) (x := s4) (y := s5) (z := s6) (n := 1) (m := 1)
                  hSlice1_meas hSlice1_sub
        _ = (figure17_1TransitionMatrix s5 s6).toReal * (P s4 : Measure Ω).real {ω | X 1 ω = s5} := by
              rw [pow_one, figure17_1_discreteMatrixKernel_apply_singleton]
    have hB_pos : 0 < (P s4 : Measure Ω).real B := by
      rw [hB_eq, hStep1]
      norm_num [figure17_1TransitionMatrix]
    have hB_meas : MeasurableSet[generatedFiltrationSpace X 2] B := by
      have h15 : MeasurableSet[generatedFiltrationSpace X 2] {ω | X 1 ω = s5} := by
        simpa using
          figure17_1_measurableSet_mem_of_le_generatedFiltration
            (X := X) (j := 1) (n := 2) (by omega) ({s5} : Set Figure17_1State)
      have h26 : MeasurableSet[generatedFiltrationSpace X 2] {ω | X 2 ω = s6} := by
        simpa using
          figure17_1_measurableSet_mem_of_le_generatedFiltration
            (X := X) (j := 2) (n := 2) le_rfl ({s6} : Set Figure17_1State)
      simpa [B] using h15.inter h26
    have hB_sub : B ⊆ {ω | X 2 ω = s6} := by
      intro ω hω
      exact hω.2
    have hTailZero :
        ∀ m : ℕ, (P s4 : Measure Ω).real (B ∩ {ω | X (m + 2) ω = s4}) = 0 := by
      intro m
      -- Proof comment: the same closed-class argument now kills all later visits to `s4`.
      simpa [B, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
        figure17_1_closedClass_pow_singleton_eq_zero
          (hy := Or.inl rfl) (hx := Or.inr <| Or.inl rfl) (n := m)] using
        figure17_1_measureInter_stateEvent_eq_mul_singletonMass
          (P := P) (X := X) (x := s4) (y := s6) (z := s4) (n := 2) (m := m)
          hB_meas hB_sub
    have hB_hit_zero :
        (P s4 : Measure Ω).real (B ∩ {ω | ∃ n : ℕ, 0 < n ∧ X n ω = s4}) = 0 := by
      have hTailUnionZero :
          (P s4 : Measure Ω).real (⋃ m : ℕ, B ∩ {ω | X (m + 2) ω = s4}) = 0 := by
        simpa using
          figure17_1_measureReal_iUnion_null
            (μ := (P s4 : Measure Ω)) (A := fun m : ℕ ↦ B ∩ {ω | X (m + 2) ω = s4}) hTailZero
      have hFirstZero : (P s4 : Measure Ω).real (B ∩ {ω | X 1 ω = s4}) = 0 := by
        have hEmpty : B ∩ {ω | X 1 ω = s4} = (∅ : Set Ω) := by
          ext ω
          constructor
          · intro hω
            rcases hω with ⟨⟨h15, _h26⟩, h14⟩
            have : s5 = s4 := h15.symm.trans h14
            cases this
          · intro hω
            cases hω
        simpa [hEmpty]
      have hUnion :
          B ∩ {ω | ∃ n : ℕ, 0 < n ∧ X n ω = s4} =
            (B ∩ {ω | X 1 ω = s4}) ∪ ⋃ m : ℕ, B ∩ {ω | X (m + 2) ω = s4} := by
        ext ω
        constructor
        · intro hω
          rcases hω.2 with ⟨n, hn, hnω⟩
          cases n with
          | zero =>
              cases Nat.lt_asymm hn hn
          | succ n =>
              cases n with
              | zero =>
                  exact Or.inl <| by simpa [B] using ⟨hω.1, hnω⟩
              | succ m =>
                  refine Or.inr <| Set.mem_iUnion.2 ?_
                  refine ⟨m, ?_⟩
                  simpa [Nat.succ_eq_add_one, Nat.add_assoc, B] using ⟨hω.1, hnω⟩
        · intro hω
          rcases hω with hω | hω
          · exact ⟨hω.1, ⟨1, by norm_num, hω.2⟩⟩
          · rcases Set.mem_iUnion.1 hω with ⟨m, hmω⟩
            exact ⟨hmω.1, ⟨m + 2, by omega, by simpa using hmω.2⟩⟩
      have hUpper :
          (P s4 : Measure Ω).real
              ((B ∩ {ω | X 1 ω = s4}) ∪ ⋃ m : ℕ, B ∩ {ω | X (m + 2) ω = s4}) ≤ 0 := by
        simpa [hFirstZero, hTailUnionZero] using
          (measureReal_union_le (μ := (P s4 : Measure Ω))
            (B ∩ {ω | X 1 ω = s4}) (⋃ m : ℕ, B ∩ {ω | X (m + 2) ω = s4}))
      rw [hUnion]
      exact le_antisymm hUpper measureReal_nonneg
    exact figure17_1_transient_of_escapeEvent (P := P) (X := X) s4 hB_pos hB_hit_zero
  · let A : Set Ω := {ω | X 1 ω = s6}
    have hA_pos : 0 < (P s5 : Measure Ω).real A := by
      -- Proof comment: the direct jump `s5 → s6` has probability `1 / 4`.
      rw [figure17_1_timeOne_stateEvent_real (P := P) (X := X) s5 s6]
      norm_num [A, figure17_1TransitionMatrix]
    have hSliceZero :
        ∀ m : ℕ, (P s5 : Measure Ω).real (A ∩ {ω | X (m + 1) ω = s5}) = 0 := by
      intro m
      have hA_meas : MeasurableSet[generatedFiltrationSpace X 1] A := by
        simpa [A] using
          figure17_1_measurableSet_mem_of_le_generatedFiltration
            (X := X) (j := 1) (n := 1) le_rfl ({s6} : Set Figure17_1State)
      have hA_sub : A ⊆ {ω | X 1 ω = s6} := by
        intro ω hω
        exact hω
      -- Proof comment: after the first-step slice `X 1 = s6`, the chain stays in the closed
      -- class and can never hit `s5` again.
      simpa [A, Nat.add_comm,
        figure17_1_closedClass_pow_singleton_eq_zero
          (hy := Or.inl rfl) (hx := Or.inr <| Or.inr rfl) (n := m)] using
        figure17_1_measureInter_stateEvent_eq_mul_singletonMass
          (P := P) (X := X) (x := s5) (y := s6) (z := s5) (n := 1) (m := m)
          hA_meas hA_sub
    have hA_hit_zero :
        (P s5 : Measure Ω).real (A ∩ {ω | ∃ n : ℕ, 0 < n ∧ X n ω = s5}) = 0 := by
      have hUnion :
          A ∩ {ω | ∃ n : ℕ, 0 < n ∧ X n ω = s5} =
            ⋃ m : ℕ, A ∩ {ω | X (m + 1) ω = s5} := by
        ext ω
        constructor
        · intro hω
          rcases hω.2 with ⟨n, hn, hnω⟩
          cases n with
          | zero =>
              cases Nat.lt_asymm hn hn
          | succ m =>
              refine Set.mem_iUnion.2 ⟨m, ?_⟩
              simpa [Nat.succ_eq_add_one] using ⟨hω.1, hnω⟩
        · intro hω
          rcases Set.mem_iUnion.1 hω with ⟨m, hmω⟩
          exact ⟨hmω.1, ⟨m + 1, Nat.succ_pos _, by simpa [Nat.succ_eq_add_one] using hmω.2⟩⟩
      simpa [hUnion] using
        figure17_1_measureReal_iUnion_null
          (μ := (P s5 : Measure Ω)) (A := fun m : ℕ ↦ A ∩ {ω | X (m + 1) ω = s5}) hSliceZero
    exact figure17_1_transient_of_escapeEvent (P := P) (X := X) s5 hA_pos hA_hit_zero

/-- Helper for Remark 17.31: the stationary weights on the closed class `{s6, s7, s8}` are
`4 / 17`, `5 / 17`, and `8 / 17`, with all transient states carrying zero mass. -/
private def figure17_1ClosedClassInvariantWeights : Figure17_1State → ℝ≥0∞
  | s6 => (4 : ℝ≥0∞) / 17
  | s7 => (5 : ℝ≥0∞) / 17
  | s8 => (8 : ℝ≥0∞) / 17
  | _ => 0

/-- Helper for Remark 17.31: the closed-class invariant weights form a probability vector. -/
private theorem figure17_1ClosedClassInvariantWeights_sum :
    Finset.univ.sum figure17_1ClosedClassInvariantWeights = 1 := by
  have huniv : (Finset.univ : Finset Figure17_1State) = {s1, s2, s3, s4, s5, s6, s7, s8} := by
    ext x
    fin_cases x <;> simp
  have hs : (((4 : ℝ≥0∞) / 17) + (5 / 17)) + (8 / 17) = 1 := by
    have h17 : (17 : ℝ≥0∞) ≠ 0 := by
      norm_num
    have h17_top : (17 : ℝ≥0∞) ≠ ∞ := by
      simp
    calc
      (((4 : ℝ≥0∞) / 17) + (5 / 17)) + (8 / 17)
          = (((4 + 5 : ℝ≥0∞) / 17) + (8 / 17)) := by
              exact congrArg (fun z : ℝ≥0∞ ↦ z + (8 / 17))
                (ENNReal.div_add_div_same (a := (4 : ℝ≥0∞)) (b := (5 : ℝ≥0∞))
                  (c := (17 : ℝ≥0∞)))
      _ = ((4 + 5 + 8 : ℝ≥0∞) / 17) := by
            exact ENNReal.div_add_div_same (a := (4 + 5 : ℝ≥0∞)) (b := (8 : ℝ≥0∞))
              (c := (17 : ℝ≥0∞))
      _ = (17 : ℝ≥0∞) / 17 := by
            norm_num
      _ = 1 := ENNReal.div_self h17 h17_top
  rw [huniv]
  simpa [figure17_1ClosedClassInvariantWeights, add_assoc, add_left_comm, add_comm] using hs

/-- Helper for Remark 17.31: the stationary distribution on the closed class `{s6, s7, s8}`. -/
private def figure17_1ClosedClassInvariantDistribution : ProbabilityMeasure Figure17_1State :=
  ⟨(PMF.ofFintype figure17_1ClosedClassInvariantWeights
      figure17_1ClosedClassInvariantWeights_sum).toMeasure,
    inferInstance⟩

/-- Helper for Remark 17.31: the closed-class invariant distribution has the prescribed singleton
masses. -/
private theorem figure17_1ClosedClassInvariantDistribution_apply_singleton
    (x : Figure17_1State) :
    (figure17_1ClosedClassInvariantDistribution : Measure Figure17_1State) {x} =
      figure17_1ClosedClassInvariantWeights x := by
  rw [figure17_1ClosedClassInvariantDistribution]
  exact (PMF.ofFintype figure17_1ClosedClassInvariantWeights
    figure17_1ClosedClassInvariantWeights_sum).toMeasure_apply_singleton x
      (measurableSet_singleton x)

/-- Helper for Remark 17.31: composing a measure on Fig. 17.1 with the discrete kernel and then
evaluating on a singleton gives the corresponding matrix action. -/
private theorem figure17_1_comp_discreteMatrixKernel_apply_singleton_eq_tsum
    (μ : Measure Figure17_1State) (x : Figure17_1State) :
    ((discreteMatrixKernel figure17_1TransitionMatrix) ∘ₘ μ) ({x} : Set Figure17_1State) =
      ∑' y : Figure17_1State, μ ({y} : Set Figure17_1State) * figure17_1TransitionMatrix y x := by
  rw [Measure.comp_eq_sum_of_countable]
  rw [Measure.sum_apply _ (measurableSet_singleton x)]
  congr with y
  rw [Measure.smul_apply]
  rw [figure17_1_discreteMatrixKernel_apply_singleton]
  simp [smul_eq_mul, mul_comm]

/-- Helper for Remark 17.31: the closed-class stationary weights satisfy the singleton balance
equations for Fig. 17.1. -/
private theorem figure17_1ClosedClassInvariantWeights_leftEigenvector
    (x : Figure17_1State) :
    ∑' y : Figure17_1State,
      figure17_1ClosedClassInvariantWeights y * figure17_1TransitionMatrix y x =
        figure17_1ClosedClassInvariantWeights x := by
  fin_cases x
  · have hsupport :
        ∀ y ∉ (∅ : Finset Figure17_1State),
          figure17_1ClosedClassInvariantWeights y * figure17_1TransitionMatrix y s1 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1ClosedClassInvariantWeights, figure17_1TransitionMatrix]
    rw [tsum_eq_sum hsupport]
    simp [figure17_1ClosedClassInvariantWeights]
  · have hsupport :
        ∀ y ∉ (∅ : Finset Figure17_1State),
          figure17_1ClosedClassInvariantWeights y * figure17_1TransitionMatrix y s2 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1ClosedClassInvariantWeights, figure17_1TransitionMatrix]
    rw [tsum_eq_sum hsupport]
    simp [figure17_1ClosedClassInvariantWeights]
  · have hsupport :
        ∀ y ∉ (∅ : Finset Figure17_1State),
          figure17_1ClosedClassInvariantWeights y * figure17_1TransitionMatrix y s3 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1ClosedClassInvariantWeights, figure17_1TransitionMatrix]
    rw [tsum_eq_sum hsupport]
    simp [figure17_1ClosedClassInvariantWeights]
  · have hsupport :
        ∀ y ∉ (∅ : Finset Figure17_1State),
          figure17_1ClosedClassInvariantWeights y * figure17_1TransitionMatrix y s4 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1ClosedClassInvariantWeights, figure17_1TransitionMatrix]
    rw [tsum_eq_sum hsupport]
    simp [figure17_1ClosedClassInvariantWeights]
  · have hsupport :
        ∀ y ∉ (∅ : Finset Figure17_1State),
          figure17_1ClosedClassInvariantWeights y * figure17_1TransitionMatrix y s5 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1ClosedClassInvariantWeights, figure17_1TransitionMatrix]
    rw [tsum_eq_sum hsupport]
    simp [figure17_1ClosedClassInvariantWeights]
  · have hsupport :
        ∀ y ∉ ({s8} : Finset Figure17_1State),
          figure17_1ClosedClassInvariantWeights y * figure17_1TransitionMatrix y s6 = 0 := by
      intro y hy
      fin_cases y <;>
        simp [figure17_1ClosedClassInvariantWeights, figure17_1TransitionMatrix] at hy ⊢
    rw [tsum_eq_sum hsupport]
    calc
      ∑ y ∈ ({s8} : Finset Figure17_1State),
          figure17_1ClosedClassInvariantWeights y * figure17_1TransitionMatrix y s6
          = (((8 : ℝ≥0∞) / 17) * (1 / 2 : ℝ≥0∞)) := by
              simp [figure17_1ClosedClassInvariantWeights, figure17_1TransitionMatrix]
      _ = (4 : ℝ≥0∞) / 17 := by
            have hleft : (((8 : ℝ≥0∞) / 17) * (1 / 2 : ℝ≥0∞)) ≠ ∞ := by
              exact ENNReal.mul_ne_top
                (ENNReal.div_ne_top (by norm_num) (by norm_num))
                (ENNReal.div_ne_top (by norm_num) (by norm_num))
            have hright : ((4 : ℝ≥0∞) / 17) ≠ ∞ := by
              exact ENNReal.div_ne_top (by norm_num) (by norm_num)
            rw [← ENNReal.toReal_eq_toReal_iff' hleft hright]
            rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_div]
            norm_num
      _ = figure17_1ClosedClassInvariantWeights s6 := by
            simp [figure17_1ClosedClassInvariantWeights]
  · have hsupport :
        ∀ y ∉ ({s6, s8} : Finset Figure17_1State),
          figure17_1ClosedClassInvariantWeights y * figure17_1TransitionMatrix y s7 = 0 := by
      intro y hy
      fin_cases y <;>
        simp [figure17_1ClosedClassInvariantWeights, figure17_1TransitionMatrix] at hy ⊢
    rw [tsum_eq_sum hsupport]
    calc
      ∑ y ∈ ({s6, s8} : Finset Figure17_1State),
          figure17_1ClosedClassInvariantWeights y * figure17_1TransitionMatrix y s7
          = (((4 : ℝ≥0∞) / 17) * (1 / 4 : ℝ≥0∞)) +
              (((8 : ℝ≥0∞) / 17) * (1 / 2 : ℝ≥0∞)) := by
                simp [Finset.sum_insert, figure17_1ClosedClassInvariantWeights,
                  figure17_1TransitionMatrix]
      _ = (5 : ℝ≥0∞) / 17 := by
            have hleft1 :
                ((4 : ℝ≥0∞) / 17) * (1 / 4 : ℝ≥0∞) ≠ ∞ := by
              exact ENNReal.mul_ne_top (ENNReal.div_ne_top (by norm_num) (by norm_num))
                (ENNReal.div_ne_top (by norm_num) (by norm_num))
            have hleft2 :
                ((8 : ℝ≥0∞) / 17) * (1 / 2 : ℝ≥0∞) ≠ ∞ := by
              exact ENNReal.mul_ne_top (ENNReal.div_ne_top (by norm_num) (by norm_num))
                (ENNReal.div_ne_top (by norm_num) (by norm_num))
            have hleft :
                (((4 : ℝ≥0∞) / 17) * (1 / 4 : ℝ≥0∞)) +
                  (((8 : ℝ≥0∞) / 17) * (1 / 2 : ℝ≥0∞)) ≠ ∞ := by
              exact ENNReal.add_ne_top.2 ⟨hleft1, hleft2⟩
            have hright : ((5 : ℝ≥0∞) / 17) ≠ ∞ := by
              exact ENNReal.div_ne_top (by norm_num) (by norm_num)
            rw [← ENNReal.toReal_eq_toReal_iff' hleft hright]
            rw [ENNReal.toReal_add hleft1 hleft2, ENNReal.toReal_mul, ENNReal.toReal_mul,
              ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]
            norm_num
      _ = figure17_1ClosedClassInvariantWeights s7 := by
            simp [figure17_1ClosedClassInvariantWeights]
  · have hsupport :
        ∀ y ∉ ({s6, s7} : Finset Figure17_1State),
          figure17_1ClosedClassInvariantWeights y * figure17_1TransitionMatrix y s8 = 0 := by
      intro y hy
      fin_cases y <;>
        simp [figure17_1ClosedClassInvariantWeights, figure17_1TransitionMatrix] at hy ⊢
    rw [tsum_eq_sum hsupport]
    calc
      ∑ y ∈ ({s6, s7} : Finset Figure17_1State),
          figure17_1ClosedClassInvariantWeights y * figure17_1TransitionMatrix y s8
          = (((4 : ℝ≥0∞) / 17) * (3 / 4 : ℝ≥0∞)) +
              (((5 : ℝ≥0∞) / 17) * (1 : ℝ≥0∞)) := by
                simp [Finset.sum_insert, figure17_1ClosedClassInvariantWeights,
                  figure17_1TransitionMatrix]
      _ = (8 : ℝ≥0∞) / 17 := by
            have hleft1 :
                ((4 : ℝ≥0∞) / 17) * (3 / 4 : ℝ≥0∞) ≠ ∞ := by
              exact ENNReal.mul_ne_top (ENNReal.div_ne_top (by norm_num) (by norm_num))
                (ENNReal.div_ne_top (by norm_num) (by norm_num))
            have hleft2 :
                ((5 : ℝ≥0∞) / 17) * (1 : ℝ≥0∞) ≠ ∞ := by
              exact ENNReal.mul_ne_top (ENNReal.div_ne_top (by norm_num) (by norm_num)) (by simp)
            have hleft :
                (((4 : ℝ≥0∞) / 17) * (3 / 4 : ℝ≥0∞)) +
                  (((5 : ℝ≥0∞) / 17) * (1 : ℝ≥0∞)) ≠ ∞ := by
              exact ENNReal.add_ne_top.2 ⟨hleft1, hleft2⟩
            have hright : ((8 : ℝ≥0∞) / 17) ≠ ∞ := by
              exact ENNReal.div_ne_top (by norm_num) (by norm_num)
            rw [← ENNReal.toReal_eq_toReal_iff' hleft hright]
            rw [ENNReal.toReal_add hleft1 hleft2, ENNReal.toReal_mul, ENNReal.toReal_mul,
              ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]
            norm_num
      _ = figure17_1ClosedClassInvariantWeights s8 := by
            simp [figure17_1ClosedClassInvariantWeights]

/-- Helper for Remark 17.31: the explicit closed-class distribution is invariant for the Fig. 17.1
one-step kernel. -/
private theorem figure17_1ClosedClassInvariantDistribution_isInvariant :
    Kernel.Invariant (discreteMatrixKernel figure17_1TransitionMatrix)
      (figure17_1ClosedClassInvariantDistribution : Measure Figure17_1State) := by
  rw [Kernel.Invariant]
  refine Measure.ext_of_singleton fun x ↦ ?_
  rw [figure17_1_comp_discreteMatrixKernel_apply_singleton_eq_tsum]
  simpa [figure17_1ClosedClassInvariantDistribution_apply_singleton] using
    figure17_1ClosedClassInvariantWeights_leftEigenvector x

/-- Helper for Remark 17.31: the explicit closed-class invariant distribution charges each of
`s6`, `s7`, and `s8`, so the owner Chapter 17 API yields positive recurrence for those states. -/
private theorem figure17_1_closedClassStates_positiveRecurrent_owner :
    ProbabilityTheory.IsPositiveRecurrentState P X s6 ∧
      ProbabilityTheory.IsPositiveRecurrentState P X s7 ∧
      ProbabilityTheory.IsPositiveRecurrentState P X s8 := by
  have hπinv :
      Kernel.Invariant ((fun n : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ n) 1)
        (figure17_1ClosedClassInvariantDistribution : Measure Figure17_1State) := by
    simpa [pow_one] using figure17_1ClosedClassInvariantDistribution_isInvariant
  refine ⟨?_, ?_, ?_⟩
  · exact ProbabilityTheory.isPositiveRecurrentState_of_invariantDistribution_singleton_pos
      (κ := fun n : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ n)
      (P := P) (X := X) (π := figure17_1ClosedClassInvariantDistribution) (y := s6)
      hπinv (by
        rw [figure17_1ClosedClassInvariantDistribution_apply_singleton]
        norm_num [figure17_1ClosedClassInvariantWeights])
  · exact ProbabilityTheory.isPositiveRecurrentState_of_invariantDistribution_singleton_pos
      (κ := fun n : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ n)
      (P := P) (X := X) (π := figure17_1ClosedClassInvariantDistribution) (y := s7)
      hπinv (by
        rw [figure17_1ClosedClassInvariantDistribution_apply_singleton]
        norm_num [figure17_1ClosedClassInvariantWeights])
  · exact ProbabilityTheory.isPositiveRecurrentState_of_invariantDistribution_singleton_pos
      (κ := fun n : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ n)
      (P := P) (X := X) (π := figure17_1ClosedClassInvariantDistribution) (y := s8)
      hπinv (by
        rw [figure17_1ClosedClassInvariantDistribution_apply_singleton]
        norm_num [figure17_1ClosedClassInvariantWeights])

/-- Helper for Remark 17.31: the diagonal singleton mass of the return-cycle occupation measure
is exactly `1`. -/
private theorem figure17_1_returnCycleOccupationMeasure_apply_singleton_self
    (x : Figure17_1State) :
    (μ[P, X] x) ({x} : Set Figure17_1State) = 1 := by
  let hReal :
      ProbabilityTheory.IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ n) P X := inferInstance
  have hinit :
      (P x : Measure Ω) {ω | X 0 ω = x} = 1 := by
    have hpreimage : {ω | X 0 ω = x} = X 0 ⁻¹' ({x} : Set Figure17_1State) := by
      ext ω
      simp
    rw [hpreimage, ← Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton x)]
    rw [hReal.initial_eq x]
    simp
  have hterm0 :
      (P x : Measure Ω) {ω | X 0 ω = x ∧ (0 : ℕ∞) < (τ_[X, x]^1) ω} = 1 := by
    have hτpos : ∀ ω : Ω, (0 : ℕ∞) < (τ_[X, x]^1) ω := by
      intro ω
      have hτge1 : (1 : ℕ∞) ≤ (τ_[X, x]^1) ω := by
        have h : (1 : ℕ) ≤ MeasureTheory.hittingAfter X ({x} : Set Figure17_1State) 1 ω :=
          le_hittingAfter ω
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
                MeasureTheory.hittingAfter X ({x} : Set Figure17_1State) 1 ω ≤ n + 1 :=
              hittingAfter_le_of_mem (by simp)
                (by simpa [Set.mem_singleton_iff] using hω.1)
            simpa [iteratedEntranceTime_one] using h
          exact False.elim <| (not_lt_of_ge hle) hω.2
        · simp
      rw [hempty]
      simp
  have htailTsum :
      (∑' m : ℕ,
        ite (m = 0) 0
            ((P x : Measure Ω) {ω | X m ω = x ∧ (m : ℕ∞) < (τ_[X, x]^1) ω})) = 0 := by
    exact ENNReal.tsum_eq_zero.2 htailZero
  have hterm0' :
      (P x : Measure Ω) {ω | X 0 ω = x ∧ ((0 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} = 1 := by
    simpa using hterm0
  have htailTsum' :
      (∑' i : ℕ,
        if i = 0 then 0 else (P x : Measure Ω) {ω | X i ω = x ∧ (i : ℕ∞) < (τ_[X, x]^1) ω}) = 0 := by
    simpa using htailTsum
  rw [returnCycleOccupationMeasure_apply_singleton, returnCycleOccupationMass,
    ENNReal.tsum_eq_add_tsum_ite 0, hterm0']
  have hsum1 :
      1 + (∑' i : ℕ,
        if i = 0 then 0 else (P x : Measure Ω) {ω | X i ω = x ∧ (i : ℕ∞) < (τ_[X, x]^1) ω}) =
          1 + 0 := congrArg (fun t : ℝ≥0∞ ↦ 1 + t) htailTsum'
  simpa using hsum1

/-- Helper for Remark 17.31: the return-cycle occupation measure rooted in the closed class
`{s6, s7, s8}` assigns zero mass to every outside singleton. -/
private theorem figure17_1_returnCycleOccupationMeasure_closedClass_outside_eq_zero
    {x y : Figure17_1State} (hx : x = s6 ∨ x = s7 ∨ x = s8)
    (hy : y = s1 ∨ y = s2 ∨ y = s3 ∨ y = s4 ∨ y = s5) :
    (μ[P, X] x) ({y} : Set Figure17_1State) = 0 := by
  let hReal :
      ProbabilityTheory.IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ n) P X := inferInstance
  rw [returnCycleOccupationMeasure_apply_singleton, returnCycleOccupationMass]
  refine ENNReal.tsum_eq_zero.2 ?_
  intro n
  have hsubset :
      {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω} ⊆ {ω | X n ω = y} := by
    intro ω hω
    exact hω.1
  have hslice :
      (P x : Measure Ω) {ω | X n ω = y} =
        ((discreteMatrixKernel figure17_1TransitionMatrix ^ n) x) ({y} : Set Figure17_1State) := by
    have hpreimage : {ω | X n ω = y} = X n ⁻¹' ({y} : Set Figure17_1State) := by
      ext ω
      simp
    rw [hpreimage, ← Measure.map_apply (hReal.measurable_process n) (measurableSet_singleton y)]
    rw [hReal.transition_eq x n]
  have hzeroKernel :
      ((discreteMatrixKernel figure17_1TransitionMatrix ^ n) x) ({y} : Set Figure17_1State) = 0 := by
    rcases figure17_1_closedClass_pow_outside_eq_zero hx n with ⟨hs1, hs2, hs3, hs4, hs5⟩
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact hs1
    · exact hs2
    · exact hs3
    · exact hs4
    · exact hs5
  exact le_antisymm
    (calc
      (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}
          ≤ (P x : Measure Ω) {ω | X n ω = y} := measure_mono hsubset
      _ = 0 := by rw [hslice, hzeroKernel])
    bot_le

/-- Helper for Remark 17.31: evaluating an invariant measure on a singleton rewrites invariance as
the corresponding balance equation for Fig. 17.1. -/
private theorem figure17_1_invariantMeasure_apply_singleton_eq_tsum
    (ν : Measure Figure17_1State)
    (hν : Kernel.Invariant (discreteMatrixKernel figure17_1TransitionMatrix) ν)
    (x : Figure17_1State) :
    ∑' y : Figure17_1State, ν ({y} : Set Figure17_1State) * figure17_1TransitionMatrix y x =
      ν ({x} : Set Figure17_1State) := by
  have hx := congrArg (fun μ : Measure Figure17_1State ↦ μ ({x} : Set Figure17_1State)) hν.def
  simpa [figure17_1_comp_discreteMatrixKernel_apply_singleton_eq_tsum] using hx

/-- Helper for Remark 17.31: the expected first return time at state `6` is `17 / 4`. -/
private theorem figure17_1_expectedFirstReturnTime_s6 :
    expectedFirstReturnTime P X s6 = (17 : ENNReal) / 4 := by
  rcases figure17_1_closedClassStates_positiveRecurrent_owner (P := P) (X := X) with
    ⟨hs6_posrec, _, _⟩
  have hs6_rec :
      ProbabilityTheory.IsRecurrentState P X s6 :=
    by
      have hs6_posrec_local : IsPositiveRecurrentState P X s6 := by
        simpa [ProbabilityTheory.IsPositiveRecurrentState, IsPositiveRecurrentState,
          ProbabilityTheory.expectedFirstReturnTime, expectedFirstReturnTime] using hs6_posrec
      have hs6_rec_local : IsRecurrentState P X s6 :=
        figure17_1_positiveRecurrentState_isRecurrentState (P := P) (X := X) s6 hs6_posrec_local
      simpa [ProbabilityTheory.IsRecurrentState, IsRecurrentState] using hs6_rec_local
  have hνinv :
      Kernel.Invariant (discreteMatrixKernel figure17_1TransitionMatrix)
        ((μ[P, X] s6) : Measure Figure17_1State) := by
    simpa [pow_one] using
      (recurrentState_returnCycleOccupationMeasure_comp_eq
        (κ := fun n : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ n)
        (P := P) (X := X) hs6_rec)
  have hνuniv_lt_top : ((μ[P, X] s6 : Measure Figure17_1State) Set.univ) < ⊤ := by
    rw [figure17_1_returnCycleOccupationMeasure_univ_eq_expectedFirstReturnTime (P := P) (X := X) s6]
    simpa [ProbabilityTheory.IsPositiveRecurrentState, IsPositiveRecurrentState,
      ProbabilityTheory.expectedFirstReturnTime, expectedFirstReturnTime] using hs6_posrec
  have hνs7_lt_top : ((μ[P, X] s6 : Measure Figure17_1State) ({s7} : Set Figure17_1State)) < ⊤ := by
    exact lt_of_le_of_lt (measure_mono (by simp)) hνuniv_lt_top
  have hνs8_lt_top : ((μ[P, X] s6 : Measure Figure17_1State) ({s8} : Set Figure17_1State)) < ⊤ := by
    exact lt_of_le_of_lt (measure_mono (by simp)) hνuniv_lt_top
  have hνself :
      (μ[P, X] s6 : Measure Figure17_1State) ({s6} : Set Figure17_1State) = 1 :=
    figure17_1_returnCycleOccupationMeasure_apply_singleton_self (P := P) (X := X) s6
  have hνs1 :
      (μ[P, X] s6 : Measure Figure17_1State) ({s1} : Set Figure17_1State) = 0 :=
    figure17_1_returnCycleOccupationMeasure_closedClass_outside_eq_zero
      (P := P) (X := X) (hx := Or.inl rfl) (hy := Or.inl rfl)
  have hνs2 :
      (μ[P, X] s6 : Measure Figure17_1State) ({s2} : Set Figure17_1State) = 0 :=
    figure17_1_returnCycleOccupationMeasure_closedClass_outside_eq_zero
      (P := P) (X := X) (hx := Or.inl rfl) (hy := Or.inr <| Or.inl rfl)
  have hνs3 :
      (μ[P, X] s6 : Measure Figure17_1State) ({s3} : Set Figure17_1State) = 0 :=
    figure17_1_returnCycleOccupationMeasure_closedClass_outside_eq_zero
      (P := P) (X := X) (hx := Or.inl rfl) (hy := Or.inr <| Or.inr <| Or.inl rfl)
  have hνs4 :
      (μ[P, X] s6 : Measure Figure17_1State) ({s4} : Set Figure17_1State) = 0 :=
    figure17_1_returnCycleOccupationMeasure_closedClass_outside_eq_zero
      (P := P) (X := X) (hx := Or.inl rfl) (hy := Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)
  have hνs5 :
      (μ[P, X] s6 : Measure Figure17_1State) ({s5} : Set Figure17_1State) = 0 :=
    figure17_1_returnCycleOccupationMeasure_closedClass_outside_eq_zero
      (P := P) (X := X) (hx := Or.inl rfl) (hy := Or.inr <| Or.inr <| Or.inr <| Or.inr rfl)
  have hs7balance := figure17_1_invariantMeasure_apply_singleton_eq_tsum
    ((μ[P, X] s6) : Measure Figure17_1State) hνinv s7
  have hs8balance := figure17_1_invariantMeasure_apply_singleton_eq_tsum
    ((μ[P, X] s6) : Measure Figure17_1State) hνinv s8
  have hs7eq :
      (((μ[P, X] s6 : Measure Figure17_1State) ({s6} : Set Figure17_1State)) * (1 / 4 : ℝ≥0∞)) +
          (((μ[P, X] s6 : Measure Figure17_1State) ({s8} : Set Figure17_1State)) * (1 / 2 : ℝ≥0∞)) =
        (μ[P, X] s6 : Measure Figure17_1State) ({s7} : Set Figure17_1State) := by
    have hsupport :
        ∀ y ∉ ({s6, s8} : Finset Figure17_1State),
          ((μ[P, X] s6 : Measure Figure17_1State) ({y} : Set Figure17_1State)) *
            figure17_1TransitionMatrix y s7 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1TransitionMatrix, hνs1, hνs2, hνs3, hνs4, hνs5] at hy ⊢
    rw [tsum_eq_sum hsupport] at hs7balance
    simpa [Finset.sum_insert, figure17_1TransitionMatrix] using hs7balance
  have hs8eq :
      (((μ[P, X] s6 : Measure Figure17_1State) ({s6} : Set Figure17_1State)) * (3 / 4 : ℝ≥0∞)) +
          (((μ[P, X] s6 : Measure Figure17_1State) ({s7} : Set Figure17_1State)) * (1 : ℝ≥0∞)) =
        (μ[P, X] s6 : Measure Figure17_1State) ({s8} : Set Figure17_1State) := by
    have hsupport :
        ∀ y ∉ ({s6, s7} : Finset Figure17_1State),
          ((μ[P, X] s6 : Measure Figure17_1State) ({y} : Set Figure17_1State)) *
            figure17_1TransitionMatrix y s8 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1TransitionMatrix, hνs1, hνs2, hνs3, hνs4, hνs5] at hy ⊢
    rw [tsum_eq_sum hsupport] at hs8balance
    simpa [Finset.sum_insert, figure17_1TransitionMatrix] using hs8balance
  have hs7real := congrArg ENNReal.toReal hs7eq
  have hs8real := congrArg ENNReal.toReal hs8eq
  have hνself_real :
      ((μ[P, X] s6 : Measure Figure17_1State) ({s6} : Set Figure17_1State)).toReal = 1 := by
    simpa [hνself]
  have hs6quarter_ne_top :
      ((μ[P, X] s6 : Measure Figure17_1State) ({s6} : Set Figure17_1State)) *
        (1 / 4 : ℝ≥0∞) ≠ ∞ := by
    rw [hνself]
    exact ENNReal.mul_ne_top (by simp) (ENNReal.div_ne_top (by norm_num) (by norm_num))
  have hs6threeQuarter_ne_top :
      ((μ[P, X] s6 : Measure Figure17_1State) ({s6} : Set Figure17_1State)) *
        (3 / 4 : ℝ≥0∞) ≠ ∞ := by
    rw [hνself]
    exact ENNReal.mul_ne_top (by simp) (ENNReal.div_ne_top (by norm_num) (by norm_num))
  have hs8half_ne_top :
      ((μ[P, X] s6 : Measure Figure17_1State) ({s8} : Set Figure17_1State)) *
        (1 / 2 : ℝ≥0∞) ≠ ∞ := by
    exact ENNReal.mul_ne_top hνs8_lt_top.ne (ENNReal.div_ne_top (by norm_num) (by norm_num))
  have hs7one_ne_top :
      ((μ[P, X] s6 : Measure Figure17_1State) ({s7} : Set Figure17_1State)) *
        (1 : ℝ≥0∞) ≠ ∞ := by
    exact ENNReal.mul_ne_top hνs7_lt_top.ne (by simp)
  rw [ENNReal.toReal_add hs6quarter_ne_top hs8half_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_mul, hνself_real] at hs7real
  rw [ENNReal.toReal_add hs6threeQuarter_ne_top hs7one_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_mul, hνself_real] at hs8real
  norm_num at hs7real hs8real
  have hs7mass_real :
      ((μ[P, X] s6 : Measure Figure17_1State) ({s7} : Set Figure17_1State)).toReal = 5 / 4 := by
    linarith
  have hs8mass_real :
      ((μ[P, X] s6 : Measure Figure17_1State) ({s8} : Set Figure17_1State)).toReal = 2 := by
    linarith
  have hs7mass :
      (μ[P, X] s6 : Measure Figure17_1State) ({s7} : Set Figure17_1State) = (5 : ℝ≥0∞) / 4 := by
    exact (ENNReal.toReal_eq_toReal_iff' hνs7_lt_top.ne (ENNReal.div_ne_top (by norm_num) (by norm_num))).1
      (by simpa [ENNReal.toReal_div] using hs7mass_real)
  have hs8mass :
      (μ[P, X] s6 : Measure Figure17_1State) ({s8} : Set Figure17_1State) = 2 := by
    exact (ENNReal.toReal_eq_toReal_iff' hνs8_lt_top.ne (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).1
      (by simpa using hs8mass_real)
  have huniv :
      (μ[P, X] s6 : Measure Figure17_1State) Set.univ = (17 : ℝ≥0∞) / 4 := by
    have hunivSet :
        (Set.univ : Set Figure17_1State) = ({s1, s2, s3, s4, s5, s6, s7, s8} : Set Figure17_1State) := by
      ext x
      fin_cases x <;> simp
    have hunivFinsetSet :
        ({s1, s2, s3, s4, s5, s6, s7, s8} : Set Figure17_1State) =
          (({s1, s2, s3, s4, s5, s6, s7, s8} : Finset Figure17_1State) : Set Figure17_1State) := by
      ext x
      fin_cases x <;> simp
    calc
      (μ[P, X] s6 : Measure Figure17_1State) Set.univ =
          (μ[P, X] s6 : Measure Figure17_1State)
            (({s1, s2, s3, s4, s5, s6, s7, s8} : Finset Figure17_1State) : Set Figure17_1State) := by
              rw [hunivSet, hunivFinsetSet]
      _ =
          Finset.sum ({s1, s2, s3, s4, s5, s6, s7, s8} : Finset Figure17_1State) fun x ↦
            (μ[P, X] s6 : Measure Figure17_1State) ({x} : Set Figure17_1State) := by
              simpa using
                (sum_measure_singleton
                  (μ := (μ[P, X] s6 : Measure Figure17_1State))
                  (s := ({s1, s2, s3, s4, s5, s6, s7, s8} : Finset Figure17_1State))).symm
      _ = (17 : ℝ≥0∞) / 4 := by
            have hclosed :
                (μ[P, X] s6 : Measure Figure17_1State) ({s6, s7, s8} : Set Figure17_1State) =
                  (μ[P, X] s6 : Measure Figure17_1State) ({s6} : Set Figure17_1State) +
                    (μ[P, X] s6 : Measure Figure17_1State) ({s7} : Set Figure17_1State) +
                    (μ[P, X] s6 : Measure Figure17_1State) ({s8} : Set Figure17_1State) := by
              simpa [add_assoc] using
                (sum_measure_singleton
                  (μ := (μ[P, X] s6 : Measure Figure17_1State))
                  (s := ({s6, s7, s8} : Finset Figure17_1State))).symm
            have hsum :
                (Finset.sum ({s1, s2, s3, s4, s5, s6, s7, s8} : Finset Figure17_1State)
                  (fun x ↦ (μ[P, X] s6 : Measure Figure17_1State) ({x} : Set Figure17_1State))) =
                    (μ[P, X] s6 : Measure Figure17_1State) ({s6, s7, s8} : Set Figure17_1State) := by
              simpa [hνs1, hνs2, hνs3, hνs4, hνs5, add_assoc, add_left_comm, add_comm] using
                hclosed.symm
            rw [hsum, hclosed, hνself, hs7mass, hs8mass]
            have hfiveQuarters_ne_top : ((5 : ENNReal) / 4) ≠ ⊤ := by
              exact ENNReal.div_ne_top (by simp) (by norm_num)
            have hleft_mid_ne_top : ((1 : ENNReal) + (5 : ENNReal) / 4) ≠ ⊤ := by
              simp [hfiveQuarters_ne_top]
            have hleft_ne_top : ((1 : ENNReal) + (5 : ENNReal) / 4 + 2) ≠ ⊤ := by
              simp [hleft_mid_ne_top]
            have hright_ne_top : ((17 : ENNReal) / 4) ≠ ⊤ := by
              exact ENNReal.div_ne_top (by simp) (by norm_num)
            refine (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top).mp ?_
            rw [ENNReal.toReal_add hleft_mid_ne_top (by simp),
              ENNReal.toReal_add (by simp) hfiveQuarters_ne_top,
              ENNReal.toReal_div, ENNReal.toReal_div]
            norm_num
  calc
    expectedFirstReturnTime P X s6 = (μ[P, X] s6 : Measure Figure17_1State) Set.univ := by
      symm
      exact figure17_1_returnCycleOccupationMeasure_univ_eq_expectedFirstReturnTime
        (P := P) (X := X) s6
    _ = (17 : ENNReal) / 4 := huniv

/-- Helper for Remark 17.31: the expected first return time at state `7` is `17 / 5`. -/
private theorem figure17_1_expectedFirstReturnTime_s7 :
    expectedFirstReturnTime P X s7 = (17 : ENNReal) / 5 := by
  rcases figure17_1_closedClassStates_positiveRecurrent_owner (P := P) (X := X) with
    ⟨_, hs7_posrec, _⟩
  have hs7_rec :
      ProbabilityTheory.IsRecurrentState P X s7 :=
    by
      have hs7_posrec_local : IsPositiveRecurrentState P X s7 := by
        simpa [ProbabilityTheory.IsPositiveRecurrentState, IsPositiveRecurrentState,
          ProbabilityTheory.expectedFirstReturnTime, expectedFirstReturnTime] using hs7_posrec
      have hs7_rec_local : IsRecurrentState P X s7 :=
        figure17_1_positiveRecurrentState_isRecurrentState (P := P) (X := X) s7 hs7_posrec_local
      simpa [ProbabilityTheory.IsRecurrentState, IsRecurrentState] using hs7_rec_local
  have hνinv :
      Kernel.Invariant (discreteMatrixKernel figure17_1TransitionMatrix)
        ((μ[P, X] s7) : Measure Figure17_1State) := by
    simpa [pow_one] using
      (recurrentState_returnCycleOccupationMeasure_comp_eq
        (κ := fun n : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ n)
        (P := P) (X := X) hs7_rec)
  have hνuniv_lt_top : ((μ[P, X] s7 : Measure Figure17_1State) Set.univ) < ⊤ := by
    rw [figure17_1_returnCycleOccupationMeasure_univ_eq_expectedFirstReturnTime (P := P) (X := X) s7]
    simpa [ProbabilityTheory.IsPositiveRecurrentState, IsPositiveRecurrentState,
      ProbabilityTheory.expectedFirstReturnTime, expectedFirstReturnTime] using hs7_posrec
  have hνs6_lt_top : ((μ[P, X] s7 : Measure Figure17_1State) ({s6} : Set Figure17_1State)) < ⊤ := by
    exact lt_of_le_of_lt (measure_mono (by simp)) hνuniv_lt_top
  have hνs8_lt_top : ((μ[P, X] s7 : Measure Figure17_1State) ({s8} : Set Figure17_1State)) < ⊤ := by
    exact lt_of_le_of_lt (measure_mono (by simp)) hνuniv_lt_top
  have hνself :
      (μ[P, X] s7 : Measure Figure17_1State) ({s7} : Set Figure17_1State) = 1 :=
    figure17_1_returnCycleOccupationMeasure_apply_singleton_self (P := P) (X := X) s7
  have hνs1 :
      (μ[P, X] s7 : Measure Figure17_1State) ({s1} : Set Figure17_1State) = 0 :=
    figure17_1_returnCycleOccupationMeasure_closedClass_outside_eq_zero
      (P := P) (X := X) (hx := Or.inr <| Or.inl rfl) (hy := Or.inl rfl)
  have hνs2 :
      (μ[P, X] s7 : Measure Figure17_1State) ({s2} : Set Figure17_1State) = 0 :=
    figure17_1_returnCycleOccupationMeasure_closedClass_outside_eq_zero
      (P := P) (X := X) (hx := Or.inr <| Or.inl rfl) (hy := Or.inr <| Or.inl rfl)
  have hνs3 :
      (μ[P, X] s7 : Measure Figure17_1State) ({s3} : Set Figure17_1State) = 0 :=
    figure17_1_returnCycleOccupationMeasure_closedClass_outside_eq_zero
      (P := P) (X := X) (hx := Or.inr <| Or.inl rfl) (hy := Or.inr <| Or.inr <| Or.inl rfl)
  have hνs4 :
      (μ[P, X] s7 : Measure Figure17_1State) ({s4} : Set Figure17_1State) = 0 :=
    figure17_1_returnCycleOccupationMeasure_closedClass_outside_eq_zero
      (P := P) (X := X) (hx := Or.inr <| Or.inl rfl) (hy := Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)
  have hνs5 :
      (μ[P, X] s7 : Measure Figure17_1State) ({s5} : Set Figure17_1State) = 0 :=
    figure17_1_returnCycleOccupationMeasure_closedClass_outside_eq_zero
      (P := P) (X := X) (hx := Or.inr <| Or.inl rfl) (hy := Or.inr <| Or.inr <| Or.inr <| Or.inr rfl)
  have hs6balance := figure17_1_invariantMeasure_apply_singleton_eq_tsum
    ((μ[P, X] s7) : Measure Figure17_1State) hνinv s6
  have hs8balance := figure17_1_invariantMeasure_apply_singleton_eq_tsum
    ((μ[P, X] s7) : Measure Figure17_1State) hνinv s8
  have hs6eq :
      (((μ[P, X] s7 : Measure Figure17_1State) ({s8} : Set Figure17_1State)) * (1 / 2 : ℝ≥0∞)) =
        (μ[P, X] s7 : Measure Figure17_1State) ({s6} : Set Figure17_1State) := by
    have hsupport :
        ∀ y ∉ ({s8} : Finset Figure17_1State),
          ((μ[P, X] s7 : Measure Figure17_1State) ({y} : Set Figure17_1State)) *
            figure17_1TransitionMatrix y s6 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1TransitionMatrix, hνs1, hνs2, hνs3, hνs4, hνs5] at hy ⊢
    rw [tsum_eq_sum hsupport] at hs6balance
    simpa [figure17_1TransitionMatrix] using hs6balance
  have hs8eq :
      (((μ[P, X] s7 : Measure Figure17_1State) ({s6} : Set Figure17_1State)) * (3 / 4 : ℝ≥0∞)) +
          (((μ[P, X] s7 : Measure Figure17_1State) ({s7} : Set Figure17_1State)) * (1 : ℝ≥0∞)) =
        (μ[P, X] s7 : Measure Figure17_1State) ({s8} : Set Figure17_1State) := by
    have hsupport :
        ∀ y ∉ ({s6, s7} : Finset Figure17_1State),
          ((μ[P, X] s7 : Measure Figure17_1State) ({y} : Set Figure17_1State)) *
            figure17_1TransitionMatrix y s8 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1TransitionMatrix, hνs1, hνs2, hνs3, hνs4, hνs5] at hy ⊢
    rw [tsum_eq_sum hsupport] at hs8balance
    simpa [Finset.sum_insert, figure17_1TransitionMatrix] using hs8balance
  have hs6real := congrArg ENNReal.toReal hs6eq
  have hs8real := congrArg ENNReal.toReal hs8eq
  have hνself_real :
      ((μ[P, X] s7 : Measure Figure17_1State) ({s7} : Set Figure17_1State)).toReal = 1 := by
    simpa [hνself]
  have hs8half_ne_top :
      ((μ[P, X] s7 : Measure Figure17_1State) ({s8} : Set Figure17_1State)) *
        (1 / 2 : ℝ≥0∞) ≠ ∞ := by
    exact ENNReal.mul_ne_top hνs8_lt_top.ne (ENNReal.div_ne_top (by norm_num) (by norm_num))
  have hs6threeQuarter_ne_top :
      ((μ[P, X] s7 : Measure Figure17_1State) ({s6} : Set Figure17_1State)) *
        (3 / 4 : ℝ≥0∞) ≠ ∞ := by
    exact ENNReal.mul_ne_top hνs6_lt_top.ne (ENNReal.div_ne_top (by norm_num) (by norm_num))
  have hs7one_ne_top :
      ((μ[P, X] s7 : Measure Figure17_1State) ({s7} : Set Figure17_1State)) *
        (1 : ℝ≥0∞) ≠ ∞ := by
    rw [hνself]
    simp
  rw [ENNReal.toReal_mul] at hs6real
  rw [ENNReal.toReal_add hs6threeQuarter_ne_top hs7one_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_mul, hνself_real] at hs8real
  norm_num at hs6real hs8real
  have hs6mass_real :
      ((μ[P, X] s7 : Measure Figure17_1State) ({s6} : Set Figure17_1State)).toReal = 4 / 5 := by
    linarith
  have hs8mass_real :
      ((μ[P, X] s7 : Measure Figure17_1State) ({s8} : Set Figure17_1State)).toReal = 8 / 5 := by
    linarith
  have hs6mass :
      (μ[P, X] s7 : Measure Figure17_1State) ({s6} : Set Figure17_1State) = (4 : ℝ≥0∞) / 5 := by
    exact (ENNReal.toReal_eq_toReal_iff' hνs6_lt_top.ne (ENNReal.div_ne_top (by norm_num) (by norm_num))).1
      (by simpa [ENNReal.toReal_div] using hs6mass_real)
  have hs8mass :
      (μ[P, X] s7 : Measure Figure17_1State) ({s8} : Set Figure17_1State) = (8 : ℝ≥0∞) / 5 := by
    exact (ENNReal.toReal_eq_toReal_iff' hνs8_lt_top.ne (ENNReal.div_ne_top (by norm_num) (by norm_num))).1
      (by simpa [ENNReal.toReal_div] using hs8mass_real)
  have huniv :
      (μ[P, X] s7 : Measure Figure17_1State) Set.univ = (17 : ℝ≥0∞) / 5 := by
    have hunivSet :
        (Set.univ : Set Figure17_1State) = ({s1, s2, s3, s4, s5, s6, s7, s8} : Set Figure17_1State) := by
      ext x
      fin_cases x <;> simp
    have hunivFinsetSet :
        ({s1, s2, s3, s4, s5, s6, s7, s8} : Set Figure17_1State) =
          (({s1, s2, s3, s4, s5, s6, s7, s8} : Finset Figure17_1State) : Set Figure17_1State) := by
      ext x
      fin_cases x <;> simp
    calc
      (μ[P, X] s7 : Measure Figure17_1State) Set.univ =
          (μ[P, X] s7 : Measure Figure17_1State)
            (({s1, s2, s3, s4, s5, s6, s7, s8} : Finset Figure17_1State) : Set Figure17_1State) := by
              rw [hunivSet, hunivFinsetSet]
      _ =
          Finset.sum ({s1, s2, s3, s4, s5, s6, s7, s8} : Finset Figure17_1State) fun x ↦
            (μ[P, X] s7 : Measure Figure17_1State) ({x} : Set Figure17_1State) := by
              simpa using
                (sum_measure_singleton
                  (μ := (μ[P, X] s7 : Measure Figure17_1State))
                  (s := ({s1, s2, s3, s4, s5, s6, s7, s8} : Finset Figure17_1State))).symm
      _ = (17 : ℝ≥0∞) / 5 := by
            have hclosed :
                (μ[P, X] s7 : Measure Figure17_1State) ({s6, s7, s8} : Set Figure17_1State) =
                  (μ[P, X] s7 : Measure Figure17_1State) ({s6} : Set Figure17_1State) +
                    (μ[P, X] s7 : Measure Figure17_1State) ({s7} : Set Figure17_1State) +
                    (μ[P, X] s7 : Measure Figure17_1State) ({s8} : Set Figure17_1State) := by
              simpa [add_assoc] using
                (sum_measure_singleton
                  (μ := (μ[P, X] s7 : Measure Figure17_1State))
                  (s := ({s6, s7, s8} : Finset Figure17_1State))).symm
            have hsum :
                (Finset.sum ({s1, s2, s3, s4, s5, s6, s7, s8} : Finset Figure17_1State)
                  (fun x ↦ (μ[P, X] s7 : Measure Figure17_1State) ({x} : Set Figure17_1State))) =
                    (μ[P, X] s7 : Measure Figure17_1State) ({s6, s7, s8} : Set Figure17_1State) := by
              simpa [hνs1, hνs2, hνs3, hνs4, hνs5, add_assoc, add_left_comm, add_comm] using
                hclosed.symm
            rw [hsum, hclosed, hs6mass, hνself, hs8mass]
            have hfourFifths_ne_top : ((4 : ENNReal) / 5) ≠ ⊤ := by
              exact ENNReal.div_ne_top (by simp) (by norm_num)
            have heightFifths_ne_top : ((8 : ENNReal) / 5) ≠ ⊤ := by
              exact ENNReal.div_ne_top (by simp) (by norm_num)
            have hleft_mid_ne_top : ((4 : ENNReal) / 5 + 1) ≠ ⊤ := by
              simp [hfourFifths_ne_top]
            have hleft_ne_top : ((4 : ENNReal) / 5 + 1 + (8 : ENNReal) / 5) ≠ ⊤ := by
              simp [hleft_mid_ne_top, heightFifths_ne_top]
            have hright_ne_top : ((17 : ENNReal) / 5) ≠ ⊤ := by
              exact ENNReal.div_ne_top (by simp) (by norm_num)
            refine (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top).mp ?_
            rw [ENNReal.toReal_add hleft_mid_ne_top heightFifths_ne_top,
              ENNReal.toReal_add hfourFifths_ne_top (by simp),
              ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]
            norm_num
  calc
    expectedFirstReturnTime P X s7 = (μ[P, X] s7 : Measure Figure17_1State) Set.univ := by
      symm
      exact figure17_1_returnCycleOccupationMeasure_univ_eq_expectedFirstReturnTime
        (P := P) (X := X) s7
    _ = (17 : ENNReal) / 5 := huniv

/-- Helper for Remark 17.31: the expected first return time at state `8` is `17 / 8`. -/
private theorem figure17_1_expectedFirstReturnTime_s8 :
    expectedFirstReturnTime P X s8 = (17 : ENNReal) / 8 := by
  rcases figure17_1_closedClassStates_positiveRecurrent_owner (P := P) (X := X) with
    ⟨_, _, hs8_posrec⟩
  have hs8_rec :
      ProbabilityTheory.IsRecurrentState P X s8 :=
    by
      have hs8_posrec_local : IsPositiveRecurrentState P X s8 := by
        simpa [ProbabilityTheory.IsPositiveRecurrentState, IsPositiveRecurrentState,
          ProbabilityTheory.expectedFirstReturnTime, expectedFirstReturnTime] using hs8_posrec
      have hs8_rec_local : IsRecurrentState P X s8 :=
        figure17_1_positiveRecurrentState_isRecurrentState (P := P) (X := X) s8 hs8_posrec_local
      simpa [ProbabilityTheory.IsRecurrentState, IsRecurrentState] using hs8_rec_local
  have hνinv :
      Kernel.Invariant (discreteMatrixKernel figure17_1TransitionMatrix)
        ((μ[P, X] s8) : Measure Figure17_1State) := by
    simpa [pow_one] using
      (recurrentState_returnCycleOccupationMeasure_comp_eq
        (κ := fun n : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ n)
        (P := P) (X := X) hs8_rec)
  have hνuniv_lt_top : ((μ[P, X] s8 : Measure Figure17_1State) Set.univ) < ⊤ := by
    rw [figure17_1_returnCycleOccupationMeasure_univ_eq_expectedFirstReturnTime (P := P) (X := X) s8]
    simpa [ProbabilityTheory.IsPositiveRecurrentState, IsPositiveRecurrentState,
      ProbabilityTheory.expectedFirstReturnTime, expectedFirstReturnTime] using hs8_posrec
  have hνself :
      (μ[P, X] s8 : Measure Figure17_1State) ({s8} : Set Figure17_1State) = 1 :=
    figure17_1_returnCycleOccupationMeasure_apply_singleton_self (P := P) (X := X) s8
  have hνs1 :
      (μ[P, X] s8 : Measure Figure17_1State) ({s1} : Set Figure17_1State) = 0 :=
    figure17_1_returnCycleOccupationMeasure_closedClass_outside_eq_zero
      (P := P) (X := X) (hx := Or.inr <| Or.inr rfl) (hy := Or.inl rfl)
  have hνs2 :
      (μ[P, X] s8 : Measure Figure17_1State) ({s2} : Set Figure17_1State) = 0 :=
    figure17_1_returnCycleOccupationMeasure_closedClass_outside_eq_zero
      (P := P) (X := X) (hx := Or.inr <| Or.inr rfl) (hy := Or.inr <| Or.inl rfl)
  have hνs3 :
      (μ[P, X] s8 : Measure Figure17_1State) ({s3} : Set Figure17_1State) = 0 :=
    figure17_1_returnCycleOccupationMeasure_closedClass_outside_eq_zero
      (P := P) (X := X) (hx := Or.inr <| Or.inr rfl) (hy := Or.inr <| Or.inr <| Or.inl rfl)
  have hνs4 :
      (μ[P, X] s8 : Measure Figure17_1State) ({s4} : Set Figure17_1State) = 0 :=
    figure17_1_returnCycleOccupationMeasure_closedClass_outside_eq_zero
      (P := P) (X := X) (hx := Or.inr <| Or.inr rfl) (hy := Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)
  have hνs5 :
      (μ[P, X] s8 : Measure Figure17_1State) ({s5} : Set Figure17_1State) = 0 :=
    figure17_1_returnCycleOccupationMeasure_closedClass_outside_eq_zero
      (P := P) (X := X) (hx := Or.inr <| Or.inr rfl) (hy := Or.inr <| Or.inr <| Or.inr <| Or.inr rfl)
  have hs6balance := figure17_1_invariantMeasure_apply_singleton_eq_tsum
    ((μ[P, X] s8) : Measure Figure17_1State) hνinv s6
  have hs7balance := figure17_1_invariantMeasure_apply_singleton_eq_tsum
    ((μ[P, X] s8) : Measure Figure17_1State) hνinv s7
  have hs6mass :
      (μ[P, X] s8 : Measure Figure17_1State) ({s6} : Set Figure17_1State) = 1 / 2 := by
    have hsupport :
        ∀ y ∉ ({s8} : Finset Figure17_1State),
          ((μ[P, X] s8 : Measure Figure17_1State) ({y} : Set Figure17_1State)) *
            figure17_1TransitionMatrix y s6 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1TransitionMatrix, hνs1, hνs2, hνs3, hνs4, hνs5] at hy ⊢
    rw [tsum_eq_sum hsupport] at hs6balance
    simpa [hνself, figure17_1TransitionMatrix] using hs6balance.symm
  have hs7eq :
      (((μ[P, X] s8 : Measure Figure17_1State) ({s6} : Set Figure17_1State)) * (1 / 4 : ℝ≥0∞)) +
          (((μ[P, X] s8 : Measure Figure17_1State) ({s8} : Set Figure17_1State)) * (1 / 2 : ℝ≥0∞)) =
        (μ[P, X] s8 : Measure Figure17_1State) ({s7} : Set Figure17_1State) := by
    have hsupport :
        ∀ y ∉ ({s6, s8} : Finset Figure17_1State),
          ((μ[P, X] s8 : Measure Figure17_1State) ({y} : Set Figure17_1State)) *
            figure17_1TransitionMatrix y s7 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1TransitionMatrix, hνs1, hνs2, hνs3, hνs4, hνs5] at hy ⊢
    rw [tsum_eq_sum hsupport] at hs7balance
    simpa [hνself, Finset.sum_insert, figure17_1TransitionMatrix] using hs7balance
  have hs7mass : (μ[P, X] s8 : Measure Figure17_1State) ({s7} : Set Figure17_1State) = (5 : ℝ≥0∞) / 8 := by
    have hs7real := congrArg ENNReal.toReal hs7eq
    have hs6quarter_ne_top :
        ((μ[P, X] s8 : Measure Figure17_1State) ({s6} : Set Figure17_1State)) *
          (1 / 4 : ℝ≥0∞) ≠ ∞ := by
      rw [hs6mass]
      exact ENNReal.mul_ne_top (by simp) (ENNReal.div_ne_top (by norm_num) (by norm_num))
    have hs8half_ne_top :
        ((μ[P, X] s8 : Measure Figure17_1State) ({s8} : Set Figure17_1State)) *
          (1 / 2 : ℝ≥0∞) ≠ ∞ := by
      rw [hνself]
      exact ENNReal.mul_ne_top (by simp) (ENNReal.div_ne_top (by norm_num) (by norm_num))
    have hs6mass_real :
        ((μ[P, X] s8 : Measure Figure17_1State) ({s6} : Set Figure17_1State)).toReal = 1 / 2 := by
      simpa [ENNReal.toReal_div] using congrArg ENNReal.toReal hs6mass
    have hνself_real :
        ((μ[P, X] s8 : Measure Figure17_1State) ({s8} : Set Figure17_1State)).toReal = 1 := by
      simpa [hνself]
    rw [ENNReal.toReal_add hs6quarter_ne_top hs8half_ne_top, ENNReal.toReal_mul,
      ENNReal.toReal_mul, hs6mass_real, hνself_real] at hs7real
    have hs7mass_real :
        ((μ[P, X] s8 : Measure Figure17_1State) ({s7} : Set Figure17_1State)).toReal = 5 / 8 := by
      norm_num at hs7real
      exact hs7real.symm
    exact
      (ENNReal.toReal_eq_toReal_iff'
        (lt_of_le_of_lt (measure_mono (by simp)) hνuniv_lt_top).ne
        (ENNReal.div_ne_top (by norm_num) (by norm_num))).1 <|
        by simpa [ENNReal.toReal_div] using hs7mass_real
  have huniv :
      (μ[P, X] s8 : Measure Figure17_1State) Set.univ = (17 : ℝ≥0∞) / 8 := by
    have hunivSet :
        (Set.univ : Set Figure17_1State) = ({s1, s2, s3, s4, s5, s6, s7, s8} : Set Figure17_1State) := by
      ext x
      fin_cases x <;> simp
    have hunivFinsetSet :
        ({s1, s2, s3, s4, s5, s6, s7, s8} : Set Figure17_1State) =
          (({s1, s2, s3, s4, s5, s6, s7, s8} : Finset Figure17_1State) : Set Figure17_1State) := by
      ext x
      fin_cases x <;> simp
    calc
      (μ[P, X] s8 : Measure Figure17_1State) Set.univ =
          (μ[P, X] s8 : Measure Figure17_1State)
            (({s1, s2, s3, s4, s5, s6, s7, s8} : Finset Figure17_1State) : Set Figure17_1State) := by
              rw [hunivSet, hunivFinsetSet]
      _ =
          Finset.sum ({s1, s2, s3, s4, s5, s6, s7, s8} : Finset Figure17_1State) fun x ↦
            (μ[P, X] s8 : Measure Figure17_1State) ({x} : Set Figure17_1State) := by
              simpa using
                (sum_measure_singleton
                  (μ := (μ[P, X] s8 : Measure Figure17_1State))
                  (s := ({s1, s2, s3, s4, s5, s6, s7, s8} : Finset Figure17_1State))).symm
      _ = (μ[P, X] s8 : Measure Figure17_1State) ({s6, s7, s8} : Set Figure17_1State) := by
            norm_num [hνs1, hνs2, hνs3, hνs4, hνs5, add_assoc, add_left_comm, add_comm]
      _ = (17 : ℝ≥0∞) / 8 := by
            have hclosed :
                (μ[P, X] s8 : Measure Figure17_1State) ({s6, s7, s8} : Set Figure17_1State) =
                  (μ[P, X] s8 : Measure Figure17_1State) ({s6} : Set Figure17_1State) +
                    (μ[P, X] s8 : Measure Figure17_1State) ({s7} : Set Figure17_1State) +
                    (μ[P, X] s8 : Measure Figure17_1State) ({s8} : Set Figure17_1State) := by
              simpa [add_assoc] using
                (sum_measure_singleton
                  (μ := (μ[P, X] s8 : Measure Figure17_1State))
                  (s := ({s6, s7, s8} : Finset Figure17_1State))).symm
            rw [hclosed, hs6mass, hs7mass, hνself]
            change (1 / 2 : ℝ≥0∞) + 5 / 8 + 1 = (17 : ℝ≥0∞) / 8
            have hhalf_lt_top : (1 / 2 : ℝ≥0∞) < ⊤ := by
              exact ENNReal.div_lt_top (by simp) (by simp)
            have hfive_lt_top : (5 / 8 : ℝ≥0∞) < ⊤ := by
              exact ENNReal.div_lt_top (by simp) (by simp)
            have hone_lt_top : (1 : ℝ≥0∞) < ⊤ := by
              exact lt_top_iff_ne_top.2 (by simp)
            have hleft_lt_top : (1 / 2 : ℝ≥0∞) + 5 / 8 + 1 < ⊤ := by
              exact ENNReal.add_lt_top.2
                ⟨ENNReal.add_lt_top.2 ⟨hhalf_lt_top, hfive_lt_top⟩, hone_lt_top⟩
            have hleft_ne_top :
                (1 / 2 : ℝ≥0∞) + 5 / 8 + 1 ≠ ⊤ := by
              exact ne_of_lt hleft_lt_top
            have hright_lt_top : ((17 : ℝ≥0∞) / 8) < ⊤ := by
              exact lt_top_iff_ne_top.2 <| by
                simpa using
                  (ENNReal.div_ne_top (x := (17 : ℝ≥0∞)) (y := (8 : ℝ≥0∞))
                    (by simp) (by simp))
            have hright_ne_top : ((17 : ℝ≥0∞) / 8) ≠ ⊤ := by
              exact ne_of_lt hright_lt_top
            refine (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top).mp ?_
            have hhalf_ne_top : (1 / 2 : ℝ≥0∞) ≠ ⊤ := ne_of_lt hhalf_lt_top
            have hfive_ne_top : (5 / 8 : ℝ≥0∞) ≠ ⊤ := ne_of_lt hfive_lt_top
            have hpair_ne_top : (1 / 2 : ℝ≥0∞) + 5 / 8 ≠ ⊤ := by
              exact ne_of_lt (ENNReal.add_lt_top.2 ⟨hhalf_lt_top, hfive_lt_top⟩)
            calc
              (((1 / 2 : ℝ≥0∞) + 5 / 8 + 1).toReal) = ((1 / 2 : ℝ≥0∞) + 5 / 8).toReal + 1 := by
                rw [ENNReal.toReal_add hpair_ne_top (by simp)]
                norm_num
              _ = (1 / 2 : ℝ≥0∞).toReal + (5 / 8 : ℝ≥0∞).toReal + 1 := by
                rw [ENNReal.toReal_add hhalf_ne_top hfive_ne_top]
              _ = (((17 : ℝ≥0∞) / 8).toReal) := by
                rw [ENNReal.toReal_div]
                norm_num
  calc
    expectedFirstReturnTime P X s8 = (μ[P, X] s8 : Measure Figure17_1State) Set.univ := by
      symm
      exact figure17_1_returnCycleOccupationMeasure_univ_eq_expectedFirstReturnTime
        (P := P) (X := X) s8
    _ = (17 : ENNReal) / 8 := huniv

/-- Helper for Remark 17.31: the quoted exact return-time values on the closed class
`{s6, s7, s8}`. -/
theorem figure17_1_expectedReturnTimes_formula :
    (expectedFirstReturnTime P X s6 = (17 : ENNReal) / 4) ∧
      (expectedFirstReturnTime P X s7 = (17 : ENNReal) / 5) ∧
      expectedFirstReturnTime P X s8 = (17 : ENNReal) / 8 := by
  exact ⟨figure17_1_expectedFirstReturnTime_s6 (P := P) (X := X),
    figure17_1_expectedFirstReturnTime_s7 (P := P) (X := X),
    figure17_1_expectedFirstReturnTime_s8 (P := P) (X := X)⟩

/-- Helper for Remark 17.31: subclaim (3) says that in any realization of the
Markov chain of Fig. 17.1, the states `6`, `7`, and `8` are positive recurrent. -/
theorem figure17_1_states678_positiveRecurrent :
    {x | x = s6 ∨ x = s7 ∨ x = s8} ⊆ {x | IsPositiveRecurrentState P X x} := by
  -- The quoted return-time identities are finite, so the three closed-class states are positive
  -- recurrent by definition.
  intro x hx
  rcases figure17_1_expectedReturnTimes_formula (P := P) (X := X) with ⟨hs6, hs7, hs8⟩
  rcases hx with rfl | rfl | rfl
  · change expectedFirstReturnTime P X s6 < ⊤
    rw [hs6]
    exact lt_of_le_of_ne le_top (ENNReal.div_ne_top (by simp) (by norm_num))
  · change expectedFirstReturnTime P X s7 < ⊤
    rw [hs7]
    exact lt_of_le_of_ne le_top (ENNReal.div_ne_top (by simp) (by norm_num))
  · change expectedFirstReturnTime P X s8 < ⊤
    rw [hs8]
    exact lt_of_le_of_ne le_top (ENNReal.div_ne_top (by simp) (by norm_num))

/-- Helper for Remark 17.31: subclaim (4) says that in any realization of the
Markov chain of Fig. 17.1, the expected first return times are `17 / 4`, `17 / 5`,
and `17 / 8` at the states `6`, `7`, and `8`. -/
theorem figure17_1_expectedReturnTimes :
    (expectedFirstReturnTime P X s6 = (17 : ENNReal) / 4) ∧
      (expectedFirstReturnTime P X s7 = (17 : ENNReal) / 5) ∧
      expectedFirstReturnTime P X s8 = (17 : ENNReal) / 8 := by
  exact figure17_1_expectedReturnTimes_formula (P := P) (X := X)

end Figure17_1

section Figure17_2

variable {Ω : Type*} [MeasurableSpace Ω]
variable {r : Set.Icc (0 : ENNReal) 1} {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℕ}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) P X]

/-- Helper for Remark 17.31: `ℕ+` is used as a discrete counting index for iterated entrance
times in the Fig. 17.2 Green-function normalization lemmas. -/
local instance : MeasurableSpace ℕ+ := ⊤

/-- Helper for Remark 17.31: the measurable structure on `ℕ+` is discrete. -/
local instance : DiscreteMeasurableSpace ℕ+ where
  forall_measurableSet := by
    intro s
    trivial

/-- Helper for Remark 17.31: the probability of a one-step state slice in Fig. 17.2 is exactly
the corresponding matrix entry. -/
private theorem figure17_2_timeOne_stateEvent
    (x y : ℕ) :
    (P x : Measure Ω) {ω | X 1 ω = y} = figure17_2TransitionMatrix r x y := by
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
  have hTransition :
      ((P x : Measure Ω).map (X 1)) ({y} : Set ℕ) =
        ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) x) ({y} : Set ℕ) :=
    congrArg (fun μ : Measure ℕ ↦ μ ({y} : Set ℕ)) (hReal.transition_eq x 1)
  have hKernel :
      discreteMatrixKernel (figure17_2TransitionMatrix r) x ({y} : Set ℕ) =
        figure17_2TransitionMatrix r x y := by
    rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
    simpa using
      (Measure.sum_smul_dirac_singleton
        (f := fun z : ℕ ↦ figure17_2TransitionMatrix r x z) (a := y))
  rw [pow_one, hKernel] at hTransition
  -- Proof comment: after reducing the one-step kernel power, the singleton mass is exactly the
  -- corresponding discrete-matrix entry.
  simpa [Measure.map_apply, hReal.measurable_process 1] using hTransition

/-- Helper for Remark 17.31: the probability of a one-step state slice in Fig. 17.2 is exactly
the corresponding matrix entry. -/
private theorem figure17_2_timeOne_stateEvent_real
    (x y : ℕ) :
    (P x : Measure Ω).real {ω | X 1 ω = y} = (figure17_2TransitionMatrix r x y).toReal := by
  -- Proof comment: the real-valued statement is the `toReal` shadow of the ENNReal one-step law.
  simpa [Measure.real_def] using
    congrArg ENNReal.toReal (figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) x y)

/-- Helper for Remark 17.31: the positive-time hit event of a fixed state in Fig. 17.2 is
measurable. -/
private theorem figure17_2_measurableSet_exists_positiveEq
    [hReal : IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X]
    (x : ℕ) :
    MeasurableSet {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} := by
  have hUnion :
      {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = ⋃ n : ℕ, {ω | 0 < n ∧ X n ω = x} := by
    ext ω
    simp
  rw [hUnion]
  refine MeasurableSet.iUnion fun n ↦ ?_
  by_cases hn : 0 < n
  · have hset : {ω | 0 < n ∧ X n ω = x} = X n ⁻¹' ({x} : Set ℕ) := by
      ext ω
      simp [hn]
    rw [hset]
    exact (hReal.measurable_process n) (measurableSet_singleton x)
  · have hset : {ω | 0 < n ∧ X n ω = x} = (∅ : Set Ω) := by
      ext ω
      simp [hn]
    rw [hset]
    simp

/-- Helper for Remark 17.31: every generated history filtration of the Fig. 17.2 realization is
contained in the ambient measurable space. -/
private theorem figure17_2_generatedFiltrationSpace_le_ambient
    (hX_meas : ∀ n : ℕ, Measurable (X n)) (n : ℕ) :
    generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
  -- Proof comment: each coordinate sigma-algebra used to build the history filtration is already
  -- ambient because every time slice of the realization is measurable.
  refine iSup_le fun j ↦ iSup_le fun hj ↦ ?_
  exact (hX_meas j).comap_le

/-- Helper for Remark 17.31: a state-membership event at time `j ≤ n` is measurable in the
generated filtration at time `n` for the Fig. 17.2 realization. -/
private theorem figure17_2_measurableSet_mem_of_le_generatedFiltration
    {j n : ℕ} (hjn : j ≤ n) (A : Set ℕ) :
    MeasurableSet[generatedFiltrationSpace X n] {ω | X j ω ∈ A} := by
  have hXj_meas : Measurable[generatedFiltrationSpace X n] (X j) := by
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le j <| le_iSup_of_le hjn le_rfl
  -- Proof comment: on the discrete state space `ℕ`, every subset is measurable.
  simpa [Set.preimage, Set.mem_setOf_eq] using hXj_meas MeasurableSet.of_discrete

/-- Helper for Remark 17.31: finite-horizon no-hit events in Fig. 17.2 are measurable. -/
private theorem figure17_2_measurableSet_noHitHorizon
    (hX_meas : ∀ n : ℕ, Measurable (X n)) (x n M : ℕ) :
    MeasurableSet (noHitHorizonLocal X x n M) := by
  classical
  have hEq :
      noHitHorizonLocal X x n M =
        ⋂ m ∈ (Finset.Icc 1 M : Finset ℕ), {ω | X (n + m) ω ≠ x} := by
    ext ω
    simp [noHitHorizonLocal, Finset.mem_Icc]
  rw [hEq]
  refine MeasurableSet.biInter (Set.to_countable _) ?_
  intro m hm
  -- Proof comment: each forbidden singleton slice `{ω | X (n + m) ω = x}` is measurable, so its
  -- complement is measurable as well.
  exact (hX_meas (n + m)) (measurableSet_singleton x).compl

/-- Helper for Remark 17.31: a singleton target row of the Fig. 17.2 discrete kernel is exactly
the corresponding transition-matrix entry. -/
private theorem figure17_2_discreteMatrixKernel_apply_singleton
    (x y : ℕ) :
    discreteMatrixKernel (figure17_2TransitionMatrix r) x ({y} : Set ℕ) =
      figure17_2TransitionMatrix r x y := by
  -- Proof comment: evaluate the weighted Dirac sum defining the discrete kernel on the singleton
  -- `{y}` and isolate the unique contributing term.
  rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
  simpa using
    (Measure.sum_smul_dirac_singleton
      (f := fun z : ℕ ↦ figure17_2TransitionMatrix r x z) (a := y))

/-- Helper for Remark 17.31: composing a measure on `ℕ` with the Fig. 17.2 discrete kernel and
then evaluating on a singleton gives the expected matrix action. -/
private theorem figure17_2_comp_discreteMatrixKernel_apply_singleton_eq_tsum
    (μ : Measure ℕ) (x : ℕ) :
    ((discreteMatrixKernel (figure17_2TransitionMatrix r)) ∘ₘ μ) ({x} : Set ℕ) =
      ∑' y : ℕ, μ ({y} : Set ℕ) * figure17_2TransitionMatrix r y x := by
  -- Proof comment: expand the composition against a countable discrete measure and then rewrite
  -- each row singleton by the local Fig. 17.2 kernel-entry identity.
  rw [Measure.comp_eq_sum_of_countable]
  rw [Measure.sum_apply _ (measurableSet_singleton x)]
  congr with y
  rw [Measure.smul_apply]
  rw [figure17_2_discreteMatrixKernel_apply_singleton]
  simp [smul_eq_mul, mul_comm]

/-- Helper for Remark 17.31: for an invariant probability measure of the Fig. 17.2 kernel, the
singleton masses satisfy the discrete balance equations. -/
private theorem figure17_2_invariantBalance_singleton
    (π : ProbabilityMeasure ℕ)
    (hπ : Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
      (π : Measure ℕ)) (x : ℕ) :
    ∑' y : ℕ, (π : Measure ℕ) ({y} : Set ℕ) * figure17_2TransitionMatrix r y x =
      (π : Measure ℕ) ({x} : Set ℕ) := by
  -- Proof comment: evaluate the invariant-measure identity on the singleton `{x}` and rewrite
  -- the composed measure via the discrete singleton expansion above.
  have hx := congrArg (fun ν : Measure ℕ ↦ ν ({x} : Set ℕ)) hπ.def
  simpa [figure17_2_comp_discreteMatrixKernel_apply_singleton_eq_tsum] using hx

/-- Helper for Remark 17.31: a positive `n`-step singleton mass followed by a positive one-step
singleton mass yields a positive `(n + 1)`-step singleton mass. -/
private theorem figure17_2_discreteKernel_singleton_pos_succ
    {x y z : ℕ} {n : ℕ}
    (hxy : 0 <
      ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) x) ({y} : Set ℕ))
    (hyz : 0 <
      (discreteMatrixKernel (figure17_2TransitionMatrix r) y) ({z} : Set ℕ)) :
    0 <
      ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ (n + 1)) x) ({z} : Set ℕ) := by
  let κ : Kernel ℕ ℕ := discreteMatrixKernel (figure17_2TransitionMatrix r)
  have hmeas : Measurable fun w : ℕ ↦ κ w ({z} : Set ℕ) :=
    Kernel.measurable_coe κ (MeasurableSet.singleton z)
  have hySupport : y ∈ Function.support fun w : ℕ ↦ κ w ({z} : Set ℕ) := by
    change (κ y) ({z} : Set ℕ) ≠ 0
    exact ne_of_gt hyz
  have hsupportPos :
      0 < ((κ ^ n) x) (Function.support fun w : ℕ ↦ κ w ({z} : Set ℕ)) :=
    measure_pos_of_superset (Set.singleton_subset_iff.mpr hySupport) hxy.ne'
  -- Proof comment: the positive intermediate state `y` belongs to the integrand support, so the
  -- successor-step lintegral is strictly positive.
  rw [Kernel.pow_succ_apply_eq_lintegral κ n x (measurableSet_singleton z)]
  rw [MeasureTheory.lintegral_pos_iff_support hmeas]
  exact hsupportPos

/-- Helper for Remark 17.31: following `n` successive right jumps from `x` has strictly positive
`n`-step mass under the Fig. 17.2 kernel whenever the right-jump probability is positive. -/
private theorem figure17_2_rightPathStepMass_pos
    (hr0 : 0 < (r : ENNReal)) (x : ℕ) :
    ∀ n : ℕ,
      0 <
        ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) x) ({x + n} : Set ℕ) := by
  intro n
  induction n generalizing x with
  | zero =>
      -- Proof comment: the zero-step kernel is the identity, so it charges the starting point.
      rw [pow_zero]
      simpa using
        (show 0 < (Kernel.id x) ({x} : Set ℕ) by
          rw [Kernel.id_apply]
          simp)
  | succ n ih =>
      have hrest :
          0 <
            ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) x)
              ({x + n} : Set ℕ) := ih x
      have hlast :
          0 <
            (discreteMatrixKernel (figure17_2TransitionMatrix r) (x + n))
              ({x + (n + 1)} : Set ℕ) := by
        rw [figure17_2_discreteMatrixKernel_apply_singleton]
        by_cases hxn : x + n = 0
        · have hx0 : x = 0 := by omega
          have hn0 : n = 0 := by omega
          subst hx0
          subst hn0
          simp [figure17_2TransitionMatrix]
        · rcases Nat.exists_eq_succ_of_ne_zero hxn with ⟨m, hm⟩
          rw [hm]
          have hstep : x + (n + 1) = m + 2 := by omega
          simpa [figure17_2TransitionMatrix, hstep] using hr0
      exact figure17_2_discreteKernel_singleton_pos_succ hrest hlast

/-- Helper for Remark 17.31: following `n` successive left jumps from `x + n` back to `x` has
strictly positive mass whenever the left-jump probability is positive. -/
private theorem figure17_2_leftPathStepMass_pos
    (hr1 : (r : ENNReal) < 1) (x : ℕ) :
    ∀ n : ℕ,
      0 <
        ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) (x + n)) ({x} : Set ℕ) := by
  have hleft : 0 < 1 - (r : ENNReal) := by
    exact tsub_pos_of_lt hr1
  intro n
  induction n generalizing x with
  | zero =>
      -- Proof comment: the zero-step kernel is the identity, so it charges the starting point.
      rw [pow_zero]
      simpa using
        (show 0 < (Kernel.id x) ({x} : Set ℕ) by
          rw [Kernel.id_apply]
          simp)
  | succ n ih =>
      have hrest :
          0 <
            ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) ((x + 1) + n))
              ({x + 1} : Set ℕ) := by
        simpa [Nat.add_assoc] using ih (x + 1)
      have hlast :
          0 <
            (discreteMatrixKernel (figure17_2TransitionMatrix r) (x + 1)) ({x} : Set ℕ) := by
        rw [figure17_2_discreteMatrixKernel_apply_singleton]
        simpa [figure17_2TransitionMatrix] using hleft
      -- Proof comment: follow the already-positive path from `x + (n + 1)` down to `x + 1`,
      -- then take one final left jump to `x`.
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        figure17_2_discreteKernel_singleton_pos_succ hrest hlast

/-- Helper for Remark 17.31: a strictly positive finite-step singleton mass already forces the
corresponding ever-hit probability to be strictly positive. -/
private theorem figure17_2_everHitsProbability_pos_of_posStepMass
    {x y n : ℕ} (hn : 0 < n)
    (hstep :
      0 < ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) x) ({y} : Set ℕ)) :
    0 < (F[P, X]) x y := by
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
  have hslice :
      0 < (P x : Measure Ω) {ω | X n ω = y} := by
    have hpreimage : {ω | X n ω = y} = X n ⁻¹' ({y} : Set ℕ) := by
      ext ω
      simp
    rw [hpreimage]
    rw [← Measure.map_apply (hReal.measurable_process n) (measurableSet_singleton y)]
    rw [hReal.transition_eq x n]
    simpa using hstep
  have hsubset :
      {ω | X n ω = y} ⊆ {ω | ∃ m : ℕ, 0 < m ∧ X m ω = y} := by
    intro ω hω
    exact ⟨n, hn, hω⟩
  have hhit_enn :
      0 < (P x : Measure Ω) {ω | ∃ m : ℕ, 0 < m ∧ X m ω = y} := by
    -- Proof comment: the concrete time-`n` slice sits inside the positive-time ever-hit event.
    exact lt_of_lt_of_le hslice (measure_mono hsubset)
  -- Proof comment: the ever-hit probability is the real mass of that positive event.
  rw [everHitsProbability_def, Measure.real_def]
  exact ENNReal.toReal_pos hhit_enn.ne' (measure_ne_top (P x : Measure Ω) _)

/-- Helper for Remark 17.31: from any state strictly below `x`, the Fig. 17.2 walk has positive
probability to hit `x` by following a finite right-moving path. -/
private theorem figure17_2_everHitsProbability_fromBelow_pos
    (hr0 : 0 < (r : ENNReal)) {y x : ℕ} (hyx : y < x) :
    0 < (F[P, X]) y x := by
  have hstep :
      0 <
        ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ (x - y)) y)
          ({x} : Set ℕ) := by
    -- Proof comment: the monotone right path of length `x - y` reaches `x` with positive mass.
    simpa [Nat.add_sub_of_le hyx.le] using
      figure17_2_rightPathStepMass_pos (r := r) hr0 y (x - y)
  -- Proof comment: any strictly positive finite-step mass already yields a strictly positive
  -- ever-hit probability.
  exact
    figure17_2_everHitsProbability_pos_of_posStepMass
      (r := r) (P := P) (X := X) (Nat.sub_pos_of_lt hyx) hstep

/-- Helper for Remark 17.31: the generated history filtration of the Fig. 17.2 realization grows
monotonically with the time index. -/
private theorem figure17_2_generatedFiltrationSpace_monoNat
    (s t : ℕ) (hst : s ≤ t) :
    generatedFiltrationSpace X s ≤ generatedFiltrationSpace X t := by
  -- Proof comment: enlarging the terminal time only enlarges the supremum of available history
  -- coordinates.
  refine iSup₂_le fun r hr ↦ ?_
  exact le_iSup_of_le r <| le_iSup_of_le (hr.trans hst) le_rfl

/-- Helper for Remark 17.31: `futurePrefixEventLocal X n f` is the exact path-cylinder event
that prescribes the deterministic-time segment `X n, X (n + 1), ..., X (n + M)`. -/
private def futurePrefixEventLocal (Y : ℕ → Ω → ℕ) (n : ℕ) {M : ℕ}
    (f : Fin (M + 1) → ℕ) : Set Ω :=
  {ω | ∀ i : Fin (M + 1), Y (n + (i : ℕ)) ω = f i}

/-- Helper for Remark 17.31: finite future-prefix events for Fig. 17.2 are measurable in the
ambient sigma-algebra. -/
private theorem figure17_2_measurableSet_futurePrefixEvent
    (hX_meas : ∀ n : ℕ, Measurable (X n)) {M n : ℕ} (f : Fin (M + 1) → ℕ) :
    MeasurableSet (futurePrefixEventLocal X n f) := by
  have hEq :
      futurePrefixEventLocal X n f =
        ⋂ i : Fin (M + 1), {ω | X (n + (i : ℕ)) ω = f i} := by
    ext ω
    simp [futurePrefixEventLocal]
  rw [hEq]
  -- Proof comment: an exact finite path cylinder is the intersection of finitely many singleton
  -- coordinate slices, one for each prescribed deterministic time.
  refine MeasurableSet.iInter fun i ↦ ?_
  exact hX_meas (n + (i : ℕ)) (measurableSet_singleton (f i))

/-- Helper for Remark 17.31: a one-term future prefix is exactly the corresponding state event. -/
private theorem figure17_2_futurePrefixEvent_zero_eq_stateEvent
    (n : ℕ) (f : Fin 1 → ℕ) :
    futurePrefixEventLocal X n f = {ω | X n ω = f 0} := by
  -- Proof comment: at horizon `0`, the unique `Fin 1` coordinate is the current state only.
  ext ω
  simp [futurePrefixEventLocal]

/-- Helper for Remark 17.31: a finite future-prefix event is measurable with respect to the
generated filtration at its terminal time. -/
private theorem figure17_2_measurableSet_futurePrefixEvent_generated
    {M n : ℕ} (f : Fin (M + 1) → ℕ) :
    MeasurableSet[generatedFiltrationSpace X (n + M)] (futurePrefixEventLocal X n f) := by
  have hEq :
      futurePrefixEventLocal X n f =
        ⋂ i : Fin (M + 1), {ω | X (n + (i : ℕ)) ω = f i} := by
    ext ω
    simp [futurePrefixEventLocal]
  rw [hEq]
  -- Proof comment: every constrained coordinate occurs no later than `n + M`, so each singleton
  -- slice already belongs to the generated history filtration at that terminal time.
  refine MeasurableSet.iInter fun i ↦ ?_
  exact figure17_2_measurableSet_mem_of_le_generatedFiltration
    (X := X) (j := n + (i : ℕ)) (n := n + M)
    (Nat.add_le_add_left (Nat.le_of_lt_succ i.2) n) ({f i} : Set ℕ)

/-- Helper for Remark 17.31: a longer Fig. 17.2 future-prefix event splits into its shorter prefix
and the final deterministic-time state event. -/
private theorem figure17_2_futurePrefixEvent_succ_eq
    {M n : ℕ} (f : Fin (M + 2) → ℕ) :
    futurePrefixEventLocal X n f =
      futurePrefixEventLocal X n (fun i : Fin (M + 1) ↦ f i.castSucc) ∩
        {ω | X (n + (M + 1)) ω = f (Fin.last (M + 1))} := by
  -- Proof comment: split the exact path condition into the first `M + 1` coordinates and the
  -- terminal coordinate.
  ext ω
  constructor
  · intro hω
    refine ⟨?_, ?_⟩
    · intro i
      simpa [futurePrefixEventLocal] using hω i.castSucc
    · simpa [futurePrefixEventLocal] using hω (Fin.last (M + 1))
  · rintro ⟨hωPrefix, hωLast⟩
    intro i
    by_cases hi : i = Fin.last (M + 1)
    · subst hi
      simpa [futurePrefixEventLocal] using hωLast
    · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      simpa [futurePrefixEventLocal] using hωPrefix j

/-- Helper for Remark 17.31: a finite Fig. 17.2 future-prefix event determines its terminal
state. -/
private theorem figure17_2_futurePrefixEvent_terminal_subset
    {M n : ℕ} (f : Fin (M + 1) → ℕ) :
    futurePrefixEventLocal X n f ⊆ {ω | X (n + M) ω = f (Fin.last M)} := by
  -- Proof comment: the terminal deterministic time is one of the prescribed coordinates.
  intro ω hω
  simpa [futurePrefixEventLocal] using hω (Fin.last M)

/-- Helper for Remark 17.31: if a history event already fixes the state at time `n`, then
intersecting it with a later singleton event factors through the corresponding transition mass. -/
private theorem figure17_2_measure_inter_prefix_stepEvent_eq_mulLocal
    {x y z : ℕ} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z}) =
      (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y) ({z} : Set ℕ)).toReal *
        (P x : Measure Ω).real A := by
  let μ : Measure Ω := P x
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
  let B : Set Ω := X (n + m) ⁻¹' ({z} : Set ℕ)
  have hB_meas : MeasurableSet B := by
    simpa [B] using (hReal.measurable_process (n + m)) (measurableSet_singleton z)
  have hA_measAmbient : MeasurableSet A := by
    have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› :=
      figure17_2_generatedFiltrationSpace_le_ambient (X := X) hReal.measurable_process n
    dsimp [LE.le] at hFiltration_le
    exact hFiltration_le (s := A) hA_meas
  have hMarkovGenerated :
      μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
        fun ω ↦ (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) (X n ω))
          ({z} : Set ℕ)).toReal := by
    simpa [μ, B, add_comm] using
      hReal.markov_property x (A := ({z} : Set ℕ)) (measurableSet_singleton z) n m
  have hIndicatorIntegrable : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB_meas
  -- Proof comment: integrate the Markov conditional expectation over `A`, then freeze the future
  -- law at `y` because `A` already pins the time-`n` state.
  calc
    μ.real (A ∩ {ω | X (n + m) ω = z}) =
        ∫ ω in A, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂ μ := by
          rw [setIntegral_condExp
              (figure17_2_generatedFiltrationSpace_le_ambient (X := X) hReal.measurable_process n)
              hIndicatorIntegrable hA_meas,
            ← integral_indicator hA_measAmbient]
          symm
          simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
            smul_eq_mul] using integral_indicator_const (1 : ℝ) (hA_measAmbient.inter hB_meas)
    _ = ∫ ω in A,
          (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) (X n ω))
            ({z} : Set ℕ)).toReal ∂ μ := by
            exact integral_congr_ae hMarkovGenerated.restrict
    _ = ∫ _ in A,
          (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y)
            ({z} : Set ℕ)).toReal ∂ μ := by
            refine integral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict (μ := μ) (s := A) hA_measAmbient] with ω hω
            have hω : X n ω = y := hA_sub hω
            rw [hω]
    _ =
        (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y)
          ({z} : Set ℕ)).toReal * μ.real A := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- Helper for Remark 17.31: the deterministic-time Fig. 17.2 prefix factorization is cleaner in
raw `Measure` (`ℝ≥0∞`) form. -/
private theorem figure17_2_measure_inter_prefix_stepEvent_eq_mul_ennrealLocal
    {x y z : ℕ} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) =
      (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y) ({z} : Set ℕ)) *
        (P x : Measure Ω) A := by
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
  let _ :
      IsMarkovKernel (discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) :=
    hReal.semigroup.isMarkovKernel m
  have hstep :
      (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z}) =
        (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y)
          ({z} : Set ℕ)).toReal * (P x : Measure Ω).real A :=
    figure17_2_measure_inter_prefix_stepEvent_eq_mulLocal
      (r := r) (P := P) (X := X) hA_meas hA_sub
  have hleft_ne_top :
      (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) ≠ ⊤ := measure_ne_top _ _
  have hkernel_ne_top :
      (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y)
        ({z} : Set ℕ)) ≠ ⊤ := measure_ne_top _ _
  have hA_ne_top : (P x : Measure Ω) A ≠ ⊤ := measure_ne_top _ _
  -- Proof comment: convert the already-proved real-valued identity back to ENNReal masses.
  calc
    (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) =
        ENNReal.ofReal ((P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z})) := by
          symm
          exact ENNReal.ofReal_toReal hleft_ne_top
    _ =
        ENNReal.ofReal
          ((((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y)
            ({z} : Set ℕ)).toReal * (P x : Measure Ω).real A) := by
              rw [hstep]
    _ =
        (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y) ({z} : Set ℕ)) *
          (P x : Measure Ω) A := by
            rw [ENNReal.ofReal_mul]
            · rw [ENNReal.ofReal_toReal hkernel_ne_top]
              change
                (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y)
                  ({z} : Set ℕ)) * ENNReal.ofReal (((P x : Measure Ω) A).toReal) =
                  (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y)
                    ({z} : Set ℕ)) * (P x : Measure Ω) A
              rw [ENNReal.ofReal_toReal hA_ne_top]
            · positivity

/-- Helper for Remark 17.31: once a history event pins down the current state, intersecting it
with a finite exact future path factors through the future path law from that state. -/
private theorem figure17_2_measure_inter_prefix_futurePrefixEvent_eq_mulLocal
    (hReal : IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X)
    {x y : ℕ} {A : Set Ω} {n M : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y})
    (f : Fin (M + 1) → ℕ) :
    (P x : Measure Ω) (A ∩ futurePrefixEventLocal X n f) =
      (P y : Measure Ω) (futurePrefixEventLocal X 0 f) * (P x : Measure Ω) A := by
  induction M generalizing n A y with
  | zero =>
      have hright_eval :
          (P y : Measure Ω) (futurePrefixEventLocal X 0 f) =
            if f 0 = y then 1 else 0 := by
        rw [figure17_2_futurePrefixEvent_zero_eq_stateEvent (X := X) (n := 0) f]
        have hpreimage : {ω | X 0 ω = f 0} = X 0 ⁻¹' ({f 0} : Set ℕ) := by
          ext ω
          simp
        rw [hpreimage]
        rw [← Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton (f 0))]
        rw [hReal.initial_eq y]
        by_cases hf0 : f 0 = y <;> simp [hf0]
      by_cases hf0 : f 0 = y
      · have hleft_eq : A ∩ futurePrefixEventLocal X n f = A := by
          ext ω
          constructor
          · intro hω
            exact hω.1
          · intro hω
            refine ⟨hω, ?_⟩
            rw [figure17_2_futurePrefixEvent_zero_eq_stateEvent (X := X) (n := n) f]
            simpa [hf0] using hA_sub hω
        -- Proof comment: at horizon `0`, the exact future path only asks for the current state.
        calc
          (P x : Measure Ω) (A ∩ futurePrefixEventLocal X n f) = (P x : Measure Ω) A := by
            rw [hleft_eq]
          _ = 1 * (P x : Measure Ω) A := by rw [one_mul]
          _ = (P y : Measure Ω) (futurePrefixEventLocal X 0 f) * (P x : Measure Ω) A := by
            rw [hright_eval, if_pos hf0]
      · have hleft_eq : A ∩ futurePrefixEventLocal X n f = ∅ := by
          ext ω
          constructor
          · rintro ⟨hωA, hωf⟩
            rw [figure17_2_futurePrefixEvent_zero_eq_stateEvent (X := X) (n := n) f] at hωf
            exact hf0 (hωf.symm.trans (hA_sub hωA))
          · intro hω
            exact False.elim (by simpa using hω)
        calc
          (P x : Measure Ω) (A ∩ futurePrefixEventLocal X n f) = 0 := by
            simp [hleft_eq]
          _ = (P y : Measure Ω) (futurePrefixEventLocal X 0 f) * (P x : Measure Ω) A := by
            rw [hright_eval, if_neg hf0]
            simp
  | succ M ih =>
      let g : Fin (M + 1) → ℕ := fun i ↦ f i.castSucc
      let B : Set Ω := A ∩ futurePrefixEventLocal X n g
      have hA_meas_big : MeasurableSet[generatedFiltrationSpace X (n + M)] A := by
        have hmono : generatedFiltrationSpace X n ≤ generatedFiltrationSpace X (n + M) :=
          figure17_2_generatedFiltrationSpace_monoNat (X := X) n (n + M) (Nat.le_add_right n M)
        exact hmono (s := A) hA_meas
      have hB_meas : MeasurableSet[generatedFiltrationSpace X (n + M)] B := by
        exact hA_meas_big.inter
          (figure17_2_measurableSet_futurePrefixEvent_generated (X := X) (n := n) g)
      have hB_sub : B ⊆ {ω | X (n + M) ω = g (Fin.last M)} := by
        intro ω hω
        exact figure17_2_futurePrefixEvent_terminal_subset (X := X) (n := n) g hω.2
      have hleft_step :
          (P x : Measure Ω) (A ∩ futurePrefixEventLocal X n f) =
            (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) (g (Fin.last M)))
              ({f (Fin.last (M + 1))} : Set ℕ)) *
              (P x : Measure Ω) B := by
        calc
          (P x : Measure Ω) (A ∩ futurePrefixEventLocal X n f) =
              (P x : Measure Ω)
                (B ∩ {ω | X ((n + M) + 1) ω = f (Fin.last (M + 1))}) := by
                  simp [B, g, figure17_2_futurePrefixEvent_succ_eq, Nat.add_assoc,
                    Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
          _ =
              (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) (g (Fin.last M)))
                ({f (Fin.last (M + 1))} : Set ℕ)) *
                (P x : Measure Ω) B := by
                  simpa [B] using
                    figure17_2_measure_inter_prefix_stepEvent_eq_mul_ennrealLocal
                      (r := r) (P := P) (X := X)
                      (x := x) (y := g (Fin.last M)) (z := f (Fin.last (M + 1)))
                      (A := B) (n := n + M) (m := 1) hB_meas hB_sub
      have hg_meas :
          MeasurableSet[generatedFiltrationSpace X M] (futurePrefixEventLocal X 0 g) := by
        have htmp :
            MeasurableSet[generatedFiltrationSpace X (0 + M)] (futurePrefixEventLocal X 0 g) :=
          figure17_2_measurableSet_futurePrefixEvent_generated (X := X) (n := 0) g
        convert htmp using 1 <;> simp [zero_add]
      have hg_sub :
          futurePrefixEventLocal X 0 g ⊆ {ω | X M ω = g (Fin.last M)} := by
        have htmp :
            futurePrefixEventLocal X 0 g ⊆ {ω | X (0 + M) ω = g (Fin.last M)} :=
          figure17_2_futurePrefixEvent_terminal_subset (X := X) (n := 0) g
        simpa [zero_add] using htmp
      have hright_step :
          (P y : Measure Ω) (futurePrefixEventLocal X 0 f) =
            (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) (g (Fin.last M)))
              ({f (Fin.last (M + 1))} : Set ℕ)) *
              (P y : Measure Ω) (futurePrefixEventLocal X 0 g) := by
        calc
          (P y : Measure Ω) (futurePrefixEventLocal X 0 f) =
              (P y : Measure Ω)
                (futurePrefixEventLocal X 0 g ∩
                  {ω | X (M + 1) ω = f (Fin.last (M + 1))}) := by
                  simp [g, figure17_2_futurePrefixEvent_succ_eq, Nat.add_assoc,
                    Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
          _ =
              (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) (g (Fin.last M)))
                ({f (Fin.last (M + 1))} : Set ℕ)) *
                (P y : Measure Ω) (futurePrefixEventLocal X 0 g) := by
                  simpa using
                    figure17_2_measure_inter_prefix_stepEvent_eq_mul_ennrealLocal
                      (r := r) (P := P) (X := X)
                      (x := y) (y := g (Fin.last M)) (z := f (Fin.last (M + 1)))
                      (A := futurePrefixEventLocal X 0 g) (n := M) (m := 1) hg_meas hg_sub
      -- Proof comment: split off the final coordinate of the exact path and reuse the induction
      -- hypothesis on the shorter prefix.
      calc
        (P x : Measure Ω) (A ∩ futurePrefixEventLocal X n f) =
            (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) (g (Fin.last M)))
              ({f (Fin.last (M + 1))} : Set ℕ)) *
              (P x : Measure Ω) B := hleft_step
        _ =
            (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) (g (Fin.last M)))
              ({f (Fin.last (M + 1))} : Set ℕ)) *
              ((P y : Measure Ω) (futurePrefixEventLocal X 0 g) * (P x : Measure Ω) A) := by
                have hBfactor :
                    (P x : Measure Ω) B =
                      (P y : Measure Ω) (futurePrefixEventLocal X 0 g) * (P x : Measure Ω) A := by
                        simpa [B] using ih hA_meas hA_sub g
                rw [hBfactor]
        _ =
            ((((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) (g (Fin.last M)))
              ({f (Fin.last (M + 1))} : Set ℕ)) *
              (P y : Measure Ω) (futurePrefixEventLocal X 0 g)) *
              (P x : Measure Ω) A := by
                rw [mul_assoc]
        _ = (P y : Measure Ω) (futurePrefixEventLocal X 0 f) * (P x : Measure Ω) A := by
              rw [hright_step]

/-- Helper for Remark 17.31: after fixing the time-`1` state to `z + 1`, a finite horizon of
avoiding `0` factors through the restarted chain from `z + 1`. -/
private theorem figure17_2_measure_inter_prefix_noHitHorizonZero_eq_mulLocal
    (r : Set.Icc (0 : ENNReal) 1)
    [IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X]
    {z start M : ℕ} {A : Set Ω}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X 1] A)
    (hA_sub : A ⊆ {ω | X 1 ω = z + 1}) :
    (P start : Measure Ω) (A ∩ noHitHorizonLocal X 0 1 M) =
      (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (P start : Measure Ω) A := by
  classical
  let μstart : Measure Ω := P start
  let μz : Measure Ω := P (z + 1)
  let T : Type := {f : Fin (M + 1) → ℕ //
    f 0 = z + 1 ∧ ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ 0}
  let hReal : IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
  have hA_ambient : MeasurableSet A := by
    have hFiltration_le : generatedFiltrationSpace X 1 ≤ ‹MeasurableSpace Ω› := by
      refine iSup₂_le fun k hk ↦ ?_
      exact (hReal.measurable_process k).comap_le
    exact hFiltration_le (s := A) hA_meas
  have hleft_union :
      A ∩ noHitHorizonLocal X 0 1 M = ⋃ f : T, A ∩ futurePrefixEventLocal X 1 f.1 := by
    ext ω
    constructor
    · rintro ⟨hωA, hωNoHit⟩
      let f : Fin (M + 1) → ℕ := fun i ↦ X (1 + (i : ℕ)) ω
      have hf0 : f 0 = z + 1 := by
        simpa [f] using hA_sub hωA
      have hfNoHit : ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ 0 := by
        intro i hi
        exact hωNoHit (i : ℕ) hi (Nat.le_of_lt_succ i.2)
      refine Set.mem_iUnion.2 ⟨⟨f, hf0, hfNoHit⟩, ?_⟩
      refine ⟨hωA, ?_⟩
      intro i
      rfl
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨f, hωf⟩
      refine ⟨hωf.1, ?_⟩
      intro m hm hmM hmEq
      let i : Fin (M + 1) := ⟨m, Nat.lt_succ_of_le hmM⟩
      have hpath : X (1 + m) ω = f.1 i := by
        simpa [futurePrefixEventLocal, i] using hωf.2 i
      exact (f.2.2 i hm) (hpath ▸ hmEq)
  have hright_union :
      {ω | X 0 ω = z + 1} ∩ noHitHorizonLocal X 0 0 M = ⋃ f : T, futurePrefixEventLocal X 0 f.1 := by
    ext ω
    constructor
    · rintro ⟨hω0, hωNoHit⟩
      let f : Fin (M + 1) → ℕ := fun i ↦ X (i : ℕ) ω
      have hf0 : f 0 = z + 1 := by
        simpa [f] using hω0
      have hfNoHit : ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ 0 := by
        intro i hi
        simpa [f, zero_add] using hωNoHit (i : ℕ) hi (Nat.le_of_lt_succ i.2)
      refine Set.mem_iUnion.2 ⟨⟨f, hf0, hfNoHit⟩, ?_⟩
      intro i
      simp [f, zero_add]
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨f, hωf⟩
      refine ⟨?_, ?_⟩
      · simpa [f.2.1] using hωf 0
      · intro m hm hmM hmEq
        let i : Fin (M + 1) := ⟨m, Nat.lt_succ_of_le hmM⟩
        have hpath : X (0 + m) ω = f.1 i := by
          simpa [futurePrefixEventLocal, i, zero_add] using hωf i
        exact (f.2.2 i hm) (by simpa [zero_add] using hpath ▸ hmEq)
  have hpairwise_left :
      Pairwise (fun f g : T ↦ Disjoint (A ∩ futurePrefixEventLocal X 1 f.1)
        (A ∩ futurePrefixEventLocal X 1 g.1)) := by
    intro f g hfg
    refine Set.disjoint_left.2 ?_
    intro ω hωf hωg
    have hEq : f.1 = g.1 := by
      funext i
      exact (hωf.2 i).symm.trans (hωg.2 i)
    exact hfg (Subtype.ext hEq)
  have hpairwise_right :
      Pairwise (fun f g : T ↦ Disjoint (futurePrefixEventLocal X 0 f.1)
        (futurePrefixEventLocal X 0 g.1)) := by
    intro f g hfg
    refine Set.disjoint_left.2 ?_
    intro ω hωf hωg
    have hEq : f.1 = g.1 := by
      funext i
      exact (hωf i).symm.trans (hωg i)
    exact hfg (Subtype.ext hEq)
  have hleft_sum :
      μstart (A ∩ noHitHorizonLocal X 0 1 M) =
        ∑' f : T, μstart (A ∩ futurePrefixEventLocal X 1 f.1) := by
    rw [hleft_union, measure_iUnion hpairwise_left]
    intro f
    exact hA_ambient.inter
      (figure17_2_measurableSet_futurePrefixEvent (X := X) hReal.measurable_process
        (n := 1) f.1)
  have hright_sum :
      μz ({ω | X 0 ω = z + 1} ∩ noHitHorizonLocal X 0 0 M) =
        ∑' f : T, μz (futurePrefixEventLocal X 0 f.1) := by
    rw [hright_union, measure_iUnion hpairwise_right]
    intro f
    exact figure17_2_measurableSet_futurePrefixEvent (X := X) hReal.measurable_process
      (n := 0) f.1
  have hslices :
      ∀ f : T,
        μstart (A ∩ futurePrefixEventLocal X 1 f.1) =
          μz (futurePrefixEventLocal X 0 f.1) * μstart A := by
    intro f
    have hA_sub_f : A ⊆ {ω | X 1 ω = f.1 0} := by
      intro ω hω
      rw [f.2.1]
      exact hA_sub hω
    -- Proof comment: once the time-`1` state is fixed to `z + 1`, each exact future path is
    -- governed by the restarted chain started from `z + 1`.
    simpa [μstart, μz, f.2.1] using
      (figure17_2_measure_inter_prefix_futurePrefixEvent_eq_mulLocal
        (r := r) (P := P) (X := X) hReal (x := start) (y := f.1 0)
        (A := A) (n := 1) hA_meas hA_sub_f f.1)
  have hstate_meas : MeasurableSet {ω | X 0 ω = z + 1} :=
    hReal.measurable_process 0 (measurableSet_singleton (z + 1))
  have hstate_prob_one : μz {ω | X 0 ω = z + 1} = 1 := by
    have hpreimage : {ω | X 0 ω = z + 1} = X 0 ⁻¹' ({z + 1} : Set ℕ) := by
      ext ω
      simp
    rw [hpreimage, ← Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton (z + 1))]
    rw [hReal.initial_eq (z + 1)]
    simp
  have hstate_compl_zero : μz ({ω | X 0 ω = z + 1}ᶜ) = 0 := by
    exact (prob_compl_eq_zero_iff hstate_meas).2 hstate_prob_one
  have hright_full :
      μz ({ω | X 0 ω = z + 1} ∩ noHitHorizonLocal X 0 0 M) =
        μz (noHitHorizonLocal X 0 0 M) := by
    have hstate_ae : ∀ᵐ ω ∂ μz, ω ∈ {ω | X 0 ω = z + 1} := by
      rw [ae_iff]
      exact hstate_compl_zero
    simpa [Set.inter_comm] using
      (Measure.measure_inter_eq_of_ae (μ := μz) (s := noHitHorizonLocal X 0 0 M)
        (t := {ω | X 0 ω = z + 1}) hstate_ae)
  -- Proof comment: partition the finite no-hit slice by exact future paths, factor each path
  -- through the restarted chain, and then drop the deterministic time-`0` state constraint.
  calc
    μstart (A ∩ noHitHorizonLocal X 0 1 M) =
        ∑' f : T, μstart (A ∩ futurePrefixEventLocal X 1 f.1) := hleft_sum
    _ = ∑' f : T, μz (futurePrefixEventLocal X 0 f.1) * μstart A := by
          refine tsum_congr fun f ↦ hslices f
    _ = (∑' f : T, μz (futurePrefixEventLocal X 0 f.1)) * μstart A := by
          rw [ENNReal.tsum_mul_right]
    _ = μz ({ω | X 0 ω = z + 1} ∩ noHitHorizonLocal X 0 0 M) * μstart A := by
          rw [← hright_sum]
    _ = μz (noHitHorizonLocal X 0 0 M) * μstart A := by
          rw [hright_full]

/-- Helper for Remark 17.31: `tailNoHitLocal X y n` is the event that after time `n` the path
never visits `y` again. -/
private def tailNoHitLocal (Y : ℕ → Ω → ℕ) (y : ℕ) (n : ℕ) : Set Ω :=
  ⋂ M : ℕ, noHitHorizonLocal Y y n M

/-- Helper for Remark 17.31: tail no-hit events are measurable. -/
private theorem figure17_2_measurableSet_tailNoHitLocal
    (r : Set.Icc (0 : ENNReal) 1)
    [IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X]
    (y n : ℕ) :
    MeasurableSet (tailNoHitLocal X y n) := by
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
  -- Proof comment: the tail event is the countable intersection of the measurable finite-horizon
  -- no-hit events.
  refine MeasurableSet.iInter fun M ↦ ?_
  exact figure17_2_measurableSet_noHitHorizon (X := X) hReal.measurable_process y n M

/-- Helper for Remark 17.31: the tail no-hit event is exactly the complement of the shifted
future-hit event. -/
private theorem figure17_2_tailNoHitLocal_compl_eq_futureHit
    (y n : ℕ) :
    (tailNoHitLocal X y n)ᶜ = {ω | ∃ m : ℕ, 0 < m ∧ X (n + m) ω = y} := by
  ext ω
  constructor
  · intro hω
    by_contra hhit
    apply hω
    refine Set.mem_iInter.2 ?_
    intro M
    intro m hm hmM
    exact fun hmEq ↦ hhit ⟨m, hm, hmEq⟩
  · rintro ⟨m, hm, hmEq⟩ hω
    exact (Set.mem_iInter.1 hω m) m hm le_rfl hmEq

/-- Helper for Remark 17.31: on a slice where the time-`1` state is fixed to `z + 1`, the tail
event of never hitting `0` again factors through the restarted chain from `z + 1`. -/
private theorem figure17_2_measure_inter_prefix_tailNoHitZero_eq_mulLocal
    (r : Set.Icc (0 : ENNReal) 1)
    [IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X]
    {z start : ℕ} {A : Set Ω}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X 1] A)
    (hA_sub : A ⊆ {ω | X 1 ω = z + 1}) :
    (P start : Measure Ω) (A ∩ tailNoHitLocal X 0 1) =
      (P (z + 1) : Measure Ω) (tailNoHitLocal X 0 0) * (P start : Measure Ω) A := by
  let μstart : Measure Ω := P start
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
  have hA_ambient : MeasurableSet A := by
    have hFiltration_le : generatedFiltrationSpace X 1 ≤ ‹MeasurableSpace Ω› :=
      figure17_2_generatedFiltrationSpace_le_ambient (X := X) hReal.measurable_process 1
    dsimp [LE.le] at hFiltration_le
    exact hFiltration_le (s := A) hA_meas
  have htail_eq :
      A ∩ tailNoHitLocal X 0 1 = ⋂ M : ℕ, A ∩ noHitHorizonLocal X 0 1 M := by
    ext ω
    constructor
    · rintro ⟨hωA, hωtail⟩
      refine Set.mem_iInter.2 ?_
      intro M
      exact ⟨hωA, Set.mem_iInter.1 hωtail M⟩
    · intro hω
      refine ⟨(Set.mem_iInter.1 hω 0).1, Set.mem_iInter.2 ?_⟩
      intro M
      exact (Set.mem_iInter.1 hω M).2
  have hleft_antitone :
      Antitone (fun M : ℕ ↦ A ∩ noHitHorizonLocal X 0 1 M) := by
    -- Proof comment: increasing the horizon strengthens the no-hit requirement.
    intro M N hMN
    intro ω hω
    refine ⟨hω.1, ?_⟩
    intro m hm hmN
    exact hω.2 m hm (hmN.trans hMN)
  have hright_antitone :
      Antitone (fun M : ℕ ↦ noHitHorizonLocal X 0 0 M) := by
    -- Proof comment: the restarted no-hit events are decreasing in the same way.
    intro M N hMN
    intro ω hω
    intro m hm hmN
    exact hω m hm (hmN.trans hMN)
  have hleft_tendsto :
      Filter.Tendsto (fun M ↦ μstart (A ∩ noHitHorizonLocal X 0 1 M)) Filter.atTop
        (nhds (μstart (A ∩ tailNoHitLocal X 0 1))) := by
    -- Proof comment: continuity from above identifies the tail event as the decreasing
    -- intersection of its finite-horizon approximations.
    simpa [htail_eq] using
      tendsto_measure_iInter_atTop (μ := μstart)
        (fun M ↦ (hA_ambient.inter
          (figure17_2_measurableSet_noHitHorizon (X := X)
            hReal.measurable_process
            0 1 M)).nullMeasurableSet)
        hleft_antitone
        ⟨0, measure_ne_top _ _⟩
  have hright_tendsto :
      Filter.Tendsto (fun M ↦ (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M)) Filter.atTop
        (nhds ((P (z + 1) : Measure Ω) (tailNoHitLocal X 0 0))) := by
    -- Proof comment: the restarted chain sees the same decreasing finite-horizon intersection.
    simpa [tailNoHitLocal] using
      tendsto_measure_iInter_atTop (μ := (P (z + 1) : Measure Ω))
        (fun M ↦ (figure17_2_measurableSet_noHitHorizon (X := X)
          hReal.measurable_process
          0 0 M).nullMeasurableSet)
        hright_antitone
        ⟨0, measure_ne_top _ _⟩
  have hfinite_real_eq :
      (fun M ↦ (μstart (A ∩ noHitHorizonLocal X 0 1 M)).toReal) =
        fun M ↦ ((P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M)).toReal * (μstart A).toReal := by
    funext M
    have hEqM :
        μstart (A ∩ noHitHorizonLocal X 0 1 M) =
          (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) * μstart A :=
      figure17_2_measure_inter_prefix_noHitHorizonZero_eq_mulLocal
        (r := r) (P := P) (X := X) (z := z) (start := start) (M := M)
        (A := A) hA_meas hA_sub
    simpa [ENNReal.toReal_mul, measure_ne_top _ _, measure_ne_top _ _] using
      congrArg ENNReal.toReal hEqM
  have hleft_real_tendsto :
      Filter.Tendsto (fun M ↦ (μstart (A ∩ noHitHorizonLocal X 0 1 M)).toReal) Filter.atTop
        (nhds ((μstart (A ∩ tailNoHitLocal X 0 1)).toReal)) := by
    exact
      (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp hleft_tendsto
  have hright_real_base :
      Filter.Tendsto
        (fun M ↦ ((P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M)).toReal)
        Filter.atTop
        (nhds (((P (z + 1) : Measure Ω) (tailNoHitLocal X 0 0)).toReal)) := by
    exact
      (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp hright_tendsto
  have hright_real_tendsto :
      Filter.Tendsto
        (fun M ↦
          ((P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M)).toReal * (μstart A).toReal)
        Filter.atTop
        (nhds (((P (z + 1) : Measure Ω) (tailNoHitLocal X 0 0)).toReal * (μstart A).toReal)) := by
    exact hright_real_base.mul_const ((μstart A).toReal)
  rw [hfinite_real_eq] at hleft_real_tendsto
  have hreal_eq :
      (μstart (A ∩ tailNoHitLocal X 0 1)).toReal =
        ((P (z + 1) : Measure Ω) (tailNoHitLocal X 0 0)).toReal * (μstart A).toReal :=
    tendsto_nhds_unique hleft_real_tendsto hright_real_tendsto
  have hleft_ne_top : μstart (A ∩ tailNoHitLocal X 0 1) ≠ ⊤ := measure_ne_top _ _
  have hright_ne_top :
      (P (z + 1) : Measure Ω) (tailNoHitLocal X 0 0) * μstart A ≠ ⊤ := by
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  -- Proof comment: the tail factorization is the limit of the finite-horizon factorization along
  -- the decreasing no-hit approximation.
  exact (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top).mp <| by
    simpa [ENNReal.toReal_mul, measure_ne_top _ _, measure_ne_top _ _] using hreal_eq

/-- Helper for Remark 17.31: after fixing the time-`1` state to `z + 1`, the probability of
eventually hitting `0` factors by the hit probability from the restarted chain at `z + 1`. -/
private theorem figure17_2_measure_inter_prefix_futureHitZero_eq_mul
    (r : Set.Icc (0 : ENNReal) 1)
    [IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X]
    {z start : ℕ} {A : Set Ω}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X 1] A)
    (hA_sub : A ⊆ {ω | X 1 ω = z + 1}) :
    (P start : Measure Ω).real (A ∩ {ω | ∃ m : ℕ, 0 < m ∧ X (1 + m) ω = 0}) =
      (F[P, X]) (z + 1) 0 * (P start : Measure Ω).real A := by
  let μstart : Measure Ω := P start
  have htail_meas : MeasurableSet (tailNoHitLocal X 0 1) :=
    figure17_2_measurableSet_tailNoHitLocal (r := r) (P := P) (X := X) 0 1
  have htail_factor :
      μstart.real (A ∩ tailNoHitLocal X 0 1) =
        (P (z + 1) : Measure Ω).real (tailNoHitLocal X 0 0) * μstart.real A := by
    have htail_eq :
        μstart (A ∩ tailNoHitLocal X 0 1) =
          (P (z + 1) : Measure Ω) (tailNoHitLocal X 0 0) * μstart A :=
      figure17_2_measure_inter_prefix_tailNoHitZero_eq_mulLocal
        (r := r) (P := P) (X := X) (z := z) (start := start) (A := A) hA_meas hA_sub
    simpa [Measure.real_def, ENNReal.toReal_mul, measure_ne_top _ _, measure_ne_top _ _] using
      congrArg ENNReal.toReal htail_eq
  have hsplit :
      μstart.real (A ∩ tailNoHitLocal X 0 1) +
        μstart.real (A ∩ {ω | ∃ m : ℕ, 0 < m ∧ X (1 + m) ω = 0}) =
          μstart.real A := by
    have hbase :=
      MeasureTheory.measureReal_inter_add_diff₀ (μ := μstart) (s := A) htail_meas.nullMeasurableSet
    simpa [Set.diff_eq, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
      figure17_2_tailNoHitLocal_compl_eq_futureHit (X := X) 0 1] using hbase
  have htail_zero :
      (P (z + 1) : Measure Ω).real (tailNoHitLocal X 0 0) = 1 - (F[P, X]) (z + 1) 0 := by
    have htail_meas_zero : MeasurableSet (tailNoHitLocal X 0 0) :=
      figure17_2_measurableSet_tailNoHitLocal (r := r) (P := P) (X := X) 0 0
    calc
      (P (z + 1) : Measure Ω).real (tailNoHitLocal X 0 0) =
          (P (z + 1) : Measure Ω).real ((tailNoHitLocal X 0 0)ᶜ)ᶜ := by simp
      _ = 1 - (P (z + 1) : Measure Ω).real ((tailNoHitLocal X 0 0)ᶜ) := by
            simpa using
              (MeasureTheory.probReal_compl_eq_one_sub (μ := (P (z + 1) : Measure Ω))
                (s := (tailNoHitLocal X 0 0)ᶜ) htail_meas_zero.compl)
      _ = 1 - (F[P, X]) (z + 1) 0 := by
            rw [figure17_2_tailNoHitLocal_compl_eq_futureHit (X := X) 0 0]
            simp [everHitsProbability_def, Nat.zero_add]
  -- Proof comment: split the time-`1` slice into the tail-no-hit part and its complementary
  -- future-hit part, then solve the resulting scalar identity.
  rw [htail_factor, htail_zero] at hsplit
  nlinarith

/-- Helper for Remark 17.31: finite no-hit horizons in Fig. 17.2 split according to the
strictly positive state visited at time `1`. -/
private theorem figure17_2_noHitHorizon_step_decomposition
    (start M : ℕ) :
    (P start : Measure Ω) (noHitHorizonLocal X 0 0 (M + 1)) =
      ∑' z : ℕ,
        (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
          (figure17_2TransitionMatrix r start (z + 1)) := by
  let A : ℕ → Set Ω := fun z ↦ {ω | X 1 ω = z + 1}
  have hsplit :
      noHitHorizonLocal X 0 0 (M + 1) =
        ⋃ z : ℕ, A z ∩ noHitHorizonLocal X 0 1 M := by
    ext ω
    constructor
    · intro hω
      have hstep_ne_zero : X 1 ω ≠ 0 := by
        exact hω 1 (by simp) (by omega)
      rcases Nat.exists_eq_succ_of_ne_zero hstep_ne_zero with ⟨z, hz⟩
      refine Set.mem_iUnion.2 ⟨z, ?_⟩
      refine ⟨by simpa [A, hz], ?_⟩
      intro m hm hmM
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hω (m + 1) (by omega) (by omega)
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨z, hωz⟩
      rcases hωz with ⟨hz, htail⟩
      intro m hm hmM
      cases m with
      | zero =>
          omega
      | succ m =>
          cases m with
          | zero =>
              have hstep_ne_zero : X 1 ω ≠ 0 := by
                rw [hz]
                omega
              simpa using hstep_ne_zero
          | succ k =>
              have htail' : X (1 + (k + 1)) ω ≠ 0 := htail (k + 1) (by simp) (by omega)
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.succ_eq_add_one] using
                htail'
  have hpairwise :
      Pairwise (fun z w : ℕ ↦ Disjoint (A z ∩ noHitHorizonLocal X 0 1 M)
        (A w ∩ noHitHorizonLocal X 0 1 M)) := by
    intro z w hzw
    refine Set.disjoint_left.2 ?_
    intro ω hωz hωw
    have : z + 1 = w + 1 := hωz.1.symm.trans hωw.1
    exact hzw (Nat.succ.inj this)
  have hmeas :
      ∀ z : ℕ, MeasurableSet (A z ∩ noHitHorizonLocal X 0 1 M) := by
    intro z
    exact ((inferInstance : IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X).measurable_process 1
        (measurableSet_singleton (z + 1))).inter
      (figure17_2_measurableSet_noHitHorizon (X := X)
        ((inferInstance : IsMarkovProcessRealization
          (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X).measurable_process)
        0 1 M)
  have hslices :
      ∀ z : ℕ,
        (P start : Measure Ω) (A z ∩ noHitHorizonLocal X 0 1 M) =
          (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
            (P start : Measure Ω) (A z) := by
    intro z
    have hA_meas : MeasurableSet[generatedFiltrationSpace X 1] (A z) := by
      simpa [A] using
        figure17_2_measurableSet_mem_of_le_generatedFiltration
          (X := X) (j := 1) (n := 1) le_rfl ({z + 1} : Set ℕ)
    have hA_sub : A z ⊆ {ω | X 1 ω = z + 1} := by
      intro ω hω
      exact hω
    let T : Type := {f : Fin (M + 1) → ℕ // ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ 0}
    have hleft_union :
        A z ∩ noHitHorizonLocal X 0 1 M =
          ⋃ f : T, A z ∩ futurePrefixEventLocal X 1 f.1 := by
      ext ω
      constructor
      · rintro ⟨hωA, hωNoHit⟩
        let f : Fin (M + 1) → ℕ := fun i ↦ X (1 + (i : ℕ)) ω
        have hf : ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ 0 := by
          intro i hi
          simpa [f, Nat.add_assoc] using hωNoHit (i : ℕ) hi (Nat.le_of_lt_succ i.2)
        refine Set.mem_iUnion.2 ⟨⟨f, hf⟩, ?_⟩
        refine ⟨hωA, ?_⟩
        intro i
        rfl
      · intro hω
        rcases Set.mem_iUnion.1 hω with ⟨f, hωf⟩
        refine ⟨hωf.1, ?_⟩
        intro m hm hmM
        let i : Fin (M + 1) := ⟨m, Nat.lt_succ_of_le hmM⟩
        have hpath : X (1 + m) ω = f.1 i := by
          simpa [futurePrefixEventLocal, i] using hωf.2 i
        exact hpath.trans_ne (f.2 i hm)
    have hright_union :
        noHitHorizonLocal X 0 0 M = ⋃ f : T, futurePrefixEventLocal X 0 f.1 := by
      ext ω
      constructor
      · intro hωNoHit
        let f : Fin (M + 1) → ℕ := fun i ↦ X (i : ℕ) ω
        have hf : ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ 0 := by
          intro i hi
          simpa [f, zero_add] using hωNoHit (i : ℕ) hi (Nat.le_of_lt_succ i.2)
        refine Set.mem_iUnion.2 ⟨⟨f, hf⟩, ?_⟩
        intro i
        simp [f, zero_add]
      · intro hω
        rcases Set.mem_iUnion.1 hω with ⟨f, hωf⟩
        intro m hm hmM
        let i : Fin (M + 1) := ⟨m, Nat.lt_succ_of_le hmM⟩
        have hpath : X (0 + m) ω = f.1 i := by
          simpa [futurePrefixEventLocal, i, zero_add] using hωf i
        exact hpath.trans_ne (f.2 i hm)
    have hpairwise_left :
        Pairwise (fun f g : T ↦ Disjoint (A z ∩ futurePrefixEventLocal X 1 f.1)
          (A z ∩ futurePrefixEventLocal X 1 g.1)) := by
      intro f g hfg
      refine Set.disjoint_left.2 ?_
      intro ω hωf hωg
      have hEq : f.1 = g.1 := by
        funext i
        exact (hωf.2 i).symm.trans (hωg.2 i)
      exact hfg (Subtype.ext hEq)
    have hpairwise_right :
        Pairwise (fun f g : T ↦ Disjoint (futurePrefixEventLocal X 0 f.1)
          (futurePrefixEventLocal X 0 g.1)) := by
      intro f g hfg
      refine Set.disjoint_left.2 ?_
      intro ω hωf hωg
      have hEq : f.1 = g.1 := by
        funext i
        exact (hωf i).symm.trans (hωg i)
      exact hfg (Subtype.ext hEq)
    have hleft_sum :
        (P start : Measure Ω) (A z ∩ noHitHorizonLocal X 0 1 M) =
          ∑' f : T, (P start : Measure Ω) (A z ∩ futurePrefixEventLocal X 1 f.1) := by
      rw [hleft_union, measure_iUnion hpairwise_left]
      intro f
      exact (((inferInstance : IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X).measurable_process 1
          (measurableSet_singleton (z + 1)))).inter
        (figure17_2_measurableSet_futurePrefixEvent
          (X := X)
          ((inferInstance : IsMarkovProcessRealization
            (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X).measurable_process)
          (n := 1) f.1)
    have hright_sum :
        (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) =
          ∑' f : T, (P (z + 1) : Measure Ω) (futurePrefixEventLocal X 0 f.1) := by
      rw [hright_union, measure_iUnion hpairwise_right]
      intro f
      exact figure17_2_measurableSet_futurePrefixEvent
        (X := X)
        ((inferInstance : IsMarkovProcessRealization
          (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X).measurable_process)
        (n := 0) f.1
    -- Proof comment: partition the positive tail into exact finite paths, apply the exact-prefix
    -- Markov factorization on each slice, and then sum the resulting equalities.
    calc
      (P start : Measure Ω) (A z ∩ noHitHorizonLocal X 0 1 M) =
          ∑' f : T, (P start : Measure Ω) (A z ∩ futurePrefixEventLocal X 1 f.1) := hleft_sum
      _ =
          ∑' f : T, (P (z + 1) : Measure Ω) (futurePrefixEventLocal X 0 f.1) *
            (P start : Measure Ω) (A z) := by
              refine tsum_congr fun f ↦ ?_
              exact figure17_2_measure_inter_prefix_futurePrefixEvent_eq_mulLocal
                (r := r) (P := P) (X := X)
                (inferInstance : IsMarkovProcessRealization
                  (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X)
                hA_meas hA_sub f.1
      _ =
          (∑' f : T, (P (z + 1) : Measure Ω) (futurePrefixEventLocal X 0 f.1)) *
            (P start : Measure Ω) (A z) := by
              rw [ENNReal.tsum_mul_right]
      _ = (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (P start : Measure Ω) (A z) := by
            rw [← hright_sum]
  calc
    (P start : Measure Ω) (noHitHorizonLocal X 0 0 (M + 1)) =
        (P start : Measure Ω) (⋃ z : ℕ, A z ∩ noHitHorizonLocal X 0 1 M) := by
          rw [hsplit]
    _ = ∑' z : ℕ, (P start : Measure Ω) (A z ∩ noHitHorizonLocal X 0 1 M) := by
          rw [measure_iUnion hpairwise]
          exact hmeas
    _ = ∑' z : ℕ,
          (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
            (P start : Measure Ω) (A z) := by
              refine tsum_congr fun z ↦ hslices z
    _ = ∑' z : ℕ,
          (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
            (figure17_2TransitionMatrix r start (z + 1)) := by
              refine tsum_congr fun z ↦ ?_
              rw [figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) start (z + 1)]

/-- Helper for Remark 17.31: starting from `0`, the finite no-hit horizons are exactly the
shifted finite no-hit horizons from `1`. -/
private theorem figure17_2_noHitHorizon_zero_eq_from_one
    (r : Set.Icc (0 : ENNReal) 1)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) P X]
    (M : ℕ) :
    (P 0 : Measure Ω) (noHitHorizonLocal X 0 0 (M + 1)) =
      (P 1 : Measure Ω) (noHitHorizonLocal X 0 0 M) := by
  calc
    (P 0 : Measure Ω) (noHitHorizonLocal X 0 0 (M + 1)) =
        ∑' z : ℕ,
          (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
            figure17_2TransitionMatrix r 0 (z + 1) := by
              exact figure17_2_noHitHorizon_step_decomposition (r := r) (P := P) (X := X) 0 M
    _ = (P 1 : Measure Ω) (noHitHorizonLocal X 0 0 M) * 1 := by
          rw [ENNReal.tsum_eq_add_tsum_ite 0]
          have htail :
              (∑' x : ℕ,
                if x = 0 then 0
                else
                  (P (x + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                    figure17_2TransitionMatrix r 0 (x + 1)) = 0 := by
            refine ENNReal.tsum_eq_zero.2 ?_
            intro x
            by_cases hx : x = 0
            · simp [hx]
            · simp [hx, figure17_2TransitionMatrix]
          have hcollapse :=
            congrArg
              (fun t : ENNReal ↦
                (P 1 : Measure Ω) (noHitHorizonLocal X 0 0 M) * 1 + t)
              htail
          simpa [figure17_2TransitionMatrix] using hcollapse
    _ = (P 1 : Measure Ω) (noHitHorizonLocal X 0 0 M) := by simp

/-- Helper for Remark 17.31: from state `1`, a finite no-hit horizon advances only through the
right jump to `2`. -/
private theorem figure17_2_noHitHorizon_step_one
    (M : ℕ) :
    (P 1 : Measure Ω) (noHitHorizonLocal X 0 0 (M + 1)) =
      (P 2 : Measure Ω) (noHitHorizonLocal X 0 0 M) * (r : ENNReal) := by
  calc
    (P 1 : Measure Ω) (noHitHorizonLocal X 0 0 (M + 1)) =
        ∑' z : ℕ,
          (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
            figure17_2TransitionMatrix r 1 (z + 1) := by
              exact figure17_2_noHitHorizon_step_decomposition (r := r) (P := P) (X := X) 1 M
    _ = (P 2 : Measure Ω) (noHitHorizonLocal X 0 0 M) * (r : ENNReal) := by
          rw [ENNReal.tsum_eq_add_tsum_ite 1]
          have htail :
              (∑' x : ℕ,
                if x = 1 then 0
                else
                  (P (x + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                    figure17_2TransitionMatrix r 1 (x + 1)) = 0 := by
            refine ENNReal.tsum_eq_zero.2 ?_
            intro x
            by_cases hx : x = 1
            · simp [hx]
            · simp [hx, figure17_2TransitionMatrix]
          have hcollapse :=
            congrArg
              (fun t : ENNReal ↦
                (P 2 : Measure Ω) (noHitHorizonLocal X 0 0 M) * (r : ENNReal) + t)
              htail
          simpa [figure17_2TransitionMatrix] using hcollapse

/-- Helper for Remark 17.31: from state `n + 2`, a finite no-hit horizon decomposes into the
left move to `n + 1` and the right move to `n + 3`. -/
private theorem figure17_2_noHitHorizon_step_succ
    (n M : ℕ) :
    (P (n + 2) : Measure Ω) (noHitHorizonLocal X 0 0 (M + 1)) =
      (P (n + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (1 - (r : ENNReal)) +
        (P (n + 3) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (r : ENNReal) := by
  calc
    (P (n + 2) : Measure Ω) (noHitHorizonLocal X 0 0 (M + 1)) =
        ∑' z : ℕ,
          (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
            figure17_2TransitionMatrix r (n + 2) (z + 1) := by
              exact
                figure17_2_noHitHorizon_step_decomposition
                  (r := r) (P := P) (X := X) (n + 2) M
    _ = (P (n + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (1 - (r : ENNReal)) +
          ((P (n + 3) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (r : ENNReal) +
            ∑' z : ℕ,
              if z = n then 0
              else if z = n + 2 then 0
              else
                (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                  figure17_2TransitionMatrix r (n + 2) (z + 1)) := by
            rw [ENNReal.tsum_eq_add_tsum_ite n]
            have htail :
                (∑' x : ℕ,
                  if x = n then 0
                  else
                    (P (x + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                      figure17_2TransitionMatrix r (n + 2) (x + 1)) =
                  (P (n + 3) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (r : ENNReal) +
                    ∑' z : ℕ,
                      if z = n then 0
                      else if z = n + 2 then 0
                      else
                        (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                          figure17_2TransitionMatrix r (n + 2) (z + 1) := by
              rw [ENNReal.tsum_eq_add_tsum_ite (n + 2)]
              have htail' :
                  (∑' z : ℕ,
                    if z = n + 2 then 0
                    else
                      (if z = n then 0
                      else
                        (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                          figure17_2TransitionMatrix r (n + 2) (z + 1))) =
                    ∑' z : ℕ,
                      if z = n then 0
                      else if z = n + 2 then 0
                      else
                        (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                          figure17_2TransitionMatrix r (n + 2) (z + 1) := by
                refine tsum_congr fun z ↦ ?_
                by_cases hz1 : z = n
                · simp [hz1]
                · by_cases hz2 : z = n + 2
                  · simp [hz1, hz2]
                  · simp [hz1, hz2]
              have hcollapse :=
                congrArg
                  (fun t : ENNReal ↦
                    (P (n + 3) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (r : ENNReal) + t)
                  htail'
              simpa [figure17_2TransitionMatrix] using hcollapse
            have hcollapse :=
              congrArg
                (fun t : ENNReal ↦
                  (P (n + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                    (1 - (r : ENNReal)) + t)
                htail
            simpa [figure17_2TransitionMatrix, add_assoc] using hcollapse
    _ = (P (n + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (1 - (r : ENNReal)) +
          (P (n + 3) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (r : ENNReal) := by
            have htail :
                (∑' z : ℕ,
                  if z = n then 0
                  else if z = n + 2 then 0
                  else
                    (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                      figure17_2TransitionMatrix r (n + 2) (z + 1)) = 0 := by
              refine ENNReal.tsum_eq_zero.2 ?_
              intro z
              by_cases hz1 : z = n
              · simp [hz1]
              · by_cases hz2 : z = n + 2
                · simp [hz1, hz2]
                · simp [hz1, hz2, figure17_2TransitionMatrix]
            have hcollapse :=
              congrArg
                (fun t : ENNReal ↦
                  (P (n + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (1 - (r : ENNReal)) +
                    ((P (n + 3) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                      (r : ENNReal) + t))
                htail
            simpa [add_assoc] using hcollapse

/-- Helper for Remark 17.31: the positive-time return probability at `0` is the hit probability
of `0` when the chain is started from `1`. -/
private theorem figure17_2_returnProbability_zero_eq_hitProbability_one_zero
    [hReal : IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X] :
    (F[P, X]) 0 0 = (F[P, X]) 1 0 := by
  let μ0 : Measure Ω := P 0
  let μ1 : Measure Ω := P 1
  let hitWithin : ℕ → Set Ω := fun M ↦ {ω | ∃ n ∈ Set.Icc 1 M, X n ω = 0}
  let hitEvent : Set Ω := {ω | ∃ n : ℕ, 0 < n ∧ X n ω = 0}
  have hhitWithin_eq_compl :
      ∀ M : ℕ, hitWithin M = (noHitHorizonLocal X 0 0 M)ᶜ := by
    intro M
    ext ω
    constructor
    · intro hω hnohit
      rcases hω with ⟨n, hn, hnx⟩
      exact (hnohit n hn.1 hn.2 (by simpa [zero_add] using hnx)).elim
    · intro hω
      by_contra hhit
      exact hω <| by
        intro n hn1 hnM hnEq
        exact hhit ⟨n, ⟨hn1, hnM⟩, by simpa [zero_add] using hnEq⟩
  have hfinite_eq :
      ∀ M : ℕ, μ0.real (hitWithin (M + 1)) = μ1.real (hitWithin M) := by
    intro M
    have hμ0 :
        μ0.real (hitWithin (M + 1)) = 1 - μ0.real (noHitHorizonLocal X 0 0 (M + 1)) := by
      rw [hhitWithin_eq_compl (M + 1), probReal_compl_eq_one_sub (μ := μ0)]
      exact figure17_2_measurableSet_noHitHorizon (X := X) hReal.measurable_process 0 0 (M + 1)
    have hμ1 :
        μ1.real (hitWithin M) = 1 - μ1.real (noHitHorizonLocal X 0 0 M) := by
      rw [hhitWithin_eq_compl M, probReal_compl_eq_one_sub (μ := μ1)]
      exact figure17_2_measurableSet_noHitHorizon (X := X) hReal.measurable_process 0 0 M
    -- Proof comment: the deterministic first step `0 → 1` identifies the bounded hit event from
    -- `0` within `M + 1` steps with the bounded hit event from `1` within `M` steps.
    rw [hμ0, hμ1]
    congr 1
    simpa [Measure.real_def] using
      congrArg ENNReal.toReal
        (figure17_2_noHitHorizon_zero_eq_from_one (r := r) (P := P) (X := X) M)
  have hhitEvent_union :
      hitEvent = ⋃ M : ℕ, hitWithin (M + 1) := by
    ext ω
    constructor
    · rintro ⟨n, hn, hnx⟩
      exact Set.mem_iUnion.2 ⟨n, ⟨n, ⟨by simpa using hn, Nat.le_succ n⟩, hnx⟩⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨M, hM⟩
      rcases hM with ⟨n, hn, hnx⟩
      exact ⟨n, hn.1, hnx⟩
  have hhitWithin_union :
      hitEvent = ⋃ M : ℕ, hitWithin M := by
    ext ω
    constructor
    · rintro ⟨n, hn, hnx⟩
      exact Set.mem_iUnion.2 ⟨n, ⟨n, ⟨hn, le_rfl⟩, hnx⟩⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨M, hM⟩
      rcases hM with ⟨n, hn, hnx⟩
      exact ⟨n, hn.1, hnx⟩
  have hmono0 : Directed (· ⊆ ·) fun M : ℕ ↦ hitWithin (M + 1) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · intro ω hω
      rcases hω with ⟨n, hn, hnx⟩
      exact ⟨n, ⟨hn.1, le_trans hn.2 (Nat.succ_le_succ (le_max_left i j))⟩, hnx⟩
    · intro ω hω
      rcases hω with ⟨n, hn, hnx⟩
      exact ⟨n, ⟨hn.1, le_trans hn.2 (Nat.succ_le_succ (le_max_right i j))⟩, hnx⟩
  have hmono1 : Directed (· ⊆ ·) hitWithin := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · intro ω hω
      rcases hω with ⟨n, hn, hnx⟩
      exact ⟨n, ⟨hn.1, le_trans hn.2 (le_max_left i j)⟩, hnx⟩
    · intro ω hω
      rcases hω with ⟨n, hn, hnx⟩
      exact ⟨n, ⟨hn.1, le_trans hn.2 (le_max_right i j)⟩, hnx⟩
  have hμ0_union :
      μ0 (⋃ M : ℕ, hitWithin (M + 1)) = ⨆ M : ℕ, μ0 (hitWithin (M + 1)) := hmono0.measure_iUnion
  have hμ1_union :
      μ1 (⋃ M : ℕ, hitWithin M) = ⨆ M : ℕ, μ1 (hitWithin M) := hmono1.measure_iUnion
  have hsups_eq :
      ⨆ M : ℕ, μ0 (hitWithin (M + 1)) = ⨆ M : ℕ, μ1 (hitWithin M) := by
    apply le_antisymm
    · refine iSup_le fun M ↦ ?_
      have hEq : μ0 (hitWithin (M + 1)) = μ1 (hitWithin M) := by
        exact
          (ENNReal.toReal_eq_toReal_iff'
            (measure_ne_top μ0 (hitWithin (M + 1)))
            (measure_ne_top μ1 (hitWithin M))).mp (by
              simpa [Measure.real_def] using hfinite_eq M)
      rw [hEq]
      exact le_iSup (fun N : ℕ ↦ μ1 (hitWithin N)) M
    · refine iSup_le fun M ↦ ?_
      have hEq : μ0 (hitWithin (M + 1)) = μ1 (hitWithin M) := by
        exact
          (ENNReal.toReal_eq_toReal_iff'
            (measure_ne_top μ0 (hitWithin (M + 1)))
            (measure_ne_top μ1 (hitWithin M))).mp (by
              simpa [Measure.real_def] using hfinite_eq M)
      rw [← hEq]
      exact le_iSup (fun N : ℕ ↦ μ0 (hitWithin (N + 1))) M
  -- Proof comment: both eventual positive-time hit events are directed unions of bounded
  -- horizons, so the finite-horizon equality passes to the full ever-hit probabilities.
  calc
    (F[P, X]) 0 0 = μ0.real hitEvent := by
      simpa [hitEvent] using (show (F[P, X]) 0 0 =
        (P 0 : Measure Ω).real {ω | ∃ n : ℕ, 0 < n ∧ X n ω = 0} by
          rw [everHitsProbability_def])
    _ = μ0.real (⋃ M : ℕ, hitWithin (M + 1)) := by
          rw [hhitEvent_union]
    _ = (⨆ M : ℕ, μ0 (hitWithin (M + 1))).toReal := by
          rw [Measure.real_def, hμ0_union]
    _ = (⨆ M : ℕ, μ1 (hitWithin M)).toReal := by
          rw [hsups_eq]
    _ = μ1.real (⋃ M : ℕ, hitWithin M) := by
          rw [Measure.real_def, hμ1_union]
    _ = μ1.real hitEvent := by
          rw [hhitWithin_union]
    _ = (F[P, X]) 1 0 := by
      simpa [hitEvent] using (show (P 1 : Measure Ω).real {ω | ∃ n : ℕ, 0 < n ∧ X n ω = 0} =
        (F[P, X]) 1 0 by
          rw [everHitsProbability_def])

/-- Helper for Remark 17.31: the eventual hit probability of `0` from state `1` splits over the
two possible first-step outcomes. -/
private theorem figure17_2_hitProbability_zero_step_one
    (r : Set.Icc (0 : ENNReal) 1)
    [IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X] :
    (F[P, X]) 1 0 = (1 - (r : ENNReal)).toReal + (r : ENNReal).toReal * (F[P, X]) 2 0 := by
  let μ1 : Measure Ω := P 1
  let hitEvent : Set Ω := {ω | ∃ m : ℕ, 0 < m ∧ X m ω = 0}
  let futureHit : Set Ω := {ω | ∃ m : ℕ, 0 < m ∧ X (1 + m) ω = 0}
  let B0 : Set Ω := {ω | X 1 ω = 0}
  let B2 : Set Ω := {ω | X 1 ω = 2}
  let Bad : Set Ω := {ω | X 1 ω ≠ 0 ∧ X 1 ω ≠ 2}
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
  have hB0_meas : MeasurableSet B0 := by
    change MeasurableSet (X 1 ⁻¹' ({0} : Set ℕ))
    exact hReal.measurable_process 1 (measurableSet_singleton 0)
  have hB2_meas : MeasurableSet B2 := by
    change MeasurableSet (X 1 ⁻¹' ({2} : Set ℕ))
    exact hReal.measurable_process 1 (measurableSet_singleton 2)
  have hB0_mass :
      μ1.real B0 = (1 - (r : ENNReal)).toReal := by
    simpa [μ1, B0, Measure.real_def] using
      congrArg ENNReal.toReal (figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) 1 0)
  have hB2_mass :
      μ1.real B2 = (r : ENNReal).toReal := by
    simpa [μ1, B2, Measure.real_def, figure17_2TransitionMatrix] using
      congrArg ENNReal.toReal (figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) 1 2)
  have hgood_prob : μ1 (B0 ∪ B2) = 1 := by
    calc
      μ1 (B0 ∪ B2) = μ1 B0 + μ1 B2 := by
        rw [measure_union]
        · refine Set.disjoint_left.2 ?_
          intro ω hω0 hω2
          have : (0 : ℕ) = 2 := hω0.symm.trans hω2
          omega
        · exact hB2_meas
      _ = (1 - (r : ENNReal)) + (r : ENNReal) := by
            rw [figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) 1 0,
              figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) 1 2]
            simp [figure17_2TransitionMatrix]
      _ = 1 := by
            exact tsub_add_cancel_of_le r.2.2
  have hBad_zero : μ1 Bad = 0 := by
    have hEq : Bad = (B0 ∪ B2)ᶜ := by
      ext ω
      simp [Bad, B0, B2]
    rw [hEq]
    exact (prob_compl_eq_zero_iff (hB0_meas.union hB2_meas)).2 hgood_prob
  have hfuture_meas : MeasurableSet futureHit := by
    change MeasurableSet {ω | ∃ m : ℕ, 0 < m ∧ X (1 + m) ω = 0}
    rw [← figure17_2_tailNoHitLocal_compl_eq_futureHit (X := X) 0 1]
    simpa using
      (figure17_2_measurableSet_tailNoHitLocal (r := r) (P := P) (X := X) 0 1).compl
  have hhitEvent_meas : MeasurableSet hitEvent := by
    simpa [hitEvent] using
      figure17_2_measurableSet_exists_positiveEq (r := r) (P := P) (X := X) 0
  have hBad_meas : MeasurableSet Bad := by
    have hEq : Bad = (B0 ∪ B2)ᶜ := by
      ext ω
      simp [Bad, B0, B2]
    rw [hEq]
    exact (hB0_meas.union hB2_meas).compl
  have hBad_hit_zero : μ1 (Bad ∩ hitEvent) = 0 := by
    refine measure_mono_null ?_ hBad_zero
    intro ω hω
    exact hω.1
  have hdecomp :
      hitEvent = (B0 ∪ (B2 ∩ futureHit)) ∪ (Bad ∩ hitEvent) := by
    ext ω
    constructor
    · rintro hω
      by_cases h0 : X 1 ω = 0
      · exact Or.inl (Or.inl h0)
      · by_cases h2 : X 1 ω = 2
        · refine Or.inl (Or.inr ⟨h2, ?_⟩)
          rcases hω with ⟨m, hm, hmEq⟩
          rcases Nat.exists_eq_succ_of_ne_zero hm.ne' with ⟨k, rfl⟩
          cases k with
          | zero =>
              exact False.elim (h0 (by simpa using hmEq))
          | succ l =>
              exact ⟨l + 1, by simpa using Nat.succ_pos l,
                by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmEq⟩
        · exact Or.inr ⟨⟨h0, h2⟩, hω⟩
    · intro hω
      rcases hω with hω | hω
      · rcases hω with hω | hω
        · exact ⟨1, Nat.succ_pos _, hω⟩
        · rcases hω with ⟨hω2, hfuture⟩
          rcases hfuture with ⟨m, hm, hmEq⟩
          exact ⟨1 + m, by simpa [Nat.add_comm] using Nat.succ_pos m,
            by simpa [Nat.add_assoc] using hmEq⟩
      · exact hω.2
  have hB0_disj_B2future : Disjoint B0 (B2 ∩ futureHit) := by
    refine Set.disjoint_left.2 ?_
    intro ω hω0 hω2
    have : (0 : ℕ) = 2 := hω0.symm.trans hω2.1
    omega
  have hmain_disj_bad : Disjoint (B0 ∪ (B2 ∩ futureHit)) (Bad ∩ hitEvent) := by
    refine Set.disjoint_left.2 ?_
    intro ω hωmain hωbad
    rcases hωmain with hω0 | hω2
    · exact hωbad.1.1 hω0
    · exact hωbad.1.2 hω2.1
  have hfuture_factor :
      μ1.real (B2 ∩ futureHit) = (F[P, X]) 2 0 * μ1.real B2 := by
    have hB2_meas_generated :
        MeasurableSet[generatedFiltrationSpace X 1] B2 := by
      simpa [B2] using
        figure17_2_measurableSet_mem_of_le_generatedFiltration
          (X := X) (j := 1) (n := 1) le_rfl ({2} : Set ℕ)
    have hB2_sub : B2 ⊆ {ω | X 1 ω = 1 + 1} := by
      intro ω hω
      simpa using hω
    simpa [μ1, B2, futureHit, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      figure17_2_measure_inter_prefix_futureHitZero_eq_mul
        (r := r) (P := P) (X := X) (z := 1) (start := 1) (A := B2) hB2_meas_generated hB2_sub
  have hμ_eq :
      μ1 hitEvent = μ1 B0 + μ1 (B2 ∩ futureHit) := by
    calc
      μ1 hitEvent = μ1 ((B0 ∪ (B2 ∩ futureHit)) ∪ (Bad ∩ hitEvent)) := by
        simpa using congrArg μ1 hdecomp
      _ = μ1 (B0 ∪ (B2 ∩ futureHit)) + μ1 (Bad ∩ hitEvent) := by
            rw [measure_union hmain_disj_bad]
            exact hBad_meas.inter hhitEvent_meas
      _ = μ1 (B0 ∪ (B2 ∩ futureHit)) := by rw [hBad_hit_zero, add_zero]
      _ = μ1 B0 + μ1 (B2 ∩ futureHit) := by
            rw [measure_union hB0_disj_B2future]
            exact hB2_meas.inter hfuture_meas
  have hμ_real :
      μ1.real hitEvent = μ1.real B0 + μ1.real (B2 ∩ futureHit) := by
    simpa [Measure.real_def, ENNReal.toReal_add, measure_ne_top _ _, measure_ne_top _ _] using
      congrArg ENNReal.toReal hμ_eq
  -- Proof comment: decompose the hit event by the first step, discard the null bad branch, and
  -- factor the surviving `1 → 2` branch through the restarted hit probability from `2`.
  calc
    (F[P, X]) 1 0 = μ1.real hitEvent := by
      simpa [μ1, hitEvent] using (show (F[P, X]) 1 0 =
        (P 1 : Measure Ω).real {ω | ∃ m : ℕ, 0 < m ∧ X m ω = 0} by
          rw [everHitsProbability_def])
    _ = μ1.real B0 + μ1.real (B2 ∩ futureHit) := hμ_real
    _ = (1 - (r : ENNReal)).toReal + (r : ENNReal).toReal * (F[P, X]) 2 0 := by
          rw [hB0_mass, hfuture_factor, hB2_mass, mul_comm]

/-- Helper for Remark 17.31: from state `n + 2`, the eventual hit probability of `0` splits over
the left and right nearest-neighbor moves. -/
private theorem figure17_2_hitProbability_zero_step_succ
    (r : Set.Icc (0 : ENNReal) 1)
    [IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X]
    (n : ℕ) :
    (F[P, X]) (n + 2) 0 =
      (1 - (r : ENNReal)).toReal * (F[P, X]) (n + 1) 0 +
        (r : ENNReal).toReal * (F[P, X]) (n + 3) 0 := by
  let μ : Measure Ω := P (n + 2)
  let hitEvent : Set Ω := {ω | ∃ m : ℕ, 0 < m ∧ X m ω = 0}
  let futureHit : Set Ω := {ω | ∃ m : ℕ, 0 < m ∧ X (1 + m) ω = 0}
  let Bleft : Set Ω := {ω | X 1 ω = n + 1}
  let Bright : Set Ω := {ω | X 1 ω = n + 3}
  let Bad : Set Ω := {ω | X 1 ω ≠ n + 1 ∧ X 1 ω ≠ n + 3}
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
  have hBleft_meas : MeasurableSet Bleft := by
    change MeasurableSet (X 1 ⁻¹' ({n + 1} : Set ℕ))
    exact hReal.measurable_process 1 (measurableSet_singleton (n + 1))
  have hBright_meas : MeasurableSet Bright := by
    change MeasurableSet (X 1 ⁻¹' ({n + 3} : Set ℕ))
    exact hReal.measurable_process 1 (measurableSet_singleton (n + 3))
  have hgood_prob : μ (Bleft ∪ Bright) = 1 := by
    calc
      μ (Bleft ∪ Bright) = μ Bleft + μ Bright := by
        rw [measure_union]
        · refine Set.disjoint_left.2 ?_
          intro ω hωl hωr
          have : n + 1 = n + 3 := hωl.symm.trans hωr
          omega
        · exact hBright_meas
      _ = figure17_2TransitionMatrix r (n + 2) (n + 1) +
            figure17_2TransitionMatrix r (n + 2) (n + 3) := by
            rw [figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) (n + 2) (n + 1),
              figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) (n + 2) (n + 3)]
      _ = 1 := by
            simpa [figure17_2TransitionMatrix, add_comm] using
              (tsub_add_cancel_of_le r.2.2 : (1 - (r : ENNReal)) + (r : ENNReal) = 1)
  have hBad_zero : μ Bad = 0 := by
    have hEq : Bad = (Bleft ∪ Bright)ᶜ := by
      ext ω
      simp [Bad, Bleft, Bright]
    rw [hEq]
    exact (prob_compl_eq_zero_iff (hBleft_meas.union hBright_meas)).2 hgood_prob
  have hfuture_meas : MeasurableSet futureHit := by
    change MeasurableSet {ω | ∃ m : ℕ, 0 < m ∧ X (1 + m) ω = 0}
    rw [← figure17_2_tailNoHitLocal_compl_eq_futureHit (X := X) 0 1]
    simpa using
      (figure17_2_measurableSet_tailNoHitLocal (r := r) (P := P) (X := X) 0 1).compl
  have hhitEvent_meas : MeasurableSet hitEvent := by
    simpa [hitEvent] using
      figure17_2_measurableSet_exists_positiveEq (r := r) (P := P) (X := X) 0
  have hBad_meas : MeasurableSet Bad := by
    have hEq : Bad = (Bleft ∪ Bright)ᶜ := by
      ext ω
      simp [Bad, Bleft, Bright]
    rw [hEq]
    exact (hBleft_meas.union hBright_meas).compl
  have hBad_hit_zero : μ (Bad ∩ hitEvent) = 0 := by
    refine measure_mono_null ?_ hBad_zero
    intro ω hω
    exact hω.1
  have hdecomp :
      hitEvent = ((Bleft ∩ futureHit) ∪ (Bright ∩ futureHit)) ∪ (Bad ∩ hitEvent) := by
    ext ω
    constructor
    · rintro hω
      by_cases hl : X 1 ω = n + 1
      · refine Or.inl (Or.inl ⟨hl, ?_⟩)
        rcases hω with ⟨m, hm, hmEq⟩
        rcases Nat.exists_eq_succ_of_ne_zero hm.ne' with ⟨k, rfl⟩
        cases k with
        | zero =>
            have hzero : X 1 ω = 0 := by simpa using hmEq
            have : n + 1 = 0 := hl.symm.trans hzero
            omega
        | succ l =>
            exact ⟨l + 1, by simpa using Nat.succ_pos l,
              by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmEq⟩
      · by_cases hr : X 1 ω = n + 3
        · refine Or.inl (Or.inr ⟨hr, ?_⟩)
          rcases hω with ⟨m, hm, hmEq⟩
          rcases Nat.exists_eq_succ_of_ne_zero hm.ne' with ⟨k, rfl⟩
          cases k with
        | zero =>
            have hzero : X 1 ω = 0 := by simpa using hmEq
            have : n + 3 = 0 := hr.symm.trans hzero
            omega
        | succ l =>
              exact ⟨l + 1, by simpa using Nat.succ_pos l,
                by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmEq⟩
        · exact Or.inr ⟨⟨hl, hr⟩, hω⟩
    · intro hω
      rcases hω with hω | hω
      · rcases hω with hω | hω
        · rcases hω with ⟨_, hfuture⟩
          rcases hfuture with ⟨m, hm, hmEq⟩
          exact ⟨1 + m, by simpa [Nat.add_comm] using Nat.succ_pos m,
            by simpa [Nat.add_assoc] using hmEq⟩
        · rcases hω with ⟨_, hfuture⟩
          rcases hfuture with ⟨m, hm, hmEq⟩
          exact ⟨1 + m, by simpa [Nat.add_comm] using Nat.succ_pos m,
            by simpa [Nat.add_assoc] using hmEq⟩
      · exact hω.2
  have hleft_disj_bright : Disjoint (Bleft ∩ futureHit) (Bright ∩ futureHit) := by
    refine Set.disjoint_left.2 ?_
    intro ω hωl hωr
    have hEq : n + 1 = n + 3 := hωl.1.symm.trans hωr.1
    omega
  have hmain_disj_bad :
      Disjoint ((Bleft ∩ futureHit) ∪ (Bright ∩ futureHit)) (Bad ∩ hitEvent) := by
    refine Set.disjoint_left.2 ?_
    intro ω hωmain hωbad
    rcases hωmain with hωl | hωr
    · exact hωbad.1.1 hωl.1
    · exact hωbad.1.2 hωr.1
  have hleft_factor :
      μ.real (Bleft ∩ futureHit) = (F[P, X]) (n + 1) 0 * μ.real Bleft := by
    have hBleft_meas_generated :
        MeasurableSet[generatedFiltrationSpace X 1] Bleft := by
      simpa [Bleft] using
        figure17_2_measurableSet_mem_of_le_generatedFiltration
          (X := X) (j := 1) (n := 1) le_rfl ({n + 1} : Set ℕ)
    have hBleft_sub : Bleft ⊆ {ω | X 1 ω = n + 1} := by
      intro ω hω
      exact hω
    simpa [μ, Bleft, futureHit, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      figure17_2_measure_inter_prefix_futureHitZero_eq_mul
        (r := r) (P := P) (X := X) (z := n) (start := n + 2) (A := Bleft)
        hBleft_meas_generated hBleft_sub
  have hright_factor :
      μ.real (Bright ∩ futureHit) = (F[P, X]) (n + 3) 0 * μ.real Bright := by
    have hBright_meas_generated :
        MeasurableSet[generatedFiltrationSpace X 1] Bright := by
      simpa [Bright] using
        figure17_2_measurableSet_mem_of_le_generatedFiltration
          (X := X) (j := 1) (n := 1) le_rfl ({n + 3} : Set ℕ)
    have hBright_sub : Bright ⊆ {ω | X 1 ω = n + 2 + 1} := by
      intro ω hω
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hω
    simpa [μ, Bright, futureHit, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      figure17_2_measure_inter_prefix_futureHitZero_eq_mul
        (r := r) (P := P) (X := X) (z := n + 2) (start := n + 2) (A := Bright)
        hBright_meas_generated hBright_sub
  have hμ_eq :
      μ hitEvent = μ (Bleft ∩ futureHit) + μ (Bright ∩ futureHit) := by
    calc
      μ hitEvent = μ (((Bleft ∩ futureHit) ∪ (Bright ∩ futureHit)) ∪ (Bad ∩ hitEvent)) := by
        simpa using congrArg μ hdecomp
      _ = μ ((Bleft ∩ futureHit) ∪ (Bright ∩ futureHit)) + μ (Bad ∩ hitEvent) := by
            rw [measure_union hmain_disj_bad]
            exact hBad_meas.inter hhitEvent_meas
      _ = μ ((Bleft ∩ futureHit) ∪ (Bright ∩ futureHit)) := by rw [hBad_hit_zero, add_zero]
      _ = μ (Bleft ∩ futureHit) + μ (Bright ∩ futureHit) := by
            rw [measure_union hleft_disj_bright]
            exact hBright_meas.inter hfuture_meas
  have hμ_real :
      μ.real hitEvent = μ.real (Bleft ∩ futureHit) + μ.real (Bright ∩ futureHit) := by
    simpa [Measure.real_def, ENNReal.toReal_add, measure_ne_top _ _, measure_ne_top _ _] using
      congrArg ENNReal.toReal hμ_eq
  have hBleft_mass :
      μ.real Bleft = (1 - (r : ENNReal)).toReal := by
    simpa [μ, Bleft, Measure.real_def, figure17_2TransitionMatrix] using
      congrArg ENNReal.toReal
        (figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) (n + 2) (n + 1))
  have hBright_mass :
      μ.real Bright = (r : ENNReal).toReal := by
    simpa [μ, Bright, Measure.real_def, figure17_2TransitionMatrix] using
      congrArg ENNReal.toReal
        (figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) (n + 2) (n + 3))
  -- Proof comment: only the left and right nearest-neighbor branches carry positive time-`1`
  -- mass, and each branch restarts the same eventual-hit problem from the reached state.
  calc
    (F[P, X]) (n + 2) 0 = μ.real hitEvent := by
      simpa [μ, hitEvent] using (show (F[P, X]) (n + 2) 0 =
        (P (n + 2) : Measure Ω).real {ω | ∃ m : ℕ, 0 < m ∧ X m ω = 0} by
          rw [everHitsProbability_def])
    _ = μ.real (Bleft ∩ futureHit) + μ.real (Bright ∩ futureHit) := hμ_real
    _ = (F[P, X]) (n + 1) 0 * (1 - (r : ENNReal)).toReal +
          (F[P, X]) (n + 3) 0 * (r : ENNReal).toReal := by
            rw [hleft_factor, hright_factor, hBleft_mass, hBright_mass]
    _ = (1 - (r : ENNReal)).toReal * (F[P, X]) (n + 1) 0 +
          (r : ENNReal).toReal * (F[P, X]) (n + 3) 0 := by
            ring

/-- Helper for Remark 17.31: the geometric singleton-mass profile for the left-drift invariant
measure of Fig. 17.2. -/
private def figure17_2InvariantMass (r : Set.Icc (0 : ENNReal) 1) : ℕ → ℝ≥0∞
  | 0 => 1 - (r : ENNReal)
  | n + 1 => ((r : ENNReal) / (1 - (r : ENNReal))) ^ n

/-- Helper for Remark 17.31: in the left-drift regime, the geometric ratio
`r / (1 - r)` is strictly smaller than `1`. -/
private theorem figure17_2InvariantRatio_lt_one
    (hrhalf : (r : ENNReal) < 1 / 2) :
    (r : ENNReal) / (1 - (r : ENNReal)) < 1 := by
  have hr1 : (r : ENNReal) < 1 := lt_trans hrhalf (by norm_num)
  have hden_ne_zero : 1 - (r : ENNReal) ≠ 0 := ne_of_gt (tsub_pos_of_lt hr1)
  have hden_ne_top : 1 - (r : ENNReal) ≠ ⊤ := by
    exact ne_of_lt (lt_top_of_lt (b := 2) (tsub_le_self.trans_lt (by simp)))
  have hhalf_eq : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 2 by norm_num)]
    norm_num
  have hhalf : (1 / 2 : ENNReal) + 1 / 2 = 1 := by
    calc
      (1 / 2 : ENNReal) + 1 / 2
          = ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) := by
              rw [hhalf_eq]
      _ = ENNReal.ofReal (1 : ℝ) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            norm_num
      _ = 1 := by norm_num
  have hhalf_sub : 1 - (1 / 2 : ENNReal) = 1 / 2 := by
    exact
      ENNReal.eq_sub_of_add_eq (a := (1 / 2 : ENNReal)) (c := (1 / 2 : ENNReal)) (b := 1)
        (by simp) hhalf |>.symm
  have hhalf_le : (1 / 2 : ENNReal) ≤ 1 - (r : ENNReal) := by
    calc
      (1 / 2 : ENNReal) = 1 - (1 / 2 : ENNReal) := hhalf_sub.symm
      _ ≤ 1 - (r : ENNReal) := by
            exact tsub_le_tsub_left (le_of_lt hrhalf) 1
  have hlt : (r : ENNReal) < 1 - (r : ENNReal) := by
    exact lt_of_lt_of_le hrhalf hhalf_le
  -- Proof comment: once `r < 1 - r`, the quotient inequality is a direct `div_lt_iff` rewrite.
  rw [ENNReal.div_lt_iff (Or.inl hden_ne_zero) (Or.inl hden_ne_top)]
  simpa using hlt

/-- Helper for Remark 17.31: the left-drift invariant-mass series has strictly positive total
mass. -/
private theorem figure17_2InvariantMass_tsum_ne_zero
    (hrhalf : (r : ENNReal) < 1 / 2) :
    (∑' n : ℕ, figure17_2InvariantMass r n) ≠ 0 := by
  have hr1 : (r : ENNReal) < 1 := lt_trans hrhalf (by norm_num)
  have hmass0_pos : 0 < figure17_2InvariantMass r 0 := by
    simpa [figure17_2InvariantMass] using tsub_pos_of_lt hr1
  have hmass0_le :
      figure17_2InvariantMass r 0 ≤ ∑' n : ℕ, figure17_2InvariantMass r n := by
    exact ENNReal.le_tsum 0
  -- Proof comment: the boundary term `n = 0` is already strictly positive, so the full series
  -- cannot vanish.
  exact ne_of_gt (lt_of_lt_of_le hmass0_pos hmass0_le)

/-- Helper for Remark 17.31: the left-drift invariant-mass series is finite. -/
private theorem figure17_2InvariantMass_tsum_ne_top
    (hrhalf : (r : ENNReal) < 1 / 2) :
    (∑' n : ℕ, figure17_2InvariantMass r n) ≠ ⊤ := by
  let q : ENNReal := (r : ENNReal) / (1 - (r : ENNReal))
  have hq_lt_one : q < 1 := figure17_2InvariantRatio_lt_one (r := r) hrhalf
  have htail_ne_top : (∑' n : ℕ, q ^ n) ≠ ⊤ :=
    ((tsum_geometric_lt_top).2 hq_lt_one).ne
  -- Proof comment: split off the boundary mass `1 - r`; the remaining series is geometric with
  -- ratio `q = r / (1 - r) < 1`.
  rw [tsum_eq_zero_add' ENNReal.summable]
  have htail :
      (∑' b : ℕ, figure17_2InvariantMass r (b + 1)) = ∑' n : ℕ, q ^ n := by
    simp [figure17_2InvariantMass, q]
  rw [htail]
  exact ENNReal.add_ne_top.2 ⟨by simp [figure17_2InvariantMass], htail_ne_top⟩

/-- Helper for Remark 17.31: the normalized geometric mass profile gives a probability mass
function on `ℕ` in the left-drift regime. -/
private def figure17_2InvariantPMF (r : Set.Icc (0 : ENNReal) 1)
    (hrhalf : (r : ENNReal) < 1 / 2) : PMF ℕ :=
  PMF.normalize (figure17_2InvariantMass r)
    (figure17_2InvariantMass_tsum_ne_zero (r := r) hrhalf)
    (figure17_2InvariantMass_tsum_ne_top (r := r) hrhalf)

/-- Helper for Remark 17.31: the normalized geometric invariant distribution of Fig. 17.2 in the
left-drift regime. -/
private def figure17_2InvariantDistribution (r : Set.Icc (0 : ENNReal) 1)
    (hrhalf : (r : ENNReal) < 1 / 2) : ProbabilityMeasure ℕ :=
  ⟨(figure17_2InvariantPMF r hrhalf).toMeasure, inferInstance⟩

/-- Helper for Remark 17.31: the normalized invariant distribution has singleton masses given by
the geometric profile times the normalization constant. -/
private theorem figure17_2InvariantDistribution_apply_singleton
    (hrhalf : (r : ENNReal) < 1 / 2) (n : ℕ) :
    (figure17_2InvariantDistribution r hrhalf : Measure ℕ) ({n} : Set ℕ) =
      figure17_2InvariantMass r n * (∑' k : ℕ, figure17_2InvariantMass r k)⁻¹ := by
  -- Proof comment: the invariant distribution is the measure of the normalized PMF, so singleton
  -- masses are exactly the normalized weights.
  change (figure17_2InvariantPMF r hrhalf).toMeasure ({n} : Set ℕ) =
    figure17_2InvariantMass r n * (∑' k : ℕ, figure17_2InvariantMass r k)⁻¹
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n)]
  simp [figure17_2InvariantPMF, PMF.normalize_apply]

/-- Helper for Remark 17.31: the geometric invariant masses satisfy the boundary balance at
state `0`. -/
private theorem figure17_2InvariantMass_balance_zero :
    figure17_2InvariantMass r 1 * (1 - (r : ENNReal)) =
      figure17_2InvariantMass r 0 := by
  -- Proof comment: the mass at `1` is `1`, so the left jump from `1` back to `0` reproduces the
  -- boundary mass `1 - r`.
  simp [figure17_2InvariantMass]

/-- Helper for Remark 17.31: the geometric invariant masses satisfy the boundary balance at
state `1`. -/
private theorem figure17_2InvariantMass_balance_one
    (hrhalf : (r : ENNReal) < 1 / 2) :
    figure17_2InvariantMass r 0 +
        figure17_2InvariantMass r 2 * (1 - (r : ENNReal)) =
      figure17_2InvariantMass r 1 := by
  let q : ENNReal := (r : ENNReal) / (1 - (r : ENNReal))
  have hr1 : (r : ENNReal) < 1 := lt_trans hrhalf (by norm_num)
  have hqmul : q * (1 - (r : ENNReal)) = (r : ENNReal) := by
    -- Proof comment: the geometric ratio was chosen exactly so that multiplying by the left-jump
    -- probability recovers the right-jump weight `r`.
    have hden0 : 1 - (r : ENNReal) ≠ 0 := ne_of_gt (tsub_pos_of_lt hr1)
    dsimp [q]
    rw [div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel hden0 (by simp [hden0]), mul_one]
  calc
    figure17_2InvariantMass r 0 + figure17_2InvariantMass r 2 * (1 - (r : ENNReal))
      = (1 - (r : ENNReal)) + q * (1 - (r : ENNReal)) := by
          simp [figure17_2InvariantMass, q]
    _ = (1 - (r : ENNReal)) + (r : ENNReal) := by rw [hqmul]
    _ = 1 := by simpa using tsub_add_cancel_of_le r.2.2
    _ = figure17_2InvariantMass r 1 := by simp [figure17_2InvariantMass]

/-- Helper for Remark 17.31: the geometric invariant masses satisfy the interior two-neighbor
balance equations. -/
private theorem figure17_2InvariantMass_balance_succ_succ
    (hrhalf : (r : ENNReal) < 1 / 2) (n : ℕ) :
    figure17_2InvariantMass r (n + 1) * (r : ENNReal) +
        figure17_2InvariantMass r (n + 3) * (1 - (r : ENNReal)) =
      figure17_2InvariantMass r (n + 2) := by
  let q : ENNReal := (r : ENNReal) / (1 - (r : ENNReal))
  have hr1 : (r : ENNReal) < 1 := lt_trans hrhalf (by norm_num)
  have hden0 : 1 - (r : ENNReal) ≠ 0 := ne_of_gt (tsub_pos_of_lt hr1)
  have hqmul : q * (1 - (r : ENNReal)) = (r : ENNReal) := by
    -- Proof comment: multiplying the geometric ratio by the left-jump weight recovers `r`.
    dsimp [q]
    rw [div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel hden0 (by simp [hden0]), mul_one]
  have hqsum : (r : ENNReal) + q * (r : ENNReal) = q := by
    calc
      (r : ENNReal) + q * (r : ENNReal)
        = q * (1 - (r : ENNReal)) + q * (r : ENNReal) := by rw [hqmul]
      _ = q * ((1 - (r : ENNReal)) + (r : ENNReal)) := by rw [mul_add]
      _ = q := by rw [tsub_add_cancel_of_le r.2.2, mul_one]
  -- Proof comment: factor out the common power `q ^ n` and use the relation
  -- `q = r + q * r`, which is equivalent to `q * (1 - r) = r`.
  calc
    figure17_2InvariantMass r (n + 1) * (r : ENNReal) +
        figure17_2InvariantMass r (n + 3) * (1 - (r : ENNReal))
      = q ^ n * (r : ENNReal) + q ^ (n + 2) * (1 - (r : ENNReal)) := by
          simp [figure17_2InvariantMass, q]
    _ = q ^ n * (r : ENNReal) + q ^ (n + 1) * (q * (1 - (r : ENNReal))) := by
          simp [pow_succ', mul_assoc, mul_left_comm, mul_comm]
    _ = q ^ n * (r : ENNReal) + q ^ (n + 1) * (r : ENNReal) := by
          rw [hqmul]
    _ = q ^ n * (r : ENNReal) + q ^ n * (q * (r : ENNReal)) := by
          rw [pow_succ']
          ac_rfl
    _ = q ^ n * ((r : ENNReal) + q * (r : ENNReal)) := by
          rw [← mul_add]
    _ = q ^ (n + 1) := by
          rw [hqsum, pow_succ']
          ac_rfl
    _ = figure17_2InvariantMass r (n + 2) := by
          simp [figure17_2InvariantMass, q]

/-- Helper for Remark 17.31: on the countable discrete state space `ℕ`, invariance of the
Fig. 17.2 kernel is equivalent to the singleton balance equations. -/
private theorem figure17_2_kernelInvariant_iff_singleton
    (μ : Measure ℕ) :
    Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r)) μ ↔
      ∀ x : ℕ,
        ∑' y : ℕ, μ ({y} : Set ℕ) * figure17_2TransitionMatrix r y x =
          μ ({x} : Set ℕ) := by
  constructor
  · intro hμ x
    -- Proof comment: evaluate the invariant-measure identity on the singleton `{x}`.
    have hx := congrArg (fun ν : Measure ℕ ↦ ν ({x} : Set ℕ)) hμ.def
    simpa [figure17_2_comp_discreteMatrixKernel_apply_singleton_eq_tsum] using hx
  · intro hμ
    rw [Kernel.Invariant]
    refine Measure.ext_of_singleton fun x ↦ ?_
    -- Proof comment: singleton balance determines the whole measure on the discrete state space.
    simpa [figure17_2_comp_discreteMatrixKernel_apply_singleton_eq_tsum] using hμ x

/-- Helper for Remark 17.31: the raw weighted counting measure with density
`figure17_2InvariantMass r` has the expected singleton masses. -/
private theorem figure17_2InvariantRawMeasure_apply_singleton
    (n : ℕ) :
    (Measure.count.withDensity (figure17_2InvariantMass r)) ({n} : Set ℕ) =
      figure17_2InvariantMass r n := by
  -- Proof comment: on the discrete state space `ℕ`, the weighted counting measure integrates the
  -- singleton indicator down to the single density value at `n`.
  rw [withDensity_apply _ (measurableSet_singleton n),
    ← lintegral_indicator (measurableSet_singleton n), lintegral_count]
  simp

/-- Helper for Remark 17.31: scalar multiples of invariant measures stay invariant for the
Fig. 17.2 kernel. -/
private theorem figure17_2_kernelInvariant_smul
    {μ : Measure ℕ}
    (hμ : Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r)) μ)
    (a : ℝ≥0∞) :
    Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r)) (a • μ) := by
  -- Proof comment: composing a scalar multiple with the kernel factors the scalar outside the
  -- bind, so invariance survives scaling.
  simpa [Kernel.Invariant, Measure.comp_smul] using
    congrArg (fun ν : Measure ℕ ↦ a • ν) hμ.def

/-- Helper for Remark 17.31: the only incoming edge to state `0` in Fig. 17.2 is the left jump
from state `1`. -/
private theorem figure17_2TransitionMatrix_apply_zero
    (y : ℕ) :
    figure17_2TransitionMatrix r y 0 =
      if y = 1 then 1 - (r : ENNReal) else 0 := by
  cases y with
  | zero =>
      -- Proof comment: state `0` jumps deterministically to `1`, so it sends no mass back to `0`.
      simp [figure17_2TransitionMatrix]
  | succ n =>
      cases n with
      | zero =>
          -- Proof comment: state `1` is the unique predecessor of `0`.
          simp [figure17_2TransitionMatrix]
      | succ k =>
          -- Proof comment: no state `k + 2 ≥ 2` can reach `0` in one step.
          simp [figure17_2TransitionMatrix]

/-- Helper for Remark 17.31: the only incoming edges to state `1` in Fig. 17.2 are the
deterministic jump from `0` and the left jump from `2`. -/
private theorem figure17_2TransitionMatrix_apply_one
    (y : ℕ) :
    figure17_2TransitionMatrix r y 1 =
      if y = 0 then 1 else if y = 2 then 1 - (r : ENNReal) else 0 := by
  cases y with
  | zero =>
      -- Proof comment: state `0` reaches `1` with probability `1`.
      simp [figure17_2TransitionMatrix]
  | succ n =>
      cases n with
      | zero =>
          -- Proof comment: state `1` has no self-loop.
          simp [figure17_2TransitionMatrix]
      | succ k =>
          cases k with
          | zero =>
              -- Proof comment: state `2` reaches `1` by its left jump.
              simp [figure17_2TransitionMatrix]
          | succ l =>
              -- Proof comment: all states `≥ 3` miss `1` in one step.
              simp [figure17_2TransitionMatrix]

/-- Helper for Remark 17.31: the only incoming edges to state `n + 2` in Fig. 17.2 are the
right jump from `n + 1` and the left jump from `n + 3`. -/
private theorem figure17_2TransitionMatrix_apply_succ_succ
    (y n : ℕ) :
    figure17_2TransitionMatrix r y (n + 2) =
      if y = n + 1 then (r : ENNReal) else if y = n + 3 then 1 - (r : ENNReal) else 0 := by
  cases y with
  | zero =>
      -- Proof comment: state `0` can only jump to `1`, so it never reaches `n + 2 ≥ 2`.
      simp [figure17_2TransitionMatrix]
  | succ m =>
      by_cases hm : m = n
      · -- Proof comment: `m = n` means `y = n + 1`, so only the right-jump branch survives.
        subst hm
        simp [figure17_2TransitionMatrix]
      · by_cases hm' : m = n + 2
        · -- Proof comment: `m = n + 2` means `y = n + 3`, so only the left-jump branch survives.
          subst hm'
          simp [figure17_2TransitionMatrix]
        · -- Proof comment: all other predecessors miss `n + 2` in one step.
          rw [figure17_2TransitionMatrix]
          by_cases hnm : n = m
          · exact (hm hnm.symm).elim
          · by_cases hnm2 : n + 2 = m
            · exact (hm' hnm2.symm).elim
            · have hmn : m ≠ n := fun h => hnm h.symm
              have hmn2 : m ≠ n + 2 := fun h => hnm2 h.symm
              simp [hnm, hnm2, hmn, hmn2]

/-- Helper for Remark 17.31: the raw weighted counting measure with density
`figure17_2InvariantMass r` is invariant in the left-drift regime. -/
private theorem figure17_2InvariantRawMeasure_isInvariant
    (hrhalf : (r : ENNReal) < 1 / 2) :
    Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
      (Measure.count.withDensity (figure17_2InvariantMass r)) := by
  rw [figure17_2_kernelInvariant_iff_singleton]
  intro x
  cases x with
  | zero =>
      -- Proof comment: only the left jump from state `1` contributes to the incoming mass at `0`.
      calc
        ∑' y : ℕ,
            (Measure.count.withDensity (figure17_2InvariantMass r)) ({y} : Set ℕ) *
              figure17_2TransitionMatrix r y 0
          = ∑' y : ℕ, figure17_2InvariantMass r y * figure17_2TransitionMatrix r y 0 := by
              congr with y
              rw [figure17_2InvariantRawMeasure_apply_singleton (r := r) y]
        _ = ∑' y : ℕ,
              figure17_2InvariantMass r y *
                (if y = 1 then 1 - (r : ENNReal) else 0) := by
              congr with y
              rw [figure17_2TransitionMatrix_apply_zero (r := r) y]
        _ = figure17_2InvariantMass r 1 * (1 - (r : ENNReal)) := by
              rw [ENNReal.tsum_eq_add_tsum_ite 1]
              have htail :
                  (∑' x : ℕ,
                    if x = 1 then 0
                    else figure17_2InvariantMass r x * if x = 1 then 1 - (r : ENNReal) else 0)
                    = 0 := by
                refine ENNReal.tsum_eq_zero.2 ?_
                intro x
                by_cases hx : x = 1
                · simp [hx]
                · simp [hx]
              simp only [if_pos rfl]
              have hcollapse :=
                congrArg
                  (fun t : ENNReal ↦ figure17_2InvariantMass r 1 * (1 - (r : ENNReal)) + t)
                  htail
              simpa using hcollapse
        _ = figure17_2InvariantMass r 0 := figure17_2InvariantMass_balance_zero (r := r)
        _ = (Measure.count.withDensity (figure17_2InvariantMass r)) ({0} : Set ℕ) := by
              rw [figure17_2InvariantRawMeasure_apply_singleton (r := r) 0]
  | succ x =>
      cases x with
      | zero =>
          -- Proof comment: the incoming mass at `1` splits into the deterministic jump from `0`
          -- and the left jump from `2`.
          calc
            ∑' y : ℕ,
                (Measure.count.withDensity (figure17_2InvariantMass r)) ({y} : Set ℕ) *
                  figure17_2TransitionMatrix r y 1
              = ∑' y : ℕ, figure17_2InvariantMass r y * figure17_2TransitionMatrix r y 1 := by
                  congr with y
                  rw [figure17_2InvariantRawMeasure_apply_singleton (r := r) y]
            _ = ∑' y : ℕ,
                  figure17_2InvariantMass r y *
                    (if y = 0 then 1 else if y = 2 then 1 - (r : ENNReal) else 0) := by
                  congr with y
                  rw [figure17_2TransitionMatrix_apply_one (r := r) y]
            _ = figure17_2InvariantMass r 0 +
                  figure17_2InvariantMass r 2 * (1 - (r : ENNReal)) := by
                  rw [ENNReal.tsum_eq_add_tsum_ite 0, ENNReal.tsum_eq_add_tsum_ite 2]
                  have htail :
                      (∑' x : ℕ,
                        if x = 2 then 0
                        else
                          if x = 0 then 0
                          else
                            figure17_2InvariantMass r x *
                              if x = 0 then 1 else if x = 2 then 1 - (r : ENNReal) else 0) =
                        0 := by
                    refine ENNReal.tsum_eq_zero.2 ?_
                    intro x
                    by_cases hx2 : x = 2
                    · simp [hx2]
                    · by_cases hx0 : x = 0
                      · simp [hx2, hx0]
                      · simp [hx2, hx0]
                  simp
                  have hcollapse :=
                    congrArg
                      (fun t : ENNReal ↦
                        figure17_2InvariantMass r 0 +
                          (figure17_2InvariantMass r 2 * (1 - (r : ENNReal)) + t))
                      htail
                  simpa [add_assoc] using hcollapse
            _ = figure17_2InvariantMass r 1 := figure17_2InvariantMass_balance_one (r := r) hrhalf
            _ = (Measure.count.withDensity (figure17_2InvariantMass r)) ({1} : Set ℕ) := by
                  rw [figure17_2InvariantRawMeasure_apply_singleton (r := r) 1]
      | succ n =>
          -- Proof comment: for interior states `n + 2`, only the right jump from `n + 1` and the
          -- left jump from `n + 3` contribute.
          calc
            ∑' y : ℕ,
                (Measure.count.withDensity (figure17_2InvariantMass r)) ({y} : Set ℕ) *
                  figure17_2TransitionMatrix r y (n + 2)
              = ∑' y : ℕ,
                  figure17_2InvariantMass r y * figure17_2TransitionMatrix r y (n + 2) := by
                  congr with y
                  rw [figure17_2InvariantRawMeasure_apply_singleton (r := r) y]
            _ = ∑' y : ℕ,
                  figure17_2InvariantMass r y *
                    (if y = n + 1 then (r : ENNReal)
                      else if y = n + 3 then 1 - (r : ENNReal) else 0) := by
                  congr with y
                  rw [figure17_2TransitionMatrix_apply_succ_succ (r := r) y n]
            _ = figure17_2InvariantMass r (n + 1) * (r : ENNReal) +
                  figure17_2InvariantMass r (n + 3) * (1 - (r : ENNReal)) := by
                  rw [ENNReal.tsum_eq_add_tsum_ite (n + 1), ENNReal.tsum_eq_add_tsum_ite (n + 3)]
                  have htail :
                      (∑' x : ℕ,
                        if x = n + 3 then 0
                        else
                          if x = n + 1 then 0
                          else
                            figure17_2InvariantMass r x *
                              if x = n + 1 then (r : ENNReal)
                              else if x = n + 3 then 1 - (r : ENNReal) else 0) = 0 := by
                    refine ENNReal.tsum_eq_zero.2 ?_
                    intro x
                    by_cases hx3 : x = n + 3
                    · simp [hx3]
                    · by_cases hx1 : x = n + 1
                      · simp [hx3, hx1]
                      · simp [hx3, hx1]
                  simp
                  have hcollapse :=
                    congrArg
                      (fun t : ENNReal ↦
                        figure17_2InvariantMass r (n + 1) * (r : ENNReal) +
                          (figure17_2InvariantMass r (n + 3) * (1 - (r : ENNReal)) + t))
                      htail
                  simpa [add_assoc] using hcollapse
            _ = figure17_2InvariantMass r (n + 2) :=
                figure17_2InvariantMass_balance_succ_succ (r := r) hrhalf n
            _ = (Measure.count.withDensity (figure17_2InvariantMass r)) ({n + 2} : Set ℕ) := by
                  rw [figure17_2InvariantRawMeasure_apply_singleton (r := r) (n + 2)]

/-- Helper for Remark 17.31: the normalized invariant distribution is a scalar multiple of the
raw weighted counting measure. -/
private theorem figure17_2InvariantDistribution_eq_smul_rawMeasure
    (hrhalf : (r : ENNReal) < 1 / 2) :
    (figure17_2InvariantDistribution r hrhalf : Measure ℕ) =
      (∑' k : ℕ, figure17_2InvariantMass r k)⁻¹ •
        Measure.count.withDensity (figure17_2InvariantMass r) := by
  refine Measure.ext_of_singleton fun n ↦ ?_
  -- Proof comment: both measures have the same singleton masses, namely the raw geometric mass
  -- profile scaled by the common normalization factor.
  calc
    (figure17_2InvariantDistribution r hrhalf : Measure ℕ) ({n} : Set ℕ)
      = figure17_2InvariantMass r n * (∑' k : ℕ, figure17_2InvariantMass r k)⁻¹ := by
          rw [figure17_2InvariantDistribution_apply_singleton (r := r) hrhalf n]
    _ =
        ((∑' k : ℕ, figure17_2InvariantMass r k)⁻¹ •
          Measure.count.withDensity (figure17_2InvariantMass r)) ({n} : Set ℕ) := by
            rw [Measure.smul_apply, figure17_2InvariantRawMeasure_apply_singleton]
            simp [smul_eq_mul, mul_comm]

/-- Helper for Remark 17.31: in the left-drift regime, the normalized geometric distribution is
invariant for the Fig. 17.2 kernel. -/
private theorem figure17_2InvariantDistribution_isInvariant
    (hrhalf : (r : ENNReal) < 1 / 2) :
    Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
      (figure17_2InvariantDistribution r hrhalf : Measure ℕ) := by
  -- Route correction: instead of carrying the normalization constant through every singleton
  -- balance equation, prove invariance for the raw weighted counting measure and transport it once
  -- by scalar multiplication.
  rw [figure17_2InvariantDistribution_eq_smul_rawMeasure (r := r) hrhalf]
  exact
    figure17_2_kernelInvariant_smul (r := r)
      (figure17_2InvariantRawMeasure_isInvariant (r := r) hrhalf)
      ((∑' k : ℕ, figure17_2InvariantMass r k)⁻¹)

/-- Helper for Remark 17.31: in the left-drift regime, the normalized geometric invariant
distribution charges the singleton `{0}` positively. -/
private theorem figure17_2_existsInvariantDistribution_zeroMass_pos_of_lt_half
    (hr0 : 0 < (r : ENNReal)) (hrhalf : (r : ENNReal) < 1 / 2) :
    ∃ π : ProbabilityMeasure ℕ,
      Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
        (π : Measure ℕ) ∧
      0 < (π : Measure ℕ) ({0} : Set ℕ) := by
  let c : ENNReal := (∑' k : ℕ, figure17_2InvariantMass r k)⁻¹
  have hr1 : (r : ENNReal) < 1 := lt_trans hrhalf (by norm_num)
  have hmass0_pos : 0 < figure17_2InvariantMass r 0 := by
    simpa [figure17_2InvariantMass] using tsub_pos_of_lt hr1
  have hc_ne_zero : c ≠ 0 := by
    simpa [c] using
      (ENNReal.inv_ne_zero.2 (figure17_2InvariantMass_tsum_ne_top (r := r) hrhalf))
  refine ⟨figure17_2InvariantDistribution r hrhalf,
    figure17_2InvariantDistribution_isInvariant (r := r) hrhalf, ?_⟩
  -- Proof comment: the normalized geometric invariant distribution assigns strictly positive mass
  -- to `{0}` because the raw boundary weight `1 - r` is positive and the normalization factor is
  -- nonzero.
  calc
    0 < figure17_2InvariantMass r 0 * c := ENNReal.mul_pos hmass0_pos.ne' hc_ne_zero
    _ = ((figure17_2InvariantDistribution r hrhalf : Measure ℕ) ({0} : Set ℕ)) := by
          simpa [c] using
            (figure17_2InvariantDistribution_apply_singleton (r := r) hrhalf 0).symm

/-- Helper for Remark 17.31: at the critical parameter `r = 1 / 2`, the singleton balance at
state `1` reduces to the two incoming neighbors `0` and `2`. -/
private theorem figure17_2_invariantBalance_one_half
    (hr : (r : ENNReal) = 1 / 2) (π : ProbabilityMeasure ℕ)
    (hπ : Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
      (π : Measure ℕ)) :
    (π : Measure ℕ) ({0} : Set ℕ) +
        (π : Measure ℕ) ({2} : Set ℕ) * (1 / 2 : ENNReal) =
      (π : Measure ℕ) ({1} : Set ℕ) := by
  -- Proof comment: rewrite the singleton balance at `1` so only the deterministic jump from `0`
  -- and the left jump from `2` remain.
  calc
    (π : Measure ℕ) ({0} : Set ℕ) +
        (π : Measure ℕ) ({2} : Set ℕ) * (1 / 2 : ENNReal)
      = ∑' y : ℕ, (π : Measure ℕ) ({y} : Set ℕ) *
          (if y = 0 then 1 else if y = 2 then 1 / 2 else 0) := by
            rw [ENNReal.tsum_eq_add_tsum_ite 0, ENNReal.tsum_eq_add_tsum_ite 2]
            have htail :
                (∑' x : ℕ,
                  if x = 2 then 0
                  else
                    if x = 0 then 0
                    else
                      (π : Measure ℕ) ({x} : Set ℕ) *
                        (if x = 0 then (1 : ENNReal) else if x = 2 then 1 / 2 else 0)) = 0 := by
              refine ENNReal.tsum_eq_zero.2 ?_
              intro x
              by_cases hx2 : x = 2
              · simp [hx2]
              · by_cases hx0 : x = 0
                · simp [hx2, hx0]
                · simp [hx2, hx0]
            simp
            have hcollapse :=
              congrArg
                (fun t : ENNReal ↦
                  (π : Measure ℕ) ({0} : Set ℕ) +
                    ((π : Measure ℕ) ({2} : Set ℕ) * (1 / 2 : ENNReal) + t))
                htail
            simpa [add_assoc] using hcollapse.symm
    _ = ∑' y : ℕ, (π : Measure ℕ) ({y} : Set ℕ) * figure17_2TransitionMatrix r y 1 := by
          congr with y
          rw [figure17_2TransitionMatrix_apply_one (r := r) y]
          simp [hr]
    _ = (π : Measure ℕ) ({1} : Set ℕ) :=
          figure17_2_invariantBalance_singleton (r := r) π hπ 1

/-- Helper for Remark 17.31: at the critical parameter `r = 1 / 2`, the singleton balance at an
interior state `m + 2` reduces to the two incoming neighbors `m + 1` and `m + 3`. -/
private theorem figure17_2_invariantBalance_succ_half
    (hr : (r : ENNReal) = 1 / 2) (π : ProbabilityMeasure ℕ)
    (hπ : Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
      (π : Measure ℕ)) (m : ℕ) :
    (π : Measure ℕ) ({m + 1} : Set ℕ) * (1 / 2 : ENNReal) +
        (π : Measure ℕ) ({m + 3} : Set ℕ) * (1 / 2 : ENNReal) =
      (π : Measure ℕ) ({m + 2} : Set ℕ) := by
  -- Proof comment: rewrite the singleton balance at `m + 2` so only its two nearest neighbors
  -- contribute.
  calc
    (π : Measure ℕ) ({m + 1} : Set ℕ) * (1 / 2 : ENNReal) +
        (π : Measure ℕ) ({m + 3} : Set ℕ) * (1 / 2 : ENNReal)
      = ∑' y : ℕ, (π : Measure ℕ) ({y} : Set ℕ) *
          (if y = m + 1 then 1 / 2 else if y = m + 3 then 1 / 2 else 0) := by
            rw [ENNReal.tsum_eq_add_tsum_ite (m + 1), ENNReal.tsum_eq_add_tsum_ite (m + 3)]
            have htail :
                (∑' x : ℕ,
                  if x = m + 3 then 0
                  else
                    if x = m + 1 then 0
                    else
                      (π : Measure ℕ) ({x} : Set ℕ) *
                        (if x = m + 1 then (1 / 2 : ENNReal)
                          else if x = m + 3 then 1 / 2 else 0)) = 0 := by
              refine ENNReal.tsum_eq_zero.2 ?_
              intro x
              by_cases hx3 : x = m + 3
              · simp [hx3]
              · by_cases hx1 : x = m + 1
                · simp [hx3, hx1]
                · simp [hx3, hx1]
            simp
            have hcollapse :=
              congrArg
                (fun t : ENNReal ↦
                  (π : Measure ℕ) ({m + 1} : Set ℕ) * (1 / 2 : ENNReal) +
                    ((π : Measure ℕ) ({m + 3} : Set ℕ) * (1 / 2 : ENNReal) + t))
                htail
            simpa [add_assoc] using hcollapse.symm
    _ = ∑' y : ℕ, (π : Measure ℕ) ({y} : Set ℕ) * figure17_2TransitionMatrix r y (m + 2) := by
          congr with y
          rw [figure17_2TransitionMatrix_apply_succ_succ (r := r) y m]
          simp [hr]
    _ = (π : Measure ℕ) ({m + 2} : Set ℕ) :=
          figure17_2_invariantBalance_singleton (r := r) π hπ (m + 2)

/-- Helper for Remark 17.31: at the critical parameter `r = 1 / 2`, the singleton balance at
state `0` reduces to the unique incoming neighbor `1`. -/
private theorem figure17_2_invariantBalance_zero_half
    (hr : (r : ENNReal) = 1 / 2) (π : ProbabilityMeasure ℕ)
    (hπ : Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
      (π : Measure ℕ)) :
    (π : Measure ℕ) ({1} : Set ℕ) * (1 / 2 : ENNReal) =
      (π : Measure ℕ) ({0} : Set ℕ) := by
  -- Proof comment: rewrite the singleton balance at `0` so only the left jump from `1`
  -- contributes.
  calc
    (π : Measure ℕ) ({1} : Set ℕ) * (1 / 2 : ENNReal)
      = ∑' y : ℕ, (π : Measure ℕ) ({y} : Set ℕ) *
          (if y = 1 then 1 / 2 else 0) := by
            rw [ENNReal.tsum_eq_add_tsum_ite 1]
            have htail :
                (∑' x : ℕ,
                  if x = 1 then 0
                  else
                    (π : Measure ℕ) ({x} : Set ℕ) * (if x = 1 then (1 / 2 : ENNReal) else 0)) =
                  0 := by
              refine ENNReal.tsum_eq_zero.2 ?_
              intro x
              by_cases hx : x = 1
              · simp [hx]
              · simp [hx]
            simp only [if_pos rfl]
            have hcollapse :=
              congrArg
                (fun t : ENNReal ↦ (π : Measure ℕ) ({1} : Set ℕ) * (1 / 2 : ENNReal) + t)
                htail
            simpa using hcollapse.symm
    _ = ∑' y : ℕ, (π : Measure ℕ) ({y} : Set ℕ) * figure17_2TransitionMatrix r y 0 := by
          congr with y
          rw [figure17_2TransitionMatrix_apply_zero (r := r) y]
          simp [hr]
    _ = (π : Measure ℕ) ({0} : Set ℕ) :=
          figure17_2_invariantBalance_singleton (r := r) π hπ 0

/-- Helper for Remark 17.31: at the critical parameter `r = 1 / 2`, every invariant probability
measure for the Fig. 17.2 kernel has zero singleton mass at every state. -/
private theorem figure17_2_invariantDistribution_singleton_eq_zero_of_eq_half
    (hr : (r : ENNReal) = 1 / 2) (π : ProbabilityMeasure ℕ)
    (hπ : Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
      (π : Measure ℕ)) (n : ℕ) :
    (π : Measure ℕ) ({n} : Set ℕ) = 0 := by
  let mass : ℕ → ENNReal := fun k ↦ (π : Measure ℕ) ({k} : Set ℕ)
  have hmass_ne_top : ∀ k : ℕ, mass k ≠ ⊤ := by
    intro k
    exact measure_ne_top (π : Measure ℕ) ({k} : Set ℕ)
  have hzero :
      mass 1 * (1 / 2 : ENNReal) = mass 0 :=
    figure17_2_invariantBalance_zero_half (r := r) hr π hπ
  have hone :
      mass 0 + mass 2 * (1 / 2 : ENNReal) = mass 1 :=
    figure17_2_invariantBalance_one_half (r := r) hr π hπ
  have hzero_real :
      (mass 1).toReal * (1 / 2 : ℝ) = (mass 0).toReal := by
    simpa [ENNReal.toReal_mul, hmass_ne_top 1] using congrArg ENNReal.toReal hzero
  have hone_real :
      (mass 0).toReal + (mass 2).toReal * (1 / 2 : ℝ) = (mass 1).toReal := by
    have hmul2 : mass 2 * (1 / 2 : ENNReal) ≠ ⊤ :=
      ENNReal.mul_ne_top (hmass_ne_top 2) (by simp)
    have hone_toReal := congrArg ENNReal.toReal hone
    rw [ENNReal.toReal_add (hmass_ne_top 0) hmul2, ENNReal.toReal_mul] at hone_toReal
    simpa [hmass_ne_top 0, hmass_ne_top 2] using
      hone_toReal
  have htwo_real : (mass 2).toReal = (mass 1).toReal := by
    linarith
  have hconst_pair :
      ∀ m : ℕ, (mass (m + 1)).toReal = (mass 1).toReal ∧
        (mass (m + 2)).toReal = (mass 1).toReal := by
    intro m
    induction m with
    | zero =>
        exact ⟨rfl, htwo_real⟩
    | succ m ih =>
        rcases ih with ⟨hm1, hm2⟩
        have hsucc :
            mass (m + 1) * (1 / 2 : ENNReal) + mass (m + 3) * (1 / 2 : ENNReal) =
              mass (m + 2) :=
          figure17_2_invariantBalance_succ_half (r := r) hr π hπ m
        have hsucc_real :
            (mass (m + 1)).toReal * (1 / 2 : ℝ) +
                (mass (m + 3)).toReal * (1 / 2 : ℝ) =
              (mass (m + 2)).toReal := by
          have hmul13 : mass (m + 1) * (1 / 2 : ENNReal) ≠ ⊤ :=
            ENNReal.mul_ne_top (hmass_ne_top (m + 1)) (by simp)
          have hmul33 : mass (m + 3) * (1 / 2 : ENNReal) ≠ ⊤ :=
            ENNReal.mul_ne_top (hmass_ne_top (m + 3)) (by simp)
          have hsucc_toReal := congrArg ENNReal.toReal hsucc
          rw [ENNReal.toReal_add hmul13 hmul33, ENNReal.toReal_mul, ENNReal.toReal_mul] at hsucc_toReal
          simpa [hmass_ne_top (m + 1), hmass_ne_top (m + 3), hmass_ne_top (m + 2)] using
            hsucc_toReal
        have hm3 : (mass (m + 3)).toReal = (mass 1).toReal := by
          linarith
        exact ⟨hm2, hm3⟩
  have hconst :
      ∀ k : ℕ, 0 < k → mass k = mass 1 := by
    intro k hk
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk) with ⟨m, rfl⟩
    have hm : (mass (m + 1)).toReal = (mass 1).toReal := (hconst_pair m).1
    exact (ENNReal.toReal_eq_toReal_iff' (hmass_ne_top (m + 1)) (hmass_ne_top 1)).mp hm
  have hmass_one_zero : mass 1 = 0 := by
    by_contra hmass_one_zero
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hmass_one_zero (by simp : (1 : ENNReal) ≠ ⊤)
    have hsum :
        ∑ x ∈ Finset.Icc 1 N, mass x = N * mass 1 := by
      calc
        ∑ x ∈ Finset.Icc 1 N, mass x = ∑ x ∈ Finset.Icc 1 N, mass 1 := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact hconst x (Finset.mem_Icc.mp hx).1
        _ = N * mass 1 := by
          simp [Nat.card_Icc]
    have hle :
        ∑ x ∈ Finset.Icc 1 N, mass x ≤ 1 := by
      calc
        ∑ x ∈ Finset.Icc 1 N, mass x = (π : Measure ℕ) (Finset.Icc 1 N : Set ℕ) := by
          simpa [mass] using
            (sum_measure_singleton (μ := (π : Measure ℕ)) (s := Finset.Icc 1 N)).symm
        _ ≤ (π : Measure ℕ) Set.univ := by
              exact measure_mono (by intro x hx; simp)
        _ = 1 := by simp
    have hNle : N * mass 1 ≤ 1 := by
      simpa [hsum] using hle
    exact (not_lt_of_ge hNle) hN
  rcases n with _ | n
  · have hmass_zero_real : (mass 0).toReal = 0 := by
      simpa [hmass_one_zero] using hzero_real.symm
    rcases (ENNReal.toReal_eq_zero_iff (mass 0)).1 hmass_zero_real with hzero0 | htop0
    · exact hzero0
    · exact False.elim (hmass_ne_top 0 htop0)
  · simpa [mass, hmass_one_zero] using hconst (n + 1) (Nat.succ_pos _)

/-- Helper for Remark 17.31: at the critical parameter `r = 1 / 2`, no state of Fig. 17.2 can be
positive recurrent. -/
private theorem figure17_2_not_positiveRecurrentState_of_eq_half
    (hr : (r : ENNReal) = 1 / 2) (x : ℕ) :
    ¬ IsPositiveRecurrentState P X x := by
  intro hx
  have hx_owner : ProbabilityTheory.IsPositiveRecurrentState P X x := by
    simpa [ProbabilityTheory.IsPositiveRecurrentState,
      ProbabilityTheory.expectedFirstReturnTime,
      DiscreteMarkovChain.IsPositiveRecurrentState,
      DiscreteMarkovChain.expectedFirstReturnTime] using hx
  obtain ⟨π, hπinv, hπx⟩ :=
    ProbabilityTheory.existsInvariantDistributionAtPositiveRecurrentState
      (κ := fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n)
      (P := P) (X := X) x hx_owner
  have hπinv_one :
      Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
        (π : Measure ℕ) := by
    simpa [pow_one] using hπinv
  have hzero :
      (π : Measure ℕ) ({x} : Set ℕ) = 0 :=
    figure17_2_invariantDistribution_singleton_eq_zero_of_eq_half
      (r := r) hr π hπinv_one x
  exact hπx.ne' hzero

/-- Helper for Remark 17.31: when `0 < r < 1`, the Fig. 17.2 chain communicates between any two
states by following a monotone path. -/
private theorem figure17_2_isIrreducible
    (hr0 : 0 < (r : ENNReal)) (hr1 : (r : ENNReal) < 1) :
    ProbabilityTheory.IsIrreducibleMarkovChain P X := by
  intro x y
  by_cases hxy : x = y
  · subst hxy
    have hforward :
        0 <
          ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) x) ({x + 1} : Set ℕ) := by
      -- Proof comment: every state has a one-step right move with positive mass when `r > 0`.
      simpa using figure17_2_rightPathStepMass_pos (r := r) hr0 x 1
    have hback :
        0 <
          (discreteMatrixKernel (figure17_2TransitionMatrix r) (x + 1)) ({x} : Set ℕ) := by
      -- Proof comment: from `x + 1` there is a one-step left move back to `x` whenever `r < 1`.
      simpa [pow_one, Nat.add_comm] using figure17_2_leftPathStepMass_pos (r := r) hr1 x 1
    have hstep :
        0 <
          ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 2) x) ({x} : Set ℕ) := by
      -- Proof comment: concatenating the positive right move with the positive left move yields a
      -- concrete two-step return path to `x`.
      simpa [pow_one] using
        figure17_2_discreteKernel_singleton_pos_succ
          (r := r) (n := 1) (x := x) (y := x + 1) (z := x) hforward hback
    exact
      figure17_2_everHitsProbability_pos_of_posStepMass
        (r := r) (P := P) (X := X) (by simp) hstep
  · by_cases hxy_lt : x < y
    · -- Proof comment: if `x < y`, a finite right-moving path reaches `y` with positive mass.
      exact figure17_2_everHitsProbability_fromBelow_pos
        (r := r) (P := P) (X := X) hr0 hxy_lt
    · have hyx_lt : y < x := lt_of_le_of_ne (Nat.le_of_not_gt hxy_lt) (Ne.symm hxy)
      have hstep :
          0 <
            ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ (x - y)) x) ({y} : Set ℕ) := by
        -- Proof comment: if `y < x`, follow the monotone left-moving path from `x` down to `y`.
        simpa [Nat.add_sub_of_le hyx_lt.le] using
          figure17_2_leftPathStepMass_pos (r := r) hr1 y (x - y)
      exact
        figure17_2_everHitsProbability_pos_of_posStepMass
          (r := r) (P := P) (X := X) (Nat.sub_pos_of_lt hyx_lt) hstep

/-- Helper for Remark 17.31: once state `0` is recurrent in the irreducible regime `0 < r < 1`,
Theorem 17.35 transports recurrence to every state. -/
private theorem figure17_2_allStatesRecurrent_of_zero_recurrent
    (hr0 : 0 < (r : ENNReal)) (hr1 : (r : ENNReal) < 1)
    (hzero : IsRecurrentState P X 0) :
    ∀ x : ℕ, IsRecurrentState P X x := by
  have hirr : ProbabilityTheory.IsIrreducibleMarkovChain P X :=
    figure17_2_isIrreducible (r := r) (P := P) (X := X) hr0 hr1
  have hzero_owner : ProbabilityTheory.IsRecurrentState P X 0 := by
    simpa [ProbabilityTheory.IsRecurrentState, DiscreteMarkovChain.IsRecurrentState] using hzero
  intro x
  have hx_owner : ProbabilityTheory.IsRecurrentState P X x :=
    ProbabilityTheory.isRecurrentState_of_isRecurrentState_of_everHitsProbability_pos
      (κ := fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n)
      (P := P) (X := X) hzero_owner (hirr 0 x)
  -- Proof comment: the imported communication theorem already works on the owner recurrence API,
  -- so only the local-to-owner predicate spelling needs to be rewritten here.
  simpa [ProbabilityTheory.IsRecurrentState, DiscreteMarkovChain.IsRecurrentState] using hx_owner

/-- Helper for Remark 17.31: once state `0` is transient in the irreducible regime `0 < r < 1`,
Theorem 17.37 forces every state to be transient. -/
private theorem figure17_2_allStatesTransient_of_zero_transient
    (hr0 : 0 < (r : ENNReal)) (hr1 : (r : ENNReal) < 1)
    (hzero : IsTransientState P X 0) :
    ∀ x : ℕ, IsTransientState P X x := by
  have hirr : ProbabilityTheory.IsIrreducibleMarkovChain P X :=
    figure17_2_isIrreducible (r := r) (P := P) (X := X) hr0 hr1
  rcases ProbabilityTheory.irreducibleMarkovChain_recurrent_or_transient
      (p := figure17_2TransitionMatrix r) (P := P) (X := X) hirr with hrec | htrans
  · have hzero_owner : ProbabilityTheory.IsTransientState P X 0 := by
      simpa [ProbabilityTheory.IsTransientState, DiscreteMarkovChain.IsTransientState] using hzero
    have hnot_zero_transient : ¬ ProbabilityTheory.IsTransientState P X 0 := by
      rw [ProbabilityTheory.IsTransientState, hrec 0]
      simp
    exact False.elim (hnot_zero_transient hzero_owner)
  · intro x
    -- Proof comment: in the transient branch of Theorem 17.37, the imported owner predicate is
    -- already exactly the local transient statement after unfolding the definitions.
    simpa [ProbabilityTheory.IsTransientState, DiscreteMarkovChain.IsTransientState] using htrans x

/-- Helper for Remark 17.31: at `r = 1`, the Fig. 17.2 chain moves deterministically one step to
the right. -/
private theorem figure17_2_oneStepLaw_eq_dirac_of_eq_one
    (hr : (r : ENNReal) = 1) (x : ℕ) :
    discreteMatrixKernel (figure17_2TransitionMatrix r) x = Measure.dirac (x + 1) := by
  -- Proof comment: the row of the transition matrix has a single nonzero entry at `x + 1`.
  rw [Measure.ext_iff_singleton]
  intro y
  rw [figure17_2_discreteMatrixKernel_apply_singleton]
  cases x with
  | zero =>
      by_cases hy : y = 1
      · subst hy
        simp [figure17_2TransitionMatrix, hr]
      · simp [figure17_2TransitionMatrix, hr, hy]
  | succ n =>
      by_cases hy : y = n + 2
      · subst hy
        simp [figure17_2TransitionMatrix, hr]
      · simp [figure17_2TransitionMatrix, hr, hy]

/-- Helper for Remark 17.31: at `r = 1`, every deterministic-time law is a Dirac mass on the
state reached by repeatedly moving one step to the right. -/
private theorem figure17_2_powLaw_eq_dirac_of_eq_one
    (hr : (r : ENNReal) = 1) (x n : ℕ) :
    (discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) x = Measure.dirac (x + n) := by
  induction n generalizing x with
  | zero =>
      -- Proof comment: the zero-step law is the identity kernel, hence the Dirac mass at `x`.
      rw [pow_zero]
      rw [Measure.ext_iff_singleton]
      intro y
      simpa using
        congrArg (fun μ : Measure ℕ ↦ μ ({y} : Set ℕ)) (Kernel.id_apply x)
  | succ n ih =>
      -- Proof comment: one more kernel step from the inductive Dirac state uses the already
      -- identified deterministic one-step law.
      rw [Measure.ext_iff_singleton]
      intro y
      rw [Kernel.pow_succ_apply_eq_lintegral _ n x (measurableSet_singleton y)]
      rw [ih]
      simpa [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y),
        Nat.add_assoc] using
        congrArg (fun μ : Measure ℕ ↦ μ ({y} : Set ℕ))
          (figure17_2_oneStepLaw_eq_dirac_of_eq_one (r := r) hr (x + n))

/-- Helper for Remark 17.31: at `r = 1`, every state is transient because the chain never returns
after moving strictly to the right. -/
private theorem figure17_2_allStatesTransient_of_eq_one
    (hr : (r : ENNReal) = 1) :
    ∀ x : ℕ, IsTransientState P X x := by
  intro x
  rw [IsTransientState, everHitsProbability_def]
  have hUnion :
      {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = ⋃ n : ℕ, {ω | X n.succ ω = x} := by
    ext ω
    constructor
    · rintro ⟨n, hn, hnx⟩
      rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨m, rfl⟩
      exact Set.mem_iUnion.2 ⟨m, by simpa using hnx⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      exact ⟨n.succ, Nat.succ_pos _, by simpa using hn⟩
  have hslice_zero : ∀ n : ℕ, (P x : Measure Ω) {ω | X n.succ ω = x} = 0 := by
    intro n
    let hReal :
        IsMarkovProcessRealization
          (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
    have hpreimage : {ω | X n.succ ω = x} = X n.succ ⁻¹' ({x} : Set ℕ) := by
      ext ω
      simp
    rw [hpreimage]
    rw [← Measure.map_apply (hReal.measurable_process n.succ) (measurableSet_singleton x)]
    rw [hReal.transition_eq x n.succ]
    rw [figure17_2_powLaw_eq_dirac_of_eq_one (r := r) hr x n.succ]
    simp
  have hhit_zero :
      (P x : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = 0 := by
    rw [hUnion]
    refine measure_iUnion_null ?_
    intro n
    exact hslice_zero n
  -- Proof comment: every positive-time return slice has zero mass, so the ever-return event has
  -- probability `0`, which is certainly `< 1`.
  simp [Measure.real_def, hhit_zero]

/-- Helper for Remark 17.31: in the right-drift regime, the finite no-hit probabilities dominate
the harmonic profile `1 - q^k` with `q = (1 - r) / r`. -/
private theorem figure17_2_noHitHorizon_real_lowerBound_of_half_lt
    (hrhalf : 1 / 2 < (r : ENNReal)) (hr1 : (r : ENNReal) < 1) :
    ∀ k M : ℕ,
      1 - (((1 - ((r : ENNReal).toReal)) / ((r : ENNReal).toReal)) : ℝ) ^ k ≤
        (P k : Measure Ω).real (noHitHorizonLocal X 0 0 M) := by
  let ρ : ℝ := (r : ENNReal).toReal
  let q : ℝ := (1 - ρ) / ρ
  have hr_top : (r : ENNReal) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt r.2.2 (by simp))
  have hρ_gt_half : (1 / 2 : ℝ) < ρ := by
    simpa [ρ] using (ENNReal.toReal_lt_toReal (by simp) hr_top).2 hrhalf
  have hρ_pos : 0 < ρ := by
    linarith
  have hρ_lt_one : ρ < 1 := by
    simpa [ρ] using (ENNReal.toReal_lt_toReal hr_top ENNReal.one_ne_top).2 hr1
  have hρ_nonneg : 0 ≤ ρ := le_of_lt hρ_pos
  have hone_sub_nonneg : 0 ≤ 1 - ρ := sub_nonneg.mpr hρ_lt_one.le
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hone_sub_nonneg hρ_nonneg
  have hq_lt_one : q < 1 := by
    have hnum_lt : 1 - ρ < ρ := by
      linarith
    dsimp [q]
    have hρ_ne : ρ ≠ 0 := ne_of_gt hρ_pos
    field_simp [hρ_ne]
    linarith
  have hqmul : q * ρ = 1 - ρ := by
    dsimp [q]
    field_simp [hρ_pos.ne]
  have hstep_one :
      ρ * (1 - q ^ 2) = 1 - q := by
    have hqq : ρ * q ^ 2 = q * (1 - ρ) := by
      calc
        ρ * q ^ 2 = (q * ρ) * q := by ring
        _ = (1 - ρ) * q := by rw [hqmul]
        _ = q * (1 - ρ) := by ring
    calc
      ρ * (1 - q ^ 2) = ρ - ρ * q ^ 2 := by ring
      _ = ρ - q * (1 - ρ) := by rw [hqq]
      _ = ρ - q + q * ρ := by ring
      _ = 1 - q := by linarith [hqmul]
  have hstep_succ :
      ∀ n : ℕ,
        (1 - q ^ (n + 1)) * (1 - ρ) + (1 - q ^ (n + 3)) * ρ = 1 - q ^ (n + 2) := by
    intro n
    have hcoeff :
        (1 - ρ) + ρ * q ^ 2 = q := by
      calc
        (1 - ρ) + ρ * q ^ 2 = q * ρ + ρ * q ^ 2 := by rw [hqmul]
        _ = q * (ρ + ρ * q) := by ring
        _ = q * 1 := by
              have hone : ρ + ρ * q = 1 := by
                linarith [hqmul]
              rw [hone]
        _ = q := by ring
    have hpow :
        q ^ (n + 3) = q ^ (n + 1) * q ^ 2 := by
      rw [show n + 3 = (n + 1) + 2 by omega, pow_add]
    calc
      (1 - q ^ (n + 1)) * (1 - ρ) + (1 - q ^ (n + 3)) * ρ
          = (1 - ρ) + ρ - ((1 - ρ) * q ^ (n + 1) + ρ * q ^ (n + 3)) := by ring
      _ = 1 - ((1 - ρ) * q ^ (n + 1) + ρ * q ^ (n + 3)) := by linarith
      _ = 1 - (q ^ (n + 1) * ((1 - ρ) + ρ * q ^ 2)) := by
            rw [hpow]
            ring
      _ = 1 - (q ^ (n + 1) * q) := by rw [hcoeff]
      _ = 1 - q ^ (n + 2) := by
            rw [show n + 2 = (n + 1) + 1 by omega, pow_add]
            ring
  intro k M
  change 1 - q ^ k ≤ (P k : Measure Ω).real (noHitHorizonLocal X 0 0 M)
  induction M generalizing k with
  | zero =>
      have hbase : (P k : Measure Ω).real (noHitHorizonLocal X 0 0 0) = 1 := by
        have hset : noHitHorizonLocal X 0 0 0 = Set.univ := by
          ext ω
          constructor
          · intro _
            simp
          · intro _
            intro m hm1 hm0 hmEq
            omega
        simp [Measure.real_def, hset]
      rw [hbase]
      exact sub_le_self _ (pow_nonneg hq_nonneg k)
  | succ M ih =>
      cases k with
      | zero =>
          -- Proof comment: the state `0` case only needs the trivial nonnegativity lower bound
          -- because `1 - q^0 = 0`.
          simpa [q] using
            (measureReal_nonneg (μ := (P 0 : Measure Ω))
              (s := noHitHorizonLocal X 0 0 (M + 1)))
      | succ k =>
          cases k with
          | zero =>
              have hstep :
                  (P 1 : Measure Ω).real (noHitHorizonLocal X 0 0 (M + 1)) =
                    (P 2 : Measure Ω).real (noHitHorizonLocal X 0 0 M) * ρ := by
                simpa [ρ, Measure.real_def, ENNReal.toReal_mul, hr_top, measure_ne_top _ _] using
                  congrArg ENNReal.toReal
                    (figure17_2_noHitHorizon_step_one (r := r) (P := P) (X := X) M)
              have hmul :
                  ρ * (1 - q ^ 2) ≤
                    (P 2 : Measure Ω).real (noHitHorizonLocal X 0 0 M) * ρ := by
                simpa [mul_comm] using mul_le_mul_of_nonneg_right (ih 2) hρ_nonneg
              calc
                1 - q ^ (0 + 1) = ρ * (1 - q ^ 2) := by simpa using hstep_one.symm
                _ ≤ (P 2 : Measure Ω).real (noHitHorizonLocal X 0 0 M) * ρ := hmul
                _ = (P 1 : Measure Ω).real (noHitHorizonLocal X 0 0 (M + 1)) := hstep.symm
          | succ n =>
              have hleft_ne_top :
                  (P (n + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (1 - (r : ENNReal)) ≠ ⊤ :=
                ENNReal.mul_ne_top (measure_ne_top _ _) (by simp [hr_top])
              have hright_ne_top :
                  (P (n + 3) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (r : ENNReal) ≠ ⊤ :=
                ENNReal.mul_ne_top (measure_ne_top _ _) hr_top
              have hstep :
                  (P (n + 2) : Measure Ω).real (noHitHorizonLocal X 0 0 (M + 1)) =
                    (P (n + 1) : Measure Ω).real (noHitHorizonLocal X 0 0 M) * (1 - ρ) +
                      (P (n + 3) : Measure Ω).real (noHitHorizonLocal X 0 0 M) * ρ := by
                have hstep' := congrArg ENNReal.toReal
                  (figure17_2_noHitHorizon_step_succ (r := r) (P := P) (X := X) n M)
                rw [ENNReal.toReal_add hleft_ne_top hright_ne_top, ENNReal.toReal_mul,
                  ENNReal.toReal_mul] at hstep'
                rw [ENNReal.toReal_sub_of_le r.2.2 (by simp)] at hstep'
                simpa [ρ, Measure.real_def, measure_ne_top _ _] using hstep'
              have hmul1 :
                  (1 - q ^ (n + 1)) * (1 - ρ) ≤
                    (P (n + 1) : Measure Ω).real (noHitHorizonLocal X 0 0 M) * (1 - ρ) := by
                exact mul_le_mul_of_nonneg_right (ih (n + 1)) hone_sub_nonneg
              have hmul2 :
                  (1 - q ^ (n + 3)) * ρ ≤
                    (P (n + 3) : Measure Ω).real (noHitHorizonLocal X 0 0 M) * ρ := by
                exact mul_le_mul_of_nonneg_right (ih (n + 3)) hρ_nonneg
              calc
                1 - q ^ (n + 2) =
                    (1 - q ^ (n + 1)) * (1 - ρ) + (1 - q ^ (n + 3)) * ρ := by
                      symm
                      exact hstep_succ n
                _ ≤ (P (n + 1) : Measure Ω).real (noHitHorizonLocal X 0 0 M) * (1 - ρ) +
                      (P (n + 3) : Measure Ω).real (noHitHorizonLocal X 0 0 M) * ρ :=
                      add_le_add hmul1 hmul2
                _ = (P (n + 2) : Measure Ω).real (noHitHorizonLocal X 0 0 (M + 1)) :=
                    hstep.symm

/-- Helper for Remark 17.31: in the right-drift regime `1 / 2 < r < 1`, the remaining blocker is
the anchor estimate showing that state `0` does not return almost surely. -/
private theorem figure17_2_zero_transient_of_half_lt
    (hrhalf : 1 / 2 < (r : ENNReal)) (hr1 : (r : ENNReal) < 1) :
    IsTransientState P X 0 := by
  let ρ : ℝ := (r : ENNReal).toReal
  let q : ℝ := (1 - ρ) / ρ
  let μ1 : Measure Ω := P 1
  let hitWithin : ℕ → Set Ω := fun M ↦ {ω | ∃ n ∈ Set.Icc 1 M, X n ω = 0}
  have hr_top : (r : ENNReal) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt r.2.2 (by simp))
  have hρ_lt_one : ρ < 1 := by
    simpa [ρ] using (ENNReal.toReal_lt_toReal hr_top ENNReal.one_ne_top).2 hr1
  have hρ_gt_half : (1 / 2 : ℝ) < ρ := by
    simpa [ρ] using (ENNReal.toReal_lt_toReal (by simp) hr_top).2 hrhalf
  have hρ_pos : 0 < ρ := by
    linarith
  have hq_lt_one : q < 1 := by
    have hnum_lt : 1 - ρ < ρ := by
      linarith
    dsimp [q]
    have hρ_ne : ρ ≠ 0 := ne_of_gt hρ_pos
    field_simp [hρ_ne]
    linarith
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (sub_nonneg.mpr hρ_lt_one.le) hρ_pos.le
  have hnohit_lower :
      ∀ k M : ℕ, 1 - q ^ k ≤ (P k : Measure Ω).real (noHitHorizonLocal X 0 0 M) :=
    figure17_2_noHitHorizon_real_lowerBound_of_half_lt
      (r := r) (P := P) (X := X) hrhalf hr1
  have hhitWithin_bound : ∀ M : ℕ, μ1.real (hitWithin M) ≤ q := by
    intro M
    have hprob :
        μ1.real (hitWithin M) = 1 - μ1.real (noHitHorizonLocal X 0 0 M) := by
      have hEq : hitWithin M = (noHitHorizonLocal X 0 0 M)ᶜ := by
        ext ω
        constructor
        · intro hω hnohit
          rcases hω with ⟨n, hn, hnx⟩
          exact (hnohit n hn.1 hn.2 (by simpa [zero_add] using hnx)).elim
        · intro hω
          by_contra hhit
          exact hω <| by
            intro n hn1 hnM hnEq
            exact hhit ⟨n, ⟨hn1, hnM⟩, by simpa [zero_add] using hnEq⟩
      rw [hEq, probReal_compl_eq_one_sub (μ := μ1)]
      exact
        figure17_2_measurableSet_noHitHorizon (X := X)
          ((inferInstance : IsMarkovProcessRealization
            (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X).measurable_process)
          0 0 M
    have hlower : 1 - q ≤ μ1.real (noHitHorizonLocal X 0 0 M) := by
      simpa [q] using hnohit_lower 1 M
    rw [hprob]
    nlinarith
  have hUnion : {ω | ∃ n : ℕ, 0 < n ∧ X n ω = 0} = ⋃ M : ℕ, hitWithin M := by
    ext ω
    constructor
    · rintro ⟨n, hn, hnx⟩
      exact Set.mem_iUnion.2 ⟨n, ⟨n, ⟨by simpa using hn, le_rfl⟩, hnx⟩⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨M, hM⟩
      rcases hM with ⟨n, hn, hnx⟩
      exact ⟨n, hn.1, hnx⟩
  have hmono : Directed (· ⊆ ·) hitWithin := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · intro ω hω
      rcases hω with ⟨n, hn, hnx⟩
      exact ⟨n, ⟨hn.1, le_trans hn.2 (le_max_left _ _)⟩, hnx⟩
    · intro ω hω
      rcases hω with ⟨n, hn, hnx⟩
      exact ⟨n, ⟨hn.1, le_trans hn.2 (le_max_right _ _)⟩, hnx⟩
  have hμ1 :
      μ1 (⋃ M : ℕ, hitWithin M) = ⨆ M : ℕ, μ1 (hitWithin M) := hmono.measure_iUnion
  have hiSup_ne_top : (⨆ M : ℕ, μ1 (hitWithin M)) ≠ ⊤ := by
    apply ne_of_lt
    calc
      ⨆ M : ℕ, μ1 (hitWithin M) = μ1 (⋃ M : ℕ, hitWithin M) := hμ1.symm
      _ ≤ μ1 Set.univ := measure_mono (by intro ω hω; simp)
      _ = 1 := by simp [μ1]
      _ < ⊤ := by simp
  have hsup_le :
      ⨆ M : ℕ, μ1 (hitWithin M) ≤ ENNReal.ofReal q := by
    refine iSup_le fun M ↦ ?_
    have hboundReal :
        (μ1 (hitWithin M)).toReal ≤ (ENNReal.ofReal q).toReal := by
      simpa [Measure.real_def, ENNReal.toReal_ofReal hq_nonneg] using hhitWithin_bound M
    exact
      (ENNReal.toReal_le_toReal (measure_ne_top μ1 _) ENNReal.ofReal_ne_top).1 hboundReal
  have hhit_one_zero_le_q : (F[P, X]) 1 0 ≤ q := by
    rw [everHitsProbability_def, hUnion, Measure.real_def, hμ1]
    simpa [ENNReal.toReal_ofReal hq_nonneg] using
      (ENNReal.toReal_le_toReal hiSup_ne_top ENNReal.ofReal_ne_top).2 hsup_le
  have hhit_one_zero_lt_one : (F[P, X]) 1 0 < 1 := lt_of_le_of_lt hhit_one_zero_le_q hq_lt_one
  have hreturn_lt_one : (F[P, X]) 0 0 < 1 := by
    rw [figure17_2_returnProbability_zero_eq_hitProbability_one_zero (r := r) (P := P) (X := X)]
    exact hhit_one_zero_lt_one
  -- Proof comment: the right-drift lower bound leaves uniformly positive mass on the no-hit tail,
  -- so the return probability of `0` is strictly smaller than `1`.
  simpa [IsTransientState] using hreturn_lt_one

/-- Helper for Remark 17.31: the diagonal Green value splits into the deterministic time-`0`
visit and the positive-time tail. -/
private theorem figure17_2_greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf
    (r : Set.Icc (0 : ENNReal) 1)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) P X]
    (x : ℕ) :
    (G[P, X]) x x = 1 + (G[P, X; 1]) x x := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  have hzero :
      (P x : Measure Ω) {ω | X 0 ω = x} = 1 := by
    have hpreimage : {ω | X 0 ω = x} = X 0 ⁻¹' ({x} : Set ℕ) := by
      ext ω
      simp
    -- Proof comment: under `P x`, the Fig. 17.2 chain starts from `x` almost surely.
    calc
      (P x : Measure Ω) {ω | X 0 ω = x}
          = ((P x : Measure Ω).map (X 0)) ({x} : Set ℕ) := by
              simpa [hpreimage] using
                (Measure.map_apply
                  (μ := (P x : Measure Ω))
                  (f := X 0)
                  (s := ({x} : Set ℕ))
                  (hReal.measurable_process 0)
                  (MeasurableSet.singleton x)).symm
      _ = Measure.dirac x ({x} : Set ℕ) := by
            simpa using congrArg (fun μ : Measure ℕ ↦ μ ({x} : Set ℕ)) (hReal.initial_eq x)
      _ = 1 := by
            simp
  -- Proof comment: isolate the time-`0` summand in the Green series and rewrite the remaining
  -- positive-time part through the standard `G[P, X; 1]` normalization.
  calc
    (G[P, X]) x x = ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = x} := by
      rw [greenFunction_eq_tsum_stateProbabilities P X hX x x]
    _ = (P x : Measure Ω) {ω | X 0 ω = x} +
          ∑' n : ℕ, ite (n = 0) 0 ((P x : Measure Ω) {ω | X n ω = x}) := by
            classical
            have hsplit :
                ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = x} =
                  (P x : Measure Ω) {ω | X 0 ω = x} +
                    ∑' n : ℕ,
                      @ite ℝ≥0∞ (n = 0) (Classical.propDecidable (n = 0)) 0
                        ((P x : Measure Ω) {ω | X n ω = x}) := by
                  exact ENNReal.tsum_eq_add_tsum_ite
                    (f := fun n : ℕ ↦ (P x : Measure Ω) {ω | X n ω = x}) 0
            calc
              ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = x} =
                  (P x : Measure Ω) {ω | X 0 ω = x} +
                    ∑' n : ℕ,
                      @ite ℝ≥0∞ (n = 0) (Classical.propDecidable (n = 0)) 0
                        ((P x : Measure Ω) {ω | X n ω = x}) := hsplit
              _ = (P x : Measure Ω) {ω | X 0 ω = x} +
                    ∑' n : ℕ, ite (n = 0) 0 ((P x : Measure Ω) {ω | X n ω = x}) := by
                      congr 1
                      refine tsum_congr fun n ↦ ?_
                      by_cases hn : n = 0
                      · simp [hn]
                      · simp [hn]
    _ = 1 + ∑' n : ℕ, ite (n = 0) 0 ((P x : Measure Ω) {ω | X n ω = x}) := by
          simp [hzero]
    _ = 1 + ∑' n : ℕ, (P x : Measure Ω) {ω | 0 < n ∧ X n ω = x} := by
          congr 1
          refine tsum_congr fun n ↦ ?_
          by_cases hn : n = 0
          · subst hn
            simp
          · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
            simp [hn, hnpos]
    _ = 1 + (G[P, X; 1]) x x := by
          rw [greenFunctionFrom_one_eq_tsum_positiveStateProbabilities P X hX x x]

/-- Helper for Remark 17.31: the strictly positive visit times of the path `ω` at the state
`x`. -/
private def positiveVisitSet (Y : ℕ → Ω → ℕ) (x : ℕ) (ω : Ω) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ Y n ω = x}

/-- Helper for Remark 17.31: a bound on the infimum of a set of natural times in `ℕ∞` is
equivalent to a bounded witness in the underlying set. -/
private lemma sInf_natImage_le_iff {S : Set ℕ} {N : ℕ} :
    sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) ≤ N ↔ ∃ n ∈ S, n ≤ N := by
  -- Proof comment: once `S` is nonempty, the `ℕ∞` infimum is the least witness in `S`; if `S`
  -- is empty, the infimum is `⊤`, so neither side can hold.
  by_cases hS : S.Nonempty
  · let m : ℕ := sInf S
    have hsInf : sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) = ((m : ℕ) : ℕ∞) := by
      simpa [m] using (WithTop.coe_sInf' hS (OrderBot.bddBelow S)).symm
    constructor
    · intro h
      refine ⟨m, ?_, ?_⟩
      · simpa [m] using Nat.sInf_mem hS
      · have hsInf_leN : ((m : ℕ) : ℕ∞) ≤ N := by
          simpa [hsInf] using h
        exact_mod_cast hsInf_leN
    · rintro ⟨n, hnS, hnN⟩
      have hm_le : m ≤ n := by
        simpa [m] using (Nat.sInf_le hnS)
      have hm_le' : (m : ℕ∞) ≤ n := by
        exact_mod_cast hm_le
      have hm_leN : ((m : ℕ) : ℕ∞) ≤ N := hm_le'.trans (by exact_mod_cast hnN)
      simpa [hsInf] using hm_leN
  · have hS_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    subst hS_empty
    simp

/-- Helper for Remark 17.31: the successor entrance time is bounded by `N` exactly when there is
a visit to `x` by time `N` strictly after the previous entrance. -/
private lemma iteratedEntranceTime_succ_le_iff_exists_hitAfter
    (Y : ℕ → Ω → ℕ) (x : ℕ) (ω : Ω) (k : ℕ+) (N : ℕ) :
    (τ_[Y, x]^(k + 1)) ω ≤ N ↔ ∃ n : ℕ, (τ_[Y, x]^k) ω < n ∧ n ≤ N ∧ Y n ω = x := by
  -- Proof comment: unfold the recursive successor step and replace the `sInf` bound by a bounded
  -- future hit witness.
  rw [iteratedEntranceTime_succ]
  rw [sInf_natImage_le_iff]
  constructor
  · rintro ⟨n, hn, hnN⟩
    exact ⟨n, hn.1, hnN, hn.2⟩
  · rintro ⟨n, hτ, hnN, hx⟩
    exact ⟨n, ⟨hτ, hx⟩, hnN⟩

/-- Helper for Remark 17.31: `prefixHasIteratedReturn x k m f` records `k` strictly positive
visits to `x` inside the finite prefix `f : Fin m → ℕ`. -/
private def prefixHasIteratedReturn (x : ℕ) : ℕ+ → ∀ m : ℕ, (Fin m → ℕ) → Prop
  := fun k =>
    PNat.recOn k
      (fun m f => ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = x)
      (fun _ ih m f =>
        ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = x ∧
          ih i (fun j : Fin i ↦ f ⟨j, Nat.lt_trans j.2 i.2⟩))

/-- Helper for Remark 17.31: unfold `prefixHasIteratedReturn` at the first positive index. -/
private lemma prefixHasIteratedReturn_one_iff
    (x : ℕ) (m : ℕ) (f : Fin m → ℕ) :
    prefixHasIteratedReturn x 1 m f ↔ ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = x := by
  simp [prefixHasIteratedReturn]

/-- Helper for Remark 17.31: unfold `prefixHasIteratedReturn` at a successor positive index. -/
private lemma prefixHasIteratedReturn_succ_iff
    (x : ℕ) (k : ℕ+) (m : ℕ) (f : Fin m → ℕ) :
    prefixHasIteratedReturn x (k + 1) m f ↔
      ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = x ∧
        prefixHasIteratedReturn x k i (fun j : Fin i ↦ f ⟨j, Nat.lt_trans j.2 i.2⟩) := by
  simp [prefixHasIteratedReturn]

/-- Helper for Remark 17.31: the bounded event `τ_[Y, x]^k < m` is exactly the recursive
finite-prefix predicate on the first `m` coordinates of the path. -/
private lemma iteratedEntranceTime_lt_iff_prefixHasIteratedReturn
    (Y : ℕ → Ω → ℕ) (x : ℕ) (ω : Ω) :
    ∀ (k : ℕ+) (m : ℕ),
      (τ_[Y, x]^k) ω < m ↔
        prefixHasIteratedReturn x k m (fun i : Fin m ↦ Y i ω) := by
  intro k
  induction k using PNat.recOn with
  | one =>
      intro m
      cases m with
      | zero =>
          constructor
          · intro h
            simpa using h
          · intro h
            rcases h with ⟨i, _, _⟩
            exact Fin.elim0 i
      | succ m =>
          -- Proof comment: the first entrance time is the usual positive-time hitting time, so
          -- the finite-prefix description is exactly `hittingAfter_lt_iff` at `{x}`.
          constructor
          · intro h
            have hhit :
                hittingAfter Y ({x} : Set ℕ) 1 ω < ↑(m + 1) := by
              simpa [iteratedEntranceTime_one] using h
            rcases (MeasureTheory.hittingAfter_lt_iff
              (u := Y) (s := ({x} : Set ℕ)) (n := 1) (ω := ω) (i := m + 1)).1 hhit with
              ⟨n, hn_mem, hn_eq⟩
            exact (prefixHasIteratedReturn_one_iff x (m + 1) (fun i : Fin (m + 1) ↦ Y i ω)).2
              ⟨⟨n, hn_mem.2⟩, by simpa using hn_mem.1,
                by simpa [Set.mem_singleton_iff] using hn_eq⟩
          · intro h
            rcases (prefixHasIteratedReturn_one_iff x (m + 1) (fun i : Fin (m + 1) ↦ Y i ω)).1 h
              with ⟨i, hi_pos, hi_eq⟩
            have hhit :
                hittingAfter Y ({x} : Set ℕ) 1 ω < ↑(m + 1) := by
              exact (MeasureTheory.hittingAfter_lt_iff
                (u := Y) (s := ({x} : Set ℕ)) (n := 1) (ω := ω) (i := m + 1)).2
                ⟨i, ⟨by simpa using hi_pos, i.2⟩, by simpa [Set.mem_singleton_iff] using hi_eq⟩
            simpa [iteratedEntranceTime_one] using hhit
  | succ k ih =>
      intro m
      cases m with
      | zero =>
          constructor
          · intro h
            simpa using h
          · intro h
            rcases (prefixHasIteratedReturn_succ_iff x k 0 (fun i : Fin 0 ↦ Y i ω)).1 h with
              ⟨i, _, _, _⟩
            exact Fin.elim0 i
      | succ m =>
          have hbound :
              (τ_[Y, x]^(k + 1)) ω < ↑(m + 1) ↔ (τ_[Y, x]^(k + 1)) ω ≤ m := by
            simpa using
              (ENat.lt_coe_add_one_iff (m := (τ_[Y, x]^(k + 1)) ω) (n := m))
          constructor
          · intro h
            have hle : (τ_[Y, x]^(k + 1)) ω ≤ m := hbound.mp h
            rcases (iteratedEntranceTime_succ_le_iff_exists_hitAfter
              (Y := Y) (x := x) (ω := ω) (k := k) (N := m)).1 hle with
              ⟨n, hτn, hn_le, hn_eq⟩
            have hn_pos : 0 < n := by
              by_contra hn_zero
              have hn_eq_zero : n = 0 := Nat.eq_zero_of_not_pos hn_zero
              have : ¬ (τ_[Y, x]^k) ω < (0 : ℕ) := by simp
              exact this (by simpa [hn_eq_zero] using hτn)
            exact (prefixHasIteratedReturn_succ_iff x k (m + 1)
              (fun i : Fin (m + 1) ↦ Y i ω)).2
              ⟨⟨n, Nat.lt_succ_iff.mpr hn_le⟩, by simpa using hn_pos,
                by simpa using hn_eq, (ih n).1 hτn⟩
          · intro h
            rcases (prefixHasIteratedReturn_succ_iff x k (m + 1)
              (fun i : Fin (m + 1) ↦ Y i ω)).1 h with
              ⟨i, hi_pos, hi_eq, hi_prefix⟩
            have hle : (τ_[Y, x]^(k + 1)) ω ≤ m := by
              exact (iteratedEntranceTime_succ_le_iff_exists_hitAfter
                (Y := Y) (x := x) (ω := ω) (k := k) (N := m)).2
                ⟨i, (ih i).2 hi_prefix, Nat.le_of_lt_succ i.2, by simpa using hi_eq⟩
            exact hbound.mpr hle

/-- Helper for Remark 17.31: the recursive finite-prefix witness forces at least the
corresponding number of positive visits in that prefix. -/
private lemma prefixHasIteratedReturn_le_card
    (x : ℕ) :
    ∀ {k : ℕ+} {m : ℕ} {f : Fin m → ℕ},
      prefixHasIteratedReturn x k m f →
        (k : ℕ) ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = x).card := by
  intro k
  induction k using PNat.recOn with
  | one =>
      intro m f h
      -- Proof comment: the base witness is itself one positive hit in the filtered prefix.
      rcases (prefixHasIteratedReturn_one_iff x m f).1 h with ⟨i, hi_pos, hi_eq⟩
      have hone : 1 ≤ (Finset.univ.filter fun j : Fin m ↦ 0 < (j : ℕ) ∧ f j = x).card := by
        rw [Finset.one_le_card]
        exact ⟨i, by simp [hi_pos, hi_eq]⟩
      simpa using hone
  | succ k ih =>
      intro m f h
      rcases (prefixHasIteratedReturn_succ_iff x k m f).1 h with ⟨i, hi_pos, hi_eq, hi_prefix⟩
      let s : Finset (Fin m) := Finset.univ.filter fun j : Fin m ↦ 0 < (j : ℕ) ∧ f j = x
      let t : Finset (Fin i) := Finset.univ.filter fun j : Fin i ↦
        0 < (j : ℕ) ∧ f ⟨j, Nat.lt_trans j.2 i.2⟩ = x
      have hi_mem : i ∈ s := by
        simp [s, hi_pos, hi_eq]
      have hk_le_t : (k : ℕ) ≤ t.card := ih hi_prefix
      have ht_le_erase : t.card ≤ (s.erase i).card := by
        refine Finset.card_le_card_of_injOn
          (fun j : Fin i ↦ (⟨(j : ℕ), Nat.lt_trans j.2 i.2⟩ : Fin m)) ?_ ?_
        · intro j hj
          have hj_props : 0 < (j : ℕ) ∧ f ⟨j, Nat.lt_trans j.2 i.2⟩ = x := by
            simpa [t] using hj
          refine Finset.mem_erase.2 ⟨?_, ?_⟩
          · intro hji
            exact (ne_of_lt j.2) (Fin.ext_iff.mp hji)
          · simp [s, hj_props]
        · intro a₁ ha₁ b hb hEq
          exact Fin.ext (congrArg (fun z : Fin m ↦ (z : ℕ)) hEq)
      have hk_le_erase : (k : ℕ) ≤ (s.erase i).card := le_trans hk_le_t ht_le_erase
      have hs_card : (s.erase i).card + 1 = s.card := Finset.card_erase_add_one hi_mem
      have hs_succ : (k : ℕ) + 1 ≤ s.card := by
        rw [← hs_card]
        exact Nat.succ_le_succ hk_le_erase
      simpa [s] using hs_succ

/-- Helper for Remark 17.31: inside a finite prefix, at least `k` positive visits force the
recursive prefix witness for the `k`th iterated return. -/
private lemma prefixHasIteratedReturn_of_le_card
    (x : ℕ) :
    ∀ {k : ℕ+} {m : ℕ} {f : Fin m → ℕ},
      (k : ℕ) ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = x).card →
        prefixHasIteratedReturn x k m f := by
  intro k
  induction k using PNat.recOn with
  | one =>
      intro m f h
      have h' : 1 ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = x).card := by
        simpa using h
      rw [Finset.one_le_card] at h'
      rcases h' with ⟨i, hi_mem⟩
      have hi_props : 0 < (i : ℕ) ∧ f i = x := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi_mem
      exact (prefixHasIteratedReturn_one_iff x m f).2 ⟨i, hi_props.1, hi_props.2⟩
  | succ k ih =>
      intro m f h
      -- Proof comment: remove the maximal positive hit from the filtered prefix and recurse on
      -- the earlier hits.
      let s : Finset (Fin m) := Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = x
      have hs_card_pos : 0 < s.card := by
        have hk_pos : 0 < ((k + 1 : ℕ+) : ℕ) := PNat.pos (k + 1)
        exact lt_of_lt_of_le hk_pos (by simpa [s] using h)
      have hs_nonempty : s.Nonempty := Finset.card_pos.mp hs_card_pos
      let i : Fin m := s.max' hs_nonempty
      have hi_mem : i ∈ s := Finset.max'_mem s hs_nonempty
      have hi_props : 0 < (i : ℕ) ∧ f i = x := by
        simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hi_mem
      let toInitialSegment : Fin m → Fin i :=
        fun j ↦ if hj : (j : ℕ) < i then ⟨(j : ℕ), hj⟩ else ⟨0, hi_props.1⟩
      let t : Finset (Fin i) := Finset.univ.filter fun j : Fin i ↦
        0 < (j : ℕ) ∧ f ⟨j, Nat.lt_trans j.2 i.2⟩ = x
      have hk_le_erase : (k : ℕ) ≤ (s.erase i).card := by
        have hk_succ : (k : ℕ) + 1 ≤ s.card := by
          simpa [s, Nat.succ_eq_add_one] using h
        have hs_card : (s.erase i).card + 1 = s.card := Finset.card_erase_add_one hi_mem
        have hk_succ' : Nat.succ (k : ℕ) ≤ Nat.succ (s.erase i).card := by
          simpa [hs_card, Nat.succ_eq_add_one] using hk_succ
        exact Nat.succ_le_succ_iff.mp hk_succ'
      have herase_le_t : (s.erase i).card ≤ t.card := by
        refine Finset.card_le_card_of_injOn toInitialSegment ?_ ?_
        · intro j hj
          have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
          have hj_mem : j ∈ s := (Finset.mem_erase.mp hj).2
          have hj_props : 0 < (j : ℕ) ∧ f j = x := by
            simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hj_mem
          have hj_le : j ≤ i := Finset.le_max' s j hj_mem
          have hj_lt : (j : ℕ) < i := by
            exact show (j : ℕ) < (i : ℕ) from
              lt_of_le_of_ne hj_le (fun hji ↦ hj_ne (Fin.ext hji))
          have hsegment : toInitialSegment j = ⟨(j : ℕ), hj_lt⟩ := by
            have hji : (j : ℕ) < i := hj_lt
            change
              (if h : (j : ℕ) < i then (⟨(j : ℕ), h⟩ : Fin i) else ⟨0, hi_props.1⟩) =
                ⟨(j : ℕ), hj_lt⟩
            rw [dif_pos hji]
          simp [t, hsegment, hj_props]
        · intro a₁ ha₁ b hb hEq
          have ha_ne : a₁ ≠ i := (Finset.mem_erase.mp ha₁).1
          have hb_ne : b ≠ i := (Finset.mem_erase.mp hb).1
          have ha_mem : a₁ ∈ s := (Finset.mem_erase.mp ha₁).2
          have hb_mem : b ∈ s := (Finset.mem_erase.mp hb).2
          have ha_le : a₁ ≤ i := Finset.le_max' s a₁ ha_mem
          have hb_le : b ≤ i := Finset.le_max' s b hb_mem
          have ha_lt : (a₁ : ℕ) < i := by
            exact show (a₁ : ℕ) < (i : ℕ) from
              lt_of_le_of_ne ha_le (fun hai ↦ ha_ne (Fin.ext hai))
          have hb_lt : (b : ℕ) < i := by
            exact show (b : ℕ) < (i : ℕ) from
              lt_of_le_of_ne hb_le (fun hbi ↦ hb_ne (Fin.ext hbi))
          have ha_seg : toInitialSegment a₁ = ⟨(a₁ : ℕ), ha_lt⟩ := by
            have ha' : (a₁ : ℕ) < i := ha_lt
            change
              (if h : (a₁ : ℕ) < i then (⟨(a₁ : ℕ), h⟩ : Fin i) else ⟨0, hi_props.1⟩) =
                ⟨(a₁ : ℕ), ha_lt⟩
            rw [dif_pos ha']
          have hb_seg : toInitialSegment b = ⟨(b : ℕ), hb_lt⟩ := by
            have hb' : (b : ℕ) < i := hb_lt
            change
              (if h : (b : ℕ) < i then (⟨(b : ℕ), h⟩ : Fin i) else ⟨0, hi_props.1⟩) =
                ⟨(b : ℕ), hb_lt⟩
            rw [dif_pos hb']
          have himage_eq : (⟨(a₁ : ℕ), ha_lt⟩ : Fin i) = ⟨(b : ℕ), hb_lt⟩ := by
            calc
              (⟨(a₁ : ℕ), ha_lt⟩ : Fin i) = toInitialSegment a₁ := by
                simpa using ha_seg.symm
              _ = toInitialSegment b := hEq
              _ = (⟨(b : ℕ), hb_lt⟩ : Fin i) := by
                simpa using hb_seg
          have hab_val : (a₁ : ℕ) = (b : ℕ) := by
            exact congrArg (fun z : Fin i ↦ (z : ℕ)) himage_eq
          exact Fin.ext hab_val
      have hk_le_t : (k : ℕ) ≤ t.card := le_trans hk_le_erase herase_le_t
      exact (prefixHasIteratedReturn_succ_iff x k m f).2 ⟨i, hi_props.1, hi_props.2, ih hk_le_t⟩

/-- Helper for Remark 17.31: the recursive finite-prefix witness is equivalent to requiring at
least `k` positive visits to `x` in that prefix. -/
private lemma prefixHasIteratedReturn_iff_prefixVisitCountAtLeast
    (x : ℕ) {k : ℕ+} {m : ℕ} {f : Fin m → ℕ} :
    prefixHasIteratedReturn x k m f ↔
      (k : ℕ) ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = x).card := by
  constructor
  · exact prefixHasIteratedReturn_le_card x
  · exact prefixHasIteratedReturn_of_le_card x

/-- Helper for Remark 17.31: the event `τ_[Y, x]^k < m` is equivalent to having at least `k`
positive visits to `x` in the first `m` coordinates of the path. -/
private lemma iteratedEntranceTime_lt_iff_prefixVisitCountAtLeast
    (Y : ℕ → Ω → ℕ) (x : ℕ) (ω : Ω) :
    ∀ (k : ℕ+) (m : ℕ),
      (τ_[Y, x]^k) ω < m ↔
        (k : ℕ) ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ Y i ω = x).card
  | k, m => by
      classical
      rw [iteratedEntranceTime_lt_iff_prefixHasIteratedReturn,
        prefixHasIteratedReturn_iff_prefixVisitCountAtLeast]

/-- Helper for Remark 17.31: the event `τ_[Y, x]^k ≤ N` is equivalent to having at least `k`
positive visits to `x` in the first `N + 1` coordinates of the path. -/
private lemma iteratedEntranceTime_le_iff_prefixVisitCountAtLeast
    (Y : ℕ → Ω → ℕ) (x : ℕ) (ω : Ω) :
    ∀ (k : ℕ+) (N : ℕ),
      (τ_[Y, x]^k) ω ≤ N ↔
        (k : ℕ) ≤
          (Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = x).card
  | k, N => by
      have hbound :
          (τ_[Y, x]^k) ω ≤ N ↔ (τ_[Y, x]^k) ω < N + 1 := by
        simpa using
          (ENat.lt_coe_add_one_iff (m := (τ_[Y, x]^k) ω) (n := N)).symm
      constructor
      · intro h
        exact (iteratedEntranceTime_lt_iff_prefixVisitCountAtLeast Y x ω k (N + 1)).1
          (hbound.mp h)
      · intro h
        exact hbound.mpr
          ((iteratedEntranceTime_lt_iff_prefixVisitCountAtLeast Y x ω k (N + 1)).2 h)

/-- Helper for Remark 17.31: every bounded prefix count of visits to `x` injects into the full
set of positive visit times. -/
private lemma prefixHitCount_le_positiveVisitEncard
    (Y : ℕ → Ω → ℕ) (x : ℕ) (ω : Ω) (N : ℕ) :
    ((Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = x).card : ℕ∞) ≤
      (positiveVisitSet Y x ω).encard := by
  classical
  let s : Set (Fin (N + 1)) := {i : Fin (N + 1) | 0 < (i : ℕ) ∧ Y i ω = x}
  have hs_subset : (fun i : Fin (N + 1) ↦ (i : ℕ)) '' s ⊆ positiveVisitSet Y x ω := by
    intro n hn
    rcases hn with ⟨i, hi, rfl⟩
    exact ⟨Nat.succ_le_of_lt hi.1, hi.2⟩
  -- Proof comment: identify the filtered prefix finset with its image inside the full positive
  -- visit set and compare their encards by monotonicity.
  calc
    ((Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = x).card : ℕ∞)
        = s.encard := by
          calc
            ((Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = x).card : ℕ∞)
                = s.toFinset.card := by
                    simp [s]
            _ = s.encard := by
                    symm
                    exact Set.encard_eq_coe_toFinset_card s
    _ = ((fun i : Fin (N + 1) ↦ (i : ℕ)) '' s).encard := by
      symm
      exact Fin.val_injective.encard_image s
    _ ≤ (positiveVisitSet Y x ω).encard := Set.encard_mono hs_subset

/-- Helper for Remark 17.31: among positive integers, exactly `m` indices satisfy `k ≤ m`. -/
private lemma count_pnat_le_eq (m : ℕ) :
    Measure.count {k : ℕ+ | (k : ℕ) ≤ m} = m := by
  let s : Set ℕ+ := {k : ℕ+ | (k : ℕ) ≤ m}
  have himage : Equiv.pnatEquivNat '' s = {n : ℕ | n < m} := by
    ext n
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : k.natPred + 1 ≤ m := by
        simpa [s, PNat.natPred_add_one] using hk
      exact lt_of_lt_of_le (Nat.lt_succ_self k.natPred) hk'
    · intro hn
      refine ⟨n.succPNat, ?_, by simp [Equiv.pnatEquivNat]⟩
      simpa [s] using Nat.succ_le_of_lt hn
  -- Proof comment: transport the positive-natural counting problem to the finite initial segment
  -- of `ℕ`.
  calc
    Measure.count s = Measure.count (Equiv.pnatEquivNat '' s) := by
      symm
      exact Measure.count_injective_image Equiv.pnatEquivNat.injective s
    _ = Measure.count {n : ℕ | n < m} := by
      rw [himage]
    _ = ({n : ℕ | n < m}).encard := by
      rw [Measure.count_apply MeasurableSet.of_discrete]
    _ = m := by
      exact_mod_cast (Set.Nat.encard_range m)

/-- Helper for Remark 17.31: counting positive integers bounded by an `ℕ∞` value recovers that
bound. -/
private lemma count_pnat_le_enat_eq (t : ℕ∞) :
    Measure.count {k : ℕ+ | (k : ℕ∞) ≤ t} = t := by
  by_cases ht : t = ⊤
  · subst ht
    simpa [ENat.card_eq_top_of_infinite] using
      (Measure.count_univ : Measure.count (Set.univ : Set ℕ+) = ENat.card ℕ+)
  · calc
      Measure.count {k : ℕ+ | (k : ℕ∞) ≤ t}
        = Measure.count {k : ℕ+ | (k : ℕ) ≤ ENat.toNat t} := by
            congr 1
            ext k
            constructor
            · intro hk
              simpa using ENat.toNat_le_toNat hk ht
            · intro hk
              have hk' : ((k : ℕ) : ℕ∞) ≤ (ENat.toNat t : ℕ∞) := by
                exact (ENat.coe_le_coe).2 hk
              simpa [ENat.coe_toNat ht] using hk'
      _ = ENat.toNat t := by
            simpa using count_pnat_le_eq (ENat.toNat t)
      _ = t := by
            exact_mod_cast ENat.coe_toNat ht

/-- Helper for Remark 17.31: a finite iterated entrance time is equivalent to having at least
`k` positive visits to `x`, expressed through the full positive-visit encard. -/
private lemma iteratedEntranceTime_lt_top_iff_le_positiveVisitEncard
    (Y : ℕ → Ω → ℕ) (x : ℕ) (ω : Ω) (k : ℕ+) :
    (τ_[Y, x]^k) ω < ⊤ ↔ (k : ℕ∞) ≤ (positiveVisitSet Y x ω).encard := by
  constructor
  · intro hτ
    let N : ℕ := ENat.toNat ((τ_[Y, x]^k) ω)
    have hτ_ne_top : (τ_[Y, x]^k) ω ≠ ⊤ := ne_of_lt hτ
    have hτ_le : (τ_[Y, x]^k) ω ≤ N := by
      simp [N, ENat.coe_toNat hτ_ne_top]
    have hk_le_prefix :
        (k : ℕ∞) ≤
          ((Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = x).card : ℕ∞) := by
      exact_mod_cast (iteratedEntranceTime_le_iff_prefixVisitCountAtLeast Y x ω k N).1 hτ_le
    -- Proof comment: once the `k`th entrance time is finite, the bounded prefix already contains
    -- at least `k` positive visits, hence so does the full visit set.
    exact hk_le_prefix.trans (prefixHitCount_le_positiveVisitEncard Y x ω N)
  · intro hk
    obtain ⟨t, ht_subset, ht_card⟩ :=
      Set.exists_subset_encard_eq (s := positiveVisitSet Y x ω) hk
    have ht_finite : t.Finite := Set.finite_of_encard_eq_coe (by simpa using ht_card)
    let tfin : Finset ℕ := ht_finite.toFinset
    have htfin_card_enat : (tfin.card : ℕ∞) = (k : ℕ∞) := by
      rw [← ht_finite.encard_eq_coe_toFinset_card]
      simpa [tfin] using ht_card
    have htfin_card : tfin.card = (k : ℕ) := ENat.coe_inj.mp htfin_card_enat
    have htfin_nonempty : tfin.Nonempty := by
      apply Finset.card_pos.mp
      rw [htfin_card]
      exact k.2
    let N : ℕ := tfin.max' htfin_nonempty
    let toPrefix : ℕ → Fin (N + 1) :=
      fun n ↦
        if hn : n ∈ tfin then
          ⟨n, Nat.lt_succ_of_le (Finset.le_max' tfin n hn)⟩
        else 0
    have hk_le_prefix :
        (k : ℕ) ≤ (Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = x).card := by
      have hcard_le :
          tfin.card ≤ (Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = x).card := by
        refine Finset.card_le_card_of_injOn toPrefix ?_ ?_
        · intro n hn
          have hn_t : n ∈ t := by
            simpa [tfin] using hn
          have hn_props : 1 ≤ n ∧ Y n ω = x := ht_subset hn_t
          have htoPrefix : toPrefix n = ⟨n, Nat.lt_succ_of_le (Finset.le_max' tfin n hn)⟩ := by
            by_cases hmem : n ∈ tfin
            · simp [toPrefix, hmem]
            · exact (hmem hn).elim
          have hprefix_val : ((toPrefix n : Fin (N + 1)) : ℕ) = n := by
            rw [htoPrefix]
          have hpos : 0 < ((toPrefix n : Fin (N + 1)) : ℕ) := by
            simpa [hprefix_val] using Nat.succ_le_iff.mp hn_props.1
          have hstate : Y (toPrefix n) ω = x := by
            simpa [hprefix_val] using hn_props.2
          refine Finset.mem_filter.mpr ?_
          refine ⟨by simp, ?_⟩
          exact ⟨show (0 : Fin (N + 1)) < toPrefix n from hpos, hstate⟩
        · intro n₁ hn₁ n₂ hn₂ hEq
          have hvals :
              ((toPrefix n₁ : Fin (N + 1)) : ℕ) = ((toPrefix n₂ : Fin (N + 1)) : ℕ) := by
            exact congrArg (fun i : Fin (N + 1) ↦ (i : ℕ)) hEq
          have hn₁_val : ((toPrefix n₁ : Fin (N + 1)) : ℕ) = n₁ := by
            have htoPrefix :
                toPrefix n₁ = ⟨n₁, Nat.lt_succ_of_le (Finset.le_max' tfin n₁ hn₁)⟩ := by
              by_cases hmem : n₁ ∈ tfin
              · simp [toPrefix, hmem]
              · exact (hmem hn₁).elim
            rw [htoPrefix]
          have hn₂_val : ((toPrefix n₂ : Fin (N + 1)) : ℕ) = n₂ := by
            have htoPrefix :
                toPrefix n₂ = ⟨n₂, Nat.lt_succ_of_le (Finset.le_max' tfin n₂ hn₂)⟩ := by
              by_cases hmem : n₂ ∈ tfin
              · simp [toPrefix, hmem]
              · exact (hmem hn₂).elim
            rw [htoPrefix]
          calc
            n₁ = ((toPrefix n₁ : Fin (N + 1)) : ℕ) := hn₁_val.symm
            _ = ((toPrefix n₂ : Fin (N + 1)) : ℕ) := hvals
            _ = n₂ := hn₂_val
      rw [htfin_card] at hcard_le
      exact hcard_le
    -- Proof comment: the chosen `k`-element subset of positive visits is bounded by its maximal
    -- time, so the bounded-prefix criterion yields a finite `k`th entrance time.
    have hτ_le : (τ_[Y, x]^k) ω ≤ N :=
      (iteratedEntranceTime_le_iff_prefixVisitCountAtLeast Y x ω k N).2 hk_le_prefix
    exact lt_of_le_of_lt hτ_le (by simp)

/-- Helper for Remark 17.31: the positive visit count from time `1` equals the number of finite
iterated entrance times into the same state. -/
private theorem figure17_2_totalVisitsFromOne_eq_countFiniteIteratedEntrances
    (x : ℕ) (ω : Ω) :
    totalVisitsFrom X x 1 ω = Measure.count {k : ℕ+ | (τ_[X, x]^k) ω < ⊤} := by
  -- Proof comment: rewrite the positive visit count as the encard of the positive-visit set and
  -- identify that encard with the counting measure of finite entrance indices.
  calc
    totalVisitsFrom X x 1 ω = Measure.count {n : ℕ | 1 ≤ n ∧ X n ω = x} := by
      rw [totalVisitsFrom_eq_count]
    _ = (positiveVisitSet X x ω).encard := by
      rw [Measure.count_apply MeasurableSet.of_discrete]
      simp [positiveVisitSet]
    _ = Measure.count {k : ℕ+ | (k : ℕ∞) ≤ (positiveVisitSet X x ω).encard} := by
      symm
      exact count_pnat_le_enat_eq ((positiveVisitSet X x ω).encard)
    _ = Measure.count {k : ℕ+ | (τ_[X, x]^k) ω < ⊤} := by
      congr 1
      ext k
      simpa using
        (iteratedEntranceTime_lt_top_iff_le_positiveVisitEncard X x ω k).symm

/-- Helper for Remark 17.31: pathwise, the indicator series of finite iterated entrance times is
the counting measure of the finite-entrance index set. -/
private theorem tsum_iteratedEntranceIndicators_eq_countFiniteIteratedEntrances
    (x : ℕ) (ω : Ω) :
    (∑' k : ℕ+,
      Set.indicator {ω' | (τ_[X, x]^k) ω' < ⊤} (fun _ ↦ (1 : ℝ≥0∞)) ω) =
      Measure.count {k : ℕ+ | (τ_[X, x]^k) ω < ⊤} := by
  -- Proof comment: evaluate the indicator series on the subtype of finite entrance indices.
  rw [Measure.count_apply MeasurableSet.of_discrete]
  calc
    (∑' k : ℕ+,
        Set.indicator {ω' | (τ_[X, x]^k) ω' < ⊤} (fun _ ↦ (1 : ℝ≥0∞)) ω) =
          ∑' _ : {k : ℕ+ | (τ_[X, x]^k) ω < ⊤}, (1 : ℝ≥0∞) := by
            symm
            simpa [Set.indicator_apply] using
              (tsum_subtype
                (s := {k : ℕ+ | (τ_[X, x]^k) ω < ⊤})
                (f := fun _ : ℕ+ ↦ (1 : ℝ≥0∞)))
    _ = ({k : ℕ+ | (τ_[X, x]^k) ω < ⊤}).encard := ENNReal.tsum_one

/-- Helper for Remark 17.31: finite iterated-entrance events are measurable. -/
private theorem figure17_2_iteratedEntranceTime_lt_top_measurable
    [hReal : IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) P X]
    (x : ℕ) (k : ℕ+) :
    MeasurableSet {ω | (τ_[X, x]^k) ω < ⊤} := by
  have hτ_le_meas : ∀ N : ℕ, MeasurableSet {ω | (τ_[X, x]^k) ω ≤ N} := by
    intro N
    let A : Set (Fin (N + 1) → ℕ) :=
      {f : Fin (N + 1) → ℕ |
        (k : ℕ) ≤ (Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ f i = x).card}
    have hA : MeasurableSet A := by
      classical
      exact (Set.to_countable A).measurableSet
    have hprefix :
        Measurable (fun ω : Ω ↦ fun i : Fin (N + 1) ↦ X (i : ℕ) ω) := by
      refine measurable_pi_lambda _ fun i ↦ ?_
      simpa using hReal.measurable_process (i : ℕ)
    have hEq :
        {ω | (τ_[X, x]^k) ω ≤ N} =
          (fun ω : Ω ↦ fun i : Fin (N + 1) ↦ X (i : ℕ) ω) ⁻¹' A := by
      ext ω
      simp [A, iteratedEntranceTime_le_iff_prefixVisitCountAtLeast]
    rw [hEq]
    exact hprefix hA
  have hEq :
      {ω | (τ_[X, x]^k) ω < ⊤} = ⋃ N : ℕ, {ω | (τ_[X, x]^k) ω ≤ N} := by
    ext ω
    constructor
    · intro hω
      let N : ℕ := ENat.toNat ((τ_[X, x]^k) ω)
      have hω_le : (τ_[X, x]^k) ω ≤ N := by
        simp [N, ENat.coe_toNat (ne_of_lt hω)]
      exact Set.mem_iUnion.mpr ⟨N, hω_le⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨N, hN⟩
      have hN' : (τ_[X, x]^k) ω ≤ N := by
        simpa using hN
      exact lt_of_le_of_lt hN' (by simp)
  rw [hEq]
  exact MeasurableSet.iUnion hτ_le_meas

/-- Helper for Remark 17.31: the positive-time diagonal Green function is the series of finite
iterated-entrance probabilities. -/
private theorem figure17_2_greenFunctionFromOneSelf_eq_tsum_iteratedEntranceProbabilities
    (r : Set.Icc (0 : ENNReal) 1)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) P X]
    (x : ℕ) :
    (G[P, X; 1]) x x =
      ∑' k : ℕ+, ENNReal.ofReal ((P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤}) := by
  -- Proof comment: rewrite `G[P, X; 1]` as the expected positive visit count, replace that
  -- count pathwise by the finite-entrance count, then expand it as an indicator series and
  -- integrate termwise.
  calc
    (G[P, X; 1]) x x = ∫⁻ ω, totalVisitsFrom X x 1 ω ∂(P x : Measure Ω) := by
      rw [greenFunctionFrom_eq_lintegral_totalVisitsFrom]
    _ = ∫⁻ ω, Measure.count {k : ℕ+ | (τ_[X, x]^k) ω < ⊤} ∂(P x : Measure Ω) := by
          refine lintegral_congr_ae ?_
          filter_upwards [] with ω
          rw [figure17_2_totalVisitsFromOne_eq_countFiniteIteratedEntrances (X := X) x ω]
    _ = ∫⁻ ω,
          ∑' k : ℕ+,
            Set.indicator {ω' | (τ_[X, x]^k) ω' < ⊤} (fun _ ↦ (1 : ℝ≥0∞)) ω
          ∂(P x : Measure Ω) := by
            refine lintegral_congr_ae ?_
            filter_upwards [] with ω
            symm
            exact tsum_iteratedEntranceIndicators_eq_countFiniteIteratedEntrances (X := X) x ω
    _ = ∑' k : ℕ+,
          ∫⁻ ω,
            Set.indicator {ω' | (τ_[X, x]^k) ω' < ⊤} (fun _ ↦ (1 : ℝ≥0∞)) ω
          ∂(P x : Measure Ω) := by
            rw [lintegral_tsum fun k ↦
              (measurable_const.indicator
                (figure17_2_iteratedEntranceTime_lt_top_measurable
                  (r := r) (P := P) (X := X) x k)).aemeasurable]
    _ = ∑' k : ℕ+, (P x : Measure Ω) {ω | (τ_[X, x]^k) ω < ⊤} := by
          refine tsum_congr fun k ↦ ?_
          simpa using
            (lintegral_indicator_one (μ := (P x : Measure Ω))
              (s := {ω | (τ_[X, x]^k) ω < ⊤})
              (figure17_2_iteratedEntranceTime_lt_top_measurable
                (r := r) (P := P) (X := X) x k))
    _ = ∑' k : ℕ+, ENNReal.ofReal ((P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤}) := by
          refine tsum_congr fun k ↦ ?_
          simp [MeasureTheory.measureReal_def]

/-- Helper for Remark 17.31: Theorem 17.29 rewrites the iterated entrance-probability series at
state `x` as the shifted power series of the return probability. -/
private theorem figure17_2_iteratedEntranceProbabilitySeries_eq_selfPowerSeries
    (r : Set.Icc (0 : ENNReal) 1)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) P X]
    (x : ℕ) :
    (∑' k : ℕ+, ENNReal.ofReal ((P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤})) =
      ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
  -- Proof comment: replace each iterated-entrance probability with the Theorem 17.29 formula,
  -- then reindex the `ℕ+`-series to an ordinary `ℕ`-series.
  calc
    (∑' k : ℕ+, ENNReal.ofReal ((P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤})) =
        ∑' k : ℕ+, ENNReal.ofReal ((F[P, X]) x x * (F[P, X]) x x ^ k.natPred) := by
          refine tsum_congr fun k ↦ ?_
          simpa using congrArg ENNReal.ofReal
            (iteratedEntranceTime_finite_probability_eq_everHitsProbability_mul_selfPow
              (κ := fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n)
              (P := P) (X := X) x x k)
    _ = ∑' n : ℕ, ENNReal.ofReal ((F[P, X]) x x * (F[P, X]) x x ^ n) := by
          simpa using
            (Equiv.tsum_eq Equiv.pnatEquivNat
              (fun n : ℕ ↦ ENNReal.ofReal ((F[P, X]) x x * (F[P, X]) x x ^ n)))
    _ = ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
          refine tsum_congr fun n ↦ ?_
          rw [pow_succ, mul_comm]

/-- Helper for Remark 17.31: a shifted geometric series of nonnegative real casts stays finite as
long as the ratio lies in `[0, 1)`. -/
private theorem figure17_2_ennrealOfRealTsumGeometricSucc_lt_top
    {q : ℝ} (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1) :
    ∑' n : ℕ, ENNReal.ofReal (q ^ (n + 1)) < ⊤ := by
  have hsum : Summable (fun n : ℕ ↦ q ^ (n + 1)) :=
    (_root_.summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hq_nonneg hq_lt_one)
  -- Proof comment: summability of the real geometric tail transports to `ℝ≥0∞` because every
  -- term is nonnegative.
  calc
    ∑' n : ℕ, ENNReal.ofReal (q ^ (n + 1))
      = ENNReal.ofReal (∑' n : ℕ, q ^ (n + 1)) := by
          rw [ENNReal.ofReal_tsum_of_nonneg]
          · intro n
            exact pow_nonneg hq_nonneg _
          · exact hsum
    _ < ⊤ := by
          simp

/-- Helper for Remark 17.31: an infinite diagonal Green value forces recurrence of that state. -/
private theorem figure17_2_isRecurrentState_of_greenFunctionSelf_eq_top
    (r : Set.Icc (0 : ENNReal) 1)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) P X]
    (x : ℕ) (hx : (G[P, X]) x x = ⊤) :
    IsRecurrentState P X x := by
  have hq_nonneg : 0 ≤ (F[P, X]) x x := measureReal_nonneg
  have hq_le_one : (F[P, X]) x x ≤ 1 := by
    rw [everHitsProbability_def]
    exact measureReal_le_one
  by_contra htrans
  have hq_lt_one : (F[P, X]) x x < 1 := by
    rw [IsRecurrentState] at htrans
    exact lt_of_le_of_ne hq_le_one (by simpa [eq_comm] using htrans)
  have htail_lt_top :
      ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) < ⊤ :=
    figure17_2_ennrealOfRealTsumGeometricSucc_lt_top hq_nonneg hq_lt_one
  have hgreen_lt_top : (G[P, X]) x x < ⊤ := by
    -- Proof comment: the diagonal Green value splits into `1 + G₁`, and the positive-time tail
    -- is exactly the geometric series in the return probability.
    calc
      (G[P, X]) x x = 1 + (G[P, X; 1]) x x := by
        rw [figure17_2_greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf
          (r := r) (P := P) (X := X)]
      _ = 1 + ∑' k : ℕ+,
            ENNReal.ofReal ((P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤}) := by
              rw [figure17_2_greenFunctionFromOneSelf_eq_tsum_iteratedEntranceProbabilities
                (r := r) (P := P) (X := X)]
      _ = 1 + ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
            rw [figure17_2_iteratedEntranceProbabilitySeries_eq_selfPowerSeries
              (r := r) (P := P) (X := X)]
      _ < ⊤ := by
            exact ENNReal.add_lt_top.2 ⟨by simp, htail_lt_top⟩
  exact (ne_of_lt hgreen_lt_top) hx

/-- Helper for Remark 17.31: recurrence forces the diagonal Green value to be infinite for the
Fig. 17.2 chain. -/
private theorem figure17_2_greenFunctionSelf_eq_top_of_isRecurrentState
    (r : Set.Icc (0 : ENNReal) 1)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) P X]
    (x : ℕ) (hx : IsRecurrentState P X x) :
    (G[P, X]) x x = ⊤ := by
  have htail :
      (G[P, X; 1]) x x = ∑' n : ℕ, (1 : ℝ≥0∞) := by
    -- Proof comment: recurrence makes every positive-time return term equal to the constant `1`.
    calc
      (G[P, X; 1]) x x = ∑' k : ℕ+,
            ENNReal.ofReal ((P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤}) := by
              rw [figure17_2_greenFunctionFromOneSelf_eq_tsum_iteratedEntranceProbabilities
                (r := r) (P := P) (X := X)]
      _ = ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
            rw [figure17_2_iteratedEntranceProbabilitySeries_eq_selfPowerSeries
              (r := r) (P := P) (X := X)]
      _ = ∑' n : ℕ, ENNReal.ofReal (1 ^ (n + 1 : ℕ)) := by
            refine tsum_congr fun n ↦ ?_
            rw [IsRecurrentState] at hx
            simpa [hx]
      _ = ∑' n : ℕ, (1 : ℝ≥0∞) := by
            refine tsum_congr fun n ↦ ?_
            simp
  -- Proof comment: the deterministic time-`0` visit contributes `1`, and the remaining tail is
  -- the divergent series of ones.
  calc
    (G[P, X]) x x = 1 + (G[P, X; 1]) x x := by
      rw [figure17_2_greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf
        (r := r) (P := P) (X := X)]
    _ = 1 + ∑' n : ℕ, (1 : ℝ≥0∞) := by
          rw [htail]
    _ = ⊤ := by
          simp

/-- Helper for Remark 17.31: once the diagonal Green value at `0` is infinite, the critical
transient branch is impossible. -/
private theorem figure17_2_not_zero_transient_of_greenFunctionSelf_eq_top
    (r : Set.Icc (0 : ENNReal) 1)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) P X]
    (hgreen : (G[P, X]) 0 0 = ⊤) :
    ¬ IsTransientState P X 0 := by
  intro htrans
  have hrec : IsRecurrentState P X 0 :=
    figure17_2_isRecurrentState_of_greenFunctionSelf_eq_top
      (r := r) (P := P) (X := X) 0 hgreen
  change (F[P, X]) 0 0 < 1 at htrans
  change (F[P, X]) 0 0 = 1 at hrec
  exact (lt_irrefl (1 : ℝ)) (hrec ▸ htrans)

/-- Helper for Remark 17.31: at the critical parameter `r = 1 / 2`, the remaining blocker is the
anchor return probability at state `0`. -/
private theorem figure17_2_returnProbability_zero_zero_eq_one_half
    (hr : (r : ENNReal) = 1 / 2) :
    (F[P, X]) 0 0 = 1 := by
  -- Route correction: instead of the brittle infinite-horizon `iSup` route, prove direct
  -- first-step recurrences for `a k = (F[P, X]) k 0`; at `r = 1/2` that recursion is harmonic,
  -- so boundedness in `[0,1]` forces the common difference to vanish.
  let a : ℕ → ℝ := fun k ↦ (F[P, X]) k 0
  have hrReal : (r : ENNReal).toReal = (1 / 2 : ℝ) := by
    rw [hr]
    norm_num [ENNReal.toReal_ofReal]
  have hOneSubReal : (1 - (r : ENNReal)).toReal = (1 / 2 : ℝ) := by
    rw [hr]
    norm_num [ENNReal.toReal_ofReal]
  have hnonneg : ∀ k : ℕ, 0 ≤ a k := by
    intro k
    dsimp [a]
    rw [everHitsProbability_def]
    exact measureReal_nonneg
  have hone : ∀ k : ℕ, a k ≤ 1 := by
    intro k
    dsimp [a]
    rw [everHitsProbability_def]
    exact measureReal_le_one
  have hstepOne :
      a 1 = 1 / 2 + (1 / 2 : ℝ) * a 2 := by
    have hraw := figure17_2_hitProbability_zero_step_one (r := r) (P := P) (X := X)
    simpa [a, hrReal, hOneSubReal] using hraw
  have hstepSucc :
      ∀ n : ℕ, 2 * a (n + 2) = a (n + 1) + a (n + 3) := by
    intro n
    have hraw := figure17_2_hitProbability_zero_step_succ (r := r) (P := P) (X := X) n
    have hraw' :
        a (n + 2) = (1 - (r : ENNReal)).toReal * a (n + 1) + (r : ENNReal).toReal * a (n + 3) := by
      simpa [a] using hraw
    have hrawHalf :
        a (n + 2) = (1 / 2 : ℝ) * a (n + 1) + (1 / 2 : ℝ) * a (n + 3) := by
      simpa [hrReal, hOneSubReal] using hraw'
    nlinarith [hrawHalf]
  let d : ℝ := a 2 - a 1
  have hdiff : ∀ n : ℕ, a (n + 2) - a (n + 1) = d := by
    intro n
    induction n with
    | zero =>
        simp [d]
    | succ n ih =>
        have hstep := hstepSucc n
        have : a (n + 3) - a (n + 2) = a (n + 2) - a (n + 1) := by
          nlinarith
        exact this.trans ih
  have hlinear : ∀ n : ℕ, a (n + 1) = a 1 + (n : ℝ) * d := by
    intro n
    induction n with
    | zero =>
        simp [d]
    | succ n ih =>
        have hdiffn : a (n + 2) - a (n + 1) = d := hdiff n
        calc
          a (n + 2) = a (n + 1) + d := by
            nlinarith
          _ = (a 1 + (n : ℝ) * d) + d := by rw [ih]
          _ = a 1 + ((n + 1 : ℕ) : ℝ) * d := by
            have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by
              norm_num
            rw [hcast]
            ring
  have hd_eq_zero : d = 0 := by
    by_contra hd_ne
    rcases lt_or_gt_of_ne hd_ne with hd_neg | hd_pos
    · have hpos : 0 < -d := by
        linarith
      obtain ⟨N, hN⟩ : ∃ N : ℕ, a 1 / (-d) < N := exists_nat_gt (a 1 / (-d))
      have hmul : a 1 < (N : ℝ) * (-d) := by
        exact (div_lt_iff₀ hpos).mp <| by simpa [mul_comm] using hN
      have hlt : a 1 + (N : ℝ) * d < 0 := by
        nlinarith
      have hlt' : a (N + 1) < 0 := by
        rw [hlinear N]
        exact hlt
      exact (not_lt_of_ge (hnonneg (N + 1))) hlt'
    · obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 - a 1) / d < N := exists_nat_gt ((1 - a 1) / d)
      have hmul : 1 - a 1 < (N : ℝ) * d := by
        exact (div_lt_iff₀ hd_pos).mp <| by simpa [mul_comm] using hN
      have hgt : 1 < a 1 + (N : ℝ) * d := by
        nlinarith
      have hgt' : 1 < a (N + 1) := by
        rw [hlinear N]
        exact hgt
      exact (not_lt_of_ge (hone (N + 1))) hgt'
  have ha2_eq : a 2 = a 1 := by
    have : a 2 - a 1 = 0 := by
      simpa [d] using hd_eq_zero
    nlinarith
  have ha1_eq_one : a 1 = 1 := by
    rw [ha2_eq] at hstepOne
    nlinarith
  -- Proof comment: the return probability at `0` equals the hit probability of `0` from `1`, so
  -- the critical anchor closes once the harmonic recurrence forces `a 1 = 1`.
  simpa [a] using
    (figure17_2_returnProbability_zero_eq_hitProbability_one_zero (r := r) (P := P) (X := X)).trans
      ha1_eq_one

/-- Helper for Remark 17.31: at the critical parameter `r = 1 / 2`, the origin diagonal Green
value is infinite. -/
private theorem figure17_2_greenFunction_zero_zero_eq_top_half
    (hr : (r : ENNReal) = 1 / 2) :
    (G[P, X]) 0 0 = ⊤ := by
  -- Proof comment: after the critical anchor return probability is identified as `1`, the local
  -- Green-tail computation upgrades it directly to an infinite diagonal Green value.
  exact figure17_2_greenFunctionSelf_eq_top_of_isRecurrentState
    (r := r) (P := P) (X := X) 0
    (by simpa [IsRecurrentState] using
      figure17_2_returnProbability_zero_zero_eq_one_half (r := r) (P := P) (X := X) hr)

/-- Helper for Remark 17.31: at the critical parameter `r = 1 / 2`, the remaining blocker is the
anchor recurrence of state `0`. -/
private theorem figure17_2_zero_recurrent_of_eq_half
    (hr : (r : ENNReal) = 1 / 2) :
    IsRecurrentState P X 0 := by
  -- Proof comment: the critical recurrence anchor is exactly the identity `(F[P, X]) 0 0 = 1`.
  simpa [IsRecurrentState] using
    figure17_2_returnProbability_zero_zero_eq_one_half (r := r) (P := P) (X := X) hr

/-- Helper for Remark 17.31: subclaim (5) says that for any realization of the
Markov chain of Fig. 17.2, every state is transient when `r ∈ (1 / 2, 1]`. -/
theorem figure17_2_allStatesTransient_of_half_lt
    (hrhalf : 1 / 2 < (r : ENNReal)) :
    ∀ x : ℕ, IsTransientState P X x := by
  by_cases hr_eq_one : (r : ENNReal) = 1
  · -- Proof comment: at `r = 1`, the chain is the deterministic right shift, so every state is
    -- transient without any irreducibility argument.
    exact figure17_2_allStatesTransient_of_eq_one (r := r) (P := P) (X := X) hr_eq_one
  · have hr0 : 0 < (r : ENNReal) := lt_trans (by norm_num) hrhalf
    have hr1 : (r : ENNReal) < 1 := lt_of_le_of_ne r.2.2 hr_eq_one
    have hzero : IsTransientState P X 0 :=
      figure17_2_zero_transient_of_half_lt (r := r) (P := P) (X := X) hrhalf hr1
    -- Proof comment: once state `0` is known to be transient, Theorem 17.37 propagates that
    -- transience to every state through the irreducibility helper above.
    exact
      figure17_2_allStatesTransient_of_zero_transient
        (r := r) (P := P) (X := X) hr0 hr1 hzero

/-- Helper for Remark 17.31: subclaim (6) says that for any realization of the
Markov chain of Fig. 17.2, the chain is positive recurrent when `r ∈ (0, 1 / 2)`. -/
theorem figure17_2_allStatesPositiveRecurrent_of_lt_half
    (hr0 : 0 < (r : ENNReal)) (hrhalf : (r : ENNReal) < 1 / 2) :
    IsPositiveRecurrentMarkovChain P X := by
  obtain ⟨π, hπinv, hπ0⟩ :=
    figure17_2_existsInvariantDistribution_zeroMass_pos_of_lt_half (r := r) hr0 hrhalf
  have hπinvPow :
      Kernel.Invariant
        ((fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) 1)
        (π : Measure ℕ) := by
    simpa [pow_one] using hπinv
  have hpos0_owner : ProbabilityTheory.IsPositiveRecurrentState P X 0 :=
    ProbabilityTheory.isPositiveRecurrentState_of_invariantDistribution_singleton_pos
      (κ := fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n)
      (P := P) (X := X) (y := 0) hπinvPow hπ0
  have hpos0 : IsPositiveRecurrentState P X 0 := by
    simpa [ProbabilityTheory.IsPositiveRecurrentState,
      ProbabilityTheory.expectedFirstReturnTime,
      DiscreteMarkovChain.IsPositiveRecurrentState,
      DiscreteMarkovChain.expectedFirstReturnTime] using hpos0_owner
  intro x
  by_cases hx0 : x = 0
  · simpa [hx0] using hpos0
  · have hx_pos : 0 < x := Nat.pos_iff_ne_zero.mpr hx0
    have hstep :
        0 < ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ x) 0) ({x} : Set ℕ) := by
      simpa [Nat.zero_add] using figure17_2_rightPathStepMass_pos (r := r) hr0 0 x
    have hhit : 0 < (F[P, X]) 0 x :=
      figure17_2_everHitsProbability_pos_of_posStepMass (r := r) (P := P) (X := X) hx_pos hstep
    have hx_owner : ProbabilityTheory.IsPositiveRecurrentState P X x :=
      ProbabilityTheory.isPositiveRecurrentState_of_isPositiveRecurrentState_of_everHitsProbability_pos
        (κ := fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n)
        (P := P) (X := X) (x := 0) (y := x) hpos0_owner hhit
    simpa [ProbabilityTheory.IsPositiveRecurrentState,
      ProbabilityTheory.expectedFirstReturnTime,
      DiscreteMarkovChain.IsPositiveRecurrentState,
      DiscreteMarkovChain.expectedFirstReturnTime] using hx_owner

/-- Remark 17.31 (7): for any realization of the Markov chain of Fig. 17.2, the chain is null
recurrent when `r = 1 / 2`. -/
theorem figure17_2_allStatesNullRecurrent_of_eq_half
    (hr : (r : ENNReal) = 1 / 2) :
    IsNullRecurrentMarkovChain P X := by
  have hr0 : 0 < (r : ENNReal) := by
    rw [hr]
    norm_num
  have hr1 : (r : ENNReal) < 1 := by
    rw [hr]
    norm_num
  have hzero : IsRecurrentState P X 0 :=
    figure17_2_zero_recurrent_of_eq_half (r := r) (P := P) (X := X) hr
  intro x
  refine
    ⟨figure17_2_allStatesRecurrent_of_zero_recurrent
        (r := r) (P := P) (X := X) hr0 hr1 hzero x,
      figure17_2_not_positiveRecurrentState_of_eq_half (r := r) (P := P) (X := X) hr x⟩

end Figure17_2

end DiscreteMarkovChain

end ProbabilityTheory
