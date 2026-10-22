/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_29
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]
variable {κ : ℕ → Kernel E E}
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}

/-- Helper for Theorem 17.35: `ℕ+` is used as a discrete counting index for iterated entrance
times. -/
local instance : MeasurableSpace ℕ+ := ⊤

/-- Helper for Theorem 17.35: the measurable structure on `ℕ+` is discrete. -/
local instance : DiscreteMeasurableSpace ℕ+ where
  forall_measurableSet := by
    intro s
    trivial

/-- Helper for Theorem 17.35: classical equality on the countable state space is used in the
finite-prefix visit-count normalization lemmas. -/
local instance theorem17_35DecidableEq : DecidableEq E := Classical.decEq E

-- Source alignment: Theorem 17.35 is a countable-state result. `MeasurableSingletonClass E`
-- makes point-hit events measurable, and `Countable E` upgrades this to the discrete-state
-- regime used in the textbook argument.
-- Semantic recall: leansearch only surfaced kernel irreducibility APIs, so this item stays on the
-- source-facing Chapter 17 recurrence surface.
/- Theorem 17.35 is source-facing. Its ambient owner data is the realization
`[IsMarkovProcessRealization κ P X]`, while the hypotheses and conclusions are phrased in the
derived Chapter 17 API `IsRecurrentState` and `F[P, X]`. -/
section CommunicatingStates

omit [Countable E] in
/-- Helper for Theorem 17.35: a positive ever-hit probability yields a positive singleton
transition mass at some strictly positive time. -/
private lemma existsPosTransitionMassOfEverHitsProbabilityPos
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X] {x y : E}
    (hxy : 0 < (F[P, X]) x y) :
    ∃ n : ℕ, 0 < n ∧ 0 < (κ n) x ({y} : Set E) := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let hproc : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  have hgreen : 0 < (G[P, X; 1]) x y :=
    (greenFunctionFrom_one_pos_iff_everHitsProbability_pos P X hproc x y).2 hxy
  -- Proof comment: expand the positive-time Green function into its state-probability series and
  -- extract one strictly positive summand.
  have hterm :
      ∃ n : ℕ, 0 < (P x : Measure Ω) {ω | 0 < n ∧ X n ω = y} := by
    by_contra hnot
    have hzero :
        ∑' n : ℕ, (P x : Measure Ω) {ω | 0 < n ∧ X n ω = y} = 0 := by
      rw [ENNReal.tsum_eq_zero]
      intro n
      exact le_antisymm (le_of_not_gt fun hn ↦ hnot ⟨n, hn⟩) bot_le
    rw [greenFunctionFrom_one_eq_tsum_positiveStateProbabilities P X hproc x y, hzero] at hgreen
    exact lt_irrefl _ hgreen
  rcases hterm with ⟨n, hn⟩
  have hnpos : 0 < n := by
    by_contra hnpos
    have hzeroEvent :
        (P x : Measure Ω) {ω | 0 < n ∧ X n ω = y} = 0 := by
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
      subst hnzero
      simp
    exact hzeroEvent.not_gt hn
  have hstep :
      (P x : Measure Ω) {ω | 0 < n ∧ X n ω = y} = (κ n) x ({y} : Set E) := by
    have hpreimage : {ω | 0 < n ∧ X n ω = y} = X n ⁻¹' ({y} : Set E) := by
      ext ω
      simp [hnpos]
    rw [hpreimage]
    rw [← Measure.map_apply (hReal.measurable_process n) (MeasurableSet.singleton y)]
    rw [hReal.transition_eq x n]
  have hmass : 0 < (κ n) x ({y} : Set E) := by
    simpa [hstep] using hn
  exact ⟨n, hnpos, hmass⟩

omit [Countable E] in
/-- Helper for Theorem 17.35: choose the earliest strictly positive singleton transition mass
coming from the communication hypothesis. -/
private lemma existsMinimalPosTransitionMassOfEverHitsProbabilityPos
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X] {x y : E}
    (hxy : 0 < (F[P, X]) x y) :
    ∃ n : ℕ, 0 < n ∧ 0 < (κ n) x ({y} : Set E) ∧
      ∀ m : ℕ, 0 < m → m < n → (κ m) x ({y} : Set E) = 0 := by
  let S : Set ℕ := {n : ℕ | 0 < n ∧ 0 < (κ n) x ({y} : Set E)}
  have hS : S.Nonempty := by
    rcases existsPosTransitionMassOfEverHitsProbabilityPos (P := P) (X := X) (κ := κ) hxy with
      ⟨n, hnpos, hmass⟩
    exact ⟨n, hnpos, hmass⟩
  let n : ℕ := Nat.find hS
  have hn_mem : n ∈ S := Nat.find_spec hS
  refine ⟨n, hn_mem.1, hn_mem.2, ?_⟩
  intro m hmpos hmn
  by_contra hmass_ne_zero
  have hmass : 0 < (κ m) x ({y} : Set E) := by
    exact bot_lt_iff_ne_bot.mpr hmass_ne_zero
  have hnle : n ≤ m := Nat.find_min' hS ⟨hmpos, hmass⟩
  exact (not_le_of_gt hmn) hnle

omit [Countable E] in
/-- Helper for Theorem 17.35: the generated history filtration is monotone in the time index. -/
private lemma generatedFiltrationSpace_mono
    (Y : ℕ → Ω → E) {m n : ℕ} (hmn : m ≤ n) :
    generatedFiltrationSpace Y m ≤ generatedFiltrationSpace Y n := by
  -- Proof comment: enlarging the terminal time only enlarges the supremum of available history
  -- coordinates.
  refine iSup₂_le fun r hr ↦ ?_
  exact le_iSup_of_le r <| le_iSup_of_le (hr.trans hmn) le_rfl

omit [Countable E] in
/-- Helper for Theorem 17.35: state events are measurable in every later generated history
filtration. -/
private lemma measurableSet_stateEvent_generated
    (Y : ℕ → Ω → E) (y : E) {i n : ℕ} (hi : i ≤ n) :
    MeasurableSet[generatedFiltrationSpace Y n] {ω | Y i ω = y} := by
  -- Proof comment: the coordinate sigma-algebra at time `i` already appears in the history
  -- filtration at every later time `n`.
  have hYi : Measurable[generatedFiltrationSpace Y n] (Y i) := by
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le i <| le_iSup_of_le hi le_rfl
  simpa [Set.preimage] using hYi (MeasurableSet.singleton y)

omit [Countable E] in
/-- Helper for Theorem 17.35: the first positive return time is bounded by `n` exactly when the
path hits `x` at some time in `Set.Icc 1 n`. -/
private lemma firstReturnTime_le_iff_existsHit
    (x : E) (n : ℕ) (ω : Ω) :
    (τ_[X, x]^1) ω ≤ n ↔ ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧ X j ω = x := by
  -- Proof comment: this is the singleton specialization of the standard `hittingAfter ≤` test.
  constructor
  · intro hτ
    rcases
        (MeasureTheory.hittingAfter_le_iff
          (u := X) (s := ({x} : Set E)) (n := 1) (ω := ω) (i := n)).1
          (by simpa [iteratedEntranceTime_one] using hτ) with
      ⟨j, hj, hjx⟩
    exact ⟨j, hj.1, hj.2, by simpa [Set.mem_singleton_iff] using hjx⟩
  · rintro ⟨j, hj1, hjn, hjx⟩
    simpa [iteratedEntranceTime_one] using
      (MeasureTheory.hittingAfter_le_iff
        (u := X) (s := ({x} : Set E)) (n := 1) (ω := ω) (i := n)).2
        ⟨j, ⟨hj1, hjn⟩, by simpa [Set.mem_singleton_iff] using hjx⟩

omit [Countable E] in
/-- Helper for Theorem 17.35: the first positive return time is always strictly larger than
`0`. -/
private lemma zero_lt_firstReturnTime
    (x : E) (ω : Ω) :
    ((0 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω := by
  have hτge1 : (1 : ℕ∞) ≤ (τ_[X, x]^1) ω := by
    have h :
        (1 : ℕ) ≤ MeasureTheory.hittingAfter X ({x} : Set E) 1 ω :=
      le_hittingAfter ω
    simpa [iteratedEntranceTime_one] using h
  exact lt_of_lt_of_le (by simp) hτge1

omit [Countable E] in
/-- Helper for Theorem 17.35: the first-return tail event `{ω | n < τ_[X, x]^1 ω}` is already
measurable in the time-`n` history filtration. -/
private lemma measurableSet_firstReturnTimeTail_generated
    (x : E) (n : ℕ) :
    MeasurableSet[generatedFiltrationSpace X n]
      {ω | ((n : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} := by
  have hEq :
      {ω | ((n : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} =
        {ω | (τ_[X, x]^1) ω ≤ n}ᶜ := by
    ext ω
    simp
  rw [hEq]
  have hEqLe :
      {ω | (τ_[X, x]^1) ω ≤ n} =
        ⋃ j ∈ ((Finset.Icc 1 n : Finset ℕ) : Set ℕ), {ω | X j ω = x} := by
    ext ω
    simp [firstReturnTime_le_iff_existsHit, and_assoc]
  rw [hEqLe]
  exact
    (MeasurableSet.biUnion (Set.to_countable _) fun j hj ↦
      measurableSet_stateEvent_generated (Y := X) x ((Finset.mem_Icc.mp hj).2)).compl

omit [Countable E] in
/-- Helper for Theorem 17.35: first-return tail events are measurable in the ambient sigma-algebra.
-/
private lemma measurableSet_firstReturnTimeTail
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (x : E) (n : ℕ) :
    MeasurableSet {ω | ((n : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} := by
  have hgen :
      MeasurableSet[generatedFiltrationSpace X n]
        {ω | ((n : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} :=
    measurableSet_firstReturnTimeTail_generated (X := X) x n
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    refine iSup₂_le fun j hj ↦ ?_
    exact (hReal.measurable_process j).comap_le
  exact hFiltration_le _ hgen

omit [Countable E] in
/-- Helper for Theorem 17.35: deterministic-time state events evaluate to the corresponding kernel
singleton masses. -/
private lemma measure_stateEvent_eq_transitionMass
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (s y : E) (n : ℕ) :
    (P s : Measure Ω) {ω | X n ω = y} = (κ n) s ({y} : Set E) := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  have hpreimage : {ω | X n ω = y} = X n ⁻¹' ({y} : Set E) := by
    ext ω
    simp
  rw [hpreimage]
  rw [← Measure.map_apply (hReal.measurable_process n) (MeasurableSet.singleton y)]
  rw [hReal.transition_eq s n]

omit [Countable E] in
/-- Helper for Theorem 17.35: the deterministic-time restart identity first appears on `toReal`
probabilities. -/
private lemma measure_inter_prefix_stepEvent_eq_mul_real
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    {s z y : E} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = z}) :
    (P s : Measure Ω).real (A ∩ {ω | X (n + m) ω = y}) =
      ((κ m) z ({y} : Set E)).toReal * (P s : Measure Ω).real A := by
  let μ : Measure Ω := P s
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let B : Set Ω := X (n + m) ⁻¹' ({y} : Set E)
  have hB_meas : MeasurableSet B := by
    simpa [B] using (hReal.measurable_process (n + m)) (MeasurableSet.singleton y)
  have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    refine iSup₂_le fun j hj ↦ ?_
    exact (hReal.measurable_process j).comap_le
  have hA_measAmbient : MeasurableSet A := by
    exact hFiltration_le (s := A) hA_meas
  have hMarkovGenerated :
      μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
        fun ω ↦ ((κ m) (X n ω)).real ({y} : Set E) := by
    -- Proof comment: this is the deterministic-time Markov property specialized to the singleton
    -- future event `{y}` at gap `m`.
    simpa [μ, B, add_comm] using
      hReal.markov_property s (A := ({y} : Set E)) (MeasurableSet.singleton y) n m
  have hIndicatorIntegrable : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB_meas
  -- Proof comment: integrate the deterministic-time Markov identity over the history event `A`,
  -- then freeze the transition row at `z` because `A` already forces `X n = z`.
  calc
    μ.real (A ∩ {ω | X (n + m) ω = y}) =
        ∫ ω in A, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂ μ := by
          rw [MeasureTheory.setIntegral_condExp hFiltration_le hIndicatorIntegrable hA_meas,
            ← MeasureTheory.integral_indicator hA_measAmbient]
          symm
          simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
            smul_eq_mul] using
            MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
              (hA_measAmbient.inter hB_meas)
    _ = ∫ ω in A, ((κ m) (X n ω)).real ({y} : Set E) ∂ μ := by
          exact MeasureTheory.integral_congr_ae hMarkovGenerated.restrict
    _ = ∫ _ in A, ((κ m) z ({y} : Set E)).toReal ∂ μ := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.self_mem_ae_restrict (μ := μ) (s := A) hA_measAmbient]
            with ω hω
          have hω : X n ω = z := hA_sub hω
          rw [hω]
          simp [Measure.real_def]
    _ = ((κ m) z ({y} : Set E)).toReal * μ.real A := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]

omit [Countable E] in
/-- Helper for Theorem 17.35: if a time-`n` history event already pins down the state at time
`n`, then intersecting it with a time-`n + m` singleton event factors through the `m`-step
transition mass from that pinned state. -/
private lemma measure_inter_prefix_stepEvent_eq_mul
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    {s z y : E} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = z}) :
    (P s : Measure Ω) (A ∩ {ω | X (n + m) ω = y}) =
      ((κ m) z ({y} : Set E)) * (P s : Measure Ω) A := by
  have hstep :
      (P s : Measure Ω).real (A ∩ {ω | X (n + m) ω = y}) =
        ((κ m) z ({y} : Set E)).toReal * (P s : Measure Ω).real A :=
    measure_inter_prefix_stepEvent_eq_mul_real
      (P := P) (X := X) (κ := κ) (s := s) (z := z) (y := y) (A := A) (n := n) (m := m)
        hA_meas hA_sub
  have hleft_ne_top :
      (P s : Measure Ω) (A ∩ {ω | X (n + m) ω = y}) ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ _
  have hkernel_ne_top : ((κ m) z ({y} : Set E)) ≠ ⊤ := by
    rw [← (show (P z : Measure Ω).map (X m) = κ m z from
      (inferInstance : IsMarkovProcessRealization κ P X).transition_eq z m)]
    exact MeasureTheory.measure_ne_top _ _
  have hright_ne_top :
      ((κ m) z ({y} : Set E)) * (P s : Measure Ω) A ≠ ⊤ := by
    exact ENNReal.mul_ne_top hkernel_ne_top (MeasureTheory.measure_ne_top _ _)
  exact (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top).mp <| by
    simpa [MeasureTheory.Measure.real_def, ENNReal.toReal_mul, MeasureTheory.measure_ne_top _ _]
      using hstep

omit [Countable E] in
/-- Helper for Theorem 17.35: off the reference diagonal, being at `y` at time `n + 1` while
still before the first return to `x` at time `n` already forces the stronger tail condition at
time `n + 1`. -/
private lemma beforeReturnStep_offDiag_eq_succTail
    {x y : E} (hyx : y ≠ x) (n : ℕ) :
    {ω | X (n + 1) ω = y ∧ ((n : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} =
      {ω | X (n + 1) ω = y ∧ (((n + 1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} := by
  ext ω
  constructor
  · rintro ⟨hstate, htail⟩
    have hsuccTail : (((n + 1 : ℕ) : ℕ∞) < (τ_[X, x]^1) ω) := by
      by_contra hnot
      have hle : (τ_[X, x]^1) ω ≤ n + 1 := le_of_not_gt hnot
      have hlt_top : (τ_[X, x]^1) ω < ⊤ := lt_of_le_of_lt hle (by simp)
      let m := ENat.lift ((τ_[X, x]^1) ω) hlt_top
      have hm_eq : (m : ℕ∞) = (τ_[X, x]^1) ω := ENat.coe_lift _ _
      have hm_le : m ≤ n + 1 := by
        simpa [m, hm_eq] using hle
      have hn_lt_m : n < m := by
        simpa [m, hm_eq] using htail
      have hm : m = n + 1 := Nat.le_antisymm hm_le (Nat.succ_le_of_lt hn_lt_m)
      have hτeq : (τ_[X, x]^1) ω = n + 1 := by
        calc
          (τ_[X, x]^1) ω = (m : ℕ∞) := hm_eq.symm
          _ = n + 1 := by simpa [hm]
      have hxstate : X (n + 1) ω = x := by
        have hcoene : ((n + 1 : ℕ) : ℕ∞) ≠ ⊤ := ENat.coe_ne_top (n + 1)
        have hne_top : (τ_[X, x]^1) ω ≠ ⊤ := by
          simpa [hτeq] using hcoene
        have hmem :
            X (((τ_[X, x]^1) ω).untopA) ω = x := by
          have h :
              X (MeasureTheory.hittingAfter X ({x} : Set E) 1 ω).untopA ω ∈ ({x} : Set E) :=
            MeasureTheory.hittingAfter_mem_set_of_ne_top
              (by simpa [iteratedEntranceTime_one] using hne_top)
          simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using h
        have huntop : ((τ_[X, x]^1) ω).untopA = n + 1 := by
          rw [WithTop.untopA_eq_untop hne_top]
          simpa [ENat.lift, hτeq] using (ENat.lift_coe (n + 1))
        simpa [huntop] using hmem
      exact hyx (hstate.symm.trans hxstate)
    exact ⟨hstate, hsuccTail⟩
  · rintro ⟨hstate, htail⟩
    exact ⟨hstate, lt_trans (by exact_mod_cast Nat.lt_succ_self n) htail⟩

/-- Helper for Theorem 17.35: `futurePrefixEvent X n f` fixes a finite future path after time
`n`. -/
private def futurePrefixEvent (Y : ℕ → Ω → E) (n : ℕ) {M : ℕ}
    (f : Fin (M + 1) → E) : Set Ω :=
  {ω | ∀ i : Fin (M + 1), Y (n + (i : ℕ)) ω = f i}

/-- Helper for Theorem 17.35: `noHitHorizon X x n M` records that the path avoids `x` during the
next `M` strictly positive times after time `n`. -/
private def noHitHorizon (Y : ℕ → Ω → E) (x : E) (n M : ℕ) : Set Ω :=
  {ω | ∀ m : ℕ, 1 ≤ m → m ≤ M → Y (n + m) ω ≠ x}

/-- Helper for Theorem 17.35: `tailNoHit X x n` is the event of never hitting `x` again after
time `n`. -/
private def tailNoHit (Y : ℕ → Ω → E) (x : E) (n : ℕ) : Set Ω :=
  ⋂ M : ℕ, noHitHorizon Y x n M

/-- Helper for Theorem 17.35: membership in the tail no-hit event is equivalent to avoiding `x`
at every strictly positive time after the reference time. -/
private lemma mem_tailNoHit_iff
    (Y : ℕ → Ω → E) (x : E) (n : ℕ) (ω : Ω) :
    ω ∈ tailNoHit Y x n ↔ ∀ m : ℕ, 1 ≤ m → Y (n + m) ω ≠ x := by
  constructor
  · intro hω m hm
    have hM : ω ∈ noHitHorizon Y x n m := Set.mem_iInter.mp hω m
    exact hM m hm le_rfl
  · intro hω
    refine Set.mem_iInter.mpr ?_
    intro M m hm hmM
    exact hω m hm

/-- Helper for Theorem 17.35: a finite future-prefix event is measurable in the ambient space. -/
private lemma measurableSet_futurePrefixEvent
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    {M n : ℕ} (f : Fin (M + 1) → E) :
    MeasurableSet (futurePrefixEvent X n f) := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  have hEq :
      futurePrefixEvent X n f = ⋂ i : Fin (M + 1), {ω | X (n + (i : ℕ)) ω = f i} := by
    ext ω
    simp [futurePrefixEvent]
  rw [hEq]
  refine MeasurableSet.iInter fun i ↦ ?_
  simpa [Set.preimage] using
    (hReal.measurable_process (n + (i : ℕ))) (MeasurableSet.singleton (f i))

/-- Helper for Theorem 17.35: a finite future-prefix event is measurable with respect to the
history filtration at its terminal time. -/
private lemma measurableSet_futurePrefixEvent_generated
    {M n : ℕ} (f : Fin (M + 1) → E) :
    MeasurableSet[generatedFiltrationSpace X (n + M)] (futurePrefixEvent X n f) := by
  have hEq :
      futurePrefixEvent X n f = ⋂ i : Fin (M + 1), {ω | X (n + (i : ℕ)) ω = f i} := by
    ext ω
    simp [futurePrefixEvent]
  rw [hEq]
  refine MeasurableSet.iInter fun i ↦ ?_
  have hXi : Measurable[generatedFiltrationSpace X (n + M)] (X (n + (i : ℕ))) := by
    refine Measurable.of_comap_le ?_
    exact
      le_iSup_of_le (n + (i : ℕ)) <|
        le_iSup_of_le (Nat.add_le_add_left (Nat.le_of_lt_succ i.2) n) le_rfl
  simpa [Set.preimage] using hXi (MeasurableSet.singleton (f i))

/-- Helper for Theorem 17.35: finite-horizon no-hit events are measurable. -/
private lemma measurableSet_noHitHorizon
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (x : E) (n M : ℕ) :
    MeasurableSet (noHitHorizon X x n M) := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  have hEq :
      noHitHorizon X x n M =
        ⋂ m ∈ Finset.Icc 1 M, {ω | X (n + m) ω ≠ x} := by
    ext ω
    simp [noHitHorizon]
  rw [hEq]
  refine MeasurableSet.iInter fun m ↦ ?_
  refine MeasurableSet.iInter fun _hm ↦ ?_
  exact ((hReal.measurable_process (n + m)) (MeasurableSet.singleton x)).compl

/-- Helper for Theorem 17.35: the tail no-hit event is measurable. -/
private lemma measurableSet_tailNoHit
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (x : E) (n : ℕ) :
    MeasurableSet (tailNoHit X x n) := by
  rw [tailNoHit]
  refine MeasurableSet.iInter fun M ↦ ?_
  exact measurableSet_noHitHorizon (P := P) (X := X) (κ := κ) x n M

/-- Helper for Theorem 17.35: at horizon `0`, an exact future-prefix event is just the current
state event. -/
private lemma futurePrefixEvent_zero_eq_stateEvent
    (Y : ℕ → Ω → E) (n : ℕ) (f : Fin 1 → E) :
    futurePrefixEvent Y n f = {ω | Y n ω = f 0} := by
  ext ω
  simp [futurePrefixEvent]

/-- Helper for Theorem 17.35: a longer exact future-prefix event splits into its shorter prefix
and terminal one-step event. -/
private lemma futurePrefixEvent_succ_eq
    (Y : ℕ → Ω → E) {M n : ℕ} (f : Fin (M + 2) → E) :
    futurePrefixEvent Y n f =
      futurePrefixEvent Y n (fun i : Fin (M + 1) ↦ f i.castSucc) ∩
        {ω | Y (n + (M + 1)) ω = f (Fin.last (M + 1))} := by
  ext ω
  constructor
  · intro hω
    refine ⟨?_, ?_⟩
    · intro i
      simpa [futurePrefixEvent] using hω i.castSucc
    · simpa [futurePrefixEvent] using hω (Fin.last (M + 1))
  · rintro ⟨hωPrefix, hωLast⟩
    intro i
    by_cases hi : i = Fin.last (M + 1)
    · subst hi
      simpa [futurePrefixEvent] using hωLast
    · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      simpa [futurePrefixEvent] using hωPrefix j

/-- Helper for Theorem 17.35: an exact future-prefix event determines its terminal state. -/
private lemma futurePrefixEvent_terminal_subset
    (Y : ℕ → Ω → E) {M n : ℕ} (f : Fin (M + 1) → E) :
    futurePrefixEvent Y n f ⊆ {ω | Y (n + M) ω = f (Fin.last M)} := by
  intro ω hω
  simpa [futurePrefixEvent] using hω (Fin.last M)

/-- Helper for Theorem 17.35: once a history event pins down the state at time `n`, intersecting
it with a finite exact future path factors through the path law started from that state. -/
private lemma measure_inter_prefix_futurePrefixEvent_eq_mul
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    {s y : E} {A : Set Ω} {n M : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y})
    (f : Fin (M + 1) → E) :
    (P s : Measure Ω) (A ∩ futurePrefixEvent X n f) =
      (P y : Measure Ω) (futurePrefixEvent X 0 f) * (P s : Measure Ω) A := by
  classical
  induction M with
  | zero =>
      let hReal : IsMarkovProcessRealization κ P X := inferInstance
      have hright_eval :
          (P y : Measure Ω) (futurePrefixEvent X 0 f) = if f 0 = y then 1 else 0 := by
        rw [futurePrefixEvent_zero_eq_stateEvent (Y := X) (n := 0) f]
        have hpreimage : {ω | X 0 ω = f 0} = X 0 ⁻¹' ({f 0} : Set E) := by
          ext ω
          simp
        rw [hpreimage]
        rw [← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton (f 0))]
        rw [hReal.initial_eq y]
        by_cases hf0 : f 0 = y <;> simp [hf0]
      by_cases hf0 : f 0 = y
      · have hleft_eq : A ∩ futurePrefixEvent X n f = A := by
          ext ω
          constructor
          · intro hω
            exact hω.1
          · intro hω
            refine ⟨hω, ?_⟩
            rw [futurePrefixEvent_zero_eq_stateEvent (Y := X) (n := n) f]
            simpa [hf0] using hA_sub hω
        calc
          (P s : Measure Ω) (A ∩ futurePrefixEvent X n f) = (P s : Measure Ω) A := by
            rw [hleft_eq]
          _ = 1 * (P s : Measure Ω) A := by rw [one_mul]
          _ = (P y : Measure Ω) (futurePrefixEvent X 0 f) * (P s : Measure Ω) A := by
            rw [hright_eval, if_pos hf0]
      · have hleft_eq : A ∩ futurePrefixEvent X n f = ∅ := by
          ext ω
          constructor
          · rintro ⟨hωA, hωf⟩
            rw [futurePrefixEvent_zero_eq_stateEvent (Y := X) (n := n) f] at hωf
            exact hf0 (hωf.symm.trans (hA_sub hωA))
          · intro hω
            exact False.elim (by simpa using hω)
        calc
          (P s : Measure Ω) (A ∩ futurePrefixEvent X n f) = 0 := by
            simp [hleft_eq]
          _ = (P y : Measure Ω) (futurePrefixEvent X 0 f) * (P s : Measure Ω) A := by
            rw [hright_eval, if_neg hf0]
            simp
  | succ M ih =>
      let g : Fin (M + 1) → E := fun i ↦ f i.castSucc
      let B : Set Ω := A ∩ futurePrefixEvent X n g
      have hA_meas_big : MeasurableSet[generatedFiltrationSpace X (n + M)] A := by
        let hmono :
            generatedFiltrationSpace X n ≤ generatedFiltrationSpace X (n + M) :=
          generatedFiltrationSpace_mono (Y := X) (hmn := Nat.le_add_right n M)
        exact hmono (s := A) hA_meas
      have hB_meas : MeasurableSet[generatedFiltrationSpace X (n + M)] B := by
        exact hA_meas_big.inter (measurableSet_futurePrefixEvent_generated (X := X) (n := n) g)
      have hB_sub : B ⊆ {ω | X (n + M) ω = g (Fin.last M)} := by
        intro ω hω
        exact futurePrefixEvent_terminal_subset (Y := X) (n := n) g hω.2
      have hleft_step :
          (P s : Measure Ω) (A ∩ futurePrefixEvent X n f) =
            ((κ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set E)) *
              (P s : Measure Ω) B := by
        calc
          (P s : Measure Ω) (A ∩ futurePrefixEvent X n f) =
              (P s : Measure Ω)
                (B ∩ {ω | X ((n + M) + 1) ω = f (Fin.last (M + 1))}) := by
                  simp [B, g, futurePrefixEvent_succ_eq, Nat.add_assoc, Set.inter_assoc,
                    Set.inter_left_comm, Set.inter_comm]
          _ =
              ((κ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set E)) *
                (P s : Measure Ω) B := by
                  simpa [B] using
                    measure_inter_prefix_stepEvent_eq_mul
                      (P := P) (X := X) (κ := κ) (s := s) (z := g (Fin.last M))
                      (y := f (Fin.last (M + 1))) (A := B) (n := n + M) (m := 1) hB_meas hB_sub
      have hg_meas :
          MeasurableSet[generatedFiltrationSpace X M] (futurePrefixEvent X 0 g) := by
        have htmp :
            MeasurableSet[generatedFiltrationSpace X (0 + M)] (futurePrefixEvent X 0 g) :=
          measurableSet_futurePrefixEvent_generated (X := X) (n := 0) g
        convert htmp using 1 <;> simp [zero_add]
      have hg_sub : futurePrefixEvent X 0 g ⊆ {ω | X M ω = g (Fin.last M)} := by
        have htmp :
            futurePrefixEvent X 0 g ⊆ {ω | X (0 + M) ω = g (Fin.last M)} :=
          futurePrefixEvent_terminal_subset (Y := X) (n := 0) g
        simpa [zero_add] using htmp
      have hright_step :
          (P y : Measure Ω) (futurePrefixEvent X 0 f) =
            ((κ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set E)) *
              (P y : Measure Ω) (futurePrefixEvent X 0 g) := by
        calc
          (P y : Measure Ω) (futurePrefixEvent X 0 f) =
              (P y : Measure Ω)
                (futurePrefixEvent X 0 g ∩
                  {ω | X (M + 1) ω = f (Fin.last (M + 1))}) := by
                  simp [g, futurePrefixEvent_succ_eq, Nat.add_assoc, Set.inter_assoc,
                    Set.inter_left_comm, Set.inter_comm]
          _ =
              ((κ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set E)) *
                (P y : Measure Ω) (futurePrefixEvent X 0 g) := by
                  simpa using
                    measure_inter_prefix_stepEvent_eq_mul
                      (P := P) (X := X) (κ := κ) (s := y) (z := g (Fin.last M))
                      (y := f (Fin.last (M + 1))) (A := futurePrefixEvent X 0 g) (n := M)
                      (m := 1) hg_meas hg_sub
      -- Proof comment: split off the last coordinate of the future path and reuse the induction
      -- hypothesis on the shorter prefix.
      calc
        (P s : Measure Ω) (A ∩ futurePrefixEvent X n f) =
            ((κ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set E)) *
              (P s : Measure Ω) B := hleft_step
        _ =
            ((κ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set E)) *
              ((P y : Measure Ω) (futurePrefixEvent X 0 g) * (P s : Measure Ω) A) := by
                rw [ih g]
        _ =
            (((κ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set E)) *
              (P y : Measure Ω) (futurePrefixEvent X 0 g)) * (P s : Measure Ω) A := by
                rw [mul_assoc]
        _ = (P y : Measure Ω) (futurePrefixEvent X 0 f) * (P s : Measure Ω) A := by
                rw [hright_step]

/-- Helper for Theorem 17.35: finite-horizon no-hit events factor against a history event that
already fixes the current state. -/
private lemma measure_inter_prefix_noHitHorizon_eq_mul
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    {s x y : E} {A : Set Ω} {n M : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P s : Measure Ω) (A ∩ noHitHorizon X x n M) =
      (P y : Measure Ω) (noHitHorizon X x 0 M) * (P s : Measure Ω) A := by
  classical
  let μs : Measure Ω := P s
  let T : Type v := {f : Fin (M + 1) → E // ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ x}
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  have hA_ambient : MeasurableSet A := by
    have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
      refine iSup₂_le fun k hk ↦ ?_
      exact (hReal.measurable_process k).comap_le
    exact hFiltration_le (s := A) hA_meas
  have hleft_union :
      A ∩ noHitHorizon X x n M = ⋃ f : T, A ∩ futurePrefixEvent X n f.1 := by
    ext ω
    constructor
    · rintro ⟨hωA, hωNoHit⟩
      let f : Fin (M + 1) → E := fun i ↦ X (n + (i : ℕ)) ω
      have hf : ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ x := by
        intro i hi
        exact hωNoHit (i : ℕ) hi (Nat.le_of_lt_succ i.2)
      refine Set.mem_iUnion.mpr ?_
      refine ⟨⟨f, hf⟩, ?_⟩
      refine ⟨hωA, ?_⟩
      intro i
      rfl
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨f, hωf⟩
      refine ⟨hωf.1, ?_⟩
      intro m hm hmM
      let i : Fin (M + 1) := ⟨m, Nat.lt_succ_of_le hmM⟩
      have hpath : X (n + m) ω = f.1 i := by
        simpa [futurePrefixEvent, i] using hωf.2 i
      exact hpath.trans_ne (f.2 i hm)
  have hright_union :
      noHitHorizon X x 0 M = ⋃ f : T, futurePrefixEvent X 0 f.1 := by
    ext ω
    constructor
    · intro hωNoHit
      let f : Fin (M + 1) → E := fun i ↦ X (i : ℕ) ω
      have hf : ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ x := by
        intro i hi
        simpa [f, zero_add] using hωNoHit (i : ℕ) hi (Nat.le_of_lt_succ i.2)
      refine Set.mem_iUnion.mpr ?_
      refine ⟨⟨f, hf⟩, ?_⟩
      intro i
      simp [f, zero_add]
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨f, hωf⟩
      intro m hm hmM
      let i : Fin (M + 1) := ⟨m, Nat.lt_succ_of_le hmM⟩
      have hpath : X (0 + m) ω = f.1 i := by
        simpa [futurePrefixEvent, i, zero_add] using hωf i
      exact hpath.trans_ne (f.2 i hm)
  have hpairwise_left :
      Pairwise (fun f g : T ↦ Disjoint (A ∩ futurePrefixEvent X n f.1)
        (A ∩ futurePrefixEvent X n g.1)) := by
    intro f g hfg
    refine Set.disjoint_left.2 ?_
    intro ω hωf hωg
    have hEq : f.1 = g.1 := by
      funext i
      exact (hωf.2 i).symm.trans (hωg.2 i)
    exact hfg (Subtype.ext hEq)
  have hpairwise_right :
      Pairwise (fun f g : T ↦ Disjoint (futurePrefixEvent X 0 f.1)
        (futurePrefixEvent X 0 g.1)) := by
    intro f g hfg
    refine Set.disjoint_left.2 ?_
    intro ω hωf hωg
    have hEq : f.1 = g.1 := by
      funext i
      exact (hωf i).symm.trans (hωg i)
    exact hfg (Subtype.ext hEq)
  have hleft_sum :
      μs (A ∩ noHitHorizon X x n M) =
        ∑' f : T, μs (A ∩ futurePrefixEvent X n f.1) := by
    rw [hleft_union, measure_iUnion hpairwise_left]
    intro f
    exact hA_ambient.inter (measurableSet_futurePrefixEvent (P := P) (X := X) (κ := κ) (n := n) f.1)
  have hright_sum :
      (P y : Measure Ω) (noHitHorizon X x 0 M) =
        ∑' f : T, (P y : Measure Ω) (futurePrefixEvent X 0 f.1) := by
    rw [hright_union, measure_iUnion hpairwise_right]
    intro f
    exact measurableSet_futurePrefixEvent (P := P) (X := X) (κ := κ) (n := 0) f.1
  -- Proof comment: partition the finite no-hit event by the entire future path over the horizon,
  -- then factor each cylinder set by the exact future-prefix lemma.
  calc
    μs (A ∩ noHitHorizon X x n M) =
        ∑' f : T, μs (A ∩ futurePrefixEvent X n f.1) := hleft_sum
    _ = ∑' f : T, (P y : Measure Ω) (futurePrefixEvent X 0 f.1) * μs A := by
          refine tsum_congr fun f ↦ ?_
          exact measure_inter_prefix_futurePrefixEvent_eq_mul
            (P := P) (X := X) (κ := κ) hA_meas hA_sub f.1
    _ = (∑' f : T, (P y : Measure Ω) (futurePrefixEvent X 0 f.1)) * μs A := by
          rw [ENNReal.tsum_mul_right]
    _ = (P y : Measure Ω) (noHitHorizon X x 0 M) * μs A := by
          rw [← hright_sum]

/-- Helper for Theorem 17.35: a zero-based no-hit horizon is exactly the tail event of the first
positive return time. -/
private lemma noHitHorizon_zero_eq_firstReturnTail
    (x : E) (M : ℕ) :
    noHitHorizon X x 0 M = {ω | (M : ℕ∞) < (τ_[X, x]^1) ω} := by
  -- Proof comment: avoiding `x` during the first `M` positive times is exactly the statement
  -- that the first positive return occurs after time `M`.
  ext ω
  constructor
  · intro hω
    change (M : ℕ∞) < (τ_[X, x]^1) ω
    by_contra hle
    have hle' : (τ_[X, x]^1) ω ≤ M := le_of_not_gt hle
    rcases (firstReturnTime_le_iff_existsHit (X := X) x M ω).1 hle' with ⟨j, hj1, hjM, hjx⟩
    exact hω j hj1 hjM (by simpa [zero_add] using hjx)
  · intro hω
    intro m hm1 hmM hmEq
    have hle : (τ_[X, x]^1) ω ≤ M :=
      (firstReturnTime_le_iff_existsHit (X := X) x M ω).2
        ⟨m, hm1, hmM, by simpa [zero_add] using hmEq⟩
    exact not_lt_of_ge hle hω

/-- Helper for Theorem 17.35: once `A` is already before the first return to `x` at time `n`,
adding a finite no-hit horizon after time `n` is the same as asking that the first return occurs
after time `n + M`. -/
private lemma inter_noHitHorizon_eq_inter_firstReturnTail
    {x : E} {A : Set Ω} {n M : ℕ}
    (hA_tail : A ⊆ {ω | ((n : ℕ) : ℕ∞) < (τ_[X, x]^1) ω}) :
    A ∩ noHitHorizon X x n M =
      A ∩ {ω | (((n + M : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)} := by
  ext ω
  constructor
  · rintro ⟨hωA, hωNoHit⟩
    refine ⟨hωA, ?_⟩
    by_contra hle
    have hle' : (τ_[X, x]^1) ω ≤ n + M := le_of_not_gt hle
    rcases (firstReturnTime_le_iff_existsHit (X := X) x (n + M) ω).1 hle' with ⟨j, hj1, hjnM, hjx⟩
    by_cases hjn : j ≤ n
    · have : (τ_[X, x]^1) ω ≤ n :=
        (firstReturnTime_le_iff_existsHit (X := X) x n ω).2 ⟨j, hj1, hjn, hjx⟩
      exact not_lt_of_ge this (hA_tail hωA)
    · have hlt : n < j := lt_of_not_ge hjn
      have hm : 1 ≤ j - n := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hlt)
      have hmM : j - n ≤ M := by
        omega
      have hjrew : X (n + (j - n)) ω = x := by
        simpa [Nat.add_sub_of_le (le_of_not_ge hjn)] using hjx
      exact hωNoHit (j - n) hm hmM hjrew
  · rintro ⟨hωA, hωTail⟩
    refine ⟨hωA, ?_⟩
    intro m hm hmM hmEq
    have hnm : 1 ≤ n + m := by
      omega
    have hle : (τ_[X, x]^1) ω ≤ n + M :=
      (firstReturnTime_le_iff_existsHit (X := X) x (n + M) ω).2
        ⟨n + m, hnm, Nat.add_le_add_left hmM n,
          by simpa [Nat.add_assoc] using hmEq⟩
    exact not_lt_of_ge hle hωTail

/-- Helper for Theorem 17.35: once a history event pins the chain to `y` at time `n` and is still
before the first return to `x`, finite first-return tails after time `n` factor through the
corresponding first-return tail started from `y`. -/
private lemma measure_inter_prefix_firstReturnTail_eq_mul
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    {s x y : E} {A : Set Ω} {n M : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y})
    (hA_tail : A ⊆ {ω | ((n : ℕ) : ℕ∞) < (τ_[X, x]^1) ω}) :
    (P s : Measure Ω) (A ∩ {ω | (((n + M : ℕ) : ℕ∞) < (τ_[X, x]^1) ω)}) =
      (P y : Measure Ω) {ω | ((M : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} * (P s : Measure Ω) A := by
  -- Route correction: replace the unstable raw `ℕ∞` tail manipulation by the theorem-local
  -- `noHitHorizon` interface, then translate back only at the start and end.
  rw [← inter_noHitHorizon_eq_inter_firstReturnTail (X := X) (hA_tail := hA_tail)]
  have hrestart :
      (P y : Measure Ω) {ω | ((M : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} =
        (P y : Measure Ω) (noHitHorizon X x 0 M) := by
    rw [noHitHorizon_zero_eq_firstReturnTail (X := X) x M]
  rw [hrestart]
  exact measure_inter_prefix_noHitHorizon_eq_mul
    (P := P) (X := X) (κ := κ) hA_meas hA_sub

omit [Countable E] in
/-- Helper for Theorem 17.35: positive-time hit events are measurable in the ambient
sigma-algebra. -/
private lemma measurableSet_positiveFutureHitEvent
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (x : E) :
    MeasurableSet {ω | ∃ m : ℕ, 0 < m ∧ X m ω = x} := by
  have hEq :
      {ω | ∃ m : ℕ, 0 < m ∧ X m ω = x} =
        ⋃ m : ℕ, {ω | 0 < m ∧ X m ω = x} := by
    ext ω
    simp
  rw [hEq]
  refine MeasurableSet.iUnion fun m ↦ ?_
  by_cases hm : 0 < m
  · have hEqm : {ω | 0 < m ∧ X m ω = x} = {ω | X m ω = x} := by
      ext ω
      simp [hm]
    rw [hEqm]
    let hReal : IsMarkovProcessRealization κ P X := inferInstance
    simpa [Set.preimage] using (hReal.measurable_process m) (MeasurableSet.singleton x)
  · have hEqm : {ω | 0 < m ∧ X m ω = x} = (∅ : Set Ω) := by
      ext ω
      simp [hm]
    rw [hEqm]
    simp

/-- Helper for Theorem 17.35: the first-return escape event is the complement of the positive-time
hit event. -/
private lemma firstReturnEscape_eq_compl_positiveFutureHitEvent
    (x : E) :
    {ω | (τ_[X, x]^1) ω = ⊤} = {ω | ∃ m : ℕ, 0 < m ∧ X m ω = x}ᶜ := by
  ext ω
  constructor
  · intro hω
    simp
    intro m hm hmx
    have hlt :
        MeasureTheory.hittingAfter X ({x} : Set E) 1 ω < ⊤ :=
      (hittingAfter_singleton_lt_top_iff X x ω).2 ⟨m, hm, hmx⟩
    exact ne_of_lt hlt (by simpa [iteratedEntranceTime_one] using hω)
  · intro hω
    have hnot : ¬ ∃ m : ℕ, 0 < m ∧ X m ω = x := by
      simpa using hω
    by_contra htop
    have hlt :
        MeasureTheory.hittingAfter X ({x} : Set E) 1 ω < ⊤ := by
      simpa [iteratedEntranceTime_one] using lt_top_iff_ne_top.2 htop
    rcases (hittingAfter_singleton_lt_top_iff X x ω).1 hlt with ⟨m, hm, hmx⟩
    exact hnot ⟨m, hm, hmx⟩

/-- Helper for Theorem 17.35: from time `0`, never hitting `x` again is exactly the first-return
escape event. -/
private lemma tailNoHit_zero_eq_firstReturnEscape
    (x : E) :
    tailNoHit X x 0 = {ω | (τ_[X, x]^1) ω = ⊤} := by
  ext ω
  constructor
  · intro hω
    have hnot : ¬ ∃ m : ℕ, 0 < m ∧ X m ω = x := by
      intro hhit
      rcases hhit with ⟨m, hm, hmx⟩
      exact (mem_tailNoHit_iff X x 0 ω).1 hω m hm (by simpa [Nat.zero_add] using hmx)
    by_contra htop
    have hlt :
        MeasureTheory.hittingAfter X ({x} : Set E) 1 ω < ⊤ := by
      simpa [iteratedEntranceTime_one] using lt_top_iff_ne_top.2 htop
    rcases (hittingAfter_singleton_lt_top_iff X x ω).1 hlt with ⟨m, hm, hmx⟩
    exact hnot ⟨m, hm, hmx⟩
  · intro hω
    refine (mem_tailNoHit_iff X x 0 ω).2 ?_
    intro m hm
    intro hmx
    have hlt :
        MeasureTheory.hittingAfter X ({x} : Set E) 1 ω < ⊤ :=
      (hittingAfter_singleton_lt_top_iff X x ω).2 ⟨m, hm, by simpa [Nat.zero_add] using hmx⟩
    exact ne_of_lt hlt (by simpa [iteratedEntranceTime_one] using hω)

/-- Helper for Theorem 17.35: after a history event already lies before the first return to `x`
at time `n`, the escape event is equivalent to tail-no-hit after time `n`. -/
private lemma inter_tailNoHit_eq_inter_firstReturnEscape
    {x : E} {A : Set Ω} {n : ℕ}
    (hA_tail : A ⊆ {ω | ((n : ℕ) : ℕ∞) < (τ_[X, x]^1) ω}) :
    A ∩ tailNoHit X x n = A ∩ {ω | (τ_[X, x]^1) ω = ⊤} := by
  ext ω
  constructor
  · rintro ⟨hωA, hωTail⟩
    refine ⟨hωA, ?_⟩
    by_contra htop
    have hlt :
        MeasureTheory.hittingAfter X ({x} : Set E) 1 ω < ⊤ := by
      simpa [iteratedEntranceTime_one] using lt_top_iff_ne_top.2 htop
    rcases (hittingAfter_singleton_lt_top_iff X x ω).1 hlt with ⟨m, hm, hmx⟩
    by_cases hmn : m ≤ n
    · have hle : (τ_[X, x]^1) ω ≤ n :=
        (firstReturnTime_le_iff_existsHit (X := X) x n ω).2 ⟨m, hm, hmn, hmx⟩
      exact not_lt_of_ge hle (hA_tail hωA)
    · have hmn' : n < m := lt_of_not_ge hmn
      have hm' : 1 ≤ m - n := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hmn')
      have hrew : X (n + (m - n)) ω = x := by
        simpa [Nat.add_sub_of_le hmn'.le] using hmx
      exact (mem_tailNoHit_iff X x n ω).1 hωTail (m - n) hm' hrew
  · rintro ⟨hωA, hωEscape⟩
    refine ⟨hωA, (mem_tailNoHit_iff X x n ω).2 ?_⟩
    intro m hm hmx
    have hnm : 1 ≤ n + m := by
      omega
    have hlt :
        MeasureTheory.hittingAfter X ({x} : Set E) 1 ω < ⊤ :=
      (hittingAfter_singleton_lt_top_iff X x ω).2 ⟨n + m, hnm,
        by simpa [Nat.add_assoc] using hmx⟩
    exact ne_of_lt hlt hωEscape

/-- Helper for Theorem 17.35: once a history event fixes the present state to `x`, the tail-no-hit
factorization passes from finite horizons to the full tail event by continuity from above. -/
private lemma measure_inter_prefix_tailNoHit_eq_mul
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    {s x y : E} {A : Set Ω} {n : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P s : Measure Ω) (A ∩ tailNoHit X x n) =
      (P y : Measure Ω) (tailNoHit X x 0) * (P s : Measure Ω) A := by
  let μs : Measure Ω := P s
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  have hA_ambient : MeasurableSet A := by
    exact (generatedFiltrationSpace_le_ambient (X := X) hReal.measurable_process n) _ hA_meas
  have htail_eq : A ∩ tailNoHit X x n = ⋂ M : ℕ, A ∩ noHitHorizon X x n M := by
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
  have hleft_antitone : Antitone (fun M : ℕ ↦ A ∩ noHitHorizon X x n M) := by
    intro M N hMN ω hω
    refine ⟨hω.1, ?_⟩
    exact fun m hm hmM ↦ hω.2 m hm (hmM.trans hMN)
  have hright_antitone : Antitone (fun M : ℕ ↦ noHitHorizon X x 0 M) := by
    intro M N hMN ω hω m hm hmM
    exact hω m hm (hmM.trans hMN)
  have hleft_tendsto :
      Filter.Tendsto (fun M ↦ μs (A ∩ noHitHorizon X x n M)) Filter.atTop
        (nhds (μs (A ∩ tailNoHit X x n))) := by
    simpa [htail_eq] using
      tendsto_measure_iInter_atTop (μ := μs)
        (fun M ↦ (hA_ambient.inter
          (measurableSet_noHitHorizon (P := P) (X := X) (κ := κ) x n M)).nullMeasurableSet)
        hleft_antitone
        ⟨0, measure_ne_top _ _⟩
  have hright_base :
      Filter.Tendsto (fun M ↦ (P y : Measure Ω) (noHitHorizon X x 0 M)) Filter.atTop
        (nhds ((P y : Measure Ω) (tailNoHit X x 0))) := by
    simpa [tailNoHit] using
      tendsto_measure_iInter_atTop (μ := (P y : Measure Ω))
        (fun M ↦
          (measurableSet_noHitHorizon (P := P) (X := X) (κ := κ) x 0 M).nullMeasurableSet)
        hright_antitone
        ⟨0, measure_ne_top _ _⟩
  have hEq :
      (fun M ↦ μs (A ∩ noHitHorizon X x n M)) =
        fun M ↦ (P y : Measure Ω) (noHitHorizon X x 0 M) * μs A := by
    funext M
    exact measure_inter_prefix_noHitHorizon_eq_mul
      (P := P) (X := X) (κ := κ) hA_meas hA_sub
  have hleft_real_tendsto :
      Filter.Tendsto (fun M ↦ (μs (A ∩ noHitHorizon X x n M)).toReal) Filter.atTop
        (nhds ((μs (A ∩ tailNoHit X x n)).toReal)) := by
    exact (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp hleft_tendsto
  have hright_real_base :
      Filter.Tendsto (fun M ↦ ((P y : Measure Ω) (noHitHorizon X x 0 M)).toReal) Filter.atTop
        (nhds (((P y : Measure Ω) (tailNoHit X x 0)).toReal)) := by
    exact (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp hright_base
  have hright_real_tendsto :
      Filter.Tendsto
        (fun M ↦ ((P y : Measure Ω) (noHitHorizon X x 0 M)).toReal * (μs A).toReal)
        Filter.atTop
        (nhds (((P y : Measure Ω) (tailNoHit X x 0)).toReal * (μs A).toReal)) := by
    exact hright_real_base.mul_const ((μs A).toReal)
  have hEqReal :
      (fun M ↦ (μs (A ∩ noHitHorizon X x n M)).toReal) =
        fun M ↦ ((P y : Measure Ω) (noHitHorizon X x 0 M)).toReal * (μs A).toReal := by
    funext M
    have hEqM :
        μs (A ∩ noHitHorizon X x n M) =
          (P y : Measure Ω) (noHitHorizon X x 0 M) * μs A := by
      exact measure_inter_prefix_noHitHorizon_eq_mul
        (P := P) (X := X) (κ := κ) hA_meas hA_sub
    simpa [ENNReal.toReal_mul, measure_ne_top _ _, measure_ne_top _ _] using
      congrArg ENNReal.toReal hEqM
  rw [hEqReal] at hleft_real_tendsto
  have hreal_eq :
      (μs (A ∩ tailNoHit X x n)).toReal =
        ((P y : Measure Ω) (tailNoHit X x 0)).toReal * (μs A).toReal :=
    tendsto_nhds_unique hleft_real_tendsto hright_real_tendsto
  have hleft_ne_top : μs (A ∩ tailNoHit X x n) ≠ ⊤ := measure_ne_top _ _
  have hright_ne_top :
      (P y : Measure Ω) (tailNoHit X x 0) * μs A ≠ ⊤ := by
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  exact (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top).mp <| by
    simpa [ENNReal.toReal_mul, measure_ne_top _ _, measure_ne_top _ _] using hreal_eq

/-- Helper for Theorem 17.35: once a history event pins the chain to `y` at time `n` and is still
before the first return to `x`, the escape event factors through the restarted escape probability
from `y`. -/
private lemma measure_inter_prefix_escapeEvent_eq_mul
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    {s x y : E} {A : Set Ω} {n : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y})
    (hA_tail : A ⊆ {ω | ((n : ℕ) : ℕ∞) < (τ_[X, x]^1) ω}) :
    (P s : Measure Ω) (A ∩ {ω | (τ_[X, x]^1) ω = ⊤}) =
      (P y : Measure Ω) {ω | (τ_[X, x]^1) ω = ⊤} * (P s : Measure Ω) A := by
  -- Route correction: factor the stable `tailNoHit` event and only then identify it with the
  -- first-return escape event on both sides.
  rw [← inter_tailNoHit_eq_inter_firstReturnEscape (X := X) (hA_tail := hA_tail)]
  have hrestart :
      (P y : Measure Ω) {ω | (τ_[X, x]^1) ω = ⊤} =
        (P y : Measure Ω) (tailNoHit X x 0) := by
    rw [← tailNoHit_zero_eq_firstReturnEscape (X := X) x]
  rw [hrestart]
  exact measure_inter_prefix_tailNoHit_eq_mul
    (P := P) (X := X) (κ := κ) hA_meas hA_sub

/-- Helper for Theorem 17.35: recurrence of `x` means the first-return escape event has zero
probability under `P x`. -/
private lemma measure_firstReturnEscape_eq_zero_of_isRecurrentState
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (x : E) (hx : IsRecurrentState P X x) :
    (P x : Measure Ω) {ω | (τ_[X, x]^1) ω = ⊤} = 0 := by
  have hmeas :
      MeasurableSet {ω | (τ_[X, x]^1) ω = ⊤} := by
    rw [firstReturnEscape_eq_compl_positiveFutureHitEvent (X := X) x]
    exact (measurableSet_positiveFutureHitEvent (P := P) (X := X) (κ := κ) x).compl
  have hreal :
      (P x : Measure Ω).real {ω | (τ_[X, x]^1) ω = ⊤} = 0 := by
    have hcomp :
        {ω | (τ_[X, x]^1) ω = ⊤}ᶜ = {ω | ∃ m : ℕ, 0 < m ∧ X m ω = x} := by
      ext ω
      simp [firstReturnEscape_eq_compl_positiveFutureHitEvent (X := X) x]
    -- Proof comment: the escape event is the complement of the positive-time hit event, whose
    -- probability is `F(x, x) = 1` by recurrence.
    calc
      (P x : Measure Ω).real {ω | (τ_[X, x]^1) ω = ⊤}
          = (P x : Measure Ω).real ({ω | (τ_[X, x]^1) ω = ⊤}ᶜ)ᶜ := by simp
      _ = 1 - (P x : Measure Ω).real ({ω | (τ_[X, x]^1) ω = ⊤}ᶜ) := by
            simpa using
              (MeasureTheory.probReal_compl_eq_one_sub (μ := (P x : Measure Ω))
                (s := {ω | (τ_[X, x]^1) ω = ⊤}ᶜ) hmeas.compl)
      _ = 1 - (F[P, X]) x x := by
            rw [hcomp]
            simp [everHitsProbability_def]
      _ = 0 := by
            simp [IsRecurrentState] at hx
            simp [hx]
  simpa [MeasureTheory.Measure.real_def, ENNReal.toReal_eq_zero_iff] using hreal

omit [Countable E] in
/-- Helper for Theorem 17.35: at the first positive communication time from `x` to `y`, the
time-`n` state event is already before the first positive return to `x`. -/
private lemma measure_minimalCommunicationPrefix_eq_stateEvent
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    {x y : E} {n : ℕ}
    (hxy_ne : x ≠ y)
    (hnpos : 0 < n)
    (hmin : ∀ m : ℕ, 0 < m → m < n → (κ m) x ({y} : Set E) = 0) :
    (P x : Measure Ω) {ω | X n ω = y ∧ ((n : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} =
      (P x : Measure Ω) {ω | X n ω = y} := by
  let A : Set Ω := {ω | X n ω = y ∧ ((n : ℕ) : ℕ∞) < (τ_[X, x]^1) ω}
  let bad : Set Ω := {ω | X n ω = y} \ A
  have hbad_zero : (P x : Measure Ω) bad = 0 := by
    have hbad_subset :
        bad ⊆ ⋃ m ∈ ((Finset.Icc 1 (n - 1) : Finset ℕ) : Set ℕ),
          ({ω | X m ω = x} ∩ {ω | X n ω = y}) := by
      intro ω hω
      have hτle : (τ_[X, x]^1) ω ≤ n := by
        by_contra hτgt
        exact hω.2 ⟨hω.1, lt_of_not_ge hτgt⟩
      rcases (firstReturnTime_le_iff_existsHit (X := X) x n ω).1 hτle with
        ⟨m, hm1, hmn, hmx⟩
      have hmn' : m ≤ n - 1 := by
        have hm_ne : m ≠ n := by
          intro hm_eq
          exact hxy_ne (hmx.symm.trans (by simpa [hm_eq] using hω.1))
        exact Nat.le_pred_of_lt (lt_of_le_of_ne hmn hm_ne)
      exact Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2
        ⟨Finset.mem_Icc.mpr ⟨hm1, hmn'⟩, ⟨hmx, hω.1⟩⟩⟩
    have hzero_each :
        ∀ m : ℕ,
          m ∈ ((Finset.Icc 1 (n - 1) : Finset ℕ) : Set ℕ) →
            (P x : Measure Ω) ({ω | X m ω = x} ∩ {ω | X n ω = y}) = 0 := by
      intro m hm
      have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
      have hmn : m < n := by
        exact lt_of_le_of_lt (Finset.mem_Icc.mp hm).2
          (Nat.sub_lt (Nat.succ_le_of_lt hnpos) zero_lt_one)
      have hgap_zero : (κ (n - m)) x ({y} : Set E) = 0 := by
        have hgap_pos : 0 < n - m := Nat.sub_pos_of_lt hmn
        have hgap_lt : n - m < n := Nat.sub_lt (Nat.succ_le_of_lt hnpos) hmpos
        exact hmin (n - m) hgap_pos hgap_lt
      have hmeas : MeasurableSet[generatedFiltrationSpace X m] {ω | X m ω = x} := by
        simpa using measurableSet_stateEvent_generated (Y := X) x le_rfl
      have hsub : {ω | X m ω = x} ⊆ {ω | X m ω = x} := by
        intro ω hω
        exact hω
      have hstep :
          (P x : Measure Ω) ({ω | X m ω = x} ∩ {ω | X (m + (n - m)) ω = y}) =
            (κ (n - m)) x ({y} : Set E) * (P x : Measure Ω) {ω | X m ω = x} := by
        exact measure_inter_prefix_stepEvent_eq_mul
          (P := P) (X := X) (κ := κ) (s := x) (z := x) (y := y)
          (A := {ω | X m ω = x}) (n := m) (m := n - m) hmeas hsub
      simpa [Nat.add_sub_of_le hmn.le, hgap_zero] using hstep
    have hbad_zero_union :
        (P x : Measure Ω)
          (⋃ m ∈ ((Finset.Icc 1 (n - 1) : Finset ℕ) : Set ℕ),
            ({ω | X m ω = x} ∩ {ω | X n ω = y})) = 0 := by
      exact measure_iUnion_null fun m ↦
        measure_iUnion_null fun hm ↦ hzero_each m hm
    have hbad_le :
        (P x : Measure Ω) bad ≤
          (P x : Measure Ω)
            (⋃ m ∈ ((Finset.Icc 1 (n - 1) : Finset ℕ) : Set ℕ),
              ({ω | X m ω = x} ∩ {ω | X n ω = y})) :=
      MeasureTheory.measure_mono hbad_subset
    exact le_antisymm (le_trans hbad_le (le_of_eq hbad_zero_union)) bot_le
  have hA_subset : A ⊆ {ω | X n ω = y} := by
    intro ω hω
    exact hω.1
  apply le_antisymm
  · exact MeasureTheory.measure_mono hA_subset
  · have hcover : {ω | X n ω = y} ⊆ A ∪ bad := by
      intro ω hω
      by_cases hωA : ω ∈ A
      · exact Or.inl hωA
      · exact Or.inr ⟨hω, hωA⟩
    calc
      (P x : Measure Ω) {ω | X n ω = y}
          ≤ (P x : Measure Ω) (A ∪ bad) := MeasureTheory.measure_mono hcover
      _ ≤ (P x : Measure Ω) A + (P x : Measure Ω) bad := MeasureTheory.measure_union_le _ _
      _ = (P x : Measure Ω) A := by simp [hbad_zero]

/-- Helper for Theorem 17.35: the off-diagonal case reduces to one future-path factorization
across the minimal communication time. -/
private lemma reverseEverHitsProbability_eq_one_of_isRecurrentState_of_everHitsProbability_pos
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X] {x y : E}
    (hxy_ne : x ≠ y) (hx : IsRecurrentState P X x) (hxy : 0 < (F[P, X]) x y) :
    (F[P, X]) y x = 1 := by
  rcases existsMinimalPosTransitionMassOfEverHitsProbabilityPos
      (P := P) (X := X) (κ := κ) hxy with ⟨n, hnpos, hmass, hmin⟩
  let A : Set Ω := {ω | X n ω = y ∧ ((n : ℕ) : ℕ∞) < (τ_[X, x]^1) ω}
  let escape : Set Ω := {ω | (τ_[X, x]^1) ω = ⊤}
  have hA_meas : MeasurableSet[generatedFiltrationSpace X n] A := by
    exact
      (measurableSet_stateEvent_generated (Y := X) y (hi := le_rfl)).inter
        (measurableSet_firstReturnTimeTail_generated (X := X) x n)
  have hA_sub : A ⊆ {ω | X n ω = y} := by
    intro ω hω
    exact hω.1
  have hA_tail : A ⊆ {ω | ((n : ℕ) : ℕ∞) < (τ_[X, x]^1) ω} := by
    intro ω hω
    exact hω.2
  have hA_eq :
      (P x : Measure Ω) A = (P x : Measure Ω) {ω | X n ω = y} :=
    measure_minimalCommunicationPrefix_eq_stateEvent
      (P := P) (X := X) (κ := κ) hxy_ne hnpos hmin
  have hA_pos : 0 < (P x : Measure Ω) A := by
    rw [hA_eq, measure_stateEvent_eq_transitionMass (P := P) (X := X) (κ := κ) x y n]
    exact hmass
  have hfactor :
      (P x : Measure Ω) (A ∩ escape) = (P y : Measure Ω) escape * (P x : Measure Ω) A :=
    measure_inter_prefix_escapeEvent_eq_mul
      (P := P) (X := X) (κ := κ) (s := x) (x := x) (y := y) (A := A) (n := n)
      hA_meas hA_sub hA_tail
  have hleft_zero : (P x : Measure Ω) (A ∩ escape) = 0 := by
    apply le_antisymm
    · exact le_trans (MeasureTheory.measure_mono Set.inter_subset_right)
        (le_of_eq (measure_firstReturnEscape_eq_zero_of_isRecurrentState
          (P := P) (X := X) (κ := κ) x hx))
    · exact bot_le
  have hEscape_zero : (P y : Measure Ω) escape = 0 := by
    have hmul_zero : (P y : Measure Ω) escape * (P x : Measure Ω) A = 0 := by
      simpa [hleft_zero] using hfactor.symm
    rcases mul_eq_zero.mp hmul_zero with hzero | hzero
    · exact hzero
    · exact (hA_pos.ne' hzero).elim
  have hescape_meas : MeasurableSet escape := by
    simpa [escape, firstReturnEscape_eq_compl_positiveFutureHitEvent (X := X) x] using
      (measurableSet_positiveFutureHitEvent (P := P) (X := X) (κ := κ) x).compl
  -- Proof comment: zero escape probability from `y` means the positive-time hit event of `x`
  -- has probability one under `P y`.
  calc
    (F[P, X]) y x = (P y : Measure Ω).real {ω | ∃ m : ℕ, 0 < m ∧ X m ω = x} := by
      simp [everHitsProbability_def]
    _ = (P y : Measure Ω).real (escapeᶜ) := by
          simpa [escape, firstReturnEscape_eq_compl_positiveFutureHitEvent (X := X) x]
    _ = 1 - (P y : Measure Ω).real escape := by
          simpa using
            (MeasureTheory.probReal_compl_eq_one_sub (μ := (P y : Measure Ω))
              (s := escape) hescape_meas)
    _ = 1 := by
          simp [MeasureTheory.Measure.real_def, ENNReal.toReal_eq_zero_iff, hEscape_zero]

/-- Helper for Theorem 17.35: the strictly positive visit times of the path `ω` at the state
`x`. -/
private def positiveVisitSet (Y : ℕ → Ω → E) (x : E) (ω : Ω) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ Y n ω = x}

/-- Helper for Theorem 17.35: a bound on the infimum of a set of natural times in `ℕ∞` is
equivalent to a bounded witness in the underlying set. -/
private lemma sInf_natImage_le_iff {S : Set ℕ} {N : ℕ} :
    sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) ≤ N ↔ ∃ n ∈ S, n ≤ N := by
  -- Route correction: reuse the current Chapter 17 `ℕ∞`-infimum normalization instead of the
  -- stale placeholder route from the older prefix-count port.
  by_cases hS : S.Nonempty
  · -- Proof comment: once `S` is nonempty, the `ℕ∞` infimum is the coerced natural infimum, so
    -- the bound is witnessed by `Nat.sInf_mem`.
    let m : ℕ := sInf S
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
  · -- Proof comment: for the empty set the infimum is `⊤`, so neither side can hold.
    have hS_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    subst hS_empty
    simp

/-- Helper for Theorem 17.35: the successor entrance time is bounded by `N` exactly when there
is a visit to `x` by time `N` occurring strictly after the previous entrance. -/
private lemma iteratedEntranceTime_succ_le_iff_exists_hitAfter
    (Y : ℕ → Ω → E) (x : E) (ω : Ω) (k : ℕ+) (N : ℕ) :
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

/-- Helper for Theorem 17.35: `prefixHasIteratedReturn x k m f` records `k` strictly positive
visits to `x` inside the finite prefix `f : Fin m → E`. -/
private def prefixHasIteratedReturn (x : E) : ℕ+ → ∀ m : ℕ, (Fin m → E) → Prop
  := fun k =>
    PNat.recOn k
      (fun m f => ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = x)
      (fun _ ih m f =>
        ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = x ∧
          ih i (fun j : Fin i ↦ f ⟨j, Nat.lt_trans j.2 i.2⟩))

/-- Helper for Theorem 17.35: unfold `prefixHasIteratedReturn` at the first positive index. -/
private lemma prefixHasIteratedReturn_one_iff
    (x : E) (m : ℕ) (f : Fin m → E) :
    prefixHasIteratedReturn x 1 m f ↔ ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = x := by
  simp [prefixHasIteratedReturn]

/-- Helper for Theorem 17.35: unfold `prefixHasIteratedReturn` at a successor positive index. -/
private lemma prefixHasIteratedReturn_succ_iff
    (x : E) (k : ℕ+) (m : ℕ) (f : Fin m → E) :
    prefixHasIteratedReturn x (k + 1) m f ↔
      ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = x ∧
        prefixHasIteratedReturn x k i (fun j : Fin i ↦ f ⟨j, Nat.lt_trans j.2 i.2⟩) := by
  simp [prefixHasIteratedReturn]

/-- Helper for Theorem 17.35: the bounded event `τ_[Y, x]^k < m` is exactly the recursive
finite-prefix predicate on the first `m` coordinates of the path. -/
private lemma iteratedEntranceTime_lt_iff_prefixHasIteratedReturn
    (Y : ℕ → Ω → E) (x : E) (ω : Ω) :
    ∀ (k : ℕ+) (m : ℕ),
      (τ_[Y, x]^k) ω < m ↔
        prefixHasIteratedReturn x k m (fun i : Fin m ↦ Y i ω) := by
  intro k
  induction k using PNat.recOn with
  | one =>
      intro m
      cases m with
      | zero =>
          -- Proof comment: there is no strictly positive time inside the empty prefix.
          constructor
          · intro h
            simpa using h
          · intro h
            rcases h with ⟨i, _, _⟩
            exact Fin.elim0 i
      | succ m =>
          -- Proof comment: the first entrance time is the usual positive-time hitting time, so
          -- the finite-prefix description is exactly `hittingAfter_lt_iff` specialized to `{x}`.
          constructor
          · intro h
            have hhit :
                hittingAfter Y ({x} : Set E) 1 ω < ↑(m + 1) := by
              simpa [iteratedEntranceTime_one] using h
            rcases (MeasureTheory.hittingAfter_lt_iff
              (u := Y) (s := ({x} : Set E)) (n := 1) (ω := ω) (i := m + 1)).1 hhit with
              ⟨n, hn_mem, hn_eq⟩
            exact (prefixHasIteratedReturn_one_iff x (m + 1) (fun i : Fin (m + 1) ↦ Y i ω)).2
              ⟨⟨n, hn_mem.2⟩, by simpa using hn_mem.1,
                by simpa [Set.mem_singleton_iff] using hn_eq⟩
          · intro h
            rcases (prefixHasIteratedReturn_one_iff x (m + 1) (fun i : Fin (m + 1) ↦ Y i ω)).1 h with
              ⟨i, hi_pos, hi_eq⟩
            have hhit :
                hittingAfter Y ({x} : Set E) 1 ω < ↑(m + 1) := by
              exact (MeasureTheory.hittingAfter_lt_iff
                (u := Y) (s := ({x} : Set E)) (n := 1) (ω := ω) (i := m + 1)).2
                ⟨i, ⟨by simpa using hi_pos, i.2⟩, by simpa [Set.mem_singleton_iff] using hi_eq⟩
            simpa [iteratedEntranceTime_one] using hhit
  | succ k ih =>
      intro m
      cases m with
      | zero =>
          -- Proof comment: a nontrivial iterated return cannot occur inside an empty prefix.
          constructor
          · intro h
            simpa using h
          · intro h
            rcases (prefixHasIteratedReturn_succ_iff x k 0 (fun i : Fin 0 ↦ Y i ω)).1 h with
              ⟨i, _, _, _⟩
            exact Fin.elim0 i
      | succ m =>
          -- Proof comment: the last positive visit in the prefix is the witness that converts the
          -- successor entrance-time bound into the recursive prefix predicate, and conversely.
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
                by simpa using hn_eq,
                (ih n).1 hτn⟩
          · intro h
            rcases (prefixHasIteratedReturn_succ_iff x k (m + 1)
              (fun i : Fin (m + 1) ↦ Y i ω)).1 h with
              ⟨i, hi_pos, hi_eq, hi_prefix⟩
            have hle : (τ_[Y, x]^(k + 1)) ω ≤ m := by
              exact (iteratedEntranceTime_succ_le_iff_exists_hitAfter
                (Y := Y) (x := x) (ω := ω) (k := k) (N := m)).2
                ⟨i, (ih i).2 hi_prefix, Nat.le_of_lt_succ i.2, by simpa using hi_eq⟩
            exact hbound.mpr hle

/-- Helper for Theorem 17.35: the recursive finite-prefix witness forces at least the
corresponding number of positive visits in that prefix. -/
private lemma prefixHasIteratedReturn_le_card
    (x : E) :
    ∀ {k : ℕ+} {m : ℕ} {f : Fin m → E},
      prefixHasIteratedReturn x k m f →
        (k : ℕ) ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = x).card := by
  intro k
  induction k using PNat.recOn with
  | one =>
      intro m f h
      -- Proof comment: the first-return witness already belongs to the filtered prefix set.
      rcases (prefixHasIteratedReturn_one_iff x m f).1 h with ⟨i, hi_pos, hi_eq⟩
      have hone : 1 ≤ (Finset.univ.filter fun j : Fin m ↦ 0 < (j : ℕ) ∧ f j = x).card := by
        rw [Finset.one_le_card]
        exact ⟨i, by simp [hi_pos, hi_eq]⟩
      simpa using hone
  | succ k ih =>
      intro m f h
      -- Proof comment: remove the last witnessed visit; the recursive witness gives `k` earlier
      -- visits, and they inject into the remaining filtered prefix.
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

/-- Helper for Theorem 17.35: inside a finite prefix, at least `k` positive visits force the
recursive prefix witness for the `k`th iterated return. -/
private lemma prefixHasIteratedReturn_of_le_card
    (x : E) :
    ∀ {k : ℕ+} {m : ℕ} {f : Fin m → E},
      (k : ℕ) ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = x).card →
        prefixHasIteratedReturn x k m f := by
  intro k
  induction k using PNat.recOn with
  | one =>
      intro m f h
      -- Proof comment: if the filtered hit set has cardinality at least `1`, it already supplies
      -- the witness needed for the base case.
      have h' : 1 ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = x).card := by
        simpa using h
      rw [Finset.one_le_card] at h'
      rcases h' with ⟨i, hi_mem⟩
      have hi_props : 0 < (i : ℕ) ∧ f i = x := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi_mem
      exact (prefixHasIteratedReturn_one_iff x m f).2 ⟨i, hi_props.1, hi_props.2⟩
  | succ k ih =>
      intro m f h
      -- Proof comment: choose the last positive visit in the filtered prefix, erase it, and
      -- recurse on the remaining earlier visits transported into the shorter prefix.
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
            -- Route correction: pick the strict-inequality branch first, then compare values.
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
            -- Route correction: rewrite to the true branch and close by extensionality on `Fin`.
            have ha' : (a₁ : ℕ) < i := ha_lt
            change
              (if h : (a₁ : ℕ) < i then (⟨(a₁ : ℕ), h⟩ : Fin i) else ⟨0, hi_props.1⟩) =
                ⟨(a₁ : ℕ), ha_lt⟩
            rw [dif_pos ha']
          have hb_seg : toInitialSegment b = ⟨(b : ℕ), hb_lt⟩ := by
            -- Route correction: the second image uses the same branch normalization.
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

/-- Helper for Theorem 17.35: the recursive finite-prefix witness is equivalent to asking for at
least `k` positive visits to `x` in that prefix. -/
private lemma prefixHasIteratedReturn_iff_prefixVisitCountAtLeast
    (x : E) {k : ℕ+} {m : ℕ} {f : Fin m → E} :
    prefixHasIteratedReturn x k m f ↔
      (k : ℕ) ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = x).card := by
  -- Proof comment: the recursive prefix predicate and the cardinality condition encode the same
  -- bounded-prefix notion of the `k`th positive return to `x`.
  constructor
  · exact prefixHasIteratedReturn_le_card x
  · exact prefixHasIteratedReturn_of_le_card x

/-- Helper for Theorem 17.35: the event `τ_[Y, x]^k < m` is equivalent to having at least `k`
positive visits to `x` in the first `m` coordinates of the path. -/
private lemma iteratedEntranceTime_lt_iff_prefixVisitCountAtLeast
    (Y : ℕ → Ω → E) (x : E) (ω : Ω) :
    ∀ (k : ℕ+) (m : ℕ),
      (τ_[Y, x]^k) ω < m ↔
        (k : ℕ) ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ Y i ω = x).card
  | k, m => by
      classical
      -- Proof comment: collapse the recursive prefix predicate to the direct visit-count normal
      -- form.
      rw [iteratedEntranceTime_lt_iff_prefixHasIteratedReturn,
        prefixHasIteratedReturn_iff_prefixVisitCountAtLeast]

/-- Helper for Theorem 17.35: the event `τ_[Y, x]^k ≤ N` is equivalent to having at least `k`
positive visits to `x` in the first `N + 1` coordinates of the path. -/
private lemma iteratedEntranceTime_le_iff_prefixVisitCountAtLeast
    (Y : ℕ → Ω → E) (x : E) (ω : Ω) :
    ∀ (k : ℕ+) (N : ℕ),
      (τ_[Y, x]^k) ω ≤ N ↔
        (k : ℕ) ≤
          (Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = x).card
  | k, N => by
      -- Proof comment: on `ℕ∞`, the bound `≤ N` is the same as strict inequality below `N + 1`.
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

/-- Helper for Theorem 17.35: every bounded prefix count of visits to `x` injects into the full
set of positive visit times. -/
private lemma prefixHitCount_le_positiveVisitEncard
    (Y : ℕ → Ω → E) (x : E) (ω : Ω) (N : ℕ) :
    ((Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = x).card : ℕ∞) ≤
      (positiveVisitSet Y x ω).encard := by
  classical
  let s : Set (Fin (N + 1)) := {i : Fin (N + 1) | 0 < (i : ℕ) ∧ Y i ω = x}
  have hs_subset : (fun i : Fin (N + 1) ↦ (i : ℕ)) '' s ⊆ positiveVisitSet Y x ω := by
    intro n hn
    rcases hn with ⟨i, hi, rfl⟩
    exact ⟨Nat.succ_le_of_lt hi.1, hi.2⟩
  -- Proof comment: identify the filtered prefix finset with its image inside the full positive
  -- visit set and compare the resulting encards by monotonicity.
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

/-- Helper for Theorem 17.35: among positive integers, exactly `m` indices satisfy `k ≤ m`. -/
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
  -- Proof comment: transport the positive-natural counting problem to the ordinary initial
  -- segment `{n : ℕ | n < m}`, whose counting measure is the standard `range m` cardinality.
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

/-- Helper for Theorem 17.35: counting positive integers bounded by an `ℕ∞` value recovers that
bound. -/
private lemma count_pnat_le_enat_eq (t : ℕ∞) :
    Measure.count {k : ℕ+ | (k : ℕ∞) ≤ t} = t := by
  by_cases ht : t = ⊤
  · subst ht
    simpa [ENat.card_eq_top_of_infinite] using
      (Measure.count_univ : Measure.count (Set.univ : Set ℕ+) = ENat.card ℕ+)
  · -- Proof comment: in the finite case, replace the `ℕ∞` bound by `ENat.toNat t` and reuse the
    -- explicit `ℕ+` counting lemma above.
    calc
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

/-- Helper for Theorem 17.35: a finite iterated entrance time is equivalent to having at least
`k` positive visits to `x`, expressed through the full positive-visit encard. -/
private lemma iteratedEntranceTime_lt_top_iff_le_positiveVisitEncard
    (Y : ℕ → Ω → E) (x : E) (ω : Ω) (k : ℕ+) :
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
    -- Proof comment: once the `k`th entrance time is finite, the corresponding bounded prefix
    -- contains at least `k` visits, and every such bounded prefix injects into the full visit set.
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
    -- Proof comment: a concrete `k`-element subset of positive visits is bounded by its maximal
    -- time, so the bounded-prefix criterion yields a finite `k`th entrance time.
    have hτ_le : (τ_[Y, x]^k) ω ≤ N :=
      (iteratedEntranceTime_le_iff_prefixVisitCountAtLeast Y x ω k N).2 hk_le_prefix
    exact lt_of_le_of_lt hτ_le (by simp)

/-- Helper for Theorem 17.35: the positive visit count from time `1` equals the number of finite
iterated entrance times into the same state. -/
private lemma totalVisitsFromOne_eq_countFiniteIteratedEntrances
    (x : E) (ω : Ω) :
    totalVisitsFrom X x 1 ω = Measure.count {k : ℕ+ | (τ_[X, x]^k) ω < ⊤} := by
  -- Proof comment: rewrite the positive visit count as the encard of the positive-visit set and
  -- identify that encard with the counting measure of the finite-entrance index set.
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

/-- Helper for Theorem 17.35: pathwise, the indicator series of finite iterated entrance times is
the counting measure of the finite-entrance index set. -/
private lemma tsum_iteratedEntranceIndicators_eq_countFiniteIteratedEntrances
    (x : E) (ω : Ω) :
    (∑' k : ℕ+,
      Set.indicator {ω' | (τ_[X, x]^k) ω' < ⊤} (fun _ ↦ (1 : ℝ≥0∞)) ω) =
      Measure.count {k : ℕ+ | (τ_[X, x]^k) ω < ⊤} := by
  -- Proof comment: evaluate the indicator series as the sum over the subtype of finite entrance
  -- indices, then identify that sum with counting measure.
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

/-- Helper for Theorem 17.35: rewrite the positive-time diagonal Green function as the series of
finite iterated-entrance probabilities. -/
private lemma greenFunctionFromOneSelf_eq_tsum_iteratedEntranceProbabilities
    (x : E) [IsMarkovProcessRealization κ P X] :
    (G[P, X; 1]) x x =
      ∑' k : ℕ+, ENNReal.ofReal ((P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤}) := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  have hτ_le_meas : ∀ k : ℕ+, ∀ N : ℕ, MeasurableSet {ω | (τ_[X, x]^k) ω ≤ N} := by
    intro k N
    let A : Set (Fin (N + 1) → E) :=
      {f : Fin (N + 1) → E |
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
  have hτ_meas : ∀ k : ℕ+, MeasurableSet {ω | (τ_[X, x]^k) ω < ⊤} := by
    intro k
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
    exact MeasurableSet.iUnion fun N ↦ hτ_le_meas k N
  -- Proof comment: rewrite `G[P, X; 1]` as the expected positive visit count, replace that count
  -- pathwise by the finite-entrance count, then expand it as an indicator series and integrate
  -- termwise.
  calc
    (G[P, X; 1]) x x = ∫⁻ ω, totalVisitsFrom X x 1 ω ∂(P x : Measure Ω) := by
      rw [greenFunctionFrom_eq_lintegral_totalVisitsFrom]
    _ = ∫⁻ ω, Measure.count {k : ℕ+ | (τ_[X, x]^k) ω < ⊤} ∂(P x : Measure Ω) := by
          refine lintegral_congr_ae ?_
          filter_upwards [] with ω
          rw [totalVisitsFromOne_eq_countFiniteIteratedEntrances]
    _ = ∫⁻ ω,
          ∑' k : ℕ+,
            Set.indicator {ω' | (τ_[X, x]^k) ω' < ⊤} (fun _ ↦ (1 : ℝ≥0∞)) ω
          ∂(P x : Measure Ω) := by
            refine lintegral_congr_ae ?_
            filter_upwards [] with ω
            symm
            exact tsum_iteratedEntranceIndicators_eq_countFiniteIteratedEntrances x ω
    _ = ∑' k : ℕ+,
          ∫⁻ ω,
            Set.indicator {ω' | (τ_[X, x]^k) ω' < ⊤} (fun _ ↦ (1 : ℝ≥0∞)) ω
          ∂(P x : Measure Ω) := by
            rw [lintegral_tsum fun k ↦
              (measurable_const.indicator (hτ_meas k)).aemeasurable]
    _ = ∑' k : ℕ+, (P x : Measure Ω) {ω | (τ_[X, x]^k) ω < ⊤} := by
          refine tsum_congr fun k ↦ ?_
          simpa using
            (lintegral_indicator_one (μ := (P x : Measure Ω))
              (s := {ω | (τ_[X, x]^k) ω < ⊤}) (hτ_meas k))
    _ = ∑' k : ℕ+, ENNReal.ofReal ((P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤}) := by
          refine tsum_congr fun k ↦ ?_
          simp [MeasureTheory.measureReal_def]

/-- Helper for Theorem 17.35: the iterated entrance probabilities at `x` are the shifted power
series of the return probability `F(x, x)`. -/
private lemma iteratedEntranceProbabilitySeries_eq_selfPowerSeries
    (x : E) [IsMarkovProcessRealization κ P X] :
    (∑' k : ℕ+, ENNReal.ofReal ((P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤})) =
      ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
  -- Proof comment: Theorem 17.29 already gives the exact `k`th-entrance probability, and the
  -- remaining work is only the standard `ℕ+`-to-`ℕ` reindexing.
  calc
    (∑' k : ℕ+, ENNReal.ofReal ((P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤})) =
        ∑' k : ℕ+, ENNReal.ofReal ((F[P, X]) x x * (F[P, X]) x x ^ k.natPred) := by
          refine tsum_congr fun k ↦ ?_
          simpa using congrArg ENNReal.ofReal
            (iteratedEntranceTime_finite_probability_eq_everHitsProbability_mul_selfPow
              (κ := κ) (P := P) (X := X) x x k)
    _ = ∑' n : ℕ, ENNReal.ofReal ((F[P, X]) x x * (F[P, X]) x x ^ n) := by
          simpa using
            (Equiv.tsum_eq Equiv.pnatEquivNat
              (fun n : ℕ ↦ ENNReal.ofReal ((F[P, X]) x x * (F[P, X]) x x ^ n)))
    _ = ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
          refine tsum_congr fun n ↦ ?_
          rw [pow_succ, mul_comm]

/-- Helper for Theorem 17.35: the positive-time diagonal Green function is the shifted geometric
series of successive return probabilities. -/
private lemma greenFunctionFromOneSelf_eq_tsum_selfPowers
    (x : E) [IsMarkovProcessRealization κ P X] :
    (G[P, X; 1]) x x =
      ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
  exact
    (greenFunctionFromOneSelf_eq_tsum_iteratedEntranceProbabilities
      (P := P) (X := X) (κ := κ) x).trans
      (iteratedEntranceProbabilitySeries_eq_selfPowerSeries
        (P := P) (X := X) (κ := κ) x)

/-- Helper for Theorem 17.35: the full diagonal Green function splits into the deterministic
time-`0` visit and the strictly positive-time diagonal Green tail. -/
private lemma greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf
    (x : E) [IsMarkovProcessRealization κ P X] :
    (G[P, X]) x x = 1 + (G[P, X; 1]) x x := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  have hzero :
      (P x : Measure Ω) {ω | X 0 ω = x} = 1 := by
    -- Proof comment: under `P x`, the process starts at `x` almost surely.
    have hpreimage : {ω | X 0 ω = x} = X 0 ⁻¹' ({x} : Set E) := by
      ext ω
      simp
    calc
      (P x : Measure Ω) {ω | X 0 ω = x}
        = ((P x : Measure Ω).map (X 0)) ({x} : Set E) := by
            rw [hpreimage]
            rw [← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton x)]
      _ = Measure.dirac x ({x} : Set E) := by
            rw [hReal.initial_eq x]
      _ = 1 := by
            simp
  -- Proof comment: split the full Green series into its `n = 0` term and the positive-time tail.
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
                    by_cases hn : n = 0 <;> simp [hn]
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

/-- Helper for Theorem 17.35: a shifted geometric series of `ℝ≥0∞`-casts is finite whenever the
ratio lies in `[0, 1)`. -/
private lemma ennrealOfRealTsumGeometricSucc_lt_top {q : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1) :
    ∑' n : ℕ, ENNReal.ofReal (q ^ (n + 1)) < ⊤ := by
  have hsum : Summable (fun n : ℕ ↦ q ^ (n + 1)) :=
    (_root_.summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hq_nonneg hq_lt_one)
  -- Proof comment: a summable nonnegative real series stays finite after the termwise cast to
  -- `ℝ≥0∞`.
  calc
    ∑' n : ℕ, ENNReal.ofReal (q ^ (n + 1))
      = ENNReal.ofReal (∑' n : ℕ, q ^ (n + 1)) := by
          rw [ENNReal.ofReal_tsum_of_nonneg]
          · intro n
            exact pow_nonneg hq_nonneg _
          · exact hsum
    _ < ⊤ := by
          simp

/-- Helper for Theorem 17.35: composing two singleton transition masses gives a lower bound on the
singleton mass after the combined time. -/
private lemma singletonStepMass_mul_singletonStepMass_le_stepMass
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (a b c : E) (m n : ℕ) :
    ((κ m) a ({b} : Set E)) * ((κ n) b ({c} : Set E)) ≤
      ((κ (m + n)) a) ({c} : Set E) := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  -- Proof comment: expand the composed kernel at the singleton `{c}` and keep only the
  -- intermediate state `b` in the resulting countable sum.
  calc
    ((κ m) a ({b} : Set E)) * ((κ n) b ({c} : Set E))
      = ((κ n) b ({c} : Set E)) * ((κ m) a ({b} : Set E)) := by
          rw [mul_comm]
    _ ≤ ∑' z : E, ((κ n) z ({c} : Set E)) * ((κ m) a ({z} : Set E)) := by
          exact ENNReal.le_tsum b
    _ = ((κ (m + n)) a) ({c} : Set E) := by
          rw [← hReal.semigroup.comp_eq m n]
          rw [Kernel.comp_apply' _ _ _ (MeasurableSet.singleton c)]
          simpa [MeasureTheory.lintegral_countable', mul_comm]

/-- Helper for Theorem 17.35: recurrence forces the diagonal Green value to be infinite. -/
private lemma greenFunctionSelf_eq_top_of_isRecurrentState
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X] (x : E)
    (hx : IsRecurrentState P X x) :
    (G[P, X]) x x = ⊤ := by
  have htail :
      (G[P, X; 1]) x x = ∑' n : ℕ, (1 : ℝ≥0∞) := by
    -- Proof comment: recurrence makes every return-probability power equal to `1`, so the
    -- positive-time Green tail is the divergent series of ones.
    calc
      (G[P, X; 1]) x x = ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
        rw [greenFunctionFromOneSelf_eq_tsum_selfPowers (P := P) (X := X) (κ := κ)]
      _ = ∑' n : ℕ, ENNReal.ofReal (1 ^ (n + 1 : ℕ)) := by
            refine tsum_congr fun n ↦ ?_
            rw [IsRecurrentState] at hx
            simpa [hx]
      _ = ∑' n : ℕ, (1 : ℝ≥0∞) := by
            refine tsum_congr fun n ↦ ?_
            simp
  -- Proof comment: the deterministic time-`0` visit contributes `1`, and the positive-time tail
  -- is already the divergent series of ones.
  calc
    (G[P, X]) x x = 1 + (G[P, X; 1]) x x := by
      rw [greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf (P := P) (X := X) (κ := κ)]
    _ = 1 + ∑' n : ℕ, (1 : ℝ≥0∞) := by
          rw [htail]
    _ = ⊤ := by
          simp

/-- Helper for Theorem 17.35: a positive step mass into a state with infinite diagonal Green mass
turns the corresponding cross Green value infinite. -/
private lemma greenFunctionTop_of_greenFunctionSelfTop_andStepMass
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (x y : E) {k : ℕ}
    (hxx_top : (G[P, X]) x x = ⊤)
    (hstep : 0 < (κ k) y ({x} : Set E)) :
    (G[P, X]) y x = ⊤ := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  let c : ℝ≥0∞ := (κ k) y ({x} : Set E)
  have hc_ne_zero : c ≠ 0 := hstep.ne'
  have hxx_series :
      ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = x} = ⊤ := by
    simpa [greenFunction_eq_tsum_stateProbabilities P X hX x x] using hxx_top
  have hterm_le :
      ∀ n : ℕ,
        (P x : Measure Ω) {ω | X n ω = x} * c ≤
          (P y : Measure Ω) {ω | X (k + n) ω = x} := by
    intro n
    have hpreimage_xn : {ω | X n ω = x} = X n ⁻¹' ({x} : Set E) := by
      ext ω
      simp
    have hpreimage_ykn : {ω | X (k + n) ω = x} = X (k + n) ⁻¹' ({x} : Set E) := by
      ext ω
      simp
    -- Proof comment: a positive `k`-step path from `y` to `x` followed by an `n`-step return at
    -- `x` gives a lower bound on the `(k + n)`-step mass from `y` back to `x`.
    calc
      (P x : Measure Ω) {ω | X n ω = x} * c
        = ((κ n) x ({x} : Set E)) * c := by
            rw [hpreimage_xn]
            rw [← Measure.map_apply (hReal.measurable_process n) (MeasurableSet.singleton x)]
            rw [hReal.transition_eq x n]
      _ = ((κ n) x ({x} : Set E)) * ((κ k) y ({x} : Set E)) := by
            simp [c]
      _ = ((κ k) y ({x} : Set E)) * ((κ n) x ({x} : Set E)) := by
            rw [mul_comm]
      _ ≤ ((κ (k + n)) y) ({x} : Set E) := by
            simpa [add_comm] using
              singletonStepMass_mul_singletonStepMass_le_stepMass
                (P := P) (X := X) (κ := κ) y x x k n
      _ = (P y : Measure Ω) {ω | X (k + n) ω = x} := by
            rw [hpreimage_ykn]
            rw [← Measure.map_apply (hReal.measurable_process (k + n))
              (MeasurableSet.singleton x)]
            rw [hReal.transition_eq y (k + n)]
  have hscaled_top :
      ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = x} * c = ⊤ := by
    calc
      ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = x} * c
        = (∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = x}) * c := by
            rw [ENNReal.tsum_mul_right]
      _ = ⊤ := by
            simpa [hxx_series, hc_ne_zero] using
              congrArg (fun t : ℝ≥0∞ ↦ t * c) hxx_series
  have htail_top :
      ∑' n : ℕ, (P y : Measure Ω) {ω | X (k + n) ω = x} = ⊤ := by
    apply top_unique
    rw [← hscaled_top]
    exact ENNReal.tsum_le_tsum hterm_le
  have htail_le :
      ∑' n : ℕ, (P y : Measure Ω) {ω | X (k + n) ω = x} ≤
        ∑' n : ℕ, (P y : Measure Ω) {ω | X n ω = x} := by
    exact
      (ENNReal.summable.tsum_le_tsum_of_inj (fun n : ℕ ↦ k + n)
        (by
          intro a b hab
          exact Nat.add_left_cancel hab)
        (fun _ _ ↦ zero_le _) (fun _ ↦ le_rfl)) ENNReal.summable
  have hyx_series_top :
      ∑' n : ℕ, (P y : Measure Ω) {ω | X n ω = x} = ⊤ := by
    apply top_unique
    rw [← htail_top]
    exact htail_le
  simpa [greenFunction_eq_tsum_stateProbabilities P X hX y x] using hyx_series_top

/-- Helper for Theorem 17.35: a positive step mass back to the start state upgrades an infinite
cross Green value to an infinite diagonal Green value. -/
private lemma greenFunctionSelf_eq_top_of_greenFunctionTop_andStepMass
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (x y : E) {k : ℕ}
    (hxy_top : (G[P, X]) x y = ⊤)
    (hkx : 0 < (κ k) y ({x} : Set E)) :
    (G[P, X]) x x = ⊤ := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  let c : ℝ≥0∞ := (κ k) y ({x} : Set E)
  have hc_ne_zero : c ≠ 0 := hkx.ne'
  have hy_series :
      ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = y} = ⊤ := by
    simpa [greenFunction_eq_tsum_stateProbabilities P X hX x y] using hxy_top
  have hterm_le :
      ∀ n : ℕ,
        (P x : Measure Ω) {ω | X n ω = y} * c ≤
          (P x : Measure Ω) {ω | X (n + k) ω = x} := by
    intro n
    have hpreimage_y : {ω | X n ω = y} = X n ⁻¹' ({y} : Set E) := by
      ext ω
      simp
    have hpreimage_x : {ω | X (n + k) ω = x} = X (n + k) ⁻¹' ({x} : Set E) := by
      ext ω
      simp
    -- Proof comment: the cross mass at time `n` followed by the positive `k`-step path from `y`
    -- back to `x` yields a lower bound on the diagonal mass at time `n + k`.
    calc
      (P x : Measure Ω) {ω | X n ω = y} * c
        = ((κ n) x ({y} : Set E)) * c := by
            rw [hpreimage_y]
            rw [← Measure.map_apply (hReal.measurable_process n) (MeasurableSet.singleton y)]
            rw [hReal.transition_eq x n]
      _ = ((κ n) x ({y} : Set E)) * ((κ k) y ({x} : Set E)) := by
            simp [c]
      _ ≤ ((κ (n + k)) x) ({x} : Set E) := by
            simpa using
              singletonStepMass_mul_singletonStepMass_le_stepMass
                (P := P) (X := X) (κ := κ) x y x n k
      _ = (P x : Measure Ω) {ω | X (n + k) ω = x} := by
            rw [hpreimage_x]
            rw [← Measure.map_apply (hReal.measurable_process (n + k))
              (MeasurableSet.singleton x)]
            rw [hReal.transition_eq x (n + k)]
  have hscaled_top :
      ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = y} * c = ⊤ := by
    calc
      ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = y} * c
        = (∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = y}) * c := by
            rw [ENNReal.tsum_mul_right]
      _ = ⊤ := by
            simpa [hy_series, hc_ne_zero] using
              congrArg (fun t : ℝ≥0∞ ↦ t * c) hy_series
  have htail_top :
      ∑' n : ℕ, (P x : Measure Ω) {ω | X (n + k) ω = x} = ⊤ := by
    apply top_unique
    rw [← hscaled_top]
    exact ENNReal.tsum_le_tsum hterm_le
  by_contra hxx_ne_top
  have hdiag_series_ne_top :
      ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = x} ≠ ⊤ := by
    simpa [greenFunction_eq_tsum_stateProbabilities P X hX x x] using hxx_ne_top
  have hdiag_lt_top :
      ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = x} < ⊤ :=
    lt_top_iff_ne_top.2 hdiag_series_ne_top
  have htail_le :
      ∑' n : ℕ, (P x : Measure Ω) {ω | X (n + k) ω = x} ≤
        ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = x} := by
    exact
      (ENNReal.summable.tsum_le_tsum_of_inj (fun n : ℕ ↦ n + k)
        (by
          intro a b hab
          exact Nat.add_right_cancel hab)
        (fun _ _ ↦ zero_le _) (fun _ ↦ le_rfl)) ENNReal.summable
  have htail_ne_top :
      ∑' n : ℕ, (P x : Measure Ω) {ω | X (n + k) ω = x} ≠ ⊤ := by
    exact lt_top_iff_ne_top.1 (lt_of_le_of_lt htail_le hdiag_lt_top)
  exact htail_ne_top htail_top

/-- Helper for Theorem 17.35: two-way positive communication with a recurrent state transports
infinite diagonal Green mass to the other state. -/
private lemma greenFunctionSelf_eq_top_of_recurrent_and_twoWayStepMass
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    {x y : E} {k l : ℕ}
    (hx : IsRecurrentState P X x)
    (hkxy : 0 < (κ k) x ({y} : Set E))
    (hlyx : 0 < (κ l) y ({x} : Set E)) :
    (G[P, X]) y y = ⊤ := by
  have hgreen_xx : (G[P, X]) x x = ⊤ :=
    greenFunctionSelf_eq_top_of_isRecurrentState (P := P) (X := X) (κ := κ) x hx
  -- Proof comment: first pull infinite diagonal mass at `x` back to the cross term `G(y, x)`,
  -- then use the positive `x -> y` step to close the diagonal at `y`.
  have hgreen_yx : (G[P, X]) y x = ⊤ :=
    greenFunctionTop_of_greenFunctionSelfTop_andStepMass
      (P := P) (X := X) (κ := κ) x y hgreen_xx hlyx
  exact
    greenFunctionSelf_eq_top_of_greenFunctionTop_andStepMass
      (P := P) (X := X) (κ := κ) y x hgreen_yx hkxy

/-- Helper for Theorem 17.35: an infinite diagonal Green value forces recurrence. -/
private lemma isRecurrentState_of_greenFunctionSelf_eq_top
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X] (x : E)
    (hx : (G[P, X]) x x = ⊤) :
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
    ennrealOfRealTsumGeometricSucc_lt_top hq_nonneg hq_lt_one
  have hgreen_lt_top : (G[P, X]) x x < ⊤ := by
    calc
      (G[P, X]) x x = 1 + (G[P, X; 1]) x x := by
        rw [greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf (P := P) (X := X) (κ := κ)]
      _ = 1 + ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
        rw [greenFunctionFromOneSelf_eq_tsum_selfPowers (P := P) (X := X) (κ := κ)]
      _ < ⊤ := by
        exact ENNReal.add_lt_top.2 ⟨by simp, htail_lt_top⟩
  exact (ne_of_lt hgreen_lt_top) hx

/-- Helper for Theorem 17.35: the off-diagonal case assembles the reverse-hit lemma with the
diagonal Green transport argument. -/
private lemma offDiagonalCommunicationConclusion
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X] {x y : E}
    (hxy_ne : x ≠ y) (hx : IsRecurrentState P X x) (hxy : 0 < (F[P, X]) x y) :
    IsRecurrentState P X y ∧ (F[P, X]) x y = 1 ∧ (F[P, X]) y x = 1 := by
  have hyx : (F[P, X]) y x = 1 :=
    reverseEverHitsProbability_eq_one_of_isRecurrentState_of_everHitsProbability_pos
      (P := P) (X := X) (κ := κ) hxy_ne hx hxy
  have hyx_pos : 0 < (F[P, X]) y x := by
    simpa [hyx]
  rcases existsPosTransitionMassOfEverHitsProbabilityPos
      (P := P) (X := X) (κ := κ) hxy with ⟨k, hk, hkxy⟩
  rcases existsPosTransitionMassOfEverHitsProbabilityPos
      (P := P) (X := X) (κ := κ) hyx_pos with ⟨l, hl, hlyx⟩
  have hgreen_yy : (G[P, X]) y y = ⊤ :=
    greenFunctionSelf_eq_top_of_recurrent_and_twoWayStepMass
      (P := P) (X := X) (κ := κ) hx hkxy hlyx
  have hyrec : IsRecurrentState P X y :=
    isRecurrentState_of_greenFunctionSelf_eq_top (P := P) (X := X) (κ := κ) y hgreen_yy
  have hxy_one : (F[P, X]) x y = 1 := by
    -- Proof comment: after recurrence has been transported to `y`, swap the roles of `x` and
    -- `y` in the reverse-hit lemma.
    exact
      reverseEverHitsProbability_eq_one_of_isRecurrentState_of_everHitsProbability_pos
        (P := P) (X := X) (κ := κ) hxy_ne.symm hyrec hyx_pos
  exact ⟨hyrec, hxy_one, hyx⟩

-- Proof sketch: realize the chain as a time-homogeneous Markov process, use the positive
-- probability of ever reaching `y` from `x` to deduce that any nonreturn to `x` after arriving at
-- `y` would force a nonreturn from the recurrent state `x`, and then compare Green functions
-- along a positive-probability path from `y` back to `x`.
/-- Theorem 17.35 (1): if a recurrent state `x` has positive probability of ever hitting `y`,
then `y` is also recurrent. -/
theorem isRecurrentState_of_isRecurrentState_of_everHitsProbability_pos
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X] {x y : E}
    (hx : IsRecurrentState P X x) (hxy : 0 < (F[P, X]) x y) :
    IsRecurrentState P X y := by
  by_cases hxy_eq : x = y
  · -- Proof comment: on the diagonal the conclusion is exactly the hypothesis `hx`.
    subst hxy_eq
    simpa using hx
  · -- Proof comment: the off-diagonal work is packaged into the local communication helper.
    exact (offDiagonalCommunicationConclusion (P := P) (X := X) (κ := κ) hxy_eq hx hxy).1

-- Proof sketch: combine recurrence of `x` with the Markov property at the first visit to `y`; a
-- positive-probability path from `x` to `y` forces the eventual hit probability from `x` to `y`
-- to be `1`, since otherwise the chain could avoid returning to `x` with positive probability.
/-- Theorem 17.35 (2): if a recurrent state `x` has positive probability of ever hitting `y`,
then starting from `x` the chain hits `y` almost surely. -/
theorem everHitsProbability_eq_one_of_isRecurrentState_of_everHitsProbability_pos
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X] {x y : E}
    (hx : IsRecurrentState P X x) (hxy : 0 < (F[P, X]) x y) :
    (F[P, X]) x y = 1 := by
  by_cases hxy_eq : x = y
  · -- Proof comment: on the diagonal recurrence is exactly the identity `(F[P, X]) x x = 1`.
    subst hxy_eq
    simpa [IsRecurrentState] using hx
  · -- Proof comment: the off-diagonal almost-sure hit statement is part of the packaged helper.
    exact (offDiagonalCommunicationConclusion (P := P) (X := X) (κ := κ) hxy_eq hx hxy).2.1

-- Proof sketch: after obtaining recurrence of `y` from the first clause, repeat the same
-- argument with the roles of `x` and `y` reversed; the positive-probability path from `x` to `y`
-- and recurrence of both states imply that `y` also hits `x` almost surely.
/-- Theorem 17.35 (3): if a recurrent state `x` has positive probability of ever hitting `y`,
then starting from `y` the chain hits `x` almost surely. -/
theorem everHitsProbability_swap_eq_one_of_isRecurrentState_of_everHitsProbability_pos
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X] {x y : E}
    (hx : IsRecurrentState P X x) (hxy : 0 < (F[P, X]) x y) :
    (F[P, X]) y x = 1 := by
  by_cases hxy_eq : x = y
  · -- Proof comment: on the diagonal this is again the recurrence identity for `x`.
    subst hxy_eq
    simpa [IsRecurrentState] using hx
  · -- Proof comment: the reverse almost-sure hit statement is the key off-diagonal conclusion.
    exact (offDiagonalCommunicationConclusion (P := P) (X := X) (κ := κ) hxy_eq hx hxy).2.2

end CommunicatingStates

end ProbabilityTheory
