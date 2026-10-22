/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Corollary_19_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Corollary_17_48
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_51
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Example_19_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_35

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

variable {E : Type u} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

/-- Helper for Example 19.32: the event that the trajectory `X` first hits `insert y A` at the
state `y`, allowing the hit to occur already at time `0`. -/
private def firstHitAtStateEvent (X : ℕ → Ω → E) (A : Set E) (y : E) : Set Ω :=
  {ω | hittingAfter X (insert y A) 0 ω < ⊤ ∧
      stoppedValue X (hittingAfter X (insert y A) 0) ω = y}

/-- Helper for Example 19.32: `F_A P X A x y` is the probability that the first hit of
`insert y A` occurs at the state `y`, possibly already at time `0`. -/
private def F_A (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (x y : E) : ℝ :=
  ((P x : Measure Ω) (firstHitAtStateEvent X A y)).toReal

/-- Helper for Example 19.32: under `P x`, the realized chain starts at the deterministic state
`x` with probability `1`. -/
private lemma initialState_prob_eq_one
    {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] (x : E) :
    (P x : Measure Ω) {ω | X 0 ω = x} = 1 := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  rw [show {ω | X 0 ω = x} = X 0 ⁻¹' ({x} : Set E) by
    ext ω
    simp]
  rw [← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton x)]
  rw [hReal.initial_eq x]
  simp

/-- Helper for Example 19.32: under `P x`, the realized chain starts at the deterministic state
`x` almost surely. -/
private lemma initialState_ae_eq_start
    {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] (x : E) :
    ∀ᵐ ω ∂(P x : Measure Ω), X 0 ω = x := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hMeas : MeasurableSet {ω | X 0 ω = x} := by
    rw [show {ω | X 0 ω = x} = X 0 ⁻¹' ({x} : Set E) by
      ext ω
      simp]
    exact hReal.measurable_process 0 (MeasurableSet.singleton x)
  exact (mem_ae_iff_prob_eq_one hMeas).2 <|
    initialState_prob_eq_one (p := p) (P := P) (X := X) x

/-- Helper for Example 19.32: the positive-time first-return event
`{ω | (τ_[X, x]^1) ω < ⊤}` is measurable. -/
private lemma measurableSet_positiveFirstReturnTimeFinite
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization κ P X] (x : E) :
    MeasurableSet {ω | (τ_[X, x]^1) ω < ⊤} := by
  -- Proof comment: finiteness of the first return time means the path hits `x` at some time
  -- `n + 1`, so this event is a countable union of measurable singleton fibers.
  have hEq :
      {ω | (τ_[X, x]^1) ω < ⊤} = ⋃ n : ℕ, X n.succ ⁻¹' ({x} : Set E) := by
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
  refine MeasurableSet.iUnion ?_
  intro n
  have hReal : IsMarkovProcessRealization κ P X := inferInstance
  exact (hReal.measurable_process n.succ) (measurableSet_singleton x)

/-- Helper for Example 19.32: finite expected first return time implies recurrence. -/
private lemma recurrent_of_positiveRecurrentState
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization κ P X] (x : E) (hx : IsPositiveRecurrentState P X x) :
    IsRecurrentState P X x := by
  -- Proof comment: if the complement of the finite-return event had positive mass, the first
  -- return time would integrate to `∞`, contradicting positive recurrence.
  let A : Set Ω := {ω | (τ_[X, x]^1) ω < ⊤}
  have hFirstReturnFinite :
      ∀ y : E, MeasurableSet {ω | (τ_[X, y]^1) ω < ⊤} :=
    fun y ↦ measurableSet_positiveFirstReturnTimeFinite (κ := κ) (P := P) (X := X) y
  have hA_meas : MeasurableSet A := by
    simpa [A] using hFirstReturnFinite x
  have hAc_zero : (P x : Measure Ω) Aᶜ = 0 := by
    by_contra hAc_zero
    have hindicator_top :
        ∫⁻ ω,
          Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞)) ω ∂(P x : Measure Ω) = ∞ := by
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
          have hτne : ¬ (τ_[X, x]^1) ω ≠ ⊤ := by
            simpa [A, Set.mem_setOf_eq, lt_top_iff_ne_top] using hω
          exact not_not.mp hτne
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
      have hUnion_le :
          (P x : Measure Ω) (A ∪ Aᶜ) ≤ (P x : Measure Ω) A + (P x : Measure Ω) Aᶜ :=
        measure_union_le A Aᶜ
      calc
        1 = (P x : Measure Ω) Set.univ := by simp
        _ ≤ (P x : Measure Ω) A + (P x : Measure Ω) Aᶜ := by
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

/-- Helper for Example 19.32: in a random walk with weights, every vertex has positive total
conductance. -/
private lemma conductance_ne_zero_at
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C] (x : E) :
    conductance C x ≠ 0 := by
  intro hx0
  have hC_zero : ∀ y : E, C x y = 0 := by
    intro y
    have hle : C x y ≤ conductance C x := by
      simpa [conductance] using (ENNReal.le_tsum y : C x y ≤ ∑' z : E, C x z)
    rw [hx0] at hle
    exact le_antisymm hle bot_le
  have hp_zero : ∀ y : E, p x y = 0 := by
    intro y
    rw [(inferInstance : IsRandomWalkWithWeights p C).transition_eq x y, hC_zero y, hx0]
    simp
  have hsum_zero : ∑ y : E, p x y = 0 := by
    simp [hp_zero]
  have hstochastic : ∑' y : E, p x y = 1 := by
    exact (inferInstance : IsRandomWalkWithWeights p C).isStochasticMatrix x
  have hstochastic' : ∑ y : E, p x y = 1 := by
    simpa using hstochastic
  rw [hsum_zero] at hstochastic'
  simp at hstochastic'

/-- Helper for Example 19.32: kernel irreducibility of `discreteMatrixKernel p` yields the Chapter
17 irreducibility predicate for the realized chain. -/
private lemma irreducibleMarkovChain_of_discreteMatrixKernelIsIrreducible
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)] :
    IsIrreducibleMarkovChain P X := by
  have hgreen :
      ∀ ⦃x y : E⦄, x ≠ y → 0 < (G[P, X; 1]) x y := by
    intro x y hxy
    have hy_pos : 0 < (Measure.count : Measure E) ({y} : Set E) := by
      simp
    rcases (inferInstance : Kernel.IsIrreducible (Measure.count : Measure E)
        (discreteMatrixKernel p)).irreducible
        (A := ({y} : Set E)) (MeasurableSet.singleton y) hy_pos x with ⟨n, hn⟩
    have hnpos : 0 < n := by
      by_contra hnpos
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
      subst hnzero
      have hzero : ((discreteMatrixKernel p ^ 0) x) ({y} : Set E) = 0 := by
        change (Kernel.id x) ({y} : Set E) = 0
        simp [Kernel.id_apply, hxy]
      rw [hzero] at hn
      exact lt_irrefl _ hn
    exact greenFunctionFrom_one_pos_of_posStepMass
      (κ := fun m ↦ discreteMatrixKernel p ^ m) P X hnpos hn
  exact
    (isIrreducibleMarkovChain_iff_greenFunctionFrom_one_pos_offDiagonal
      (κ := fun n ↦ discreteMatrixKernel p ^ n) P X).2 hgreen

/-- Helper for Example 19.32: a finite irreducible random walk with weights is recurrent because
the normalized conductance measure yields an invariant distribution, and Theorem 17.51 upgrades
that to positive recurrence. -/
private lemma recurrentMarkovChain_of_finite_irreducible_randomWalk
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x0 : E)
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)] :
    IsRecurrentMarkovChain P X := by
  let hWalk : IsRandomWalkWithWeights p C := inferInstance
  -- Route correction: reuse the canonical Chapter 17 invariant-scaling API instead of
  -- introducing a local scaling bridge for invariant measures.
  let hirr : IsIrreducibleMarkovChain P X :=
    irreducibleMarkovChain_of_discreteMatrixKernelIsIrreducible
      (p := p) (C := C) (P := P) (X := X)
  have hmass_ne_zero : conductanceMeasure C Set.univ ≠ 0 := by
    intro hmass_zero
    have hvertex_zero : conductanceMeasure C ({x0} : Set E) = 0 := by
      simpa [hmass_zero] using
        (measure_mono_null (show ({x0} : Set E) ⊆ Set.univ by simp) hmass_zero)
    have hcond_zero : conductance C x0 = 0 := by
      simpa [conductanceMeasure_apply_singleton] using hvertex_zero
    exact conductance_ne_zero_at (p := p) (C := C) x0 hcond_zero
  have hmass_lt_top : conductanceMeasure C Set.univ < ∞ := by
    rw [conductanceMeasure]
    rw [Measure.sum_apply _ MeasurableSet.univ]
    rw [tsum_fintype]
    have hterm : ∀ x : E, (conductance C x • Measure.dirac x) Set.univ = conductance C x := by
      intro x
      simp [Measure.smul_apply]
    simp_rw [hterm]
    simp only [ENNReal.sum_lt_top, Finset.mem_univ, forall_true_left]
    intro x
    exact hWalk.conductance_lt_top x
  let πMeasure : Measure E := (conductanceMeasure C Set.univ)⁻¹ • conductanceMeasure C
  have hπ_prob : IsProbabilityMeasure πMeasure := by
    refine isProbabilityMeasure_iff.2 ?_
    rw [Measure.smul_apply]
    exact ENNReal.inv_mul_cancel hmass_ne_zero (ne_of_lt hmass_lt_top)
  let π : ProbabilityMeasure E := ⟨πMeasure, hπ_prob⟩
  have hμ_inv_conductance :
      Kernel.Invariant
        (discreteMatrixKernel (conductanceTransitionMatrix C))
        (conductanceMeasure C) := by
    letI : IsMarkovKernel (discreteMatrixKernel (conductanceTransitionMatrix C)) :=
      discreteMatrixKernel_isMarkovKernel _
        (conductanceTransitionMatrix_isStochastic
          (C := C)
          (fun x ↦ hWalk.conductance_lt_top x)
          (fun x ↦ bot_lt_iff_ne_bot.mpr <| conductance_ne_zero_at (p := p) (C := C) x))
    -- Proof comment: reversibility of the conductance kernel supplies the invariant measure.
    exact
      (conductanceKernel_isReversible
        (C := C)
        hWalk.symmetric
        (fun x ↦ hWalk.conductance_lt_top x)
        (fun x ↦ bot_lt_iff_ne_bot.mpr <| conductance_ne_zero_at (p := p) (C := C) x)).invariant
  have hp_eq : p = conductanceTransitionMatrix C := by
    funext x y
    exact hWalk.transition_eq x y
  have hμ_inv : Kernel.Invariant (discreteMatrixKernel p) (conductanceMeasure C) := by
    simpa [hp_eq] using hμ_inv_conductance
  have hπ_inv : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E) := by
    have hscaled :
        Kernel.Invariant
          (discreteMatrixKernel p)
          ((conductanceMeasure C Set.univ)⁻¹ • conductanceMeasure C) :=
      kernelInvariant_smul
        (κ := fun _ : ℕ ↦ discreteMatrixKernel p)
        (a := (conductanceMeasure C Set.univ)⁻¹) hμ_inv
    simpa [π, πMeasure] using hscaled
  have hπ_mem : π ∈ invariantDistributions (discreteMatrixKernel p) := by
    exact (mem_invariantDistributions_iff (discreteMatrixKernel p) π).2 hπ_inv
  have hpositive : IsPositiveRecurrentMarkovChain P X := by
    refine
      (isPositiveRecurrentMarkovChain_iff_invariantDistributions_ne_empty
        (p := p) (P := P) (X := X) hirr).2 ?_
    intro hEmpty
    have : π ∈ (∅ : Set (ProbabilityMeasure E)) := by
      simpa [hEmpty] using hπ_mem
    simpa using this
  -- Proof comment: positive recurrence upgrades every state to recurrence via the local helper.
  intro x
  exact recurrent_of_positiveRecurrentState
    (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n) (P := P) (X := X) x (hpositive x)

/-- Helper for Example 19.32: if the realized trajectory starts outside `A`, then the first hit
searched from time `0` agrees with the first hit searched from time `1`. -/
private lemma hittingAfter_zero_eq_one_of_not_mem_initial
    {X : ℕ → Ω → E} {A : Set E} {ω : Ω} (h0 : X 0 ω ∉ A) :
    hittingAfter X A 0 ω = hittingAfter X A 1 ω := by
  -- Proof comment: monotonicity gives the easy direction, and `h0` rules out a time-`0` hit.
  refine le_antisymm (hittingAfter_apply_mono (u := X) (s := A) (ω := ω) (by simp)) ?_
  by_cases htop : hittingAfter X A 0 ω = ⊤
  · have hle :
        hittingAfter X A 0 ω ≤ hittingAfter X A 1 ω :=
      hittingAfter_apply_mono (u := X) (s := A) (ω := ω) (by simp)
    simpa [htop] using hle
  · lift hittingAfter X A 0 ω to ℕ using htop with n hn
    have hn_ne_top : hittingAfter X A 0 ω ≠ ⊤ := by
      rw [← hn]
      simp
    have hidx : (hittingAfter X A 0 ω).untopA = n := by
      rw [← hn, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    have hmem : X n ω ∈ A := by
      simpa [hidx] using
        hittingAfter_mem_set_of_ne_top (u := X) (s := A) (n := 0) (ω := ω) hn_ne_top
    have hn_pos : 1 ≤ n := by
      by_contra hn_pos
      have hn_zero : n = 0 := by omega
      exact h0 (hn_zero ▸ hmem)
    -- Proof comment: once the finite hit occurs at some `n ≥ 1`, the search from time `1`
    -- also stops by time `n`.
    simpa [hn] using
      hittingAfter_le_of_mem (u := X) (s := A) (n := 1) (ω := ω) hn_pos hmem

/-- Helper for Example 19.32: a coordinatewise measurable process is adapted to its natural
filtration. -/
private theorem adapted_processFiltration_of_measurable
    {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → E}
    (hY_meas : ∀ n, Measurable (Y n)) :
    Adapted (processFiltration Y) Y := by
  intro n
  -- Proof comment: measurability of `Y n` gives membership in the `n`-th stage of the natural
  -- filtration.
  refine measurable_iff_comap_le.2 ?_
  exact le_inf (measurable_iff_comap_le.1 (hY_meas n)) <| by
    -- Proof comment: that stage appears among the generators defining `processFiltration Y`.
    refine le_iSup_of_le n ?_
    refine le_iSup_of_le le_rfl ?_
    exact le_rfl

/-- Helper for Example 19.32: the event that `hittingAfter Y A 1` is finite is measurable. -/
private lemma measurableSet_hittingAfter_one_lt_top
    {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → E} (hY_meas : ∀ n, Measurable (Y n))
    (A : Set E) :
    MeasurableSet {ω | hittingAfter Y A 1 ω < ⊤} := by
  have hEq : {ω | hittingAfter Y A 1 ω < ⊤} = ⋃ n : ℕ, Y n.succ ⁻¹' A := by
    ext ω
    constructor
    · intro hω
      have hne_top : hittingAfter Y A 1 ω ≠ ⊤ := lt_top_iff_ne_top.mp hω
      lift hittingAfter Y A 1 ω to ℕ using hne_top with m hm
      have hm_ne_top : hittingAfter Y A 1 ω ≠ ⊤ := by
        rw [← hm]
        simp
      have hm_idx : (hittingAfter Y A 1 ω).untopA = m := by
        rw [← hm, WithTop.untopA_eq_untop (by simp)]
        exact (WithTop.untop_eq_iff (by simp)).2 rfl
      have hm_mem : Y m ω ∈ A := by
        -- Proof comment: any finite first entrance time lands in the target set.
        simpa [hm_idx] using
          hittingAfter_mem_set_of_ne_top (u := Y) (s := A) (n := 1) (ω := ω) hm_ne_top
      have hm_ne_zero : m ≠ 0 := by
        intro hm_zero
        have hm_pos_top : (1 : ℕ∞) ≤ hittingAfter Y A 1 ω :=
          le_hittingAfter (u := Y) (s := A) (n := 1) ω
        have hm_zero_top : hittingAfter Y A 1 ω = 0 := by
          symm
          simpa [hm_zero] using hm
        have hm_absurd : (1 : ℕ∞) ≤ (0 : ℕ∞) := by
          exact hm_zero_top ▸ hm_pos_top
        have hnot : ¬ ((1 : ℕ∞) ≤ (0 : ℕ∞)) := by simp
        exact hnot hm_absurd
      rcases Nat.exists_eq_succ_of_ne_zero hm_ne_zero with ⟨n, rfl⟩
      exact Set.mem_iUnion.2 ⟨n, by simpa [Set.mem_preimage] using hm_mem⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      have hn_mem : Y n.succ ω ∈ A := by
        simpa [Set.mem_preimage] using hn
      have hle :
          hittingAfter Y A 1 ω ≤ n.succ := by
        exact
          hittingAfter_le_of_mem (u := Y) (s := A) (n := 1) (ω := ω)
            (Nat.succ_le_succ (Nat.zero_le n)) hn_mem
      exact lt_of_le_of_lt hle (by simp)
  rw [hEq]
  refine MeasurableSet.iUnion ?_
  intro n
  exact (hY_meas n.succ) MeasurableSet.of_discrete

/-- Helper for Example 19.32: on the boundary `{zeroVertex, oneVertex}`, the local first-hit
probability `F_A` already has the prescribed boundary values. -/
private lemma F_A_eq_boundaryDatum_on_boundary
    {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    {zeroVertex oneVertex x : E} (hx : x ∈ ({zeroVertex, oneVertex} : Set E)) :
    F_A P X ({zeroVertex} : Set E) x oneVertex = if x = oneVertex then (1 : ℝ) else 0 := by
  by_cases hOne : x = oneVertex
  · subst x
    let μ : Measure Ω := (P oneVertex : Measure Ω)
    let S : Set Ω := {ω | X 0 ω = oneVertex}
    have hStart : μ S = 1 := by
      simpa [μ, S] using initialState_prob_eq_one (p := p) (P := P) (X := X) oneVertex
    have hSubset : S ⊆ firstHitAtStateEvent X ({zeroVertex} : Set E) oneVertex := by
      intro ω hω
      have hτ0 :
          hittingAfter X (insert oneVertex ({zeroVertex} : Set E)) 0 ω = 0 := by
        refine le_antisymm ?_ (le_hittingAfter (u := X) (s := insert oneVertex ({zeroVertex} : Set E))
          (n := 0) ω)
        have hmem : X 0 ω ∈ insert oneVertex ({zeroVertex} : Set E) := by
          left
          simpa [S] using hω
        exact hittingAfter_le_of_mem (u := X) (s := insert oneVertex ({zeroVertex} : Set E))
          (n := 0) (ω := ω) (by simp) hmem
      have hstop :
          stoppedValue X (hittingAfter X (insert oneVertex ({zeroVertex} : Set E)) 0) ω = X 0 ω := by
        simp [stoppedValue, hτ0]
      constructor
      · simpa [firstHitAtStateEvent, Set.mem_insert_iff, Set.mem_singleton_iff, hτ0]
      · simpa [firstHitAtStateEvent, Set.mem_insert_iff, Set.mem_singleton_iff, hτ0] using
          hstop.trans hω
    have hEvent : μ (firstHitAtStateEvent X ({zeroVertex} : Set E) oneVertex) = 1 := by
      refine le_antisymm ?_ ?_
      · calc
          μ (firstHitAtStateEvent X ({zeroVertex} : Set E) oneVertex) ≤ μ Set.univ := by
            exact measure_mono (by intro ω hω; simp)
          _ = 1 := by simp [μ]
      · calc
          1 = μ S := hStart.symm
          _ ≤ μ (firstHitAtStateEvent X ({zeroVertex} : Set E) oneVertex) := measure_mono hSubset
    -- Proof comment: starting at `oneVertex` forces the first boundary hit to be `oneVertex`.
    simpa [F_A, μ] using congrArg ENNReal.toReal hEvent
  · have hZero : x = zeroVertex := by
      rcases (by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx) with hZero | hOne'
      · exact hZero
      · exact False.elim (hOne hOne')
    subst x
    let μ : Measure Ω := (P zeroVertex : Measure Ω)
    let S : Set Ω := {ω | X 0 ω = zeroVertex}
    have hStart : μ S = 1 := by
      simpa [μ, S] using initialState_prob_eq_one (p := p) (P := P) (X := X) zeroVertex
    have hSubset : firstHitAtStateEvent X ({zeroVertex} : Set E) oneVertex ⊆ Sᶜ := by
      intro ω hω hzero
      have hzeroState : X 0 ω = zeroVertex := by
        simpa [S] using hzero
      have hτ0 :
          hittingAfter X (insert oneVertex ({zeroVertex} : Set E)) 0 ω = 0 := by
        refine le_antisymm ?_ (le_hittingAfter (u := X) (s := insert oneVertex ({zeroVertex} : Set E))
          (n := 0) ω)
        have hmem : X 0 ω ∈ insert oneVertex ({zeroVertex} : Set E) := by
          simp [hzeroState]
        exact hittingAfter_le_of_mem (u := X) (s := insert oneVertex ({zeroVertex} : Set E))
          (n := 0) (ω := ω) (by simp) hmem
      have hOneAtZero : X 0 ω = oneVertex := by
        simpa [firstHitAtStateEvent, Set.mem_insert_iff, Set.mem_singleton_iff, stoppedValue, hτ0]
          using hω.2
      exact hOne (hzeroState.symm.trans hOneAtZero)
    have hComp : μ (Sᶜ) = 0 := by
      let hReal :
          IsMarkovProcessRealization
            (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
      have hS_meas : MeasurableSet S := by
        rw [show S = X 0 ⁻¹' ({zeroVertex} : Set E) by
          ext ω
          simp [S]]
        exact hReal.measurable_process 0 (MeasurableSet.singleton zeroVertex)
      have hFinite : μ S ≠ ∞ := by
        rw [hStart]
        simp
      rw [measure_compl hS_meas hFinite, hStart]
      simp [μ]
    have hEvent : μ (firstHitAtStateEvent X ({zeroVertex} : Set E) oneVertex) = 0 := by
      exact measure_mono_null hSubset hComp
    -- Proof comment: starting at `zeroVertex ≠ oneVertex` forces the immediate boundary hit to
    -- occur at `zeroVertex`, so the `oneVertex` event has probability `0`.
    simpa [F_A, μ, hOne] using congrArg ENNReal.toReal hEvent

/-- Helper for Example 19.32: off the boundary, the stopped boundary-hit event from time `1`
matches the local time-`0` first-hit event used in `F_A`. -/
private lemma boundaryHitDistribution_eq_F_A_of_not_mem_boundary
    {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    {zeroVertex oneVertex x : E} (hx : x ∉ ({zeroVertex, oneVertex} : Set E)) :
    ((P x : Measure Ω)
      {ω | hittingAfter X ({zeroVertex, oneVertex} : Set E) 1 ω < ⊤ ∧
          stoppedValue X (hittingAfter X ({zeroVertex, oneVertex} : Set E) 1) ω =
            oneVertex}).toReal =
      F_A P X ({zeroVertex} : Set E) x oneVertex := by
  let μ : Measure Ω := (P x : Measure Ω)
  have hEventAE :
      {ω | hittingAfter X ({zeroVertex, oneVertex} : Set E) 1 ω < ⊤ ∧
          stoppedValue X (hittingAfter X ({zeroVertex, oneVertex} : Set E) 1) ω = oneVertex} =ᵐ[μ]
        firstHitAtStateEvent X ({zeroVertex} : Set E) oneVertex := by
    have hBoundarySet :
        ({oneVertex, zeroVertex} : Set E) = ({zeroVertex, oneVertex} : Set E) := by
      ext z
      simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]
    have hstart : ∀ᵐ ω ∂μ, X 0 ω = x := initialState_ae_eq_start (p := p) (P := P) (X := X) x
    filter_upwards [hstart] with ω hω
    have hx0 : X 0 ω ∉ ({zeroVertex, oneVertex} : Set E) := by
      simpa [hω] using hx
    have hτeq :
        hittingAfter X ({zeroVertex, oneVertex} : Set E) 0 ω =
          hittingAfter X ({zeroVertex, oneVertex} : Set E) 1 ω :=
      hittingAfter_zero_eq_one_of_not_mem_initial (X := X) (A := ({zeroVertex, oneVertex} : Set E))
        hx0
    have hstopEq :
        stoppedValue X (hittingAfter X ({zeroVertex, oneVertex} : Set E) 0) ω =
          stoppedValue X (hittingAfter X ({zeroVertex, oneVertex} : Set E) 1) ω := by
      simpa [stoppedValue] using congrArg (fun t : ℕ∞ ↦ X t.untopA ω) hτeq
    -- Proof comment: outside the boundary, the time-`0` and time-`1` boundary-hit descriptions coincide.
    apply propext
    constructor
    · intro hω'
      rw [firstHitAtStateEvent, hBoundarySet]
      exact ⟨by simpa [hτeq] using hω'.1, by simpa [hstopEq] using hω'.2⟩
    · intro hω'
      rw [firstHitAtStateEvent, hBoundarySet] at hω'
      exact ⟨by simpa [hτeq] using hω'.1, by simpa [hstopEq] using hω'.2⟩
  rw [measure_congr hEventAE]
  simp [F_A, μ]

/-- Helper for Example 19.32: starting away from `{zeroVertex, oneVertex}`, the chain hits that
boundary at positive time almost surely. -/
  private lemma hittingBoundary_prob_eq_one_of_not_mem
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)]
    {zeroVertex oneVertex x : E} (hx : x ∉ ({zeroVertex, oneVertex} : Set E)) :
    (P x : Measure Ω) {ω | hittingAfter X ({zeroVertex, oneVertex} : Set E) 1 ω < ⊤} = 1 := by
  let hirr : IsIrreducibleMarkovChain P X :=
    irreducibleMarkovChain_of_discreteMatrixKernelIsIrreducible
      (p := p) (C := C) (P := P) (X := X)
  let hrec : IsRecurrentMarkovChain P X :=
    recurrentMarkovChain_of_finite_irreducible_randomWalk
      (p := p) (C := C) (P := P) (X := X) x
  let Ezero : Set Ω := {ω | ∃ n : ℕ, 0 < n ∧ X n ω = zeroVertex}
  let H : Set Ω := {ω | hittingAfter X ({zeroVertex, oneVertex} : Set E) 1 ω < ⊤}
  have hzeroHit : (F[P, X]) x zeroVertex = 1 := by
    exact
      everHitsProbability_eq_one_of_isRecurrentState_of_everHitsProbability_pos
        (P := P) (X := X) (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n)
        (x := x) (y := zeroVertex) (hrec x) (hirr x zeroVertex)
  have hEzero_le_one : (P x : Measure Ω) Ezero ≤ 1 := by
    calc
      (P x : Measure Ω) Ezero ≤ (P x : Measure Ω) Set.univ := by
        exact measure_mono (by intro ω hω; simp)
      _ = 1 := by simp
  have hEzero : (P x : Measure Ω) Ezero = 1 := by
    exact (ENNReal.toReal_eq_one_iff ((P x : Measure Ω) Ezero)).mp <|
      by simpa [Ezero, everHitsProbability_def, Measure.real_def] using hzeroHit
  have hsubset : Ezero ⊆ H := by
    intro ω hω
    rcases hω with ⟨n, hn, hXn⟩
    have hmem : X n ω ∈ ({zeroVertex, oneVertex} : Set E) := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff, hXn]
    exact lt_of_le_of_lt
      (hittingAfter_le_of_mem (u := X) (s := ({zeroVertex, oneVertex} : Set E)) (n := 1)
        (ω := ω) hn hmem)
      (by simp)
  have hH_le_one : (P x : Measure Ω) H ≤ 1 := by
    calc
      (P x : Measure Ω) H ≤ (P x : Measure Ω) Set.univ := by
        exact measure_mono (by intro ω hω; simp)
      _ = 1 := by simp
  have hH_ge_one : 1 ≤ (P x : Measure Ω) H := by
    calc
      1 = (P x : Measure Ω) Ezero := hEzero.symm
      _ ≤ (P x : Measure Ω) H := measure_mono hsubset
  exact le_antisymm hH_le_one hH_ge_one

section

variable {p C : E → E → ℝ≥0∞}
variable [hWalk : IsRandomWalkWithWeights p C]
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
variable [hIrred : Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)]

include p hWalk hReal hIrred

/-- Example 19.32: for a finite conductance network, hence in particular for a graph with unit
resistors and simple random walk, the probability that the chain started at `x` visits the
boundary vertex `oneVertex` before it visits `zeroVertex` equals the electrical potential `u x`
when `u` has boundary values `0` at `zeroVertex` and `1` at `oneVertex`. In the finite irreducible
setting below, the first hit of `{zeroVertex, oneVertex}` is derived internally to be almost
surely finite, so no separate stopping-time finiteness hypothesis or off-boundary guard is part of
the public API. -/
theorem voltage_eq_probability_hit_one_before_zero
    {u : E → ℝ} {zeroVertex oneVertex x : E}
    (hu : IsElectricalPotential C ({zeroVertex, oneVertex} : Set E) u)
    (hboundary :
      Set.EqOn u (fun z : E ↦ if z = oneVertex then (1 : ℝ) else 0)
        ({zeroVertex, oneVertex} : Set E)) :
    u x = F_A P X ({zeroVertex} : Set E) x oneVertex := by
  by_cases hx : x ∈ ({zeroVertex, oneVertex} : Set E)
  · rw [hboundary hx]
    exact (F_A_eq_boundaryDatum_on_boundary (p := p) (P := P) (X := X) hx).symm
  · let A : Set E := ({zeroVertex, oneVertex} : Set E)
    let B : Set Ω :=
      {ω | hittingAfter X A 1 ω < ⊤ ∧
          stoppedValue X (hittingAfter X A 1) ω = oneVertex}
    let μ : Measure Ω := (P x : Measure Ω)
    have hτ : μ {ω | hittingAfter X A 1 ω < ⊤} = 1 := by
      simpa [A, μ] using
        hittingBoundary_prob_eq_one_of_not_mem (p := p) (C := C) (P := P) (X := X)
          (zeroVertex := zeroVertex) (oneVertex := oneVertex) hx
    let hX_adapted : Adapted (processFiltration X) X :=
      adapted_processFiltration_of_measurable (Y := X) hReal.measurable_process
    have hτ_stop : IsStoppingTime (processFiltration X) (hittingAfter X A 1) := by
      simpa [A] using
        Adapted.isStoppingTime_hittingAfter
          (u := X) (s := A) (n := 1) hX_adapted MeasurableSet.of_discrete
    have hHitMeas : MeasurableSet {ω | hittingAfter X A 1 ω < ⊤} :=
      measurableSet_hittingAfter_one_lt_top (Y := X) hReal.measurable_process A
    have hB_eq :
        B = ⋃ n : ℕ, {ω | hittingAfter X A 1 ω = n.succ} ∩ {ω | X n.succ ω = oneVertex} := by
      ext ω
      constructor
      · intro hω
        have hne_top : hittingAfter X A 1 ω ≠ ⊤ := lt_top_iff_ne_top.mp hω.1
        lift hittingAfter X A 1 ω to ℕ using hne_top with m hm
        have hm_ne_zero : m ≠ 0 := by
          intro hm_zero
          have hm_pos_top : (1 : ℕ∞) ≤ hittingAfter X A 1 ω :=
            le_hittingAfter (u := X) (s := A) (n := 1) ω
          have hm_ge_one : 1 ≤ m := by
            have hge_m : (1 : ℕ∞) ≤ (m : ℕ∞) := by
              exact le_of_le_of_eq hm_pos_top hm.symm
            exact_mod_cast hge_m
          exact (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm_ge_one)) hm_zero
        rcases Nat.exists_eq_succ_of_ne_zero hm_ne_zero with ⟨n, rfl⟩
        have hτ_idx : (hittingAfter X A 1 ω).untopA = n.succ := by
          rw [← hm, WithTop.untopA_eq_untop (by simp)]
          exact (WithTop.untop_eq_iff (by simp)).2 rfl
        have hstop :
            stoppedValue X (hittingAfter X A 1) ω = X n.succ ω := by
          rw [stoppedValue, hτ_idx]
        refine Set.mem_iUnion.2 ⟨n, ?_⟩
        constructor
        · exact hm.symm
        · simpa [hstop] using hω.2
      · intro hω
        rcases Set.mem_iUnion.1 hω with ⟨n, hωn⟩
        rcases hωn with ⟨hτ, hX⟩
        have hτ' : hittingAfter X A 1 ω = n.succ := by
          simpa using hτ
        have hlt : hittingAfter X A 1 ω < ⊤ := by
          simpa [hτ']
        have hτ_idx : (hittingAfter X A 1 ω).untopA = n.succ := by
          rw [hτ', WithTop.untopA_eq_untop (by simp)]
          exact (WithTop.untop_eq_iff (by simp)).2 rfl
        have hstop :
            stoppedValue X (hittingAfter X A 1) ω = X n.succ ω := by
          rw [stoppedValue, hτ_idx]
        constructor
        · exact hlt
        · simpa [hstop] using hX
    have hBMeas : MeasurableSet B := by
      rw [hB_eq]
      refine MeasurableSet.iUnion fun n ↦ ?_
      have hτn_meas :
          MeasurableSet[processFiltration X n.succ] {ω | hittingAfter X A 1 ω = n.succ} :=
        hτ_stop.measurableSet_eq n.succ
      have hXn_meas :
          MeasurableSet[processFiltration X n.succ] {ω | X n.succ ω = oneVertex} := by
        simpa [Set.preimage] using hX_adapted n.succ (MeasurableSet.singleton oneVertex)
      exact
        (show processFiltration X n.succ ≤ ‹MeasurableSpace Ω› from inf_le_left) _
          (hτn_meas.inter hXn_meas)
    have hHitAE : ∀ᵐ ω ∂μ, hittingAfter X A 1 ω < ⊤ := (mem_ae_iff_prob_eq_one hHitMeas).2 hτ
    have hValueAE :
        (fun ω ↦ u (stoppedValue X (hittingAfter X A 1) ω)) =ᵐ[μ]
          Set.indicator B (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [hHitAE] with ω hω
      have hmem :
          stoppedValue X (hittingAfter X A 1) ω ∈ A := by
        simpa [A, Set.mem_insert_iff, Set.mem_singleton_iff] using
          hittingAfter_mem_set_of_ne_top (u := X) (s := A) (n := 1) (ω := ω) hω.ne
      have hvalue :
          u (stoppedValue X (hittingAfter X A 1) ω) =
            if stoppedValue X (hittingAfter X A 1) ω = oneVertex then (1 : ℝ) else 0 :=
        hboundary hmem
      by_cases hone : stoppedValue X (hittingAfter X A 1) ω = oneVertex
      · have honeValue : u (stoppedValue X (hittingAfter X A 1) ω) = 1 := by
          simpa [hone] using hvalue
        simpa [B, hω, hone] using honeValue
      · have hnotOneValue : u (stoppedValue X (hittingAfter X A 1) ω) = 0 := by
          simpa [hone] using hvalue
        simpa [B, hω, hone] using hnotOneValue
    calc
      u x = ∫ ω, u (stoppedValue X (hittingAfter X A 1) ω) ∂μ := by
            simpa [A, μ] using
              electricalPotential_eq_expectation_at_firstEntrance
                (P := P) (X := X) (p := p) (C := C) (A := A) (u := u) (x := x) hu hx hτ
      _ = ∫ ω, Set.indicator B (fun _ ↦ (1 : ℝ)) ω ∂μ := by
            exact integral_congr_ae hValueAE
      _ = (μ B).toReal := by
            simpa [B, μ, Measure.real_def] using integral_indicator_one (μ := μ) (s := B) hBMeas
      _ = F_A P X ({zeroVertex} : Set E) x oneVertex := by
            simpa [A, B, μ] using
              boundaryHitDistribution_eq_F_A_of_not_mem_boundary
                (p := p) (P := P) (X := X)
                (zeroVertex := zeroVertex) (oneVertex := oneVertex) hx

end

end ProbabilityTheory
