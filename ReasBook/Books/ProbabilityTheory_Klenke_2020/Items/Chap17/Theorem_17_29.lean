/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.MarkovProcessRealization
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_11
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [MeasurableSingletonClass E]
variable {κ : ℕ → Kernel E E}
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}

section

variable [IsMarkovProcessRealization κ P X]

/-- Helper for Theorem 17.29: a bound on the infimum of a set of natural times in `ℕ∞` is
equivalent to a bounded witness in that set. -/
private lemma sInf_natImage_le_iff {S : Set ℕ} {N : ℕ} :
    sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) ≤ N ↔ ∃ n ∈ S, n ≤ N := by
  -- Proof comment: if the image set is nonempty, its infimum is the least witness in `S`; if
  -- the set is empty, the infimum is `⊤`, so neither side can hold.
  by_cases hS : S.Nonempty
  · have hsInf :
        sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) = (((sInf S : ℕ) : ℕ∞)) := by
      simpa using (WithTop.coe_sInf' hS (OrderBot.bddBelow S)).symm
    constructor
    · intro h
      refine ⟨sInf S, Nat.sInf_mem hS, ?_⟩
      have hsInf_leN : (((sInf S : ℕ) : ℕ∞)) ≤ N := by
        simpa [hsInf] using h
      exact_mod_cast hsInf_leN
    · rintro ⟨n, hnS, hnN⟩
      have hsInf_le_nat : (sInf S : ℕ) ≤ n := Nat.sInf_le hnS
      have hsInf_leN_nat : (sInf S : ℕ) ≤ N := hsInf_le_nat.trans hnN
      have hsInf_leN : (((sInf S : ℕ) : ℕ∞)) ≤ N := by
        exact_mod_cast hsInf_leN_nat
      simpa [hsInf] using hsInf_leN
  · have hS_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    subst hS_empty
    simp

/-- Helper for Theorem 17.29: the successor entrance time is bounded by `N` exactly when there is
some visit to `y` by time `N` that occurs strictly after the previous entrance. -/
private lemma iteratedEntranceTime_succ_le_iff_existsHitAfter
    (Y : ℕ → Ω → E) (y : E) (ω : Ω) (k : ℕ+) (N : ℕ) :
    (τ_[Y, y]^(k + 1)) ω ≤ N ↔ ∃ n : ℕ, (τ_[Y, y]^k) ω < n ∧ n ≤ N ∧ Y n ω = y := by
  -- Proof comment: unfold the recursive successor step and replace the `sInf` bound by the
  -- existence of one bounded future hit.
  rw [iteratedEntranceTime_succ]
  rw [sInf_natImage_le_iff]
  constructor
  · rintro ⟨n, hn, hnN⟩
    exact ⟨n, hn.1, hnN, hn.2⟩
  · rintro ⟨n, hτ, hnN, hy⟩
    exact ⟨n, ⟨hτ, hy⟩, hnN⟩

/-- Helper for Theorem 17.29: the generated history filtration is monotone in the time index. -/
private lemma generatedFiltrationSpace_mono
    (Y : ℕ → Ω → E) {m n : ℕ} (hmn : m ≤ n) :
    generatedFiltrationSpace Y m ≤ generatedFiltrationSpace Y n := by
  -- Proof comment: increasing the terminal time only enlarges the supremum of available history
  -- coordinates.
  refine iSup₂_le fun r hr ↦ ?_
  exact le_iSup_of_le r <| le_iSup_of_le (hr.trans hmn) le_rfl

/-- Helper for Theorem 17.29: every coordinate `Y i` is measurable with respect to the generated
history filtration at any later time `n ≥ i`. -/
private lemma measurable_process_generated
    (Y : ℕ → Ω → E) {i n : ℕ} (hi : i ≤ n) :
    @Measurable Ω E (generatedFiltrationSpace Y n) _ (Y i) := by
  -- Proof comment: the coordinate sigma-algebra at time `i` already appears among the generators
  -- of the history filtration at every later time `n`.
  exact Measurable.of_comap_le <|
    le_iSup_of_le i <| le_iSup_of_le hi le_rfl

/-- Helper for Theorem 17.29: the state event `{ω | Y i ω = y}` is measurable in every generated
history filtration that already contains time `i`. -/
private lemma measurableSet_stateEvent_generated
    (Y : ℕ → Ω → E) (y : E) {i n : ℕ} (hi : i ≤ n) :
    MeasurableSet[generatedFiltrationSpace Y n] {ω | Y i ω = y} := by
  -- Proof comment: this is the singleton preimage of the coordinate map `Y i` in the generated
  -- history filtration.
  let hYi : @Measurable Ω E (generatedFiltrationSpace Y n) _ (Y i) :=
    measurable_process_generated (Y := Y) hi
  change MeasurableSet[generatedFiltrationSpace Y n] ((Y i) ⁻¹' ({y} : Set E))
  exact hYi (MeasurableSet.singleton y)

/-- Helper for Theorem 17.29: the bounded entrance event `{τ_[Y, y]^k ≤ N}` is measurable with
respect to the history sigma-algebra at time `N`. -/
private lemma iteratedEntranceTime_le_measurable_generated
    (Y : ℕ → Ω → E) (y : E) :
    ∀ (k : ℕ+) (N : ℕ),
      MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, y]^k) ω ≤ N} := by
  intro k N
  induction k using PNat.recOn generalizing N with
  | one =>
      -- Proof comment: the first entrance time is the singleton hit event, so the bounded event is
      -- a finite union of singleton fibers of the coordinates `Y j` for `j ≤ N`.
      have hEq :
          {ω | (τ_[Y, y]^1) ω ≤ N} =
            ⋃ j ∈ ((Finset.Icc 1 N : Finset ℕ) : Set ℕ), {ω | Y j ω = y} := by
        ext ω
        simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using
          (MeasureTheory.hittingAfter_le_iff
            (u := Y) (s := ({y} : Set E)) (n := 1) (ω := ω) (i := N))
      rw [hEq]
      refine MeasurableSet.biUnion (Set.to_countable _) ?_
      intro j hj
      exact measurableSet_stateEvent_generated
        (Y := Y) y (hi := (Finset.mem_Icc.mp hj).2)
  | succ k ih =>
      let slice : ℕ → Set Ω := fun j =>
        {ω | (τ_[Y, y]^k) ω < j} ∩ {ω | Y j ω = y}
      -- Proof comment: the successor entrance occurs by time `N` exactly when some time
      -- `1 ≤ j ≤ N` is a hit to `y` after the previous entrance.
      have hEq :
          {ω | (τ_[Y, y]^(k + 1)) ω ≤ N} =
            ⋃ j ∈ ((Finset.Icc 1 N : Finset ℕ) : Set ℕ), slice j := by
        ext ω
        constructor
        · intro hω
          rcases (iteratedEntranceTime_succ_le_iff_existsHitAfter Y y ω k N).1 hω with
            ⟨j, hτj, hjN, hjy⟩
          have hj_pos : 0 < j := by
            cases j with
            | zero => simpa using hτj
            | succ j => exact Nat.succ_pos j
          exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨Finset.mem_Icc.mpr ⟨hj_pos, hjN⟩,
            ⟨hτj, hjy⟩⟩⟩
        · intro hω
          rcases Set.mem_iUnion.1 hω with ⟨j, hω⟩
          rcases Set.mem_iUnion.1 hω with ⟨hj, hslice⟩
          exact (iteratedEntranceTime_succ_le_iff_existsHitAfter Y y ω k N).2
            ⟨j, hslice.1, (Finset.mem_Icc.mp hj).2, hslice.2⟩
      rw [hEq]
      refine MeasurableSet.biUnion (Set.to_countable _) ?_
      intro j hj
      have hj_le : j ≤ N := (Finset.mem_Icc.mp hj).2
      have hlt_N :
          MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, y]^k) ω < j} := by
        cases j with
        | zero =>
            have hj_false : ¬ 0 ∈ (Finset.Icc 1 N : Finset ℕ) := by
              simpa using hj
            exact False.elim (hj_false hj)
        | succ j =>
            have hle_j :
                MeasurableSet[generatedFiltrationSpace Y j]
                  {ω | (τ_[Y, y]^k) ω ≤ j} :=
              ih j
            have hle_N :
                MeasurableSet[generatedFiltrationSpace Y N]
                  {ω | (τ_[Y, y]^k) ω ≤ j} := by
              have hmono := generatedFiltrationSpace_mono
                (Y := Y) (Nat.le_trans (Nat.le_succ j) hj_le)
              exact hmono (s := {ω | (τ_[Y, y]^k) ω ≤ j}) hle_j
            simpa [ENat.lt_coe_add_one_iff] using hle_N
      exact hlt_N.inter (measurableSet_stateEvent_generated (Y := Y) y (hi := hj_le))

/-- Helper for Theorem 17.29: the strict bounded entrance event `{τ_[Y, y]^k < N}` is measurable
with respect to the history sigma-algebra at time `N`. -/
private lemma iteratedEntranceTime_lt_measurable_generated
    (Y : ℕ → Ω → E) (y : E) (k : ℕ+) :
    ∀ N : ℕ,
      MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, y]^k) ω < N} := by
  intro N
  cases N with
  | zero =>
      -- Proof comment: no `ℕ∞` value is strictly smaller than `0`.
      simpa using (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  | succ N =>
      -- Proof comment: on `ℕ∞`, strict inequality below `N + 1` is the same as a non-strict bound
      -- by `N`, and that bounded event is already measurable one time step earlier.
      have hle_N :
          MeasurableSet[generatedFiltrationSpace Y (N + 1)] {ω | (τ_[Y, y]^k) ω ≤ N} := by
        have hle_N_base :
            MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, y]^k) ω ≤ N} :=
          iteratedEntranceTime_le_measurable_generated (Y := Y) y k N
        have hmono := generatedFiltrationSpace_mono (Y := Y) (Nat.le_succ N)
        exact hmono (s := {ω | (τ_[Y, y]^k) ω ≤ N}) hle_N_base
      simpa [ENat.lt_coe_add_one_iff] using hle_N

/-- Helper for Theorem 17.29: the exact entrance slice at time `n` for the `k`th entrance into
`y`. -/
private def entranceSlice (Y : ℕ → Ω → E) (y : E) (k : ℕ+) (n : ℕ) : Set Ω :=
  {ω | (τ_[Y, y]^k) ω = n}

/-- Helper for Theorem 17.29: exact entrance slices are measurable in the history sigma-algebra at
their terminal time. -/
private lemma entranceSlice_measurable_generated
    (Y : ℕ → Ω → E) (y : E) (k : ℕ+) (n : ℕ) :
    MeasurableSet[generatedFiltrationSpace Y n] (entranceSlice Y y k n) := by
  -- Proof comment: the exact slice is the bounded event `τ ≤ n` with the earlier strict event
  -- `τ < n` removed.
  have hEq :
      entranceSlice Y y k n =
        {ω | (τ_[Y, y]^k) ω ≤ n} \ {ω | (τ_[Y, y]^k) ω < n} := by
    ext ω
    constructor
    · intro hω
      have hτ : (τ_[Y, y]^k) ω = n := by
        simpa [entranceSlice] using hω
      constructor
      · simpa [hτ]
      · simpa [hτ]
    · intro hω
      exact by
        simp [entranceSlice, le_antisymm_iff, not_lt] at hω ⊢
        exact hω
  rw [hEq]
  exact
    (iteratedEntranceTime_le_measurable_generated (Y := Y) y k n).diff
      (iteratedEntranceTime_lt_measurable_generated (Y := Y) y k n)

/-- Helper for Theorem 17.29: the exact entrance slice at time `0` is empty. -/
private lemma entranceSlice_zero_eq_empty
    (Y : ℕ → Ω → E) (y : E) (k : ℕ+) :
    entranceSlice Y y k 0 = ∅ := by
  -- Proof comment: the first entrance time starts at `1`, and every successor entrance is built
  -- from a strictly later visit, so no iterated entrance can occur at time `0`.
  ext ω
  constructor
  · intro hω
    have hτ : (τ_[Y, y]^k) ω = 0 := by simpa [entranceSlice] using hω
    cases k using PNat.recOn with
    | one =>
        have hτ1 : hittingAfter Y ({y} : Set E) 1 ω = 0 := by
          simpa [iteratedEntranceTime_one] using hτ
        have hlt : hittingAfter Y ({y} : Set E) 1 ω < 1 := by
          simpa [hτ1]
        rcases (MeasureTheory.hittingAfter_lt_iff
            (u := Y) (s := ({y} : Set E)) (n := 1) (ω := ω) (i := 1)).1 hlt with
          ⟨j, hj_mem, _⟩
        simpa [Set.mem_Ico] using hj_mem
    | succ k =>
        have hle : (τ_[Y, y]^(k + 1)) ω ≤ 0 := by simpa [hτ]
        rcases (iteratedEntranceTime_succ_le_iff_existsHitAfter Y y ω k 0).1 hle with
          ⟨n, hτn, hn_le, _⟩
        have hn_zero : n = 0 := Nat.eq_zero_of_le_zero hn_le
        subst hn_zero
        simpa using hτn
  · simpa

/-- Helper for Theorem 17.29: every nonzero exact entrance slice forces the process to be at `y`
at the slice time. -/
private lemma entranceSlice_subset_state
    (Y : ℕ → Ω → E) (y : E) (k : ℕ+) (n : ℕ) :
    entranceSlice Y y k (n + 1) ⊆ {ω | Y (n + 1) ω = y} := by
  intro ω hω
  -- Proof comment: if the terminal coordinate were not `y`, then the bounded witness for
  -- `τ_[Y, y]^k ≤ n + 1` would already occur by time `n`, contradicting the exact-slice equality.
  cases k using PNat.recOn with
  | one =>
      by_contra hstate
      have hτ : (τ_[Y, y]^1) ω = n + 1 := by simpa [entranceSlice] using hω
      have hle : (τ_[Y, y]^1) ω ≤ n + 1 := by
        simpa [hτ]
      have hleHit : hittingAfter Y ({y} : Set E) 1 ω ≤ n + 1 := by
        simpa [iteratedEntranceTime_one] using hle
      rcases (MeasureTheory.hittingAfter_le_iff
          (u := Y) (s := ({y} : Set E)) (n := 1) (ω := ω) (i := n + 1)).1 hleHit with
        ⟨j, hj_mem, hjy⟩
      have hj_ne_last : j ≠ n + 1 := by
        intro hj
        apply hstate
        simpa [hj, Set.mem_singleton_iff] using hjy
      have hj_le_n : j ≤ n := Nat.lt_succ_iff.mp (lt_of_le_of_ne hj_mem.2 hj_ne_last)
      have hleHit_n : hittingAfter Y ({y} : Set E) 1 ω ≤ n := by
        exact (MeasureTheory.hittingAfter_le_iff
          (u := Y) (s := ({y} : Set E)) (n := 1) (ω := ω) (i := n)).2
            ⟨j, ⟨hj_mem.1, hj_le_n⟩, hjy⟩
      have hle_n : (τ_[Y, y]^1) ω ≤ n := by
        simpa [iteratedEntranceTime_one] using hleHit_n
      have hcontra : ((n + 1 : ℕ∞) ≤ n) := by simpa [hτ] using hle_n
      have hlt : (n : ℕ∞) < n + 1 := by
        exact_mod_cast Nat.lt_succ_self n
      exact (not_le_of_gt hlt) hcontra
  | succ k =>
      by_contra hstate
      have hτ : (τ_[Y, y]^(k + 1)) ω = n + 1 := by simpa [entranceSlice] using hω
      have hle : (τ_[Y, y]^(k + 1)) ω ≤ n + 1 := by
        simpa [hτ]
      rcases (iteratedEntranceTime_succ_le_iff_existsHitAfter Y y ω k (n + 1)).1 hle with
        ⟨m, hmτ, hm_le, hm_state⟩
      have hm_ne_last : m ≠ n + 1 := by
        intro hm
        apply hstate
        simpa [hm] using hm_state
      have hm_le_n : m ≤ n := Nat.lt_succ_iff.mp (lt_of_le_of_ne hm_le hm_ne_last)
      have hle_n : (τ_[Y, y]^(k + 1)) ω ≤ n := by
        exact (iteratedEntranceTime_succ_le_iff_existsHitAfter Y y ω k n).2
          ⟨m, hmτ, hm_le_n, hm_state⟩
      have hcontra : ((n + 1 : ℕ∞) ≤ n) := by simpa [hτ] using hle_n
      have hlt : (n : ℕ∞) < n + 1 := by
        exact_mod_cast Nat.lt_succ_self n
      exact (not_le_of_gt hlt) hcontra

/-- Helper for Theorem 17.29: the finite entrance event is the union of its exact-time slices. -/
private lemma finiteEntranceEvent_eq_iUnion_entranceSlice
    (Y : ℕ → Ω → E) (y : E) (k : ℕ+) :
    {ω | (τ_[Y, y]^k) ω < ⊤} = ⋃ n : ℕ, entranceSlice Y y k n := by
  ext ω
  constructor
  · intro hω
    refine Set.mem_iUnion.2 ⟨ENat.toNat ((τ_[Y, y]^k) ω), ?_⟩
    have hne : (τ_[Y, y]^k) ω ≠ ⊤ := ne_of_lt hω
    simp [entranceSlice, ENat.coe_toNat hne]
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨n, hn⟩
    simp [entranceSlice] at hn
    simpa [hn]

/-- Helper for Theorem 17.29: exact entrance slices for a fixed `k` are pairwise disjoint. -/
private lemma entranceSlice_pairwiseDisjoint
    (Y : ℕ → Ω → E) (y : E) (k : ℕ+) :
    Pairwise fun m n ↦ Disjoint (entranceSlice Y y k m) (entranceSlice Y y k n) := by
  intro m n hmn
  refine Set.disjoint_left.2 ?_
  intro ω hm hn
  simp [entranceSlice] at hm hn
  exact hmn (ENat.coe_inj.mp (hm.symm.trans hn))

/-- Helper for Theorem 17.29: if a history event at time `n` already forces `X n = y`, then
intersecting it with a deterministic future singleton event factors through the `m`-step
transition mass from `y`. -/
private lemma measure_inter_prefix_stepEvent_eq_mul
    {x y z : E} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z}) =
      ((κ m) y ({z} : Set E)).toReal * (P x : Measure Ω).real A := by
  let μ : Measure Ω := P x
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let B : Set Ω := X (n + m) ⁻¹' ({z} : Set E)
  have hB_meas : MeasurableSet B := by
    simpa [B] using (hReal.measurable_process (n + m)) (MeasurableSet.singleton z)
  have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    refine iSup₂_le fun j hj ↦ ?_
    exact (hReal.measurable_process j).comap_le
  have hA_measAmbient : MeasurableSet A := by
    -- Proof comment: the deterministic history sigma-algebra sits inside the ambient measurable
    -- space of the realization.
    dsimp [LE.le] at hFiltration_le
    exact hFiltration_le (s := A) hA_meas
  have hMarkovGenerated :
      μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
        fun ω ↦ ((κ m) (X n ω)).real ({z} : Set E) := by
    -- Proof comment: this is the deterministic-time Markov property specialized to the singleton
    -- future event `{z}` at gap `m`.
    simpa [μ, B, add_comm] using
      hReal.markov_property x (A := ({z} : Set E)) (MeasurableSet.singleton z) n m
  have hIndicatorIntegrable : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB_meas
  -- Proof comment: integrate the deterministic-time Markov identity over the history event `A`,
  -- then freeze the transition row at `y` because `A` already forces `X n = y`.
  calc
    μ.real (A ∩ {ω | X (n + m) ω = z}) =
        ∫ ω in A, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂ μ := by
          rw [setIntegral_condExp hFiltration_le hIndicatorIntegrable hA_meas,
            ← integral_indicator hA_measAmbient]
          symm
          simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
            smul_eq_mul] using integral_indicator_const (μ := μ) (1 : ℝ) (hA_measAmbient.inter hB_meas)
    _ = ∫ ω in A, ((κ m) (X n ω)).real ({z} : Set E) ∂ μ := by
          exact integral_congr_ae hMarkovGenerated.restrict
    _ = ∫ _ in A, ((κ m) y ({z} : Set E)).toReal ∂ μ := by
          refine integral_congr_ae ?_
          filter_upwards [self_mem_ae_restrict (μ := μ) (s := A) hA_measAmbient] with ω hω
          have hω : X n ω = y := hA_sub hω
          rw [hω]
          simp [Measure.real_def]
    _ = ((κ m) y ({z} : Set E)).toReal * μ.real A := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- Helper for Theorem 17.29: the one-step deterministic-time restart identity also holds at the
level of `ENNReal` event masses. -/
private lemma measure_inter_prefix_stepEvent_eq_mul_ennreal
    {x y z : E} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) =
      ((κ m) y ({z} : Set E)) * (P x : Measure Ω) A := by
  -- Proof comment: both event masses are finite, so the already-proved `toReal` identity can be
  -- promoted back to an `ENNReal` equality by injectivity of `toReal`.
  have hstep :
      (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z}) =
        ((κ m) y ({z} : Set E)).toReal * (P x : Measure Ω).real A :=
    measure_inter_prefix_stepEvent_eq_mul
      (x := x) (y := y) (z := z) (A := A) (n := n) (m := m) hA_meas hA_sub
  have hleft_ne_top :
      (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) ≠ ⊤ :=
    measure_ne_top _ _
  have hkernel_ne_top : ((κ m) y ({z} : Set E)) ≠ ⊤ := by
    rw [← (show (P y : Measure Ω).map (X m) = κ m y from
      (inferInstance : IsMarkovProcessRealization κ P X).transition_eq y m)]
    exact measure_ne_top _ _
  have hright_ne_top :
      ((κ m) y ({z} : Set E)) * (P x : Measure Ω) A ≠ ⊤ := by
    exact ENNReal.mul_ne_top hkernel_ne_top (measure_ne_top _ _)
  exact (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top).mp <| by
    simpa [Measure.real_def, ENNReal.toReal_mul, measure_ne_top _ _, measure_ne_top _ _] using
      hstep

/-- Helper for Theorem 17.29: `noHitHorizon X y n M` records that the trajectory avoids `y`
during the next `M` strictly positive times after time `n`. -/
private def noHitHorizon (Y : ℕ → Ω → E) (y : E) (n M : ℕ) : Set Ω :=
  {ω | ∀ m : ℕ, 1 ≤ m → m ≤ M → Y (n + m) ω ≠ y}

/-- Helper for Theorem 17.29: `tailNoHit X y n` is the event of never hitting `y` again after
time `n`. -/
private def tailNoHit (Y : ℕ → Ω → E) (y : E) (n : ℕ) : Set Ω :=
  ⋂ M : ℕ, noHitHorizon Y y n M

/-- Helper for Theorem 17.29: membership in the tail no-hit event is equivalent to avoiding `y`
at every strictly positive time after the reference time. -/
private lemma mem_tailNoHit_iff
    (Y : ℕ → Ω → E) (y : E) (n : ℕ) (ω : Ω) :
    ω ∈ tailNoHit Y y n ↔ ∀ m : ℕ, 1 ≤ m → Y (n + m) ω ≠ y := by
  constructor
  · intro hω m hm
    have hM : ω ∈ noHitHorizon Y y n m := Set.mem_iInter.mp hω m
    exact hM m hm le_rfl
  · intro hω
    refine Set.mem_iInter.mpr ?_
    intro M
    intro m hm hmM
    exact hω m hm

/-- Helper for Theorem 17.29: the future-hit event after time `n` is the complement of the tail
no-hit event. -/
private lemma tailNoHit_compl_eq_futureHitEvent
    (Y : ℕ → Ω → E) (y : E) (n : ℕ) :
    (tailNoHit Y y n)ᶜ = {ω | ∃ m : ℕ, 0 < m ∧ Y (n + m) ω = y} := by
  ext ω
  constructor
  · intro hω
    by_contra hhit
    apply hω
    refine (mem_tailNoHit_iff Y y n ω).2 ?_
    intro m hm
    exact fun hmy ↦ hhit ⟨m, hm, hmy⟩
  · rintro ⟨m, hm, hmy⟩ htail
    exact (mem_tailNoHit_iff Y y n ω).1 htail m hm hmy

/-- Helper for Theorem 17.29: from time `0`, never hitting `y` again is the complement of the
usual positive-time ever-hit event. -/
private lemma tailNoHit_zero_eq_compl_everHitsEvent
    (Y : ℕ → Ω → E) (y : E) :
    tailNoHit Y y 0 = {ω | ∃ m : ℕ, 0 < m ∧ Y m ω = y}ᶜ := by
  -- Proof comment: this is the zero-time specialization of the general tail-no-hit/future-hit
  -- complement identity.
  ext ω
  constructor
  · intro hω
    simp
    intro m hm hmy
    exact (mem_tailNoHit_iff Y y 0 ω).1 hω m hm (by simpa [Nat.zero_add] using hmy)
  · intro hω
    have hnot : ¬ ∃ m : ℕ, 0 < m ∧ Y m ω = y := by
      simpa using hω
    refine (mem_tailNoHit_iff Y y 0 ω).2 ?_
    intro m hm
    exact fun hmy ↦ hnot ⟨m, hm, by simpa [Nat.zero_add] using hmy⟩

/-- Helper for Theorem 17.29: `futurePrefixEvent X n f` fixes the first finitely many future
coordinates of the path after time `n` to the values prescribed by `f`. -/
private def futurePrefixEvent (Y : ℕ → Ω → E) (n : ℕ) {M : ℕ}
    (f : Fin (M + 1) → E) : Set Ω :=
  {ω | ∀ i : Fin (M + 1), Y (n + (i : ℕ)) ω = f i}

/-- Helper for Theorem 17.29: a finite future-prefix event is measurable in the ambient space. -/
private lemma measurableSet_futurePrefixEvent
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω} [IsMarkovProcessRealization κ P X]
    {M n : ℕ} (f : Fin (M + 1) → E) :
    MeasurableSet (futurePrefixEvent X n f) := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  have hEq :
      futurePrefixEvent X n f = ⋂ i : Fin (M + 1), {ω | X (n + (i : ℕ)) ω = f i} := by
    ext ω
    simp [futurePrefixEvent]
  rw [hEq]
  refine MeasurableSet.iInter fun i ↦ ?_
  change MeasurableSet ((X (n + (i : ℕ))) ⁻¹' ({f i} : Set E))
  exact (hReal.measurable_process (n + (i : ℕ))) (MeasurableSet.singleton (f i))

/-- Helper for Theorem 17.29: a finite future-prefix event is measurable with respect to the
history sigma-algebra at its terminal time. -/
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
  change MeasurableSet[generatedFiltrationSpace X (n + M)]
      ((X (n + (i : ℕ))) ⁻¹' ({f i} : Set E))
  exact hXi (MeasurableSet.singleton (f i))

/-- Helper for Theorem 17.29: finite-horizon no-hit events are measurable. -/
private lemma measurableSet_noHitHorizon
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω} [IsMarkovProcessRealization κ P X]
    (y : E) (n M : ℕ) :
    MeasurableSet (noHitHorizon X y n M) := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  have hEq :
      noHitHorizon X y n M =
        ⋂ m ∈ Finset.Icc 1 M, {ω | X (n + m) ω ≠ y} := by
    ext ω
    simp [noHitHorizon]
  rw [hEq]
  refine MeasurableSet.iInter fun m ↦ ?_
  refine MeasurableSet.iInter fun hm ↦ ?_
  exact ((hReal.measurable_process (n + m)) (MeasurableSet.singleton y)).compl

/-- Helper for Theorem 17.29: the tail no-hit event is measurable. -/
private lemma measurableSet_tailNoHit
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω} [IsMarkovProcessRealization κ P X]
    (y : E) (n : ℕ) :
    MeasurableSet (tailNoHit X y n) := by
  rw [tailNoHit]
  refine MeasurableSet.iInter fun M ↦ ?_
  exact measurableSet_noHitHorizon (κ := κ) (P := P) (X := X) (y := y) n M

/-- Helper for Theorem 17.29: at horizon `0`, a finite future-prefix event is just a singleton
state event at the reference time. -/
private lemma futurePrefixEvent_zero_eq_stateEvent
    (Y : ℕ → Ω → E) (n : ℕ) (f : Fin 1 → E) :
    futurePrefixEvent Y n f = {ω | Y n ω = f 0} := by
  ext ω
  simp [futurePrefixEvent]

/-- Helper for Theorem 17.29: a longer exact future-prefix event splits into its shorter prefix
and the terminal one-step event. -/
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

/-- Helper for Theorem 17.29: an exact future-prefix event determines the terminal state at its
last indexed time. -/
private lemma futurePrefixEvent_terminal_subset
    (Y : ℕ → Ω → E) {M n : ℕ} (f : Fin (M + 1) → E) :
    futurePrefixEvent Y n f ⊆ {ω | Y (n + M) ω = f (Fin.last M)} := by
  intro ω hω
  simpa [futurePrefixEvent] using hω (Fin.last M)

/-- Helper for Theorem 17.29: under the restricted law on a history event at time `n`, the
successor future tuple splits into its prefix tuple and one final step from the last prefix state.
-/
private lemma restrictMap_futureTupleSucc_eq_compProd
    {x : E} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A) :
    let prefixTuple : Ω → Fin (m + 1) → E := fun ω i ↦ X (n + (i : ℕ)) ω
    let splitTuple : Ω → (Fin (m + 1) → E) × E :=
      fun ω ↦ (prefixTuple ω, X (n + (m + 1)) ω)
    let stepKernel : Kernel (Fin (m + 1) → E) E :=
      Kernel.comap (κ 1) (fun z ↦ z (Fin.last m)) (by fun_prop)
    ((P x : Measure Ω).restrict A).map splitTuple =
      (((P x : Measure Ω).restrict A).map prefixTuple) ⊗ₘ stepKernel := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let μ : Measure Ω := (P x : Measure Ω)
  let μA : Measure Ω := μ.restrict A
  let prefixTuple : Ω → Fin (m + 1) → E := fun ω i ↦ X (n + (i : ℕ)) ω
  let splitTuple : Ω → (Fin (m + 1) → E) × E :=
    fun ω ↦ (prefixTuple ω, X (n + (m + 1)) ω)
  let prefixMeasure : Measure (Fin (m + 1) → E) := μA.map prefixTuple
  let _ : IsMarkovSemigroup κ := hReal.semigroup
  let stepKernel : Kernel (Fin (m + 1) → E) E :=
    Kernel.comap (κ 1) (fun z ↦ z (Fin.last m)) (by fun_prop)
  letI : IsMarkovKernel stepKernel :=
    by
      dsimp [stepKernel]
      infer_instance
  let realizedSplitMeasure : Measure ((Fin (m + 1) → E) × E) := μA.map splitTuple
  let productSplitMeasure : Measure ((Fin (m + 1) → E) × E) := prefixMeasure ⊗ₘ stepKernel
  have hprefixTupleMeas : Measurable prefixTuple := by
    -- Proof comment: the prefix tuple is a finite product of measurable coordinates.
    exact measurable_historyTuple
      (X := X) (times := fun i : Fin (m + 1) ↦ n + (i : ℕ)) hReal.measurable_process
  have hgenerated_le : generatedFiltrationSpace X (n + m) ≤ ‹MeasurableSpace Ω› := by
    -- Proof comment: the generated filtration at time `n + m` is still an ambient
    -- sub-sigma-algebra of the realization.
    exact generatedFiltrationSpace_le_ambient (X := X) hReal.measurable_process (n + m)
  have hrealizedRect :
      ∀ (B : Set (Fin (m + 1) → E)) (hB : MeasurableSet B) (C : Set E) (hC : MeasurableSet C),
        realizedSplitMeasure (B ×ˢ C) =
          ∫⁻ z in B, stepKernel z C ∂prefixMeasure := by
    intro B hB C hC
    let prefixEvent : Set Ω := prefixTuple ⁻¹' B
    let histEvent : Set Ω := A ∩ prefixEvent
    let lastEvent : Set Ω := X (n + (m + 1)) ⁻¹' C
    let times : Fin (m + 2) → ℕ := fun i ↦ n + (i : ℕ)
    have htimes : StrictMono times := by
      intro i j hij
      simpa [times] using Nat.add_lt_add_left hij n
    have hA_big :
        MeasurableSet[generatedFiltrationSpace X (n + m)] A := by
      -- Proof comment: the history event `A` stays measurable when the filtration is enlarged
      -- from time `n` to time `n + m`.
      exact
        (generatedFiltrationSpace_mono (Y := X) (Nat.le_add_right n m))
          (s := A) hA_meas
    have hprefixGenerated :
        MeasurableSet[generatedFiltrationSpace X (n + m)] prefixEvent := by
      -- Proof comment: the prefix tuple depends only on coordinates up to time `n + m`.
      simpa [prefixEvent, prefixTuple, times] using
        (prefixTuple_preimage_measurable_generatedFiltration
          (X := X) (times := times) htimes hB)
    have hhistGenerated :
        MeasurableSet[generatedFiltrationSpace X (n + m)] histEvent := by
      exact hA_big.inter hprefixGenerated
    have hprefixEventMeas : MeasurableSet prefixEvent := hgenerated_le prefixEvent hprefixGenerated
    have hhistEventMeas : MeasurableSet histEvent := hgenerated_le histEvent hhistGenerated
    have hlastEventMeas : MeasurableSet lastEvent := by
      -- Proof comment: the final coordinate event is ambient measurable by coordinate
      -- measurability of the realization.
      simpa [lastEvent] using (hReal.measurable_process (n + (m + 1))) hC
    have hmarkov :
        μ⟦lastEvent | generatedFiltrationSpace X (n + m)⟧ =ᵐ[μ]
          fun ω ↦ ((κ 1) (X (n + m) ω)).real C := by
      -- Proof comment: this is the deterministic-time Markov property for the one-step gap from
      -- `n + m` to `n + m + 1`.
      simpa [μ, lastEvent, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        hReal.markov_property x hC (n + m) 1
    have hIndicatorInt :
        Integrable (Set.indicator lastEvent (fun _ ↦ (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hlastEventMeas
    have hrect :
        μ.real (histEvent ∩ lastEvent) =
          ∫ ω in histEvent, ((κ 1) (X (n + m) ω)).real C ∂μ := by
      -- Proof comment: integrate the deterministic-time Markov identity over the history event
      -- `A ∩ prefixEvent`.
      calc
        μ.real (histEvent ∩ lastEvent)
            = ∫ ω in histEvent,
                (μ⟦lastEvent | generatedFiltrationSpace X (n + m)⟧) ω ∂μ := by
                  rw [MeasureTheory.setIntegral_condExp hgenerated_le hIndicatorInt hhistGenerated,
                    ← MeasureTheory.integral_indicator hhistEventMeas]
                  simpa [lastEvent, histEvent, Set.indicator_indicator, Set.inter_assoc,
                    Set.inter_left_comm, Set.inter_comm, smul_eq_mul] using
                    (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                      (hhistEventMeas.inter hlastEventMeas)).symm
        _ = ∫ ω in histEvent, ((κ 1) (X (n + m) ω)).real C ∂μ := by
              exact MeasureTheory.integral_congr_ae hmarkov.restrict
    have hstepInt :
        Integrable (fun z : Fin (m + 1) → E ↦ (stepKernel z).real C) prefixMeasure := by
      -- Proof comment: the one-step kernel row masses stay integrable against the finite prefix
      -- law.
      simpa [stepKernel] using
        (ProbabilityTheory.Kernel.IsMarkovKernel.integrable
          (μ := prefixMeasure) (κ := stepKernel) hC)
    have hstepNonneg :
        0 ≤ᵐ[prefixMeasure] fun z : Fin (m + 1) → E ↦ (stepKernel z).real C := by
      exact Filter.Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg
    have hpush :
        ∫ z in B, (stepKernel z).real C ∂prefixMeasure =
          ∫ ω in histEvent, ((κ 1) (X (n + m) ω)).real C ∂μ := by
      -- Proof comment: push the prefix integral back along the restricted prefix tuple law, then
      -- rewrite the restriction to `A` as an integral over `A ∩ prefixEvent`.
      rw [← MeasureTheory.integral_indicator hB]
      change
        ∫ z, Set.indicator B (fun z : Fin (m + 1) → E ↦ (stepKernel z).real C) z
          ∂prefixMeasure =
            ∫ ω in histEvent, ((κ 1) (X (n + m) ω)).real C ∂μ
      rw [MeasureTheory.integral_map hprefixTupleMeas.aemeasurable
        ((hstepInt.indicator hB).aestronglyMeasurable)]
      have hindicator :
          (fun ω ↦
            Set.indicator B (fun z : Fin (m + 1) → E ↦ (stepKernel z).real C) (prefixTuple ω)) =
            Set.indicator prefixEvent (fun ω ↦ ((κ 1) (X (n + m) ω)).real C) := by
        funext ω
        by_cases hω : prefixTuple ω ∈ B
        · have hlastValue : prefixTuple ω (Fin.last m) = X (n + m) ω := by
            simp [prefixTuple]
          simp [prefixEvent, hω, stepKernel, hlastValue]
        · simp [prefixEvent, hω, stepKernel]
      rw [hindicator, MeasureTheory.integral_indicator hprefixEventMeas]
      change
        ∫ ω, ((κ 1) (X (n + m) ω)).real C ∂((μ.restrict A).restrict prefixEvent) =
          ∫ ω in histEvent, ((κ 1) (X (n + m) ω)).real C ∂μ
      rw [Measure.restrict_restrict hprefixEventMeas]
      simp [μ, histEvent, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
    have hproductRect :
        productSplitMeasure.real (B ×ˢ C) =
          ∫ z in B, (stepKernel z).real C ∂prefixMeasure := by
      have hlintegral :
          ∫⁻ z in B, stepKernel z C ∂prefixMeasure =
            ENNReal.ofReal (∫ z in B, ((stepKernel z).real C) ∂prefixMeasure) := by
        calc
          ∫⁻ z in B, stepKernel z C ∂prefixMeasure
              = ∫⁻ z in B, ENNReal.ofReal ((stepKernel z).real C) ∂prefixMeasure := by
                  refine lintegral_congr_ae ?_
                  filter_upwards with z
                  rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal]
                  exact measure_ne_top _ _
          _ = ENNReal.ofReal (∫ z in B, ((stepKernel z).real C) ∂prefixMeasure) := by
                symm
                exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
                  hstepInt.restrict
                  (ae_restrict_of_ae hstepNonneg)
      have hprodRect :
          productSplitMeasure (B ×ˢ C) =
            ∫⁻ z in B, stepKernel z C ∂prefixMeasure := by
        simpa [productSplitMeasure] using
          (Measure.compProd_apply_prod (μ := prefixMeasure) (κ := stepKernel) hB hC)
      calc
        productSplitMeasure.real (B ×ˢ C)
            = (∫⁻ z in B, stepKernel z C ∂prefixMeasure).toReal := by
                simpa [MeasureTheory.measureReal_def] using congrArg ENNReal.toReal hprodRect
        _ = ∫ z in B, ((stepKernel z).real C) ∂prefixMeasure := by
              rw [hlintegral, ENNReal.toReal_ofReal]
              exact MeasureTheory.integral_nonneg_of_ae (ae_restrict_of_ae hstepNonneg)
    have hrealizedRectReal :
        realizedSplitMeasure.real (B ×ˢ C) =
          ∫ z in B, (stepKernel z).real C ∂prefixMeasure := by
      have hsplitMeas : Measurable splitTuple := by
        exact hprefixTupleMeas.prodMk (hReal.measurable_process (n + (m + 1)))
      have hsplitEventMeas : MeasurableSet (prefixEvent ∩ lastEvent) := by
        exact hprefixEventMeas.inter hlastEventMeas
      calc
        realizedSplitMeasure.real (B ×ˢ C)
            = μA.real (prefixEvent ∩ lastEvent) := by
                rw [MeasureTheory.map_measureReal_apply hsplitMeas (hB.prod hC)]
                congr
        _ = μ.real ((prefixEvent ∩ lastEvent) ∩ A) := by
              rw [MeasureTheory.measureReal_restrict_apply (μ := μ) (s := A)
                (t := prefixEvent ∩ lastEvent) hsplitEventMeas]
        _ = μ.real (histEvent ∩ lastEvent) := by
              simp [histEvent, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
        _ = ∫ ω in histEvent, ((κ 1) (X (n + m) ω)).real C ∂μ := hrect
        _ = ∫ z in B, (stepKernel z).real C ∂prefixMeasure := hpush.symm
    have hrectMeas :
        realizedSplitMeasure (B ×ˢ C) = productSplitMeasure (B ×ˢ C) := by
      have hleft_ne_top : realizedSplitMeasure (B ×ˢ C) ≠ ⊤ := measure_ne_top _ _
      have hright_ne_top : productSplitMeasure (B ×ˢ C) ≠ ⊤ := measure_ne_top _ _
      exact (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top).mp <| by
        simpa [MeasureTheory.measureReal_def] using hrealizedRectReal.trans hproductRect.symm
    exact hrectMeas.trans <| by
      simpa [productSplitMeasure] using
        (Measure.compProd_apply_prod (μ := prefixMeasure) (κ := stepKernel) hB hC)
  have hsplit :
      realizedSplitMeasure = productSplitMeasure := by
    -- Proof comment: both finite split measures agree on every measurable rectangle, so product
    -- extensionality identifies them.
    refine Measure.ext_prod ?_
    intro B C hB hC
    calc
      realizedSplitMeasure (B ×ˢ C)
          = ∫⁻ z in B, stepKernel z C ∂prefixMeasure := hrealizedRect B hB C hC
      _ = productSplitMeasure (B ×ˢ C) := by
            symm
            simpa [productSplitMeasure] using
              (Measure.compProd_apply_prod (μ := prefixMeasure) (κ := stepKernel) hB hC)
  simpa [μ, μA, prefixTuple, splitTuple, prefixMeasure, stepKernel,
    realizedSplitMeasure, productSplitMeasure] using hsplit

/-- Helper for Theorem 17.29: if a history event at time `n` already pins the present state to
`y`, then the restricted present-state law is the Dirac mass at `y` scaled by the history-event
mass. -/
private lemma restrictMap_presentState_eq_smulDirac
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    {x y : E} {A : Set Ω} {n : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    ((P x : Measure Ω).restrict A).map (X n) =
      (P x : Measure Ω) A • Measure.dirac y := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let μx : Measure Ω := (P x : Measure Ω)
  have hA_ambient : MeasurableSet A := by
    -- Proof comment: the generated filtration sits inside the ambient measurable space of the
    -- realization, so measurable history events are ambient measurable as well.
    have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
      refine iSup₂_le fun j hj ↦ ?_
      exact (hReal.measurable_process j).comap_le
    exact hFiltration_le (s := A) hA_meas
  refine Measure.ext fun B hB ↦ ?_
  have hstate_meas : MeasurableSet (X n ⁻¹' B) := (hReal.measurable_process n) hB
  rw [Measure.map_apply (hReal.measurable_process n) hB,
    Measure.restrict_apply (μ := μx) (s := A) (t := X n ⁻¹' B) hstate_meas, Measure.smul_apply]
  by_cases hy : y ∈ B
  · have hinter : X n ⁻¹' B ∩ A = A := by
      ext ω
      constructor
      · intro hω
        exact hω.2
      · intro hω
        refine ⟨?_, hω⟩
        show X n ω ∈ B
        rw [hA_sub hω]
        exact hy
    rw [hinter]
    simp [Measure.dirac_apply' _ hB, hy, μx]
  · have hinter : X n ⁻¹' B ∩ A = ∅ := by
      ext ω
      constructor
      · intro hω
        have hyω : X n ω = y := hA_sub hω.2
        exact (hy (hyω ▸ hω.1)).elim
      · simp
    rw [hinter]
    simp [Measure.dirac_apply' _ hB, hy, μx]

/-- Helper for Theorem 17.29: if a history event at time `n` pins the present state to `y`,
then the restricted law of every finite future tuple is the law from `y` scaled by the mass of
that history event. -/
private lemma restrictMap_futureTuple_eq_smul
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    {x y : E} {A : Set Ω} {n : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    ∀ M : ℕ,
      let tupleN : Ω → Fin (M + 1) → E := fun ω i ↦ X (n + (i : ℕ)) ω
      let tuple0 : Ω → Fin (M + 1) → E := fun ω i ↦ X (i : ℕ) ω
      ((P x : Measure Ω).restrict A).map tupleN =
        (P x : Measure Ω) A • ((P y : Measure Ω).map tuple0) := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let μx : Measure Ω := (P x : Measure Ω)
  let μy : Measure Ω := (P y : Measure Ω)
  intro M
  induction M with
  | zero =>
      let constantTuple : E → Fin 1 → E := fun z _ ↦ z
      let tupleN : Ω → Fin 1 → E := fun ω i ↦ X (n + (i : ℕ)) ω
      let tuple0 : Ω → Fin 1 → E := fun ω i ↦ X (i : ℕ) ω
      have hpresent :
          ((μx.restrict A).map (X n)) = μx A • Measure.dirac y :=
        restrictMap_presentState_eq_smulDirac
          (P := P) (X := X) (κ := κ) (x := x) (y := y) (A := A) (n := n) hA_meas hA_sub
      have htupleN :
          ((μx.restrict A).map (X n)).map constantTuple = (μx.restrict A).map tupleN := by
        -- Proof comment: the unique coordinate of a `Fin 1` tuple is exactly the present state.
        simpa [constantTuple, tupleN, Function.comp] using
          (Measure.map_map (μ := μx.restrict A) (by fun_prop) (hReal.measurable_process n))
      have htuple0 :
          (μy.map (X 0)).map constantTuple = μy.map tuple0 := by
        -- Proof comment: the time-zero singleton tuple is the present-state map at time `0`
        -- composed with the constant-tuple embedding.
        simpa [constantTuple, tuple0, Function.comp, Nat.zero_add] using
          (Measure.map_map (μ := μy) (by fun_prop) (hReal.measurable_process 0))
      have hinitTuple : μy.map tuple0 = Measure.dirac (constantTuple y) := by
        -- Proof comment: under `P y`, the time-zero state is deterministically `y`, so the full
        -- length-one tuple is the Dirac mass at the constant singleton tuple.
        calc
          μy.map tuple0 = (μy.map (X 0)).map constantTuple := htuple0.symm
          _ = (Measure.dirac y).map constantTuple := by
                simpa using congrArg (fun ν : Measure E ↦ ν.map constantTuple) (hReal.initial_eq y)
          _ = Measure.dirac (constantTuple y) := by rw [Measure.map_dirac y]
      calc
        (μx.restrict A).map tupleN = ((μx.restrict A).map (X n)).map constantTuple := htupleN.symm
        _ = (μx A • Measure.dirac y).map constantTuple := by rw [hpresent]
        _ = μx A • Measure.dirac (constantTuple y) := by
              rw [Measure.map_smul, Measure.map_dirac' (by fun_prop)]
        _ = μx A • (μy.map tuple0) := by rw [hinitTuple]
  | succ m ih =>
      let tupleN : Ω → Fin (m + 2) → E := fun ω i ↦ X (n + (i : ℕ)) ω
      let tuple0 : Ω → Fin (m + 2) → E := fun ω i ↦ X (i : ℕ) ω
      let prefixTupleN : Ω → Fin (m + 1) → E := fun ω i ↦ X (n + (i : ℕ)) ω
      let prefixTuple0 : Ω → Fin (m + 1) → E := fun ω i ↦ X (i : ℕ) ω
      let splitTupleN : Ω → (Fin (m + 1) → E) × E :=
        fun ω ↦ (prefixTupleN ω, X (n + (m + 1)) ω)
      let splitTuple0 : Ω → (Fin (m + 1) → E) × E :=
        fun ω ↦ (prefixTuple0 ω, X (m + 1) ω)
      let stepKernel : Kernel (Fin (m + 1) → E) E :=
        Kernel.comap (κ 1) (fun z ↦ z (Fin.last m)) (measurable_pi_apply (Fin.last m))
      let _ : IsMarkovSemigroup κ := hReal.semigroup
      letI : IsMarkovKernel stepKernel := by
        dsimp [stepKernel]
        infer_instance
      have hprefixLaw :
          (μx.restrict A).map prefixTupleN = μx A • (μy.map prefixTuple0) := by
        -- Proof comment: the induction hypothesis already identifies the restricted law of the
        -- prefix tuple with the scaled future law started from `y`.
        simpa [prefixTupleN, prefixTuple0] using ih
      have htupleN_meas : Measurable tupleN := by
        exact measurable_historyTuple
          (X := X) (times := fun i : Fin (m + 2) ↦ n + (i : ℕ)) hReal.measurable_process
      have htuple0_meas : Measurable tuple0 := by
        exact measurable_historyTuple
          (X := X) (times := fun i : Fin (m + 2) ↦ (i : ℕ)) hReal.measurable_process
      have hsplitTupleN :
          (succTupleEquiv (E := E) m) ∘ tupleN = splitTupleN := by
        -- Proof comment: `succTupleEquiv` records the successor tuple by its prefix and terminal
        -- coordinate, exactly matching the restricted split-law interface.
        funext ω
        calc
          ((succTupleEquiv (E := E) m) ∘ tupleN) ω
              = ((fun i ↦ tupleN ω i.castSucc), tupleN ω (Fin.last (m + 1))) := by
                  change succTupleEquiv (E := E) m (tupleN ω) =
                    ((fun i ↦ tupleN ω i.castSucc), tupleN ω (Fin.last (m + 1)))
                  exact succTupleEquiv_apply (E := E) m (tupleN ω)
          _ = splitTupleN ω := by
                simp [tupleN, splitTupleN, prefixTupleN]
      have hsplitTuple0 :
          (succTupleEquiv (E := E) m) ∘ tuple0 = splitTuple0 := by
        -- Proof comment: the same tuple splitting holds for the time-zero future tuple.
        funext ω
        calc
          ((succTupleEquiv (E := E) m) ∘ tuple0) ω
              = ((fun i ↦ tuple0 ω i.castSucc), tuple0 ω (Fin.last (m + 1))) := by
                  change succTupleEquiv (E := E) m (tuple0 ω) =
                    ((fun i ↦ tuple0 ω i.castSucc), tuple0 ω (Fin.last (m + 1)))
                  exact succTupleEquiv_apply (E := E) m (tuple0 ω)
          _ = splitTuple0 ω := by
                simp [tuple0, splitTuple0, prefixTuple0]
      have hmapN :
          ((μx.restrict A).map tupleN).map (succTupleEquiv (E := E) m) =
            (μx.restrict A).map splitTupleN := by
        simpa [hsplitTupleN] using
          (Measure.map_map (μ := μx.restrict A)
            (succTupleEquiv (E := E) m).measurable htupleN_meas)
      have hmap0 :
          (μy.map tuple0).map (succTupleEquiv (E := E) m) = μy.map splitTuple0 := by
        simpa [hsplitTuple0] using
          (Measure.map_map (μ := μy)
            (succTupleEquiv (E := E) m).measurable htuple0_meas)
      have hsplitN :
          (μx.restrict A).map splitTupleN =
            ((μx.restrict A).map prefixTupleN) ⊗ₘ stepKernel := by
        -- Proof comment: apply the already-proved restricted split law at the pinned history
        -- event `A`.
        simpa [prefixTupleN, splitTupleN, stepKernel] using
          (restrictMap_futureTupleSucc_eq_compProd
            (P := P) (X := X) (κ := κ) (x := x) (A := A) (n := n) (m := m) hA_meas)
      have hsplit0 :
          μy.map splitTuple0 = (μy.map prefixTuple0) ⊗ₘ stepKernel := by
        -- Proof comment: the unrestricted time-zero tuple law is the same split law with the
        -- history event `A = univ`.
        simpa [μy, prefixTuple0, splitTuple0, stepKernel] using
          (restrictMap_futureTupleSucc_eq_compProd
            (P := P) (X := X) (κ := κ) (x := y) (A := (Set.univ : Set Ω)) (n := 0) (m := m)
            (MeasurableSet.univ :
              MeasurableSet[generatedFiltrationSpace X 0] (Set.univ : Set Ω)))
      have hsplitEq :
          ((μx.restrict A).map tupleN).map (succTupleEquiv (E := E) m) =
            (μx A • (μy.map tuple0)).map (succTupleEquiv (E := E) m) := by
        -- Route correction: compare the successor tuple laws only after transporting both sides
        -- through `succTupleEquiv`, where the prefix induction hypothesis and the split laws
        -- match syntactically.
        calc
          ((μx.restrict A).map tupleN).map (succTupleEquiv (E := E) m)
              = (μx.restrict A).map splitTupleN := hmapN
          _ = ((μx.restrict A).map prefixTupleN) ⊗ₘ stepKernel := hsplitN
          _ = (μx A • (μy.map prefixTuple0)) ⊗ₘ stepKernel := by rw [hprefixLaw]
          _ = μx A • ((μy.map prefixTuple0) ⊗ₘ stepKernel) := by
                rw [Measure.compProd_smul_left]
          _ = μx A • (μy.map splitTuple0) := by rw [hsplit0.symm]
          _ = μx A • ((μy.map tuple0).map (succTupleEquiv (E := E) m)) := by rw [hmap0.symm]
          _ = (μx A • (μy.map tuple0)).map (succTupleEquiv (E := E) m) := by
                rw [Measure.map_smul]
      -- Proof comment: transport the common split law back through the inverse measurable
      -- equivalence to recover equality of the original successor tuple laws.
      calc
        (μx.restrict A).map tupleN
            = (((μx.restrict A).map tupleN).map (succTupleEquiv (E := E) m)).map
                (succTupleEquiv (E := E) m).symm := by
                  symm
                  calc
                    ((((μx.restrict A).map tupleN).map (succTupleEquiv (E := E) m)).map
                        (succTupleEquiv (E := E) m).symm)
                        = ((μx.restrict A).map tupleN).map
                            ((succTupleEquiv (E := E) m).symm ∘ succTupleEquiv (E := E) m) := by
                              exact
                                (Measure.map_map
                                  (MeasurableEquiv.symm (succTupleEquiv (E := E) m)).measurable
                                  (succTupleEquiv (E := E) m).measurable
                                  (μ := (μx.restrict A).map tupleN))
                    _ = (μx.restrict A).map tupleN := by simp
        _ = (((μx A • (μy.map tuple0)).map (succTupleEquiv (E := E) m)).map
              (succTupleEquiv (E := E) m).symm) := by
                rw [hsplitEq]
        _ = μx A • (μy.map tuple0) := by
              calc
                ((((μx A • (μy.map tuple0)).map (succTupleEquiv (E := E) m)).map
                    (succTupleEquiv (E := E) m).symm))
                    = (μx A • (μy.map tuple0)).map
                        ((succTupleEquiv (E := E) m).symm ∘ succTupleEquiv (E := E) m) := by
                          exact
                            (Measure.map_map
                              (MeasurableEquiv.symm (succTupleEquiv (E := E) m)).measurable
                              (succTupleEquiv (E := E) m).measurable
                              (μ := μx A • (μy.map tuple0)))
                _ = μx A • (μy.map tuple0) := by simp

/-- Helper for Theorem 17.29: once a history event pins the state at time `n` to `y`, any
measurable event of the next finitely many coordinates factors by the law started from `y`. -/
private lemma measure_inter_prefix_futureBlock_eq_mul
    {κ : ℕ → Kernel E E}
    [IsMarkovProcessRealization κ P X]
    {x y : E} {A : Set Ω} {n M : ℕ} {C : Set (Fin (M + 1) → E)}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y})
    (hC : MeasurableSet C) :
    (P x : Measure Ω) (A ∩ {ω | (fun i : Fin (M + 1) ↦ X (n + (i : ℕ)) ω) ∈ C}) =
      (P y : Measure Ω) {ω | (fun i : Fin (M + 1) ↦ X (i : ℕ) ω) ∈ C} * (P x : Measure Ω) A := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let μx : Measure Ω := (P x : Measure Ω)
  let μy : Measure Ω := (P y : Measure Ω)
  let tupleN : Ω → Fin (M + 1) → E := fun ω i ↦ X (n + (i : ℕ)) ω
  let tuple0 : Ω → Fin (M + 1) → E := fun ω i ↦ X (i : ℕ) ω
  have htupleN_meas : Measurable tupleN := by
    -- Proof comment: the shifted future tuple is a finite product of measurable coordinates.
    exact measurable_historyTuple
      (X := X) (times := fun i : Fin (M + 1) ↦ n + (i : ℕ)) hReal.measurable_process
  have htuple0_meas : Measurable tuple0 := by
    -- Proof comment: the time-zero future tuple is the same finite product at the origin.
    exact measurable_historyTuple
      (X := X) (times := fun i : Fin (M + 1) ↦ (i : ℕ)) hReal.measurable_process
  have htupleEvent_meas : MeasurableSet {ω | tupleN ω ∈ C} := by
    change MeasurableSet (tupleN ⁻¹' C)
    exact htupleN_meas hC
  have htupleLaw :
      ((μx.restrict A).map tupleN) C = (μx A • (μy.map tuple0)) C := by
    -- Proof comment: evaluate the restricted tuple-law equality on the measurable block `C`.
    exact congrArg (fun ν : Measure (Fin (M + 1) → E) => ν C)
      (restrictMap_futureTuple_eq_smul
        (P := P) (X := X) (κ := κ) (x := x) (y := y) (A := A) (n := n) hA_meas hA_sub M)
  calc
    μx (A ∩ {ω | tupleN ω ∈ C})
        = ((μx.restrict A).map tupleN) C := by
            -- Proof comment: rewrite the restricted history mass as the pushforward of the
            -- restricted tuple law on the measurable block `C`.
            rw [Measure.map_apply htupleN_meas hC]
            change μx (A ∩ tupleN ⁻¹' C) = μx.restrict A (tupleN ⁻¹' C)
            simpa [Set.inter_comm] using
              (Measure.restrict_apply (μ := μx) (s := A) (t := tupleN ⁻¹' C) htupleEvent_meas).symm
    _ = (μx A • (μy.map tuple0)) C := htupleLaw
    _ = μx A * (μy.map tuple0) C := by
          rw [Measure.smul_apply, smul_eq_mul]
    _ = μy {ω | tuple0 ω ∈ C} * μx A := by
          rw [Measure.map_apply htuple0_meas hC]
          change μx A * μy (tuple0 ⁻¹' C) = μy (tuple0 ⁻¹' C) * μx A
          rw [mul_comm]
    _ = (P y : Measure Ω) {ω | (fun i : Fin (M + 1) ↦ X (i : ℕ) ω) ∈ C} * (P x : Measure Ω) A := by
          rfl

/-- Helper for Theorem 17.29: the measurable tuple block describing the finite future path that
avoids `y` at every strictly positive coordinate up to horizon `M`. -/
private def noHitBlock (y : E) (M : ℕ) : Set (Fin (M + 1) → E) :=
  {f | ∀ i : Fin (M + 1), 0 < i → f i ≠ y}

/-- Helper for Theorem 17.29: the no-hit tuple block is measurable in the finite product space.
-/
private lemma measurableSet_noHitBlock
    (y : E) (M : ℕ) :
    MeasurableSet (noHitBlock y M) := by
  -- Proof comment: each positive coordinate only requires membership in the complement of the
  -- singleton `{y}`, and there are only finitely many coordinates.
  let positiveCoord : Fin (M + 1) → Set (Fin (M + 1) → E) :=
    fun i ↦ if 0 < i then ((fun f : Fin (M + 1) → E ↦ f i) ⁻¹' ({y} : Set E))ᶜ else Set.univ
  have hEq : noHitBlock y M = ⋂ i : Fin (M + 1), positiveCoord i := by
    ext f
    simp [noHitBlock, positiveCoord]
  rw [hEq]
  refine MeasurableSet.iInter fun i ↦ ?_
  by_cases hi : 0 < i
  · simpa [positiveCoord, hi] using
      (((measurable_pi_apply i) (MeasurableSet.singleton y)).compl :
        MeasurableSet (((fun f : Fin (M + 1) → E ↦ f i) ⁻¹' ({y} : Set E))ᶜ))
  · simpa [positiveCoord, hi]

/-- Helper for Theorem 17.29: the finite-horizon no-hit event is exactly the preimage of the
tuple-space no-hit block under the corresponding future tuple map. -/
private lemma noHitHorizon_eq_futureTuple_preimage
    (Y : ℕ → Ω → E) (y : E) (n M : ℕ) :
    noHitHorizon Y y n M =
      {ω | (fun i : Fin (M + 1) ↦ Y (n + (i : ℕ)) ω) ∈ noHitBlock y M} := by
  ext ω
  constructor
  · intro hω
    intro i hi
    exact hω i hi (Nat.le_of_lt_succ i.2)
  · intro hω
    intro m hm hmM
    exact hω ⟨m, Nat.lt_succ_of_le hmM⟩ hm

/-- Helper for Theorem 17.29: once a history event pins down the state at time `n`, intersecting
it with an exact finite future path factors through the path law started from that pinned state. -/
private lemma measure_inter_prefix_futurePrefixEvent_eq_mul
    {κ : ℕ → Kernel E E}
    [IsMarkovProcessRealization κ P X]
    {x y : E} {A : Set Ω} {n M : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y})
    (f : Fin (M + 1) → E) :
    (P x : Measure Ω) (A ∩ futurePrefixEvent X n f) =
      (P y : Measure Ω) (futurePrefixEvent X 0 f) * (P x : Measure Ω) A := by
  -- Proof comment: an exact future prefix event is the singleton block `{f}` in tuple space.
  have hsingleton : MeasurableSet ({f} : Set (Fin (M + 1) → E)) := MeasurableSet.singleton f
  have hEventN :
      {ω | (fun i : Fin (M + 1) ↦ X (n + (i : ℕ)) ω) = f} =
        futurePrefixEvent X n f := by
    ext ω
    constructor
    · intro hω
      intro i
      simpa [hω] using congrFun hω i
    · intro hω
      funext i
      exact hω i
  have hEvent0 :
      {ω | (fun i : Fin (M + 1) ↦ X (i : ℕ) ω) = f} =
        futurePrefixEvent X 0 f := by
    ext ω
    constructor
    · intro hω
      intro i
      simpa [Nat.zero_add, hω] using congrFun hω i
    · intro hω
      funext i
      simpa [Nat.zero_add] using hω i
  have hblock :=
    measure_inter_prefix_futureBlock_eq_mul
      (P := P) (X := X) (κ := κ) (x := x) (y := y) (A := A) (n := n)
      (M := M) (C := ({f} : Set (Fin (M + 1) → E))) hA_meas hA_sub hsingleton
  simpa [Set.mem_singleton_iff, hEventN, hEvent0] using hblock

/-- Helper for Theorem 17.29: finite-horizon no-hit events factor against a history event that
already fixes the current state. -/
private lemma measure_inter_prefix_noHitHorizon_eq_mul
    {κ : ℕ → Kernel E E}
    [IsMarkovProcessRealization κ P X]
    {x y : E} {A : Set Ω} {n M : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω) (A ∩ noHitHorizon X y n M) =
      (P y : Measure Ω) (noHitHorizon X y 0 M) * (P x : Measure Ω) A := by
  -- Proof comment: the finite-horizon no-hit event is the preimage of the measurable tuple block
  -- `noHitBlock y M`, so the general future-block factorization applies directly.
  have hblock :
      (P x : Measure Ω) (A ∩ {ω | (fun i : Fin (M + 1) ↦ X (n + (i : ℕ)) ω) ∈ noHitBlock y M}) =
        (P y : Measure Ω) {ω | (fun i : Fin (M + 1) ↦ X (i : ℕ) ω) ∈ noHitBlock y M} *
          (P x : Measure Ω) A :=
    measure_inter_prefix_futureBlock_eq_mul
      (P := P) (X := X) (κ := κ) (x := x) (y := y) (A := A) (n := n)
      (M := M) (C := noHitBlock y M) hA_meas hA_sub (measurableSet_noHitBlock y M)
  simpa [noHitHorizon_eq_futureTuple_preimage] using hblock

/-- Helper for Theorem 17.29: the finite-horizon factorization passes to the tail no-hit event by
continuity from above. -/
private lemma measure_inter_prefix_tailNoHit_eq_mul
    {κ : ℕ → Kernel E E}
    [IsMarkovProcessRealization κ P X]
    {x y : E} {A : Set Ω} {n : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω) (A ∩ tailNoHit X y n) =
      (P y : Measure Ω) (tailNoHit X y 0) * (P x : Measure Ω) A := by
  let μx : Measure Ω := P x
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  have hA_ambient : MeasurableSet A := by
    -- Proof comment: the deterministic history sigma-algebra embeds into the ambient measurable
    -- space of the Markov realization.
    exact (generatedFiltrationSpace_le_ambient (X := X) hReal.measurable_process n) _ hA_meas
  have htail_eq : A ∩ tailNoHit X y n = ⋂ M : ℕ, A ∩ noHitHorizon X y n M := by
    -- Proof comment: expand the tail event as the intersection of the decreasing finite-horizon
    -- no-hit events and commute the fixed history event through the intersection.
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
  have hleft_antitone : Antitone (fun M : ℕ ↦ A ∩ noHitHorizon X y n M) := by
    -- Proof comment: enlarging the horizon only strengthens the no-hit requirement.
    intro M N hMN
    intro ω hω
    refine ⟨hω.1, ?_⟩
    exact fun m hm hmM ↦ hω.2 m hm (hmM.trans hMN)
  have hright_antitone : Antitone (fun M : ℕ ↦ noHitHorizon X y 0 M) := by
    -- Proof comment: the same monotonicity holds at time `0` for the restarted chain from `y`.
    intro M N hMN
    intro ω hω m hm hmM
    exact hω m hm (hmM.trans hMN)
  have hleft_tendsto :
      Filter.Tendsto (fun M ↦ μx (A ∩ noHitHorizon X y n M)) Filter.atTop
        (nhds (μx (A ∩ tailNoHit X y n))) := by
    -- Proof comment: continuity from above turns the finite-horizon factorization into the tail
    -- factorization on the left-hand side.
    simpa [htail_eq] using
      tendsto_measure_iInter_atTop (μ := μx)
        (fun M ↦ (hA_ambient.inter
          (measurableSet_noHitHorizon (P := P) (X := X) (κ := κ) y n M)).nullMeasurableSet)
        hleft_antitone
        ⟨0, measure_ne_top _ _⟩
  have hright_base :
      Filter.Tendsto (fun M ↦ (P y : Measure Ω) (noHitHorizon X y 0 M)) Filter.atTop
        (nhds ((P y : Measure Ω) (tailNoHit X y 0))) := by
    -- Proof comment: the restarted right-hand side has the same decreasing intersection shape.
    simpa [tailNoHit] using
      tendsto_measure_iInter_atTop (μ := (P y : Measure Ω))
        (fun M ↦
          (measurableSet_noHitHorizon (P := P) (X := X) (κ := κ) y 0 M).nullMeasurableSet)
        hright_antitone
        ⟨0, measure_ne_top _ _⟩
  have hEq :
      (fun M ↦ μx (A ∩ noHitHorizon X y n M)) =
        fun M ↦ (P y : Measure Ω) (noHitHorizon X y 0 M) * μx A := by
    -- Proof comment: each finite horizon already factors by the previously proved block lemma.
    funext M
    exact measure_inter_prefix_noHitHorizon_eq_mul
      (P := P) (X := X) (κ := κ) hA_meas hA_sub
  have hleft_real_tendsto :
      Filter.Tendsto (fun M ↦ (μx (A ∩ noHitHorizon X y n M)).toReal) Filter.atTop
        (nhds ((μx (A ∩ tailNoHit X y n)).toReal)) := by
    -- Proof comment: the left continuity-from-above statement remains valid after passing to
    -- real-valued event masses because all measures are finite.
    exact
      (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp hleft_tendsto
  have hright_real_base :
      Filter.Tendsto (fun M ↦ ((P y : Measure Ω) (noHitHorizon X y 0 M)).toReal) Filter.atTop
        (nhds (((P y : Measure Ω) (tailNoHit X y 0)).toReal)) := by
    -- Proof comment: the restarted horizon masses also converge after applying `toReal`.
    exact
      (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp hright_base
  have hright_real_tendsto :
      Filter.Tendsto
        (fun M ↦ ((P y : Measure Ω) (noHitHorizon X y 0 M)).toReal * (μx A).toReal)
        Filter.atTop
        (nhds (((P y : Measure Ω) (tailNoHit X y 0)).toReal * (μx A).toReal)) := by
    -- Proof comment: multiplication by the fixed prefix mass is continuous on `ℝ`.
    exact hright_real_base.mul_const ((μx A).toReal)
  have hEqReal :
      (fun M ↦ (μx (A ∩ noHitHorizon X y n M)).toReal) =
        fun M ↦ ((P y : Measure Ω) (noHitHorizon X y 0 M)).toReal * (μx A).toReal := by
    -- Proof comment: this is the finite-horizon factorization rewritten in real event masses.
    funext M
    have hEqM :
        μx (A ∩ noHitHorizon X y n M) =
          (P y : Measure Ω) (noHitHorizon X y 0 M) * μx A := by
      exact measure_inter_prefix_noHitHorizon_eq_mul
        (P := P) (X := X) (κ := κ) hA_meas hA_sub
    simpa [ENNReal.toReal_mul, measure_ne_top _ _, measure_ne_top _ _] using
      congrArg ENNReal.toReal hEqM
  rw [hEqReal] at hleft_real_tendsto
  have hreal_eq :
      (μx (A ∩ tailNoHit X y n)).toReal =
        ((P y : Measure Ω) (tailNoHit X y 0)).toReal * (μx A).toReal :=
    tendsto_nhds_unique hleft_real_tendsto hright_real_tendsto
  have hleft_ne_top : μx (A ∩ tailNoHit X y n) ≠ ⊤ := measure_ne_top _ _
  have hright_ne_top :
      (P y : Measure Ω) (tailNoHit X y 0) * μx A ≠ ⊤ := by
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  exact (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top).mp <| by
    simpa [ENNReal.toReal_mul, measure_ne_top _ _, measure_ne_top _ _] using hreal_eq

/-- Helper for Theorem 17.29: the time-`0` tail no-hit mass is the complement of the one-point
ever-hit probability. -/
private lemma tailNoHitReal_zero_eq_one_sub_everHitsProbability
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X] (y : E) :
    (P y : Measure Ω).real (tailNoHit X y 0) = 1 - (F[P, X]) y y := by
  have htail_meas : MeasurableSet (tailNoHit X y 0) :=
    measurableSet_tailNoHit (P := P) (X := X) (κ := κ) y 0
  -- Proof comment: rewrite the time-`0` tail event as the complement of the positive-time hit
  -- event and then invoke the definition of `F[P, X]`.
  calc
    (P y : Measure Ω).real (tailNoHit X y 0) =
        (P y : Measure Ω).real ((tailNoHit X y 0)ᶜ)ᶜ := by simp
    _ = 1 - (P y : Measure Ω).real ((tailNoHit X y 0)ᶜ) := by
          simpa using
            (MeasureTheory.probReal_compl_eq_one_sub (μ := (P y : Measure Ω))
              (s := (tailNoHit X y 0)ᶜ) htail_meas.compl)
    _ = 1 - (F[P, X]) y y := by
          rw [tailNoHit_zero_eq_compl_everHitsEvent]
          simp [everHitsProbability_def]

/-- Helper for Theorem 17.29: after a history event fixes the present state to `y`, the chance of
seeing a future hit of `y` factors by the one-point ever-hit probability from `y`. -/
private lemma measure_inter_prefix_futureHit_eq_mul
    {κ : ℕ → Kernel E E}
    [IsMarkovProcessRealization κ P X]
    {x y : E} {A : Set Ω} {n : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω).real (A ∩ {ω | ∃ m : ℕ, 0 < m ∧ X (n + m) ω = y}) =
      (F[P, X]) y y * (P x : Measure Ω).real A := by
  let μx : Measure Ω := P x
  have htail_meas : MeasurableSet (tailNoHit X y n) :=
    measurableSet_tailNoHit (P := P) (X := X) (κ := κ) y n
  have htail_factor :
      μx.real (A ∩ tailNoHit X y n) =
        (P y : Measure Ω).real (tailNoHit X y 0) * μx.real A := by
    -- Proof comment: first move the tail factorization from `ENNReal` masses to real
    -- probabilities.
    have htail_eq :
        μx (A ∩ tailNoHit X y n) =
          (P y : Measure Ω) (tailNoHit X y 0) * μx A :=
      measure_inter_prefix_tailNoHit_eq_mul
        (P := P) (X := X) (κ := κ) hA_meas hA_sub
    have := congrArg ENNReal.toReal htail_eq
    simpa [Measure.real_def, ENNReal.toReal_mul, measure_ne_top _ _, measure_ne_top _ _] using
      this
  have hsplit :
      μx.real (A ∩ tailNoHit X y n) +
        μx.real (A ∩ {ω | ∃ m : ℕ, 0 < m ∧ X (n + m) ω = y}) =
          μx.real A := by
    -- Proof comment: split the history event `A` into its tail-no-hit part and its complementary
    -- future-hit part.
    have hbase :=
      MeasureTheory.measureReal_inter_add_diff₀ (μ := μx) (s := A) htail_meas.nullMeasurableSet
    simpa [Set.diff_eq, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
      tailNoHit_compl_eq_futureHitEvent (Y := X) (y := y) (n := n)] using hbase
  have htail_zero :
      (P y : Measure Ω).real (tailNoHit X y 0) = 1 - (F[P, X]) y y :=
    tailNoHitReal_zero_eq_one_sub_everHitsProbability (P := P) (X := X) (κ := κ) y
  -- Proof comment: substitute the tail factor into the partition identity and solve the resulting
  -- scalar equation for the future-hit term.
  rw [htail_factor, htail_zero] at hsplit
  nlinarith

/-- Helper for Theorem 17.29: the future-hit restart factor also holds for `ENNReal` event
masses. -/
private lemma measure_inter_prefix_futureHit_eq_mul_ennreal
    {κ : ℕ → Kernel E E}
    [IsMarkovProcessRealization κ P X]
    {x y : E} {A : Set Ω} {n : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω) (A ∩ {ω | ∃ m : ℕ, 0 < m ∧ X (n + m) ω = y}) =
      ENNReal.ofReal ((F[P, X]) y y) * (P x : Measure Ω) A := by
  have hreal :
      (P x : Measure Ω).real (A ∩ {ω | ∃ m : ℕ, 0 < m ∧ X (n + m) ω = y}) =
        (F[P, X]) y y * (P x : Measure Ω).real A :=
    measure_inter_prefix_futureHit_eq_mul
      (P := P) (X := X) (κ := κ) hA_meas hA_sub
  have hFy_nonneg : 0 ≤ (F[P, X]) y y := by
    rw [everHitsProbability_def]
    exact MeasureTheory.measureReal_nonneg
  have hleft_ne_top :
      (P x : Measure Ω) (A ∩ {ω | ∃ m : ℕ, 0 < m ∧ X (n + m) ω = y}) ≠ ⊤ :=
    measure_ne_top _ _
  have hright_ne_top :
      ENNReal.ofReal ((F[P, X]) y y) * (P x : Measure Ω) A ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  exact (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top).mp <| by
    simpa [Measure.real_def, ENNReal.toReal_mul, hFy_nonneg, measure_ne_top _ _, measure_ne_top _ _]
      using hreal

/-- Helper for Theorem 17.29: on the exact `k`th entrance slice at time `n`, finiteness of the
next entrance is equivalent to one further future hit after time `n`. -/
private lemma entranceSlice_inter_nextEntranceFinite_eq_futureHit
    (k : ℕ+) (n : ℕ) :
    entranceSlice X y k n ∩ {ω | (τ_[X, y]^(k + 1)) ω < ⊤} =
      entranceSlice X y k n ∩ {ω | ∃ m : ℕ, 0 < m ∧ X (n + m) ω = y} := by
  ext ω
  constructor
  · rintro ⟨hSlice, hNext⟩
    have hτ : (τ_[X, y]^k) ω = n := by
      simpa [entranceSlice] using hSlice
    have hnext_ne_top : (τ_[X, y]^(k + 1)) ω ≠ ⊤ := ne_of_lt hNext
    let N : ℕ := ENat.toNat ((τ_[X, y]^(k + 1)) ω)
    have hle : (τ_[X, y]^(k + 1)) ω ≤ N := by
      simpa [N, ENat.coe_toNat hnext_ne_top]
    rcases (iteratedEntranceTime_succ_le_iff_existsHitAfter X y ω k N).1 hle with
      ⟨j, hjτ, _, hjy⟩
    have hj_gt_n : n < j := by
      simpa [hτ] using hjτ
    refine ⟨hSlice, ⟨j - n, Nat.sub_pos_of_lt hj_gt_n, ?_⟩⟩
    simpa [Nat.add_sub_of_le hj_gt_n.le] using hjy
  · rintro ⟨hSlice, ⟨m, hmpos, hmy⟩⟩
    have hτ : (τ_[X, y]^k) ω = n := by
      simpa [entranceSlice] using hSlice
    have hlt : (τ_[X, y]^k) ω < n + m := by
      simpa [hτ] using (show (n : ℕ∞) < n + m by exact_mod_cast Nat.lt_add_of_pos_right hmpos)
    have hle :
        (τ_[X, y]^(k + 1)) ω ≤ n + m := by
      exact (iteratedEntranceTime_succ_le_iff_existsHitAfter X y ω k (n + m)).2
        ⟨n + m, hlt, le_rfl, hmy⟩
    exact ⟨hSlice, lt_of_le_of_lt hle (by simp)⟩

/-- Helper for Theorem 17.29: exact entrance slices are measurable in the ambient sigma-algebra. -/
private lemma entranceSlice_measurable
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (y : E) (k : ℕ+) (n : ℕ) :
    MeasurableSet (entranceSlice X y k n) := by
  have hslice_meas_gen :
      MeasurableSet[generatedFiltrationSpace X n] (entranceSlice X y k n) :=
    entranceSlice_measurable_generated (Y := X) (y := y) (k := k) (n := n)
  exact (generatedFiltrationSpace_le_ambient (X := X)
    (inferInstance : IsMarkovProcessRealization κ P X).measurable_process n) _ hslice_meas_gen

/-- Helper for Theorem 17.29: the deterministic future-hit event is measurable in the ambient
sigma-algebra. -/
private lemma futureHitEvent_measurable
    {κ : ℕ → Kernel E E} [IsMarkovProcessRealization κ P X]
    (y : E) (n : ℕ) :
    MeasurableSet {ω | ∃ m : ℕ, 0 < m ∧ X (n + m) ω = y} := by
  rw [← tailNoHit_compl_eq_futureHitEvent (Y := X) (y := y) (n := n)]
  exact (measurableSet_tailNoHit (P := P) (X := X) (κ := κ) y n).compl

/-- Helper for Theorem 17.29: the finite entrance event is the union of the nonzero exact
entrance slices. -/
private lemma finiteEntranceEvent_eq_iUnion_succEntranceSlice
    (y : E) (k : ℕ+) :
    {ω | (τ_[X, y]^k) ω < ⊤} = ⋃ n : ℕ, entranceSlice X y k (n + 1) := by
  ext ω
  constructor
  · intro hω
    have hUnion : ω ∈ ⋃ n : ℕ, entranceSlice X y k n := by
      rw [← finiteEntranceEvent_eq_iUnion_entranceSlice (Y := X) (y := y) (k := k)]
      exact hω
    rcases Set.mem_iUnion.1 hUnion with ⟨n, hn⟩
    -- Proof comment: the zero slice is empty, so every finite entrance time lands in a shifted
    -- slice indexed by `n + 1`.
    cases n with
    | zero =>
        have hzero : ω ∈ (∅ : Set Ω) := by
          simpa [entranceSlice_zero_eq_empty (Y := X) (y := y) (k := k)] using hn
        simpa using hzero
    | succ n =>
        exact Set.mem_iUnion.2 ⟨n, by simpa using hn⟩
  · intro hω
    rw [finiteEntranceEvent_eq_iUnion_entranceSlice (Y := X) (y := y) (k := k)]
    rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
    exact Set.mem_iUnion.2 ⟨n + 1, hn⟩

/-- Helper for Theorem 17.29: on each exact `k`th entrance slice, one more finite entrance
contributes exactly one factor `F(y, y)` to the event mass. -/
private lemma entranceSliceNextFiniteMass_eq_returnProbMul
    {κ : ℕ → Kernel E E}
    [IsMarkovProcessRealization κ P X]
    (x y : E) (k : ℕ+) (n : ℕ) :
    (P x : Measure Ω) (entranceSlice X y k (n + 1) ∩ {ω | (τ_[X, y]^(k + 1)) ω < ⊤}) =
      ENNReal.ofReal ((F[P, X]) y y) * (P x : Measure Ω) (entranceSlice X y k (n + 1)) := by
  -- Proof comment: on the exact slice `τ^k = n + 1`, finiteness of `τ^(k + 1)` is the same as a
  -- deterministic future hit after time `n + 1`, so the restart factor is exactly `F(y, y)`.
  rw [entranceSlice_inter_nextEntranceFinite_eq_futureHit (X := X) (y := y) (k := k) (n := n + 1)]
  exact measure_inter_prefix_futureHit_eq_mul_ennreal
    (P := P) (X := X) (κ := κ)
    (x := x) (y := y) (A := entranceSlice X y k (n + 1)) (n := n + 1)
    (entranceSlice_measurable_generated (Y := X) (y := y) (k := k) (n := n + 1))
    (entranceSlice_subset_state (Y := X) (y := y) (k := k) (n := n))

/-- Helper for Theorem 17.29: the finite masses of successive entrance events satisfy the
geometric recurrence with ratio `F(y, y)`. -/
private lemma finiteEntranceMass_succ_eq_returnProb_mul_ennreal
    {κ : ℕ → Kernel E E}
    [IsMarkovProcessRealization κ P X]
    (x y : E) (k : ℕ+) :
    (P x : Measure Ω) {ω | (τ_[X, y]^(k + 1)) ω < ⊤} =
      ENNReal.ofReal ((F[P, X]) y y) * (P x : Measure Ω) {ω | (τ_[X, y]^k) ω < ⊤} := by
  let nextSlice : ℕ → Set Ω :=
    fun n ↦ entranceSlice X y k (n + 1) ∩ {ω | (τ_[X, y]^(k + 1)) ω < ⊤}
  have hprev_pairwise :
      Pairwise fun m n ↦ Disjoint (entranceSlice X y k (m + 1)) (entranceSlice X y k (n + 1)) := by
    intro m n hmn
    exact entranceSlice_pairwiseDisjoint (Y := X) (y := y) (k := k) (by simpa using hmn)
  have hnext_pairwise :
      Pairwise fun m n ↦ Disjoint (nextSlice m) (nextSlice n) := by
    intro m n hmn
    refine Set.disjoint_left.2 ?_
    intro ω hm hn
    exact Set.disjoint_left.1 (hprev_pairwise hmn) hm.1 hn.1
  have hprev_meas :
      ∀ n : ℕ, MeasurableSet (entranceSlice X y k (n + 1)) := by
    intro n
    exact entranceSlice_measurable (κ := κ) (P := P) (X := X) y k (n + 1)
  have hnext_meas : ∀ n : ℕ, MeasurableSet (nextSlice n) := by
    intro n
    -- Proof comment: the shifted slice is measurable, and the next-entrance event rewrites to a
    -- measurable deterministic future-hit event.
    rw [show nextSlice n =
        entranceSlice X y k (n + 1) ∩ {ω | ∃ m : ℕ, 0 < m ∧ X (n + 1 + m) ω = y} by
      simpa [nextSlice] using
        (entranceSlice_inter_nextEntranceFinite_eq_futureHit
          (X := X) (y := y) (k := k) (n := n + 1))]
    exact (hprev_meas n).inter (futureHitEvent_measurable (κ := κ) (P := P) (X := X) y (n + 1))
  have hnext_union :
      {ω | (τ_[X, y]^(k + 1)) ω < ⊤} = ⋃ n : ℕ, nextSlice n := by
    ext ω
    constructor
    · intro hω
      have hprev_finite : (τ_[X, y]^k) ω < ⊤ := by
        let N : ℕ := ENat.toNat ((τ_[X, y]^(k + 1)) ω)
        have hnext_ne_top : (τ_[X, y]^(k + 1)) ω ≠ ⊤ := ne_of_lt hω
        have hle : (τ_[X, y]^(k + 1)) ω ≤ N := by
          simpa [N, ENat.coe_toNat hnext_ne_top]
        rcases (iteratedEntranceTime_succ_le_iff_existsHitAfter X y ω k N).1 hle with
          ⟨j, hjτ, _, _⟩
        exact lt_of_lt_of_le hjτ le_top
      have hprev_mem : ω ∈ ⋃ n : ℕ, entranceSlice X y k (n + 1) := by
        rw [← finiteEntranceEvent_eq_iUnion_succEntranceSlice (X := X) (y := y) (k := k)]
        exact hprev_finite
      rcases Set.mem_iUnion.1 hprev_mem with ⟨n, hn⟩
      exact Set.mem_iUnion.2 ⟨n, ⟨hn, hω⟩⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      exact hn.2
  -- Proof comment: reassemble the disjoint shifted slices, factor out the constant restart
  -- probability, and recover the previous finite entrance mass.
  calc
    (P x : Measure Ω) {ω | (τ_[X, y]^(k + 1)) ω < ⊤} =
        (P x : Measure Ω) (⋃ n : ℕ, nextSlice n) := by
          rw [hnext_union]
    _ = ∑' n : ℕ, (P x : Measure Ω) (nextSlice n) := by
          exact MeasureTheory.measure_iUnion hnext_pairwise hnext_meas
    _ = ∑' n : ℕ, ENNReal.ofReal ((F[P, X]) y y) * (P x : Measure Ω) (entranceSlice X y k (n + 1)) := by
          refine tsum_congr fun n ↦ ?_
          simpa [nextSlice] using
            entranceSliceNextFiniteMass_eq_returnProbMul
              (P := P) (X := X) (κ := κ) x y k n
    _ = ENNReal.ofReal ((F[P, X]) y y) *
          ∑' n : ℕ, (P x : Measure Ω) (entranceSlice X y k (n + 1)) := by
            rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal ((F[P, X]) y y) *
          (P x : Measure Ω) (⋃ n : ℕ, entranceSlice X y k (n + 1)) := by
            congr 1
            symm
            exact MeasureTheory.measure_iUnion hprev_pairwise hprev_meas
    _ = ENNReal.ofReal ((F[P, X]) y y) * (P x : Measure Ω) {ω | (τ_[X, y]^k) ω < ⊤} := by
          rw [finiteEntranceEvent_eq_iUnion_succEntranceSlice (X := X) (y := y) (k := k)]

-- Proof sketch: argue by induction on the positive entrance index `k`. For `k = 1`, the event is
-- exactly the defining event for `F[P, X] x y`. For the induction step, stop the chain at
-- the `(k - 1)`st entrance time and apply the strong Markov property from Theorem 17.14 to the
-- event of one further entrance into `y`, which contributes the factor `F[P, X] y y`.
/-- Theorem 17.29: for a discrete-time Markov process realization, the probability under `P x`
that the `k`th entrance time into `y` is finite is the first-entrance probability from `x` to
`y` times the `(k - 1)`st power of the return probability from `y` to itself. Here `τ_[X, y]^k` is
the textbook `k`th entrance time into `y`. -/
theorem iteratedEntranceTime_finite_probability_eq_everHitsProbability_mul_selfPow
    [IsMarkovProcessRealization κ P X]
    (x y : E) (k : ℕ+) :
    (P x : Measure Ω).real {ω | (τ_[X, y]^k) ω < ⊤} =
      (F[P, X]) x y * (F[P, X]) y y ^ k.natPred := by
  -- Route correction: the source proof phrases the induction at the random time `τ_y^(k-1)`,
  -- but the current realization API only exposes deterministic-time conditioning. The proof
  -- therefore runs through the exact-slice ENNReal recurrence proved just above.
  induction k using PNat.recOn with
  | one =>
      -- Proof comment: the first entrance event is exactly the defining event for `F(x, y)`.
      have hOnePred : (1 : ℕ+).natPred = 0 := by
        rfl
      have hEq :
          {ω | (τ_[X, y]^1) ω < ⊤} = {ω | ∃ n : ℕ, 0 < n ∧ X n ω = y} := by
        ext ω
        simpa [iteratedEntranceTime_one] using (hittingAfter_singleton_lt_top_iff X y ω)
      calc
        (P x : Measure Ω).real {ω | (τ_[X, y]^1) ω < ⊤} = (F[P, X]) x y := by
          rw [hEq, everHitsProbability_def]
        _ = (F[P, X]) x y * (F[P, X]) y y ^ (1 : ℕ+).natPred := by
          simp [hOnePred]
  | succ k ih =>
      have hFy_nonneg : 0 ≤ (F[P, X]) y y := by
        rw [everHitsProbability_def]
        exact MeasureTheory.measureReal_nonneg
      have hstep_real :
          (P x : Measure Ω).real {ω | (τ_[X, y]^(k + 1)) ω < ⊤} =
            (F[P, X]) y y * (P x : Measure Ω).real {ω | (τ_[X, y]^k) ω < ⊤} := by
        -- Proof comment: convert the ENNReal recurrence to reals once, using finiteness of all
        -- event masses under a probability measure.
        have hstep :=
          congrArg ENNReal.toReal
            (finiteEntranceMass_succ_eq_returnProb_mul_ennreal
              (κ := κ) (P := P) (X := X) (x := x) (y := y) (k := k))
        simpa [Measure.real_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hFy_nonneg,
          measure_ne_top _ _, mul_assoc, mul_left_comm, mul_comm] using hstep
      -- Proof comment: the recurrence adds one more factor of the return probability `F(y, y)`.
      calc
        (P x : Measure Ω).real {ω | (τ_[X, y]^(k + 1)) ω < ⊤} =
            (F[P, X]) y y * (P x : Measure Ω).real {ω | (τ_[X, y]^k) ω < ⊤} := hstep_real
        _ = (F[P, X]) y y * ((F[P, X]) x y * (F[P, X]) y y ^ k.natPred) := by
              rw [ih]
        _ = (F[P, X]) x y *
              ((F[P, X]) y y ^ k.natPred * (F[P, X]) y y) := by
              ac_rfl
        _ = (F[P, X]) x y * (F[P, X]) y y ^ (k.natPred + 1) := by
              exact congrArg
                (fun t : ℝ ↦ (F[P, X]) x y * t)
                (pow_succ ((F[P, X]) y y) k.natPred).symm
        _ = (F[P, X]) x y * (F[P, X]) y y ^ (k : ℕ) := by
              rw [PNat.natPred_add_one]
        _ = (F[P, X]) x y * (F[P, X]) y y ^ (k + 1).natPred := by
              rw [PNat.add_one, Nat.natPred_succPNat]

end

end ProbabilityTheory
