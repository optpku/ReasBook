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

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]
variable {κ : ℕ → Kernel E E}
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}

/-- Helper for Theorem 17.38: `ℕ+` is used as a discrete counting index for iterated entrance
times. -/
local instance : MeasurableSpace ℕ+ := ⊤

/-- Helper for Theorem 17.38: the measurable structure on `ℕ+` is discrete. -/
local instance : DiscreteMeasurableSpace ℕ+ where
  forall_measurableSet := by
    intro s
    trivial

/-- Helper for Theorem 17.38: the finite-prefix normalization compares states by classical
equality. -/
local instance : DecidableEq E := Classical.decEq E

/-- Helper for Theorem 17.38: the pathwise positive visit times of `ω` at the state `x`. -/
private def positiveVisitSet (Y : ℕ → Ω → E) (x : E) (ω : Ω) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ Y n ω = x}

/-- Helper for Theorem 17.38: a bound on the infimum of a set of natural times in `ℕ∞` is
equivalent to a bounded witness in the underlying set. -/
private lemma sInf_natImage_le_iff {S : Set ℕ} {N : ℕ} :
    sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) ≤ N ↔ ∃ n ∈ S, n ≤ N := by
  -- Proof comment: if the image set is nonempty, its infimum is the least witness in `S`; if
  -- the set is empty, the infimum is `⊤`, so neither side can hold.
  by_cases hS : S.Nonempty
  · -- Proof comment: for a nonempty set, `sInf` in `ℕ∞` is the coerced natural infimum.
    have hsInf :
        sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) = (((sInf S : ℕ) : ℕ∞)) := by
      simpa using (WithTop.coe_sInf' hS (OrderBot.bddBelow S)).symm
    constructor
    · intro h
      refine ⟨(sInf S : ℕ), Nat.sInf_mem hS, ?_⟩
      have hsInf_leN : ((((sInf S : ℕ) : ℕ) : ℕ∞)) ≤ N := by
        simpa [hsInf] using h
      exact_mod_cast hsInf_leN
    · rintro ⟨n, hnS, hnN⟩
      have hsInf_le_nat : (sInf S : ℕ) ≤ n := Nat.sInf_le hnS
      have hsInf_leN_nat : (sInf S : ℕ) ≤ N := hsInf_le_nat.trans hnN
      have hsInf_leN : ((((sInf S : ℕ) : ℕ) : ℕ∞)) ≤ N := by
        exact_mod_cast hsInf_leN_nat
      simpa [hsInf] using hsInf_leN
  · -- Proof comment: the empty set has infimum `⊤`, so neither side can hold.
    have hS_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    subst hS_empty
    simp

/-- Helper for Theorem 17.38: the successor entrance time is bounded by `N` exactly when there is
a visit to `x` by time `N` occurring strictly after the previous entrance. -/
private lemma iteratedEntranceTime_succ_le_iff_existsHitAfter
    (Y : ℕ → Ω → E) (x : E) (ω : Ω) (k : ℕ+) (N : ℕ) :
    (τ_[Y, x]^(k + 1)) ω ≤ N ↔
      ∃ n : ℕ, (τ_[Y, x]^k) ω < n ∧ n ≤ N ∧ Y n ω = x := by
  -- Proof comment: unfold the recursive successor step and replace the `sInf` bound by a bounded
  -- future hit witness.
  rw [iteratedEntranceTime_succ]
  rw [sInf_natImage_le_iff]
  constructor
  · rintro ⟨n, hn, hnN⟩
    exact ⟨n, hn.1, hnN, hn.2⟩
  · rintro ⟨n, hτ, hnN, hx⟩
    exact ⟨n, ⟨hτ, hx⟩, hnN⟩

/-- Helper for Theorem 17.38: the generated history filtration is monotone in the time index. -/
private lemma generatedFiltrationSpace_mono
    (Y : ℕ → Ω → E) {m n : ℕ} (hmn : m ≤ n) :
    generatedFiltrationSpace Y m ≤ generatedFiltrationSpace Y n := by
  -- Proof comment: increasing the terminal time only enlarges the supremum of available history
  -- coordinates.
  refine iSup₂_le fun r hr ↦ ?_
  exact le_iSup_of_le r <| le_iSup_of_le (hr.trans hmn) le_rfl

/-- Helper for Theorem 17.38: every coordinate `Y i` is measurable with respect to the generated
history filtration at any later time `n ≥ i`. -/
private lemma measurable_process_generated
    (Y : ℕ → Ω → E) {i n : ℕ} (hi : i ≤ n) :
    @Measurable Ω E (generatedFiltrationSpace Y n) _ (Y i) := by
  -- Proof comment: the coordinate sigma-algebra at time `i` already appears among the generators
  -- of the history filtration at every later time `n`.
  exact Measurable.of_comap_le <|
    le_iSup_of_le i <| le_iSup_of_le hi le_rfl

/-- Helper for Theorem 17.38: the state event `{ω | Y i ω = x}` is measurable in every generated
history filtration that already contains time `i`. -/
private lemma measurableSet_stateEvent_generated
    (Y : ℕ → Ω → E) (x : E) {i n : ℕ} (hi : i ≤ n) :
    MeasurableSet[generatedFiltrationSpace Y n] {ω | Y i ω = x} := by
  -- Proof comment: this is the singleton preimage of the coordinate map `Y i`.
  let hYi : @Measurable Ω E (generatedFiltrationSpace Y n) _ (Y i) :=
    measurable_process_generated (Y := Y) hi
  change MeasurableSet[generatedFiltrationSpace Y n] ((Y i) ⁻¹' ({x} : Set E))
  exact hYi (MeasurableSet.singleton x)

/-- Helper for Theorem 17.38: the bounded entrance event `{τ_[Y, x]^k ≤ N}` is measurable with
respect to the history sigma-algebra at time `N`. -/
private lemma iteratedEntranceTime_le_measurable_generated
    (Y : ℕ → Ω → E) (x : E) :
    ∀ (k : ℕ+) (N : ℕ),
      MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, x]^k) ω ≤ N} := by
  intro k N
  induction k using PNat.recOn generalizing N with
  | one =>
      have hEq :
          {ω | (τ_[Y, x]^1) ω ≤ N} =
            ⋃ j ∈ ((Finset.Icc 1 N : Finset ℕ) : Set ℕ), {ω | Y j ω = x} := by
        ext ω
        simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using
          (MeasureTheory.hittingAfter_le_iff
            (u := Y) (s := ({x} : Set E)) (n := 1) (ω := ω) (i := N))
      rw [hEq]
      refine MeasurableSet.biUnion (Set.to_countable _) ?_
      intro j hj
      exact measurableSet_stateEvent_generated
        (Y := Y) x (hi := (Finset.mem_Icc.mp hj).2)
  | succ k ih =>
      let slice : ℕ → Set Ω := fun j =>
        {ω | (τ_[Y, x]^k) ω < j} ∩ {ω | Y j ω = x}
      have hEq :
          {ω | (τ_[Y, x]^(k + 1)) ω ≤ N} =
            ⋃ j ∈ ((Finset.Icc 1 N : Finset ℕ) : Set ℕ), slice j := by
        ext ω
        constructor
        · intro hω
          rcases (iteratedEntranceTime_succ_le_iff_existsHitAfter Y x ω k N).1 hω with
            ⟨j, hτj, hjN, hjx⟩
          have hj_pos : 0 < j := by
            cases j with
            | zero => simpa using hτj
            | succ j => exact Nat.succ_pos j
          exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨Finset.mem_Icc.mpr ⟨hj_pos, hjN⟩,
            ⟨hτj, hjx⟩⟩⟩
        · intro hω
          rcases Set.mem_iUnion.1 hω with ⟨j, hω⟩
          rcases Set.mem_iUnion.1 hω with ⟨hj, hslice⟩
          exact (iteratedEntranceTime_succ_le_iff_existsHitAfter Y x ω k N).2
            ⟨j, hslice.1, (Finset.mem_Icc.mp hj).2, hslice.2⟩
      rw [hEq]
      refine MeasurableSet.biUnion (Set.to_countable _) ?_
      intro j hj
      have hj_le : j ≤ N := (Finset.mem_Icc.mp hj).2
      have hlt_N :
          MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, x]^k) ω < j} := by
        cases j with
        | zero =>
            have hj_false : ¬ 0 ∈ (Finset.Icc 1 N : Finset ℕ) := by
              simpa using hj
            exact False.elim (hj_false hj)
        | succ j =>
            have hle_j :
                MeasurableSet[generatedFiltrationSpace Y j]
                  {ω | (τ_[Y, x]^k) ω ≤ j} :=
              ih j
            have hle_N :
                MeasurableSet[generatedFiltrationSpace Y N]
                  {ω | (τ_[Y, x]^k) ω ≤ j} := by
              have hmono := generatedFiltrationSpace_mono
                (Y := Y) (Nat.le_trans (Nat.le_succ j) hj_le)
              exact hmono (s := {ω | (τ_[Y, x]^k) ω ≤ j}) hle_j
            simpa [ENat.lt_coe_add_one_iff] using hle_N
      exact hlt_N.inter (measurableSet_stateEvent_generated (Y := Y) x (hi := hj_le))

/-- Helper for Theorem 17.38: the strict bounded entrance event `{τ_[Y, x]^k < N}` is measurable
with respect to the history sigma-algebra at time `N`. -/
private lemma iteratedEntranceTime_lt_measurable_generated
    (Y : ℕ → Ω → E) (x : E) (k : ℕ+) :
    ∀ N : ℕ,
      MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, x]^k) ω < N} := by
  intro N
  cases N with
  | zero =>
      simpa using (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  | succ N =>
      have hle_N :
          MeasurableSet[generatedFiltrationSpace Y (N + 1)] {ω | (τ_[Y, x]^k) ω ≤ N} := by
        have hle_N_base :
            MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, x]^k) ω ≤ N} :=
          iteratedEntranceTime_le_measurable_generated (Y := Y) x k N
        have hmono := generatedFiltrationSpace_mono (Y := Y) (Nat.le_succ N)
        exact hmono (s := {ω | (τ_[Y, x]^k) ω ≤ N}) hle_N_base
      simpa [ENat.lt_coe_add_one_iff] using hle_N

/-- Helper for Theorem 17.38: the exact entrance slice at time `n` for the `k`th entrance into
`x`. -/
private def entranceSlice (Y : ℕ → Ω → E) (x : E) (k : ℕ+) (n : ℕ) : Set Ω :=
  {ω | (τ_[Y, x]^k) ω = n}

/-- Helper for Theorem 17.38: exact entrance slices are measurable in the history sigma-algebra at
their terminal time. -/
private lemma entranceSlice_measurable_generated
    (Y : ℕ → Ω → E) (x : E) (k : ℕ+) (n : ℕ) :
    MeasurableSet[generatedFiltrationSpace Y n] (entranceSlice Y x k n) := by
  have hEq :
      entranceSlice Y x k n =
        {ω | (τ_[Y, x]^k) ω ≤ n} \ {ω | (τ_[Y, x]^k) ω < n} := by
    ext ω
    constructor
    · intro hω
      have hτ : (τ_[Y, x]^k) ω = n := by
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
    (iteratedEntranceTime_le_measurable_generated (Y := Y) x k n).diff
      (iteratedEntranceTime_lt_measurable_generated (Y := Y) x k n)

/-- Helper for Theorem 17.38: the finite entrance event is the union of its exact-time slices. -/
private lemma finiteEntranceEvent_eq_iUnion_entranceSlice
    (Y : ℕ → Ω → E) (x : E) (k : ℕ+) :
    {ω | (τ_[Y, x]^k) ω < ⊤} = ⋃ n : ℕ, entranceSlice Y x k n := by
  ext ω
  constructor
  · intro hω
    refine Set.mem_iUnion.2 ⟨ENat.toNat ((τ_[Y, x]^k) ω), ?_⟩
    have hne : (τ_[Y, x]^k) ω ≠ ⊤ := ne_of_lt hω
    simp [entranceSlice, ENat.coe_toNat hne]
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨n, hn⟩
    simp [entranceSlice] at hn
    simpa [hn]

/-- Helper for Theorem 17.38: exact entrance slices are measurable in the ambient sigma-algebra. -/
private lemma entranceSlice_measurable
    [IsMarkovProcessRealization κ P X] (x : E) (k : ℕ+) (n : ℕ) :
    MeasurableSet (entranceSlice X x k n) := by
  have hslice_meas_gen :
      MeasurableSet[generatedFiltrationSpace X n] (entranceSlice X x k n) :=
    entranceSlice_measurable_generated (Y := X) (x := x) (k := k) (n := n)
  exact (generatedFiltrationSpace_le_ambient (X := X)
    (inferInstance : IsMarkovProcessRealization κ P X).measurable_process n) _ hslice_meas_gen

/-- Helper for Theorem 17.38: `prefixHasIteratedReturn x k m f` records `k` strictly positive
visits to `x` inside the finite prefix `f : Fin m → E`. -/
private def prefixHasIteratedReturn (x : E) : ℕ+ → ∀ m : ℕ, (Fin m → E) → Prop :=
  fun k =>
    PNat.recOn k
      (fun m f => ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = x)
      (fun _ ih m f =>
        ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = x ∧
          ih i (fun j : Fin i ↦ f ⟨j, Nat.lt_trans j.2 i.2⟩))

/-- Helper for Theorem 17.38: the first positive return in a prefix is just one positive index
carrying the value `x`. -/
private lemma prefixHasIteratedReturn_one_iff
    (x : E) (m : ℕ) (f : Fin m → E) :
    prefixHasIteratedReturn x 1 m f ↔ ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = x := by
  simp [prefixHasIteratedReturn]

/-- Helper for Theorem 17.38: the successor prefix-return predicate peels off the last positive
return and recurses on the earlier prefix. -/
private lemma prefixHasIteratedReturn_succ_iff
    (x : E) (k : ℕ+) (m : ℕ) (f : Fin m → E) :
    prefixHasIteratedReturn x (k + 1) m f ↔
      ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = x ∧
        prefixHasIteratedReturn x k i (fun j : Fin i ↦ f ⟨j, Nat.lt_trans j.2 i.2⟩) := by
  simp [prefixHasIteratedReturn]

/-- Helper for Theorem 17.38: the bounded event `τ_[Y,x]^k < m` is equivalent to the recursive
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
          constructor
          · intro h
            simpa using h
          · intro h
            rcases h with ⟨i, _, _⟩
            exact Fin.elim0 i
      | succ m =>
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
            rcases (iteratedEntranceTime_succ_le_iff_existsHitAfter
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
              exact (iteratedEntranceTime_succ_le_iff_existsHitAfter
                (Y := Y) (x := x) (ω := ω) (k := k) (N := m)).2
                ⟨i, (ih i).2 hi_prefix, Nat.le_of_lt_succ i.2, by simpa using hi_eq⟩
            exact hbound.mpr hle

/-- Helper for Theorem 17.38: the recursive finite-prefix witness forces at least the
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

/-- Helper for Theorem 17.38: a prefix with at least `k` positive visits already carries the
recursive witness for the `k`th iterated return. -/
private lemma prefixHasIteratedReturn_of_le_card
    (x : E) :
    ∀ {k : ℕ+} {m : ℕ} {f : Fin m → E},
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
          exact Fin.ext (congrArg (fun z : Fin i ↦ (z : ℕ)) himage_eq)
      have hk_le_t : (k : ℕ) ≤ t.card := le_trans hk_le_erase herase_le_t
      exact (prefixHasIteratedReturn_succ_iff x k m f).2 ⟨i, hi_props.1, hi_props.2, ih hk_le_t⟩

/-- Helper for Theorem 17.38: the recursive finite-prefix predicate is equivalent to the
corresponding prefix visit-count lower bound. -/
private lemma prefixHasIteratedReturn_iff_prefixVisitCountAtLeast
    (x : E) {k : ℕ+} {m : ℕ} {f : Fin m → E} :
    prefixHasIteratedReturn x k m f ↔
      (k : ℕ) ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = x).card := by
  constructor
  · exact prefixHasIteratedReturn_le_card x
  · exact prefixHasIteratedReturn_of_le_card x

/-- Helper for Theorem 17.38: the event `τ_[Y,x]^k < m` is equivalent to having at least `k`
positive visits to `x` in the first `m` coordinates of the path. -/
private lemma iteratedEntranceTime_lt_iff_prefixVisitCountAtLeast
    (Y : ℕ → Ω → E) (x : E) (ω : Ω) :
    ∀ (k : ℕ+) (m : ℕ),
      (τ_[Y, x]^k) ω < m ↔
        (k : ℕ) ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ Y i ω = x).card
  | k, m => by
      -- Proof comment: normalize the recursive prefix witness to a plain cardinality statement.
      rw [iteratedEntranceTime_lt_iff_prefixHasIteratedReturn,
        prefixHasIteratedReturn_iff_prefixVisitCountAtLeast]

/-- Helper for Theorem 17.38: the event `τ_[Y,x]^k ≤ N` is equivalent to having at least `k`
positive visits to `x` in the first `N + 1` coordinates of the path. -/
private lemma iteratedEntranceTime_le_iff_prefixVisitCountAtLeast
    (Y : ℕ → Ω → E) (x : E) (ω : Ω) :
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

/-- Helper for Theorem 17.38: every bounded prefix count of visits to `x` injects into the full
set of positive visit times, so its cardinality is bounded by the total positive-visit encard. -/
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
  -- Proof comment: compare the filtered prefix with its image inside the full positive-visit set.
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

/-- Helper for Theorem 17.38: among positive integers, exactly `m` indices satisfy `k ≤ m`. -/
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
  -- Proof comment: transport the positive-natural counting problem to the usual range `0, ..., m-1`.
  calc
    Measure.count s = Measure.count (Equiv.pnatEquivNat '' s) := by
      symm
      exact Measure.count_injective_image Equiv.pnatEquivNat.injective s
    _ = Measure.count {n : ℕ | n < m} := by
      rw [himage]
    _ = ({n : ℕ | n < m}).encard := by
      rw [Measure.count_apply MeasurableSet.of_discrete]
    _ = (m : ℝ≥0∞) := by
      exact_mod_cast (Set.Nat.encard_range m)

/-- Helper for Theorem 17.38: counting positive integers bounded by an `ℕ∞` value recovers that
bound. -/
private lemma count_pnat_le_enat_eq (t : ℕ∞) :
    Measure.count {k : ℕ+ | (k : ℕ∞) ≤ t} = t := by
  by_cases ht : t = ⊤
  · subst ht
    simpa [ENat.card_eq_top_of_infinite] using
      (Measure.count_univ : Measure.count (Set.univ : Set ℕ+) = ENat.card ℕ+)
  · -- Proof comment: in the finite case, replace the `ℕ∞` bound by `ENat.toNat t`.
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
      _ = (t : ℝ≥0∞) := by
            exact_mod_cast ENat.coe_toNat ht

/-- Helper for Theorem 17.38: a finite iterated entrance time is equivalent to having at least
`k` positive visits to `x`; the right-hand side is expressed through the full positive-visit
encard. -/
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
    -- Proof comment: a finite entrance time gives a bounded prefix with enough positive visits.
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
    -- Proof comment: a concrete `k`-element positive-visit subset is bounded by its maximum.
    have hτ_le : (τ_[Y, x]^k) ω ≤ N :=
      (iteratedEntranceTime_le_iff_prefixVisitCountAtLeast Y x ω k N).2 hk_le_prefix
    exact lt_of_le_of_lt hτ_le (by simp)

/-- Helper for Theorem 17.38: pathwise, the indicator series of finite iterated entrance times is
the counting measure of the finite-entrance index set. -/
private lemma tsum_iteratedEntranceIndicators_eq_countFiniteIteratedEntrances
    (x : E) (ω : Ω) :
    (∑' k : ℕ+,
      Set.indicator {ω' | (τ_[X, x]^k) ω' < ⊤} (fun _ ↦ (1 : ℝ≥0∞)) ω) =
      Measure.count {k : ℕ+ | (τ_[X, x]^k) ω < ⊤} := by
  rw [Measure.count_apply MeasurableSet.of_discrete]
  -- Proof comment: evaluate the indicator series over the subtype of finite entrance indices.
  calc
    ∑' k : ℕ+, Set.indicator {ω' | (τ_[X, x]^k) ω' < ⊤} (fun _ ↦ (1 : ℝ≥0∞)) ω
      = ∑' _ : {k : ℕ+ | (τ_[X, x]^k) ω < ⊤}, (1 : ℝ≥0∞) := by
          symm
          simpa [Set.indicator_apply] using
            (tsum_subtype
              (s := {k : ℕ+ | (τ_[X, x]^k) ω < ⊤})
              (f := fun _ : ℕ+ ↦ (1 : ℝ≥0∞)))
    _ = ENat.card {k : ℕ+ | (τ_[X, x]^k) ω < ⊤} := by
          simpa using
            (ENNReal.tsum_one : ∑' _ : {k : ℕ+ | (τ_[X, x]^k) ω < ⊤}, (1 : ℝ≥0∞) =
              ENat.card {k : ℕ+ | (τ_[X, x]^k) ω < ⊤})
    _ = ({k : ℕ+ | (τ_[X, x]^k) ω < ⊤}).encard := by
          rw [ENat.card_coe_set_eq]

/-- Helper for Theorem 17.38: pathwise, the positive-time visit count equals the number of finite
iterated entrance times into `x`. -/
private lemma totalVisitsFromOne_eq_countFiniteIteratedEntrances
    (x : E) (ω : Ω) :
    totalVisitsFrom X x 1 ω = Measure.count {k : ℕ+ | (τ_[X, x]^k) ω < ⊤} := by
  -- Proof comment: identify the positive visit count with the encard of the positive-visit set.
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

-- Route correction: the positive-time Green normalization is kept in this support file so the
-- main Theorem 17.38 proof only consumes the owner-level bridge.
/-- Helper for Theorem 17.38: rewrite the positive-time diagonal Green function as the series of
finite iterated-entrance probabilities. -/
lemma greenFunctionFromOneSelf_eq_tsum_iteratedEntranceProbabilities
    [IsMarkovProcessRealization κ P X] (x : E) :
    (G[P, X; 1]) x x =
      ∑' k : ℕ+, ENNReal.ofReal ((P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤}) := by
  have hτ_meas : ∀ k : ℕ+, MeasurableSet {ω | (τ_[X, x]^k) ω < ⊤} := by
    intro k
    rw [finiteEntranceEvent_eq_iUnion_entranceSlice (Y := X) (x := x) k]
    exact MeasurableSet.iUnion fun n =>
      entranceSlice_measurable (κ := κ) (P := P) (X := X) x k n
  -- Proof comment: rewrite `G[P, X; 1]` as the expected positive visit count, replace it pathwise
  -- by the finite-entrance count, then expand as an indicator series and integrate termwise.
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

end ProbabilityTheory
