/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory unitInterval

noncomputable section

universe u

namespace ProbabilityTheory

section FiniteStateSimulation

variable {k : ℕ}

/-- The cumulative row sums of the `i`th row of the stochastic matrix `p`. -/
def stochasticMatrixSimulationCumulative
    (p : Fin k → Fin k → ℝ≥0∞) (i : Fin k) :
    Fin (k + 1) → ℝ :=
  Fin.partialSum fun j ↦ (p i j).toReal

/-- For Example 17.19, for a finite stochastic matrix, the interval used to simulate the transition
from the state `i` to the state `j` is the half-open interval between the successive partial sums of
the `i`th row. Here `stochasticMatrixSimulationCumulative p i` is the textbook cumulative
function `r(i, ·)`, and the textbook states `{1, ..., k}` are encoded in Lean as `Fin k`. -/
def stochasticMatrixSimulationInterval
    (p : Fin k → Fin k → ℝ≥0∞) (i j : Fin k) : Set ℝ :=
  Set.Ico (stochasticMatrixSimulationCumulative p i j.castSucc)
    (stochasticMatrixSimulationCumulative p i j.succ)

-- Proof sketch: unfold `stochasticMatrixSimulationInterval`; membership in `Set.Ico` is exactly
-- the pair of inequalities cutting out the half-open interval between the two successive partial
-- sums.
/-- A real number lies in the simulation interval for `j` in row `i` exactly when it lies between
the two successive cumulative row sums. -/
theorem mem_stochasticMatrixSimulationInterval_iff
    (p : Fin k → Fin k → ℝ≥0∞) (i j : Fin k) {u : ℝ} :
    u ∈ stochasticMatrixSimulationInterval p i j ↔
      stochasticMatrixSimulationCumulative p i j.castSucc ≤ u ∧
        u < stochasticMatrixSimulationCumulative p i j.succ := by
  simp [stochasticMatrixSimulationInterval]

-- Proof sketch: apply `Fin.partialSum_succ`; the difference of two consecutive partial sums is the
-- corresponding summand, hence the matrix entry `p i j`.
/-- The width of the simulation interval for `j` in row `i` is exactly the transition probability
`p i j`. -/
theorem stochasticMatrixSimulationInterval_width
    (p : Fin k → Fin k → ℝ≥0∞) (i j : Fin k) :
    stochasticMatrixSimulationCumulative p i j.succ -
      stochasticMatrixSimulationCumulative p i j.castSucc = (p i j).toReal := by
  rw [sub_eq_iff_eq_add]
  simpa [stochasticMatrixSimulationCumulative, add_comm] using
    Fin.partialSum_succ (fun m ↦ (p i m).toReal) j

/-- The deterministic next-state map obtained by locating a driver value `u ∈ [0,1]` in the row
partition induced by the cumulative transition probabilities of the `i`th row of `p`. For `u < 1`,
the textbook half-open interval criterion is recovered by `stochasticMatrixSimulationState_eq_iff`;
at the boundary point `u = 1`, this definition returns the final state. -/
def stochasticMatrixSimulationState
    (p : Fin k → Fin k → ℝ≥0∞) (i : Fin k) (u : I) : Fin k :=
  let lower : Fin k → ℝ := fun j ↦ stochasticMatrixSimulationCumulative p i j.castSucc
  let j := Nat.findGreatest (fun n ↦ ∃ h : n < k, lower ⟨n, h⟩ ≤ (u : ℝ)) (k - 1)
  ⟨j, by
    have hj : j ≤ k - 1 := Nat.findGreatest_le (k - 1)
    have hk : 0 < k := lt_of_lt_of_le (Nat.zero_lt_succ i.1) (Nat.succ_le_of_lt i.2)
    exact lt_of_le_of_lt hj (Nat.sub_lt hk (by decide))⟩

/-- Helper for Example 17.19: the initial cumulative row sum is `0`. -/
theorem stochasticMatrixSimulationCumulative_zero
    (p : Fin k → Fin k → ℝ≥0∞) (i : Fin k) :
    stochasticMatrixSimulationCumulative p i 0 = 0 := by
  -- Proof comment: this is the zero case of `Fin.partialSum`.
  simp [stochasticMatrixSimulationCumulative]

/-- Helper for Example 17.19: the cumulative row sums form a monotone family. -/
theorem stochasticMatrixSimulationCumulative_mono
    (p : Fin k → Fin k → ℝ≥0∞) (i : Fin k) :
    Monotone (stochasticMatrixSimulationCumulative p i) := by
  -- Proof comment: it is enough to compare consecutive cutoffs, and `Fin.partialSum_succ`
  -- increases by the nonnegative summand `(p i j).toReal`.
  rw [Fin.monotone_iff_le_succ]
  intro j
  have hnonneg : 0 ≤ (p i j).toReal := ENNReal.toReal_nonneg
  calc
    stochasticMatrixSimulationCumulative p i j.castSucc
        ≤ stochasticMatrixSimulationCumulative p i j.castSucc + (p i j).toReal := by
          linarith
    _ = stochasticMatrixSimulationCumulative p i j.succ := by
          symm
          simpa [stochasticMatrixSimulationCumulative, add_comm] using
            Fin.partialSum_succ (fun m ↦ (p i m).toReal) j

/-- Helper for Example 17.19: every entry of a stochastic matrix row is finite. -/
theorem stochasticMatrixEntry_ne_top
    (p : Fin k → Fin k → ℝ≥0∞) (hp : IsStochasticMatrix p) (i j : Fin k) :
    p i j ≠ ∞ := by
  -- Proof comment: each entry is bounded above by the full row sum, and that row sum is `1`.
  have hrow : ∑ x : Fin k, p i x = (1 : ℝ≥0∞) := by
    simpa using hp i
  have hle : p i j ≤ ∑ x : Fin k, p i x := by
    exact Finset.single_le_sum (fun _ _ ↦ bot_le) (by simp)
  refine ne_of_lt ?_
  calc
    p i j ≤ ∑ x : Fin k, p i x := hle
    _ = 1 := hrow
    _ < ∞ := by simp

/-- Helper for Example 17.19: the terminal cumulative row sum is the full finite row sum in
real coordinates. -/
theorem stochasticMatrixSimulationCumulative_last_eq_rowSumReal
    (p : Fin k → Fin k → ℝ≥0∞) (i : Fin k) :
    stochasticMatrixSimulationCumulative p i (Fin.last k) =
      ∑ x : Fin k, (p i x).toReal := by
  -- Proof comment: the last cutoff of `Fin.partialSum` takes all entries of `List.ofFn`.
  rw [stochasticMatrixSimulationCumulative, Fin.partialSum]
  have htake :
      (List.ofFn fun j : Fin k ↦ (p i j).toReal).take k =
        List.ofFn (fun j : Fin k ↦ (p i j).toReal) :=
    (List.take_eq_self_iff _).2 (by simp)
  simpa [List.sum_ofFn] using congrArg List.sum htake

/-- Helper for Example 17.19: the terminal cumulative row sum of a stochastic matrix row is `1`. -/
theorem stochasticMatrixSimulationCumulative_last_eq_one
    (p : Fin k → Fin k → ℝ≥0∞) (hp : IsStochasticMatrix p) (i : Fin k) :
    stochasticMatrixSimulationCumulative p i (Fin.last k) = 1 := by
  -- Proof comment: identify the terminal partial sum with the full finite row sum and use the
  -- stochastic-row identity.
  have hrow : ∑ x : Fin k, p i x = (1 : ℝ≥0∞) := by
    simpa using hp i
  calc
    stochasticMatrixSimulationCumulative p i (Fin.last k)
        = ∑ x : Fin k, (p i x).toReal :=
          stochasticMatrixSimulationCumulative_last_eq_rowSumReal p i
    _ = (∑ x : Fin k, p i x).toReal := by
          rw [ENNReal.toReal_sum]
          intro x _
          exact stochasticMatrixEntry_ne_top p hp i x
    _ = 1 := by simp [hrow]

/-- Helper for Example 17.19: membership in `Set.Ico` inside the unit interval is the expected
pair of real inequalities. -/
theorem mem_Ico_subtype_iff (a b u : I) :
    u ∈ Set.Ico a b ↔ ((a : ℝ) ≤ (u : ℝ) ∧ (u : ℝ) < (b : ℝ)) :=
  Iff.rfl

/-- Helper for Example 17.19: every cumulative row sum lies in the unit interval. -/
theorem stochasticMatrixSimulationCumulative_memUnitInterval
    (p : Fin k → Fin k → ℝ≥0∞) (hp : IsStochasticMatrix p) (i : Fin k) (m : Fin (k + 1)) :
    0 ≤ stochasticMatrixSimulationCumulative p i m ∧
      stochasticMatrixSimulationCumulative p i m ≤ 1 := by
  -- Proof comment: the cumulative sums start at `0`, are monotone, and terminate at `1`.
  have hmono := stochasticMatrixSimulationCumulative_mono p i
  constructor
  · have h0m : (0 : Fin (k + 1)) ≤ m := by
      exact Nat.zero_le _
    calc
      0 = stochasticMatrixSimulationCumulative p i 0 := by
            rw [stochasticMatrixSimulationCumulative_zero]
      _ ≤ stochasticMatrixSimulationCumulative p i m := hmono h0m
  · calc
      stochasticMatrixSimulationCumulative p i m ≤
          stochasticMatrixSimulationCumulative p i (Fin.last k) := hmono (Fin.le_last _)
      _ = 1 := stochasticMatrixSimulationCumulative_last_eq_one p hp i

/-- Helper for Example 17.19: the boundary point `1` is sent to the final state. -/
theorem stochasticMatrixSimulationState_succ_eq_last_of_eq_one
    (p : Fin k → Fin k → ℝ≥0∞) (hp : IsStochasticMatrix p) (i : Fin k) :
    (stochasticMatrixSimulationState p i (1 : I)).succ = Fin.last k := by
  -- Proof comment: at `u = 1`, every lower endpoint is admissible, so `Nat.findGreatest`
  -- selects the maximal index `k - 1`.
  let lower : Fin k → ℝ := fun j ↦ stochasticMatrixSimulationCumulative p i j.castSucc
  let P : ℕ → Prop := fun n ↦ ∃ h : n < k, lower ⟨n, h⟩ ≤ (1 : ℝ)
  have hkpos : 0 < k := Nat.zero_lt_of_lt i.2
  let lastState : Fin k := ⟨k - 1, Nat.sub_lt hkpos (by decide)⟩
  have hP_last : P (k - 1) := by
    refine ⟨lastState.2, ?_⟩
    simpa [lower, lastState] using
      (stochasticMatrixSimulationCumulative_memUnitInterval p hp i lastState.castSucc).2
  have hfind : Nat.findGreatest P (k - 1) = k - 1 := Nat.findGreatest_eq hP_last
  have hstate : stochasticMatrixSimulationState p i (1 : I) = lastState := by
    -- Proof comment: once the chosen natural index is identified, equality of `Fin` values is
    -- immediate.
    apply Fin.ext
    simpa [stochasticMatrixSimulationState, lower, P, lastState, hfind]
  calc
    (stochasticMatrixSimulationState p i (1 : I)).succ = lastState.succ := congrArg Fin.succ hstate
    _ = Fin.last k := by
          apply Fin.ext
          simp [lastState, Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)]

-- Proof sketch: for `u : I` with `(u : ℝ) < 1`, the stochastic-row equation turns the cumulative
-- values into a genuine partition of the unit interval by the half-open intervals
-- `stochasticMatrixSimulationInterval p i j`; `Nat.findGreatest` selects exactly the label of
-- the interval containing `u`.
/-- For a driver value `u ∈ [0,1]` with `u < 1`, the simulation state is exactly the label of the
half-open interval containing `u`. -/
theorem stochasticMatrixSimulationState_eq_iff
    (p : Fin k → Fin k → ℝ≥0∞) (hp : IsStochasticMatrix p)
    (i j : Fin k) (u : I) (hu : (u : ℝ) < 1) :
    stochasticMatrixSimulationState p i u = j ↔
      (u : ℝ) ∈ stochasticMatrixSimulationInterval p i j := by
  let lower : Fin k → ℝ := fun l ↦ stochasticMatrixSimulationCumulative p i l.castSucc
  let P : ℕ → Prop := fun n ↦ ∃ h : n < k, lower ⟨n, h⟩ ≤ (u : ℝ)
  have hkpos : 0 < k := Nat.zero_lt_of_lt i.2
  have hmono := stochasticMatrixSimulationCumulative_mono p i
  have hPzero : P 0 := by
    -- Proof comment: the first lower endpoint is `0`, and every `u ∈ I` lies above it.
    refine ⟨hkpos, ?_⟩
    simpa [lower, stochasticMatrixSimulationCumulative_zero] using u.2.1
  constructor
  · intro hstate
    -- Proof comment: the chosen index satisfies the lower bound by the defining property of
    -- `Nat.findGreatest`; then the failure of the next index gives the strict upper bound.
    have hfind_eq : Nat.findGreatest P (k - 1) = j := by
      simpa [stochasticMatrixSimulationState, lower, P] using congrArg Fin.val hstate
    have hPfind : P (Nat.findGreatest P (k - 1)) := by
      exact Nat.findGreatest_spec (P := P) (m := 0) (Nat.zero_le _) hPzero
    have hPj : P j := by
      simpa [hfind_eq] using hPfind
    rcases hPj with ⟨_, hj_lower⟩
    have hu_upper : (u : ℝ) < stochasticMatrixSimulationCumulative p i j.succ := by
      by_contra hu_upper
      have hnot_lt :
          stochasticMatrixSimulationCumulative p i j.succ ≤ (u : ℝ) := not_lt.mp hu_upper
      by_cases hlast : j.succ = Fin.last k
      · have htop : stochasticMatrixSimulationCumulative p i j.succ = 1 := by
          simpa [hlast] using stochasticMatrixSimulationCumulative_last_eq_one p hp i
        have hOne_le_u : (1 : ℝ) ≤ (u : ℝ) := by
          simpa [htop] using hnot_lt
        exact (not_le_of_gt hu) hOne_le_u
      · have hnext_lt : (j : ℕ) + 1 < k := by
          exact Fin.lt_def.mp ((Fin.lt_last_iff_ne_last).2 hlast)
        have hPnext : P (j + 1) := by
          refine ⟨hnext_lt, ?_⟩
          simpa [lower] using hnot_lt
        have hnotPnext : ¬ P (j + 1) := by
          refine Nat.findGreatest_is_greatest (P := P) ?_ (Nat.le_pred_of_lt hnext_lt)
          simp [hfind_eq]
        exact hnotPnext hPnext
    exact (mem_stochasticMatrixSimulationInterval_iff p i j).2 ⟨hj_lower, hu_upper⟩
  · intro hu_mem
    -- Proof comment: verify the characterization of `Nat.findGreatest` directly: `j` satisfies
    -- the lower inequality, and any larger index would force the upper inequality to fail.
    have hfind_eq : Nat.findGreatest P (k - 1) = j := by
      apply (Nat.findGreatest_eq_iff (P := P)).2
      refine ⟨Nat.le_pred_of_lt j.2, ?_, ?_⟩
      · intro _
        exact ⟨j.2, (mem_stochasticMatrixSimulationInterval_iff p i j).1 hu_mem |>.1⟩
      · intro n hjn _ hPn
        rcases hPn with ⟨hnk, hn_lower⟩
        have hsucc_le : j.succ ≤ (⟨n, hnk⟩ : Fin k).castSucc := by
          exact Fin.le_iff_val_le_val.mpr (Nat.succ_le_of_lt hjn)
        have hle :=
          hmono hsucc_le
        exact (not_lt_of_ge (le_trans hle hn_lower))
          ((mem_stochasticMatrixSimulationInterval_iff p i j).1 hu_mem).2
    apply Fin.ext
    simpa [stochasticMatrixSimulationState, lower, P] using hfind_eq

/-- Helper for Example 17.19: under the uniform measure on `I`, the fiber of the simulated state
`j` has mass `p i j`. -/
theorem volume_preimage_stochasticMatrixSimulationState
    (p : Fin k → Fin k → ℝ≥0∞) (hp : IsStochasticMatrix p) (i j : Fin k) :
    volume {u : I | stochasticMatrixSimulationState p i u = j} = p i j := by
  -- Proof comment: split according to whether `j` is the final state, and compute the relevant
  -- subtype interval volume in each branch.
  let a : I :=
    ⟨stochasticMatrixSimulationCumulative p i j.castSucc,
      (stochasticMatrixSimulationCumulative_memUnitInterval p hp i j.castSucc).1,
      (stochasticMatrixSimulationCumulative_memUnitInterval p hp i j.castSucc).2⟩
  let b : I :=
    ⟨stochasticMatrixSimulationCumulative p i j.succ,
      (stochasticMatrixSimulationCumulative_memUnitInterval p hp i j.succ).1,
      (stochasticMatrixSimulationCumulative_memUnitInterval p hp i j.succ).2⟩
  have hpij_ne_top := stochasticMatrixEntry_ne_top p hp i j
  by_cases hlast : j.succ = Fin.last k
  · have htop : stochasticMatrixSimulationCumulative p i j.succ = 1 := by
      simpa [hlast] using stochasticMatrixSimulationCumulative_last_eq_one p hp i
    have hfiber : {u : I | stochasticMatrixSimulationState p i u = j} = Set.Ici a := by
      ext u
      constructor
      · intro huj
        by_cases hu_lt : (u : ℝ) < 1
        · have hu_interval := (stochasticMatrixSimulationState_eq_iff p hp i j u hu_lt).1 huj
          simpa [a] using hu_interval.1
        · have hu_eq : u = (1 : I) := by
            apply Subtype.ext
            exact le_antisymm u.2.2 (not_lt.mp hu_lt)
          simpa [a, hu_eq] using
            (stochasticMatrixSimulationCumulative_memUnitInterval p hp i j.castSucc).2
      · intro hau
        by_cases hu_lt : (u : ℝ) < 1
        · apply (stochasticMatrixSimulationState_eq_iff p hp i j u hu_lt).2
          exact (mem_stochasticMatrixSimulationInterval_iff p i j).2 ⟨by simpa [a] using hau, by
            simpa [htop]⟩
        · have hu_eq : u = (1 : I) := by
            apply Subtype.ext
            exact le_antisymm u.2.2 (not_lt.mp hu_lt)
          rw [hu_eq]
          have hsucc :
              (stochasticMatrixSimulationState p i (1 : I)).succ = j.succ := by
            calc
              (stochasticMatrixSimulationState p i (1 : I)).succ = Fin.last k :=
                stochasticMatrixSimulationState_succ_eq_last_of_eq_one p hp i
              _ = j.succ := hlast.symm
          apply Fin.ext
          exact Nat.succ.inj (congrArg Fin.val hsucc)
    rw [hfiber, unitInterval.volume_Ici]
    calc
      ENNReal.ofReal (1 - (a : ℝ))
          = ENNReal.ofReal
              (stochasticMatrixSimulationCumulative p i j.succ -
                stochasticMatrixSimulationCumulative p i j.castSucc) := by
              simp [a, htop]
      _ = ENNReal.ofReal ((p i j).toReal) := by
            rw [stochasticMatrixSimulationInterval_width]
      _ = p i j := by
            rw [ENNReal.ofReal_toReal hpij_ne_top]
  · have hpreimage :
        {u : I | (u : ℝ) ∈ stochasticMatrixSimulationInterval p i j} = Set.Ico a b := by
      ext u
      -- Proof comment: rewrite both sides to the same real-inequality normal form.
      rw [Set.mem_setOf_eq, mem_stochasticMatrixSimulationInterval_iff, mem_Ico_subtype_iff]
    have hfiber :
        {u : I | stochasticMatrixSimulationState p i u = j} =
          {u : I | (u : ℝ) ∈ stochasticMatrixSimulationInterval p i j} := by
      ext u
      constructor
      · intro huj
        by_cases hu_eq : u = (1 : I)
        · have hsucc_eq : j.succ = Fin.last k := by
            rw [hu_eq] at huj
            have hcongr := congrArg Fin.succ huj
            exact hcongr.symm.trans (stochasticMatrixSimulationState_succ_eq_last_of_eq_one p hp i)
          exact (hlast hsucc_eq).elim
        · have hu_lt : (u : ℝ) < 1 := by
            exact lt_of_le_of_ne u.2.2 fun hu_val ↦ hu_eq (Subtype.ext hu_val)
          exact (stochasticMatrixSimulationState_eq_iff p hp i j u hu_lt).1 huj
      · intro hu_interval
        have hu_lt : (u : ℝ) < 1 := by
          exact lt_of_lt_of_le
            ((mem_stochasticMatrixSimulationInterval_iff p i j).1 hu_interval).2
            (stochasticMatrixSimulationCumulative_memUnitInterval p hp i j.succ).2
        exact (stochasticMatrixSimulationState_eq_iff p hp i j u hu_lt).2 hu_interval
    rw [hfiber, hpreimage, unitInterval.volume_Ico, stochasticMatrixSimulationInterval_width,
      ENNReal.ofReal_toReal hpij_ne_top]

/-- Helper for Example 17.19: each singleton fiber of the unit-interval simulation state map is
measurable. -/
theorem measurableSet_preimage_stochasticMatrixSimulationState
    (p : Fin k → Fin k → ℝ≥0∞) (hp : IsStochasticMatrix p) (i j : Fin k) :
    MeasurableSet {u : I | stochasticMatrixSimulationState p i u = j} := by
  let a : I :=
    ⟨stochasticMatrixSimulationCumulative p i j.castSucc,
      (stochasticMatrixSimulationCumulative_memUnitInterval p hp i j.castSucc).1,
      (stochasticMatrixSimulationCumulative_memUnitInterval p hp i j.castSucc).2⟩
  let b : I :=
    ⟨stochasticMatrixSimulationCumulative p i j.succ,
      (stochasticMatrixSimulationCumulative_memUnitInterval p hp i j.succ).1,
      (stochasticMatrixSimulationCumulative_memUnitInterval p hp i j.succ).2⟩
  by_cases hlast : j.succ = Fin.last k
  · have hfiber : {u : I | stochasticMatrixSimulationState p i u = j} = Set.Ici a := by
      ext u
      constructor
      · intro huj
        by_cases hu_lt : (u : ℝ) < 1
        · have hu_interval := (stochasticMatrixSimulationState_eq_iff p hp i j u hu_lt).1 huj
          simpa [a] using hu_interval.1
        · have hu_eq : u = (1 : I) := by
            apply Subtype.ext
            exact le_antisymm u.2.2 (not_lt.mp hu_lt)
          simpa [a, hu_eq] using
            (stochasticMatrixSimulationCumulative_memUnitInterval p hp i j.castSucc).2
      · intro hau
        by_cases hu_lt : (u : ℝ) < 1
        · apply (stochasticMatrixSimulationState_eq_iff p hp i j u hu_lt).2
          have htop : stochasticMatrixSimulationCumulative p i j.succ = 1 := by
            simpa [hlast] using stochasticMatrixSimulationCumulative_last_eq_one p hp i
          exact (mem_stochasticMatrixSimulationInterval_iff p i j).2
            ⟨by simpa [a] using hau, by
              simpa [htop] using hu_lt⟩
        · have hu_eq : u = (1 : I) := by
            apply Subtype.ext
            exact le_antisymm u.2.2 (not_lt.mp hu_lt)
          rw [hu_eq]
          have hsucc :
              (stochasticMatrixSimulationState p i (1 : I)).succ = j.succ := by
            calc
              (stochasticMatrixSimulationState p i (1 : I)).succ = Fin.last k :=
                stochasticMatrixSimulationState_succ_eq_last_of_eq_one p hp i
              _ = j.succ := hlast.symm
          apply Fin.ext
          exact Nat.succ.inj (congrArg Fin.val hsucc)
    rw [hfiber]
    exact measurableSet_Ici
  · have hpreimage :
        {u : I | (u : ℝ) ∈ stochasticMatrixSimulationInterval p i j} = Set.Ico a b := by
      ext u
      -- Proof comment: rewrite both sides to the same real-inequality normal form.
      rw [Set.mem_setOf_eq, mem_stochasticMatrixSimulationInterval_iff, mem_Ico_subtype_iff]
    have hfiber :
        {u : I | stochasticMatrixSimulationState p i u = j} =
          {u : I | (u : ℝ) ∈ stochasticMatrixSimulationInterval p i j} := by
      ext u
      constructor
      · intro huj
        by_cases hu_eq : u = (1 : I)
        · have hsucc_eq : j.succ = Fin.last k := by
            rw [hu_eq] at huj
            have hcongr := congrArg Fin.succ huj
            exact hcongr.symm.trans (stochasticMatrixSimulationState_succ_eq_last_of_eq_one p hp i)
          exact (hlast hsucc_eq).elim
        · have hu_lt : (u : ℝ) < 1 := by
            exact lt_of_le_of_ne u.2.2 fun hu_val ↦ hu_eq (Subtype.ext hu_val)
          exact (stochasticMatrixSimulationState_eq_iff p hp i j u hu_lt).1 huj
      · intro hu_interval
        have hu_lt : (u : ℝ) < 1 := by
          exact lt_of_lt_of_le
            ((mem_stochasticMatrixSimulationInterval_iff p i j).1 hu_interval).2
            (stochasticMatrixSimulationCumulative_memUnitInterval p hp i j.succ).2
        exact (stochasticMatrixSimulationState_eq_iff p hp i j u hu_lt).2 hu_interval
    rw [hfiber, hpreimage]
    exact measurableSet_Ico

section RandomMapping

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Example 17.19: evaluating the discrete matrix kernel row on a singleton recovers
the corresponding matrix entry. -/
@[simp] theorem discreteMatrixKernel_apply_singleton_local
    (p : Fin k → Fin k → ℝ≥0∞) (i j : Fin k) :
    discreteMatrixKernel p i ({j} : Set (Fin k)) = p i j := by
  -- Proof comment: expand the row measure into weighted Dirac masses and evaluate at `{j}`.
  rw [discreteMatrixKernel_apply]
  simpa using
    (Measure.sum_smul_dirac_singleton (f := fun x : Fin k ↦ p i x) (a := j))

/-- Helper for Example 17.19: under the uniform measure on `I`, the deterministic simulator from
state `i` has law `discreteMatrixKernel p i`. -/
theorem hasLaw_stochasticMatrixSimulationState
    (p : Fin k → Fin k → ℝ≥0∞) (hp : IsStochasticMatrix p) (i : Fin k) :
    HasLaw (stochasticMatrixSimulationState p i) (discreteMatrixKernel p i)
      (volume : Measure I) := by
  -- Proof comment: both measures are determined by singleton masses on the finite state space.
  have hmeas : Measurable (stochasticMatrixSimulationState p i) :=
    measurable_to_countable' fun j ↦
      measurableSet_preimage_stochasticMatrixSimulationState p hp i j
  refine ⟨hmeas.aemeasurable, ?_⟩
  refine Measure.ext_of_singleton ?_
  intro j
  have hpreimage :
      stochasticMatrixSimulationState p i ⁻¹' ({j} : Set (Fin k)) =
        {u : I | stochasticMatrixSimulationState p i u = j} := by
    ext u
    simp
  rw [Measure.map_apply_of_aemeasurable hmeas.aemeasurable (measurableSet_singleton j)]
  rw [hpreimage]
  rw [volume_preimage_stochasticMatrixSimulationState p hp i j]
  rw [discreteMatrixKernel_apply_singleton_local]

/-- The source-facing simulated step map `Rₙ(ω, i)` attached to the finite stochastic matrix `p`
and the unit-interval-valued drivers `Uₙ`. Its currying is chosen so that the owner construction
`stochasticMatrixTrajectory` can be applied directly to
`fun n ↦ stochasticMatrixSimulationStep p U n`. This is the intrinsic textbook interval
simulation map. -/
def stochasticMatrixSimulationStep
    (p : Fin k → Fin k → ℝ≥0∞) (U : ℕ → Ω → I) (n : ℕ) : Ω → Fin k → Fin k :=
  fun ω i ↦ stochasticMatrixSimulationState p i (U n ω)

-- Proof sketch: for a uniform driver `U n : Ω → I`, the fiber of the simulated state `j` is,
-- away from the endpoint `1`, exactly the interval `stochasticMatrixSimulationInterval p i j`,
-- whose Lebesgue length is `(p i j).toReal`; the endpoint is sent to the final state by
-- `stochasticMatrixSimulationState`. This identifies the pushforward law with the `i`th row of
-- the canonical discrete kernel `discreteMatrixKernel p`.
/-- If the driving variable `U n` is uniform on `[0,1]`, then the simulated next state from `i`
has law given by the `i`th row of the canonical discrete kernel of `p`. -/
theorem hasLaw_stochasticMatrixSimulationStep
    (P : Measure Ω)
    (p : Fin k → Fin k → ℝ≥0∞) (hp : IsStochasticMatrix p) (U : ℕ → Ω → I)
    (n : ℕ) (hU : HasLaw (U n) (volume : Measure I) P) (i : Fin k) :
    HasLaw (fun ω ↦ stochasticMatrixSimulationStep p U n ω i) (discreteMatrixKernel p i) P := by
  -- Proof comment: compose the uniform law of `U n` with the deterministic simulator on the unit
  -- interval.
  have hState :
      HasLaw (stochasticMatrixSimulationState p i) (discreteMatrixKernel p i)
        (volume : Measure I) :=
    hasLaw_stochasticMatrixSimulationState p hp i
  simpa [stochasticMatrixSimulationStep, Function.comp] using hState.comp hU

-- Proof sketch: evaluate the measure identity from `hasLaw_stochasticMatrixSimulationStep` on the
-- singleton `{j}` and rewrite with the explicit row of `discreteMatrixKernel p`.
/-- Example 17.19: if `U n` is uniform on `[0,1]`, then the simulated next state satisfies the
textbook probability identity `P[R_n(i) = j] = p(i,j)`. -/
theorem measure_stochasticMatrixSimulationStep_eq_transitionProb
    (P : Measure Ω)
    (p : Fin k → Fin k → ℝ≥0∞) (hp : IsStochasticMatrix p) (U : ℕ → Ω → I)
    (n : ℕ) (hU : HasLaw (U n) (volume : Measure I) P) (i j : Fin k) :
    P.real {ω | stochasticMatrixSimulationStep p U n ω i = j} = (p i j).toReal := by
  -- Proof comment: evaluate the pushforward identity on the singleton `{j}` and take `toReal`.
  have hLaw := hasLaw_stochasticMatrixSimulationStep P p hp U n hU i
  have hpreimage :
      {ω | stochasticMatrixSimulationStep p U n ω i = j} =
        (fun ω ↦ stochasticMatrixSimulationStep p U n ω i) ⁻¹' ({j} : Set (Fin k)) := by
    ext ω
    simp
  have hsingleton :
      P {ω | stochasticMatrixSimulationStep p U n ω i = j} = p i j := by
    calc
      P {ω | stochasticMatrixSimulationStep p U n ω i = j}
          = (Measure.map (fun ω ↦ stochasticMatrixSimulationStep p U n ω i) P) {j} := by
              rw [hpreimage]
              symm
              rw [Measure.map_apply_of_aemeasurable hLaw.aemeasurable (measurableSet_singleton j)]
      _ = (discreteMatrixKernel p i) {j} := by
            simpa using congrArg (fun μ : Measure (Fin k) ↦ μ {j}) hLaw.map_eq
      _ = p i j := by rw [discreteMatrixKernel_apply_singleton_local]
  simpa [Measure.real_def] using congrArg ENNReal.toReal hsingleton

end RandomMapping
end FiniteStateSimulation

end ProbabilityTheory
