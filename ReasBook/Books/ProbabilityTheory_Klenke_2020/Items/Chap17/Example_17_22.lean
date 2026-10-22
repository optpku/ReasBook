/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Definition_10_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.MarkovProcessRealization
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable (N : ℕ+)

/-- The type-`A` gene frequency corresponding to the Moran count state `i ∈ {0, ..., N}`. -/
def moranFrequency (i : Fin (N + 1)) : ℝ :=
  (i : ℝ) / N

/-- The one-step move probability `x (1 - x)` of the Moran model, written in terms of the
current frequency `x = i / N`. -/
def moranMoveProb : Fin (N + 1) → ℝ≥0∞ :=
  fun i ↦ ENNReal.ofReal <| moranFrequency N i * (1 - moranFrequency N i)

/-- The probability of staying at the same count in the discrete Moran model. -/
def moranStayProb : Fin (N + 1) → ℝ≥0∞ :=
  fun i ↦ ENNReal.ofReal <| (moranFrequency N i) ^ (2 : ℕ) + (1 - moranFrequency N i) ^ (2 : ℕ)

/-- The discrete Moran model from Example 17.22 has state space
`Fin (N + 1)`, representing the frequencies `{0, 1 / N, ..., 1}`, and one-step transition matrix
given by moving from `i` to `i ± 1` with probability `x (1 - x)` and staying put with
probability `x^2 + (1 - x)^2`, where `x = i / N`. -/
def moranTransitionMatrix : Fin (N + 1) → Fin (N + 1) → ℝ≥0∞
  | i, j =>
      if (j : ℕ) = (i : ℕ) + 1 then moranMoveProb N i
      else if j = i then moranStayProb N i
      else if (i : ℕ) = (j : ℕ) + 1 then moranMoveProb N i
      else 0

/-- Helper for Example 17.22: the Moran frequency at state `0` is `0`. -/
private theorem moranFrequency_zero :
    moranFrequency N 0 = 0 := by
  -- The zero count state has zero frequency by definition.
  simp [moranFrequency]

/-- Helper for Example 17.22: the Moran frequency at the maximal state is `1`. -/
private theorem moranFrequency_last :
    moranFrequency N (Fin.last N) = 1 := by
  -- The maximal count state has count `N`, so dividing by `N` gives frequency `1`.
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast N.ne_zero
  simp [moranFrequency, hN]

/-- Helper for Example 17.22: every Moran frequency is nonnegative. -/
private theorem moranFrequency_nonneg (i : Fin (N + 1)) :
    0 ≤ moranFrequency N i := by
  -- The count `i` and the population size `N` are both nonnegative.
  have hN : (0 : ℝ) < N := by
    exact_mod_cast N.pos
  exact div_nonneg (by positivity) hN.le

/-- Helper for Example 17.22: every Moran frequency is at most `1`. -/
private theorem moranFrequency_le_one (i : Fin (N + 1)) :
    moranFrequency N i ≤ 1 := by
  -- The count coordinate satisfies `i ≤ N`, and division by the positive size `N` preserves
  -- that bound.
  have hN : (0 : ℝ) < N := by
    exact_mod_cast N.pos
  have hi : (i : ℝ) ≤ N := by
    exact_mod_cast (Nat.lt_succ_iff.mp i.2)
  have hdiv : (i : ℝ) / N ≤ N / N := by
    exact div_le_div_of_nonneg_right hi hN.le
  simpa [moranFrequency, hN.ne'] using hdiv

/-- Helper for Example 17.22: the Moran move probability vanishes at state `0`. -/
private theorem moranMoveProb_zero :
    moranMoveProb N 0 = 0 := by
  -- At frequency `0`, the factor `x` in `x (1 - x)` vanishes.
  simp [moranMoveProb, moranFrequency_zero]

/-- Helper for Example 17.22: the Moran move probability vanishes at the maximal state. -/
private theorem moranMoveProb_last :
    moranMoveProb N (Fin.last N) = 0 := by
  -- At frequency `1`, the factor `(1 - x)` in `x (1 - x)` vanishes.
  simp [moranMoveProb, moranFrequency_last]

/-- Helper for Example 17.22: each Moran row entry splits into the mutually exclusive successor,
self, and predecessor contributions. -/
private theorem moranTransitionMatrix_apply_nat
    (i : Fin (N + 1)) {k : ℕ} (hk : k < N + 1) :
    moranTransitionMatrix N i ⟨k, hk⟩ =
      (if k = (i : ℕ) + 1 then moranMoveProb N i else 0) +
        (if k = (i : ℕ) then moranStayProb N i else 0) +
          (if (i : ℕ) = k + 1 then moranMoveProb N i else 0) := by
  -- Split into the three mutually exclusive one-step destinations.
  by_cases hsucc : k = (i : ℕ) + 1
  · have hstay : k ≠ (i : ℕ) := by omega
    have himpossible : (i : ℕ) ≠ (i : ℕ) + 1 + 1 := by omega
    simp [moranTransitionMatrix, hsucc, himpossible]
  · by_cases hstay : k = (i : ℕ)
    · have hpred : (i : ℕ) ≠ k + 1 := by omega
      simp [moranTransitionMatrix, hstay]
    · by_cases hpred : (i : ℕ) = k + 1
      · have himpossible : k ≠ k + 1 + 1 := by omega
        have hne : (⟨k, hk⟩ : Fin (N + 1)) ≠ i := by
          intro hki
          exact hstay (Fin.ext_iff.mp hki)
        simp [moranTransitionMatrix, hpred, himpossible, hne]
      · simp [moranTransitionMatrix, hsucc, hstay, hpred, Fin.ext_iff]

/-- Helper for Example 17.22: the successor contribution in a Moran row always reduces to the move
probability itself, because the missing boundary case has move mass `0`. -/
private theorem moranSuccessorMass (i : Fin (N + 1)) :
    (if _h : (i : ℕ) + 1 < N + 1 then moranMoveProb N i else 0) = moranMoveProb N i := by
  by_cases h : (i : ℕ) + 1 < N + 1
  · -- In the interior, the successor index exists and the `if` is literal.
    simp [h]
  · -- At the top boundary, `i` must be the maximal state and the move mass is zero.
    have hiVal : (i : ℕ) = N := by
      omega
    have hi : i = Fin.last N := by
      exact Fin.ext hiVal
    simp [hi, moranMoveProb_last]

/-- Helper for Example 17.22: taking `toReal` removes the `ENNReal.ofReal` wrapper on the Moran
move probability. -/
private theorem moranMoveProb_toReal (i : Fin (N + 1)) :
    (moranMoveProb N i).toReal =
      moranFrequency N i * (1 - moranFrequency N i) := by
  have hnonneg : 0 ≤ moranFrequency N i * (1 - moranFrequency N i) := by
    exact mul_nonneg (moranFrequency_nonneg (N := N) i)
      (sub_nonneg.mpr (moranFrequency_le_one (N := N) i))
  -- The Moran move probability is an `ENNReal.ofReal` of a nonnegative quantity.
  simp [moranMoveProb, ENNReal.toReal_ofReal, hnonneg]

/-- Helper for Example 17.22: taking `toReal` removes the `ENNReal.ofReal` wrapper on the Moran
stay probability. -/
private theorem moranStayProb_toReal (i : Fin (N + 1)) :
    (moranStayProb N i).toReal =
      (moranFrequency N i) ^ (2 : ℕ) + (1 - moranFrequency N i) ^ (2 : ℕ) := by
  have hnonneg :
      0 ≤ (moranFrequency N i) ^ (2 : ℕ) + (1 - moranFrequency N i) ^ (2 : ℕ) := by
    positivity
  -- The stay mass is also an `ENNReal.ofReal`, now of the textbook polynomial `x^2 + (1-x)^2`.
  simp [moranStayProb, ENNReal.toReal_ofReal, hnonneg]

/-- Helper for Example 17.22: moving to the successor state raises the Moran frequency by `1 / N`.
-/
private theorem moranFrequency_succ (i : Fin (N + 1)) (h : (i : ℕ) + 1 < N + 1) :
    moranFrequency N ⟨(i : ℕ) + 1, h⟩ = moranFrequency N i + 1 / N := by
  -- Rewrite both sides to the same rational expression in the count coordinate.
  calc
    moranFrequency N ⟨(i : ℕ) + 1, h⟩ = ((((i : ℕ) + 1 : ℕ) : ℝ) / N) := by
      rw [moranFrequency]
    _ = (((i : ℝ) + 1) / N) := by
      rw [Nat.cast_add, Nat.cast_one]
    _ = moranFrequency N i + 1 / N := by
      rw [moranFrequency]
      ring

/-- Helper for Example 17.22: moving to the predecessor state lowers the Moran frequency by
`1 / N`. -/
private theorem moranFrequency_pred (i : Fin (N + 1)) (h : (i : ℕ) ≠ 0) :
    moranFrequency N ⟨(i : ℕ) - 1, by omega⟩ = moranFrequency N i - 1 / N := by
  have hi : 1 ≤ (i : ℕ) := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
  -- Rewrite both sides to the same linear expression in the count coordinate.
  calc
    moranFrequency N ⟨(i : ℕ) - 1, by omega⟩ = ((((i : ℕ) - 1 : ℕ) : ℝ) / N) := by
      rw [moranFrequency]
    _ = (((i : ℝ) - 1) / N) := by
      rw [Nat.cast_sub hi, Nat.cast_one]
    _ = moranFrequency N i - 1 / N := by
      rw [moranFrequency]
      ring

/-- Helper for Example 17.22: the predecessor contribution in a Moran row always reduces to the
move probability itself, because the missing boundary case has move mass `0`. -/
private theorem moranPredecessorMass (i : Fin (N + 1)) :
    (if _h : (i : ℕ) = 0 then 0 else moranMoveProb N i) = moranMoveProb N i := by
  by_cases h : (i : ℕ) = 0
  · -- At the bottom boundary, the predecessor move probability vanishes.
    have hi : i = 0 := by
      apply Fin.ext
      simpa using h
    simp [hi, moranMoveProb_zero]
  · -- Away from the boundary, the predecessor mass is literally the move probability.
    simp [h]

/-- Helper for Example 17.22: the three possible one-step masses from state `i` add up to `1`. -/
private theorem moranLocalMass_sum_one (i : Fin (N + 1)) :
    moranMoveProb N i + moranStayProb N i + moranMoveProb N i = 1 := by
  have hmove_nonneg : 0 ≤ moranFrequency N i * (1 - moranFrequency N i) := by
    exact mul_nonneg (moranFrequency_nonneg (N := N) i)
      (sub_nonneg.mpr (moranFrequency_le_one (N := N) i))
  have hstay_nonneg :
      0 ≤ (moranFrequency N i) ^ (2 : ℕ) + (1 - moranFrequency N i) ^ (2 : ℕ) := by
    positivity
  have hsum_nonneg :
      0 ≤ moranFrequency N i * (1 - moranFrequency N i) +
        ((moranFrequency N i) ^ (2 : ℕ) + (1 - moranFrequency N i) ^ (2 : ℕ)) := by
    exact add_nonneg hmove_nonneg hstay_nonneg
  have hpoly :
      moranFrequency N i * (1 - moranFrequency N i) +
        ((moranFrequency N i) ^ (2 : ℕ) + (1 - moranFrequency N i) ^ (2 : ℕ)) +
        moranFrequency N i * (1 - moranFrequency N i) = 1 := by
    ring
  -- Rewrite the three masses to a single `ENNReal.ofReal` and apply the polynomial identity.
  rw [moranMoveProb, moranStayProb]
  rw [← ENNReal.ofReal_add hmove_nonneg hstay_nonneg]
  rw [← ENNReal.ofReal_add hsum_nonneg hmove_nonneg]
  simpa using congrArg ENNReal.ofReal hpoly

/-- Helper for Example 17.22: summing the successor indicator over the finite Moran state space
selects the successor move mass when the successor exists, and otherwise gives `0`. -/
private theorem moranSuccessorMassSum (i : Fin (N + 1)) :
    Finset.sum (Finset.range (N + 1))
        (fun k ↦ if k = (i : ℕ) + 1 then moranMoveProb N i else 0) =
      (if _h : (i : ℕ) + 1 < N + 1 then moranMoveProb N i else 0) := by
  by_cases h : (i : ℕ) + 1 < N + 1
  · -- Exactly the successor index contributes in the interior case.
    rw [Finset.sum_eq_single_of_mem ((i : ℕ) + 1)]
    · simp [h]
    · simp [Finset.mem_range, h]
    · intro k hk hk_ne
      simp [hk_ne]
  · -- At the top boundary there is no successor index in `range (N + 1)`.
    rw [Finset.sum_eq_zero]
    · simp [h]
    · intro k hk
      have hk_ne : k ≠ (i : ℕ) + 1 := by
        intro hk_eq
        have : (i : ℕ) + 1 < N + 1 := by
          simpa [hk_eq] using hk
        exact h this
      simp [hk_ne]

/-- Helper for Example 17.22: summing the stay indicator over the finite Moran state space
selects the stay mass at the current index. -/
private theorem moranStayMassSum (i : Fin (N + 1)) :
    Finset.sum (Finset.range (N + 1))
        (fun k ↦ if k = (i : ℕ) then moranStayProb N i else 0) =
      moranStayProb N i := by
  -- Exactly the current state contributes to the stay summand.
  rw [Finset.sum_eq_single_of_mem (i : ℕ)]
  · simp
  · simpa [Finset.mem_range] using i.2
  · intro k hk hk_ne
    simp [hk_ne]

/-- Helper for Example 17.22: summing the predecessor indicator over the finite Moran state space
selects the predecessor move mass when the predecessor exists, and otherwise gives `0`. -/
private theorem moranPredecessorMassSum (i : Fin (N + 1)) :
    Finset.sum (Finset.range (N + 1))
        (fun k ↦ if (i : ℕ) = k + 1 then moranMoveProb N i else 0) =
      (if _h : (i : ℕ) = 0 then 0 else moranMoveProb N i) := by
  by_cases h : (i : ℕ) = 0
  · -- At the bottom boundary, no predecessor index contributes.
    rw [Finset.sum_eq_zero]
    · simp [h]
    · intro k hk
      have hk_ne : (i : ℕ) ≠ k + 1 := by omega
      simp [hk_ne]
  · -- Away from `0`, the unique predecessor index `i - 1` contributes.
    have hpred_mem : (i : ℕ) - 1 < N + 1 := by omega
    have hpred_eq : (i : ℕ) = ((i : ℕ) - 1) + 1 := by omega
    rw [Finset.sum_eq_single_of_mem ((i : ℕ) - 1)]
    · rw [if_pos hpred_eq]
      simp [h]
    · simp [Finset.mem_range, hpred_mem]
    · intro k hk hk_ne
      have hk_ne' : (i : ℕ) ≠ k + 1 := by
        intro hk_eq
        apply hk_ne
        omega
      simp [hk_ne']

/-- Helper for Example 17.22: summing the successor branch over `Finset.univ` picks out the
successor move mass when the successor state exists. -/
private theorem moranSuccessorMassUniv (i : Fin (N + 1)) :
    Finset.sum Finset.univ
        (fun j : Fin (N + 1) ↦ if (j : ℕ) = (i : ℕ) + 1 then moranMoveProb N i else 0) =
      (if _h : (i : ℕ) + 1 < N + 1 then moranMoveProb N i else 0) := by
  by_cases h : (i : ℕ) + 1 < N + 1
  · let jsucc : Fin (N + 1) := ⟨(i : ℕ) + 1, h⟩
    rw [Finset.sum_eq_single_of_mem jsucc (by simp)]
    · simp [jsucc, h]
    · intro j _ hj
      have hneq : (j : ℕ) ≠ (i : ℕ) + 1 := by
        intro hji
        exact hj (Fin.ext hji)
      simp [hneq]
  · rw [Finset.sum_eq_zero]
    · simp [h]
    · intro j _
      have hneq : (j : ℕ) ≠ (i : ℕ) + 1 := by
        intro hji
        exact h (by simpa [hji] using j.2)
      simp [hneq]

/-- Helper for Example 17.22: summing the stay branch over `Finset.univ` picks out the stay
mass. -/
private theorem moranStayMassUniv (i : Fin (N + 1)) :
    Finset.sum Finset.univ
        (fun j : Fin (N + 1) ↦ if (j : ℕ) = (i : ℕ) then moranStayProb N i else 0) =
      moranStayProb N i := by
  rw [Finset.sum_eq_single_of_mem i (by simp)]
  · simp
  · intro j _ hj
    have hneq : (j : ℕ) ≠ (i : ℕ) := by
      intro hji
      exact hj (Fin.ext hji)
    simp [hneq]

/-- Helper for Example 17.22: summing the predecessor branch over `Finset.univ` picks out the
predecessor move mass when the predecessor state exists. -/
private theorem moranPredecessorMassUniv (i : Fin (N + 1)) :
    Finset.sum Finset.univ
        (fun j : Fin (N + 1) ↦ if (i : ℕ) = (j : ℕ) + 1 then moranMoveProb N i else 0) =
      (if _h : (i : ℕ) = 0 then 0 else moranMoveProb N i) := by
  by_cases h : (i : ℕ) = 0
  · rw [Finset.sum_eq_zero]
    · simp [h]
    · intro j _
      have hneq : (i : ℕ) ≠ (j : ℕ) + 1 := by omega
      simp [hneq]
  · let jpred : Fin (N + 1) := ⟨(i : ℕ) - 1, by omega⟩
    have hjpred : (i : ℕ) = (jpred : ℕ) + 1 := by
      dsimp [jpred]
      omega
    rw [Finset.sum_eq_single_of_mem jpred (by simp [jpred])]
    · rw [if_pos hjpred]
      simp [h]
    · intro j _ hj
      have hneq : (i : ℕ) ≠ (j : ℕ) + 1 := by
        intro hij
        exact hj (Fin.ext (by omega))
      simp [hneq]

-- Proof sketch: for each count state `i`, only the three states `i - 1`, `i`, and `i + 1`
-- contribute; the corresponding probabilities add up to
-- `2 * i * (N - i) / N^2 + (i^2 + (N - i)^2) / N^2 = 1`.
/-- The discrete Moran transition matrix is stochastic. -/
theorem moranTransitionMatrix_isStochasticMatrix :
    IsStochasticMatrix (moranTransitionMatrix N) := by
  intro i
  -- Rewrite one row into the three successor/stay/predecessor branches and collapse them on
  -- `Finset.univ`.
  rw [tsum_fintype]
  calc
    ∑ j : Fin (N + 1), moranTransitionMatrix N i j
      = ∑ j : Fin (N + 1),
          ((if (j : ℕ) = (i : ℕ) + 1 then moranMoveProb N i else 0) +
            ((if (j : ℕ) = (i : ℕ) then moranStayProb N i else 0) +
              (if (i : ℕ) = (j : ℕ) + 1 then moranMoveProb N i else 0))) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          simpa [add_assoc] using
            moranTransitionMatrix_apply_nat (N := N) i (k := (j : ℕ)) j.2
    _ = Finset.sum Finset.univ
          (fun j : Fin (N + 1) ↦
            if (j : ℕ) = (i : ℕ) + 1 then moranMoveProb N i else 0) +
        (Finset.sum Finset.univ
            (fun j : Fin (N + 1) ↦
              if (j : ℕ) = (i : ℕ) then moranStayProb N i else 0) +
          Finset.sum Finset.univ
            (fun j : Fin (N + 1) ↦
              if (i : ℕ) = (j : ℕ) + 1 then moranMoveProb N i else 0)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = moranMoveProb N i + moranStayProb N i + moranMoveProb N i := by
          rw [moranSuccessorMassUniv, moranStayMassUniv, moranPredecessorMassUniv,
            moranSuccessorMass, moranPredecessorMass]
          ring
    _ = 1 := moranLocalMass_sum_one (N := N) i

/-- Helper for Example 17.22: the range of the Moran frequency map is bounded. -/
private theorem moranFrequency_isBounded :
    Bornology.IsBounded (Set.range (moranFrequency N)) := by
  -- The Moran state space is finite, so the frequency image is automatically bounded.
  simpa using (Set.toFinite (Set.range (moranFrequency N))).isBounded

/-- Helper for Example 17.22: the real mass of a Moran row entry is the corresponding real-valued
successor/self/predecessor branch. -/
private theorem moranTransitionMatrix_apply_nat_toReal
    (i : Fin (N + 1)) {k : ℕ} (hk : k < N + 1) :
    (moranTransitionMatrix N i ⟨k, hk⟩).toReal =
      (if k = (i : ℕ) + 1 then (moranMoveProb N i).toReal else 0) +
        (if k = (i : ℕ) then (moranStayProb N i).toReal else 0) +
          (if (i : ℕ) = k + 1 then (moranMoveProb N i).toReal else 0) := by
  -- The real-valued row formula has the same three cases as the ENNReal-valued row formula.
  by_cases hsucc : k = (i : ℕ) + 1
  · have hstay : k ≠ (i : ℕ) := by omega
    have himpossible : (i : ℕ) ≠ (i : ℕ) + 1 + 1 := by omega
    simp [moranTransitionMatrix, hsucc, himpossible]
  · by_cases hstay : k = (i : ℕ)
    · have hpred : (i : ℕ) ≠ k + 1 := by omega
      simp [moranTransitionMatrix, hstay]
    · by_cases hpred : (i : ℕ) = k + 1
      · have himpossible : k ≠ k + 1 + 1 := by omega
        have hne : (⟨k, hk⟩ : Fin (N + 1)) ≠ i := by
          intro hki
          exact hstay (Fin.ext_iff.mp hki)
        simp [moranTransitionMatrix, hpred, himpossible, hne]
      · have hne : (⟨k, hk⟩ : Fin (N + 1)) ≠ i := by
          intro hki
          exact hstay (Fin.ext_iff.mp hki)
        simp [moranTransitionMatrix, hsucc, hstay, hpred, hne]

/-- Helper for Example 17.22: summing a successor-indicator weighted term over the Moran state
space collapses to the unique successor index when it exists. -/
private theorem moranSuccessorWeightedSum
    (i : Fin (N + 1)) (g : Fin (N + 1) → ℝ) (c : ℝ) :
    Finset.sum Finset.univ
        (fun j : Fin (N + 1) ↦
          g j * (if (j : ℕ) = (i : ℕ) + 1 then c else 0)) =
      (if h : (i : ℕ) + 1 < N + 1 then g ⟨(i : ℕ) + 1, h⟩ * c else 0) := by
  by_cases h : (i : ℕ) + 1 < N + 1
  · let jsucc : Fin (N + 1) := ⟨(i : ℕ) + 1, h⟩
    -- Only the unique successor index contributes in the interior case.
    rw [Finset.sum_eq_single_of_mem jsucc (by simp)]
    · simp [jsucc, h]
    · intro j _ hj
      have hneq : (j : ℕ) ≠ (i : ℕ) + 1 := by
        intro hji
        exact hj (Fin.ext hji)
      simp [hneq]
  · -- At the top boundary there is no successor state, so every summand vanishes.
    rw [Finset.sum_eq_zero]
    · simp [h]
    · intro j _
      have hneq : (j : ℕ) ≠ (i : ℕ) + 1 := by
        intro hji
        exact h (by simpa [hji] using j.2)
      simp [hneq]

/-- Helper for Example 17.22: summing a stay-indicator weighted term over the Moran state space
collapses to the current state. -/
private theorem moranStayWeightedSum
    (i : Fin (N + 1)) (g : Fin (N + 1) → ℝ) (c : ℝ) :
    Finset.sum Finset.univ
        (fun j : Fin (N + 1) ↦ g j * (if (j : ℕ) = (i : ℕ) then c else 0)) =
      g i * c := by
  -- Only the current state survives the stay-indicator weight.
  rw [Finset.sum_eq_single_of_mem i (by simp)]
  · simp
  · intro j _ hj
    have hneq : (j : ℕ) ≠ (i : ℕ) := by
      intro hji
      exact hj (Fin.ext hji)
    simp [hneq]

/-- Helper for Example 17.22: summing a predecessor-indicator weighted term over the Moran state
space collapses to the unique predecessor index when it exists. -/
private theorem moranPredecessorWeightedSum
    (i : Fin (N + 1)) (g : Fin (N + 1) → ℝ) (c : ℝ) :
    Finset.sum Finset.univ
        (fun j : Fin (N + 1) ↦ g j * (if (i : ℕ) = (j : ℕ) + 1 then c else 0)) =
      (if h : (i : ℕ) = 0 then 0 else g ⟨(i : ℕ) - 1, by omega⟩ * c) := by
  by_cases h : (i : ℕ) = 0
  · -- At the lower boundary there is no predecessor index, so every summand vanishes.
    rw [Finset.sum_eq_zero]
    · simp [h]
    · intro j _
      have hneq : (i : ℕ) ≠ (j : ℕ) + 1 := by omega
      simp [hneq]
  · let jpred : Fin (N + 1) := ⟨(i : ℕ) - 1, by omega⟩
    have hjpred : (i : ℕ) = (jpred : ℕ) + 1 := by
      dsimp [jpred]
      omega
    -- Away from `0`, exactly the predecessor index contributes.
    rw [Finset.sum_eq_single_of_mem jpred (by simp [jpred])]
    · rw [if_pos hjpred]
      simp [h, jpred]
    · intro j _ hj
      have hneq : (i : ℕ) ≠ (j : ℕ) + 1 := by
        intro hij
        apply hj
        exact Fin.ext (by omega)
      simp [hneq]

/-- Helper for Example 17.22: collapsing a weighted Moran row once and for all avoids repeating
the same `Finset.univ` and predecessor-transport bookkeeping in the mean and variance
computations. -/
private theorem moranWeightedRowToReal
    (i : Fin (N + 1)) (g : Fin (N + 1) → ℝ) :
    Finset.sum Finset.univ (fun j : Fin (N + 1) ↦
      g j * (moranTransitionMatrix N i j).toReal) =
      (if h : (i : ℕ) + 1 < N + 1 then
        g ⟨(i : ℕ) + 1, h⟩ * (moranMoveProb N i).toReal
      else 0) +
        (g i * (moranStayProb N i).toReal +
          (if _h : (i : ℕ) = 0 then
            0
          else
            g ⟨(i : ℕ) - 1, by omega⟩ * (moranMoveProb N i).toReal)) := by
  -- Route correction: rewrite the whole row to the stable three-point real interface once, then
  -- collapse the three weighted supports separately.
  calc
    Finset.sum Finset.univ (fun j : Fin (N + 1) ↦
      g j * (moranTransitionMatrix N i j).toReal)
      = Finset.sum Finset.univ (fun j : Fin (N + 1) ↦
          g j *
            ((if (j : ℕ) = (i : ℕ) + 1 then (moranMoveProb N i).toReal else 0) +
              ((if (j : ℕ) = (i : ℕ) then (moranStayProb N i).toReal else 0) +
                (if (i : ℕ) = (j : ℕ) + 1 then (moranMoveProb N i).toReal else 0)))) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          simpa [add_assoc] using congrArg (fun t : ℝ ↦ g j * t)
            (moranTransitionMatrix_apply_nat_toReal (N := N) i (k := (j : ℕ)) j.2)
    _ = Finset.sum Finset.univ
          (fun j : Fin (N + 1) ↦
            g j * (if (j : ℕ) = (i : ℕ) + 1 then (moranMoveProb N i).toReal else 0)) +
        (Finset.sum Finset.univ
          (fun j : Fin (N + 1) ↦
            g j * (if (j : ℕ) = (i : ℕ) then (moranStayProb N i).toReal else 0)) +
          Finset.sum Finset.univ
            (fun j : Fin (N + 1) ↦
              g j * (if (i : ℕ) = (j : ℕ) + 1 then (moranMoveProb N i).toReal else 0))) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (if h : (i : ℕ) + 1 < N + 1 then
          g ⟨(i : ℕ) + 1, h⟩ * (moranMoveProb N i).toReal
        else 0) +
        (g i * (moranStayProb N i).toReal +
          (if _h : (i : ℕ) = 0 then
            0
          else
            g ⟨(i : ℕ) - 1, by omega⟩ * (moranMoveProb N i).toReal)) := by
          rw [moranSuccessorWeightedSum, moranStayWeightedSum, moranPredecessorWeightedSum]

/-- Helper for Example 17.22: the real-valued Moran local masses still sum to `1`. -/
private theorem moranLocalMass_sum_one_toReal (i : Fin (N + 1)) :
    (moranMoveProb N i).toReal + (moranStayProb N i).toReal + (moranMoveProb N i).toReal = 1 := by
  -- Remove the `ENNReal.ofReal` wrappers and simplify the textbook polynomial identity.
  rw [moranMoveProb_toReal, moranStayProb_toReal]
  ring

/-- Helper for Example 17.22: averaging the Moran frequency over one row of the transition matrix
returns the current frequency. -/
private theorem moranFrequencyMeanStep (i : Fin (N + 1)) :
    Finset.sum Finset.univ (fun j : Fin (N + 1) ↦
      moranFrequency N j * (moranTransitionMatrix N i j).toReal) =
      moranFrequency N i := by
  by_cases hzero : (i : ℕ) = 0
  · have hi : i = 0 := Fin.ext hzero
    have hsucc : (i : ℕ) + 1 < N + 1 := by
      simp [hzero]
    -- At the absorbing state `0`, both the move mass and the frequency vanish.
    simp [moranWeightedRowToReal, hi, moranFrequency_zero, moranMoveProb_zero,
      moranStayProb_toReal]
  · by_cases hsucc : (i : ℕ) + 1 < N + 1
    · -- In the interior, the successor and predecessor shifts cancel and only the local mass sum
      -- remains.
      calc
        Finset.sum Finset.univ (fun j : Fin (N + 1) ↦
          moranFrequency N j * (moranTransitionMatrix N i j).toReal)
          = (moranFrequency N i + 1 / N) * (moranMoveProb N i).toReal +
              (moranFrequency N i * (moranStayProb N i).toReal +
                (moranFrequency N i - 1 / N) * (moranMoveProb N i).toReal) := by
              simp [moranWeightedRowToReal, hzero, hsucc, moranFrequency_succ, moranFrequency_pred]
        _ = moranFrequency N i *
              ((moranMoveProb N i).toReal + (moranStayProb N i).toReal +
                (moranMoveProb N i).toReal) := by ring
        _ = moranFrequency N i * 1 := by
              rw [moranLocalMass_sum_one_toReal]
        _ = moranFrequency N i := by ring
    · have hiVal : (i : ℕ) = N := by omega
      have hi : i = Fin.last N := Fin.ext hiVal
      -- At the absorbing state `1`, the move mass vanishes and only the stay term remains.
      simp [moranWeightedRowToReal, hi, moranFrequency_last, moranMoveProb_last,
        moranStayProb_toReal]

/-- Helper for Example 17.22: the one-step squared frequency increment has rowwise mean
`(2 / N^2) * x * (1 - x)`. -/
private theorem moranSquaredIncrementMeanStep (i : Fin (N + 1)) :
    Finset.sum Finset.univ (fun j : Fin (N + 1) ↦
      (moranFrequency N j - moranFrequency N i) ^ (2 : ℕ) *
        (moranTransitionMatrix N i j).toReal) =
      ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) * moranFrequency N i * (1 - moranFrequency N i) := by
  by_cases hzero : (i : ℕ) = 0
  · have hi : i = 0 := Fin.ext hzero
    have hsucc : (i : ℕ) + 1 < N + 1 := by
      simp [hzero]
    -- At the bottom boundary, the chain does not move, so the squared increment is zero.
    simp [moranWeightedRowToReal, hi, moranFrequency_zero, moranMoveProb_zero,
      moranStayProb_toReal]
  · by_cases hsucc : (i : ℕ) + 1 < N + 1
    · -- In the interior, only the two neighboring states contribute, each with squared increment
      -- `(1 / N)^2`.
      calc
        Finset.sum Finset.univ (fun j : Fin (N + 1) ↦
          (moranFrequency N j - moranFrequency N i) ^ (2 : ℕ) *
            (moranTransitionMatrix N i j).toReal)
          = ((1 / N : ℝ) ^ (2 : ℕ)) * (moranMoveProb N i).toReal +
              (0 * (moranStayProb N i).toReal +
                ((1 / N : ℝ) ^ (2 : ℕ)) * (moranMoveProb N i).toReal) := by
              simp [moranWeightedRowToReal, hzero, hsucc, moranFrequency_succ, moranFrequency_pred]
        _ = ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) * moranFrequency N i * (1 - moranFrequency N i) := by
              rw [moranMoveProb_toReal]
              ring
    · have hiVal : (i : ℕ) = N := by omega
      have hi : i = Fin.last N := Fin.ext hiVal
      -- At the top boundary, the chain again stays put almost surely.
      simp [moranWeightedRowToReal, hi, moranFrequency_last, moranMoveProb_last,
        moranStayProb_toReal]

/-- The predictable quadratic variation formula from Example 17.22, written as a process built
from the Moran frequencies. -/
def moranPredictableQuadraticVariation {Ω : Type u}
    (X : ℕ → Ω → Fin (N + 1)) : ℕ → Ω → ℝ :=
  fun n ω ↦ ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) *
    Finset.sum (Finset.range n) (fun i ↦
      moranFrequency N (X i ω) * (1 - moranFrequency N (X i ω)))

/-- Helper for Example 17.22: the explicit Moran compensator satisfies the expected one-step
recursion. -/
private theorem moranPredictableQuadraticVariation_succ {Ω : Type u}
    (X : ℕ → Ω → Fin (N + 1)) (n : ℕ) :
    moranPredictableQuadraticVariation N X (n + 1) =
      moranPredictableQuadraticVariation N X n +
        fun ω ↦ ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) *
          moranFrequency N (X n ω) * (1 - moranFrequency N (X n ω)) := by
  -- Split the finite sum at the last index and factor out the constant prefactor.
  ext ω
  simp [moranPredictableQuadraticVariation, Finset.sum_range_succ]
  ring

variable {N}

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Fin (N + 1) → ProbabilityMeasure Ω}
variable {X : ℕ → Ω → Fin (N + 1)}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel (moranTransitionMatrix N) ^ n) P X]

local notation "M" => fun n ω ↦ moranFrequency N (X n ω)
local notation "ℱ" => processFiltration X

/-- Helper for Example 17.22: a realized chain is adapted to its own process filtration. -/
private theorem adapted_processFiltration_of_realization
    (hReal : IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (moranTransitionMatrix N) ^ n) P X := inferInstance) :
    Adapted (processFiltration X) X := by
  intro n
  refine measurable_iff_comap_le.2 ?_
  exact le_inf
    ((hReal.measurable_process n).comap_le)
    (le_iSup_of_le n <| le_iSup_of_le le_rfl le_rfl)

/-- Helper for Example 17.22: the singleton mass of the discrete Moran kernel is the corresponding
transition-matrix entry. -/
private theorem moranDiscreteKernel_real_singleton
    (x j : Fin (N + 1)) :
    ((discreteMatrixKernel (moranTransitionMatrix N) x).real ({j} : Set (Fin (N + 1)))) =
      (moranTransitionMatrix N x j).toReal := by
  -- Evaluate the discrete kernel on a singleton and then take its real mass.
  rw [Measure.real_def, discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton j)]
  have hsum :
      ∑' i : Fin (N + 1),
          moranTransitionMatrix N x i * (if i = j then (1 : ℝ≥0∞) else 0) =
        moranTransitionMatrix N x j := by
    rw [tsum_eq_single j]
    · simp
    · intro i hij
      simp [hij]
  simp [Pi.single_apply]

/-- Helper for Example 17.22: for this measurable Markov realization, the process filtration agrees
with the generated history filtration. -/
private theorem processFiltration_eq_generatedFiltrationSpace_of_measurableProcess
    (n : ℕ)
    (hReal : IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (moranTransitionMatrix N) ^ n) P X := inferInstance) :
    processFiltration X n = generatedFiltrationSpace X n := by
  have hgenerated_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    refine iSup₂_le fun k hk ↦ ?_
    exact (hReal.measurable_process k).comap_le
  -- Route correction: the only missing filtration bridge is the ambient-space infimum collapse.
  simpa [processFiltration, generatedFiltrationSpace] using inf_eq_right.mpr hgenerated_le

/-- Helper for Example 17.22: conditioning the next-state singleton event on the natural history
returns the current Moran transition probability. -/
private theorem moranOneStepConditionalProb_eq_transitionMatrix
    (i : Fin (N + 1)) (n : ℕ) (j : Fin (N + 1)) :
    (P i : Measure Ω)⟦X (n + 1) ⁻¹' ({j} : Set (Fin (N + 1))) | ℱ n⟧ =ᵐ[(P i : Measure Ω)]
      fun ω ↦ (moranTransitionMatrix N (X n ω) j).toReal := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (moranTransitionMatrix N) ^ n) P X := inferInstance
  have hMarkovGenerated :
      (P i : Measure Ω)⟦X (n + 1) ⁻¹' ({j} : Set (Fin (N + 1))) |
        generatedFiltrationSpace X n⟧ =ᵐ[(P i : Measure Ω)]
          fun ω ↦
            ((discreteMatrixKernel (moranTransitionMatrix N) (X n ω)).real
              ({j} : Set (Fin (N + 1)))) := by
    -- Specialize the Markov property at one step and the singleton event `{j}`.
    simpa [pow_one, add_comm] using
      hReal.markov_property i (A := ({j} : Set (Fin (N + 1))))
        (measurableSet_singleton j) n 1
  -- Rewrite the generated filtration back to the process filtration and identify the singleton
  -- mass with the corresponding matrix entry.
  have hProcess :
      (P i : Measure Ω)⟦X (n + 1) ⁻¹' ({j} : Set (Fin (N + 1))) | ℱ n⟧ =ᵐ[(P i : Measure Ω)]
        fun ω ↦
          ((discreteMatrixKernel (moranTransitionMatrix N) (X n ω)).real
            ({j} : Set (Fin (N + 1)))) := by
    simpa [processFiltration_eq_generatedFiltrationSpace_of_measurableProcess (N := N)
        (P := P) (X := X) n] using hMarkovGenerated
  exact hProcess.trans <| Filter.EventuallyEq.of_eq <| by
    funext ω
    exact moranDiscreteKernel_real_singleton (N := N) (x := X n ω) j

/-- Helper for Example 17.22: bounded range makes every sampled observable `f (X n)` integrable
under the Moran realization law. -/
private theorem integrable_comp_process_of_boundedRange_realization
    {f : Fin (N + 1) → ℝ}
    (hf_bdd : Bornology.IsBounded (Set.range f)) (i : Fin (N + 1)) :
    ∀ n, Integrable (fun ω ↦ f (X n ω)) (P i : Measure Ω) := by
  intro n
  obtain ⟨R, hR⟩ := hf_bdd.exists_norm_le
  refine Integrable.mono' (integrable_const R)
    ((Measurable.of_discrete.comp
      (IsMarkovProcessRealization.measurable_process
        (κ := fun n : ℕ ↦ discreteMatrixKernel (moranTransitionMatrix N) ^ n)
        (P := P) (X := X) n)).aestronglyMeasurable) ?_
  filter_upwards with ω
  simpa using hR (f (X n ω)) ⟨X n ω, rfl⟩

/-- Helper for Example 17.22: conditioning any bounded function of the next Moran state on the
current history collapses to the corresponding one-step row average. -/
private theorem moranCondExp_nextFunction
    (i : Fin (N + 1)) (n : ℕ) (f : Fin (N + 1) → ℝ) :
    (P i : Measure Ω)[fun ω ↦ f (X (n + 1) ω) | ℱ n] =ᵐ[(P i : Measure Ω)]
      fun ω ↦ ∑ j : Fin (N + 1), f j * (moranTransitionMatrix N (X n ω) j).toReal := by
  let ind : Fin (N + 1) → Ω → ℝ :=
    fun j ↦ Set.indicator (X (n + 1) ⁻¹' ({j} : Set (Fin (N + 1)))) (fun _ ↦ (1 : ℝ))
  have hEventMeas :
      ∀ j : Fin (N + 1), MeasurableSet (X (n + 1) ⁻¹' ({j} : Set (Fin (N + 1)))) := by
    intro j
    exact
      (IsMarkovProcessRealization.measurable_process
        (κ := fun n : ℕ ↦ discreteMatrixKernel (moranTransitionMatrix N) ^ n)
        (P := P) (X := X) (n + 1)) (measurableSet_singleton j)
  have hIndInt : ∀ j : Fin (N + 1), Integrable (ind j) (P i : Measure Ω) := by
    intro j
    -- Each singleton indicator is bounded by the integrable constant `1`.
    simpa [ind] using ((integrable_const (1 : ℝ)).indicator (hEventMeas j))
  have hRep :
      (fun ω ↦ f (X (n + 1) ω)) = fun ω ↦ ∑ j : Fin (N + 1), f j * ind j ω := by
    -- Route correction: write the next-step observable as a finite sum over singleton events.
    funext ω
    change f (X (n + 1) ω) = ∑ j : Fin (N + 1), f j * ind j ω
    rw [Finset.sum_eq_single_of_mem (X (n + 1) ω) (by simp)]
    · simp [ind]
    · intro j _ hj
      have hj' : X (n + 1) ω ≠ j := by
        simpa [eq_comm] using hj
      simp [ind, hj']
  -- Push the finite decomposition through conditional expectation termwise, then replace each
  -- singleton conditional expectation with the explicit Moran row mass.
  calc
    (P i : Measure Ω)[fun ω ↦ f (X (n + 1) ω) | ℱ n] =ᵐ[(P i : Measure Ω)]
        (P i : Measure Ω)[fun ω ↦ ∑ j : Fin (N + 1), f j * ind j ω | ℱ n] := by
          exact condExp_congr_ae (Filter.EventuallyEq.of_eq hRep)
    _ =ᵐ[(P i : Measure Ω)]
        (P i : Measure Ω)[∑ j : Fin (N + 1), fun ω ↦ f j * ind j ω | ℱ n] := by
          exact condExp_congr_ae <| Filter.EventuallyEq.of_eq <| by
            funext ω
            simp [Finset.sum_apply]
    _ =ᵐ[(P i : Measure Ω)]
        ∑ j : Fin (N + 1), (P i : Measure Ω)[fun ω ↦ f j * ind j ω | ℱ n] := by
          simpa using
            (condExp_finset_sum
              (μ := (P i : Measure Ω))
              (s := Finset.univ)
              (f := fun j ω ↦ f j * ind j ω)
              (fun j _ ↦ (hIndInt j).const_mul (f j))
              (ℱ n))
    _ =ᵐ[(P i : Measure Ω)]
        ∑ j : Fin (N + 1), fun ω ↦ f j * ((P i : Measure Ω)[ind j | ℱ n]) ω := by
          exact eventuallyEq_sum fun j _ ↦ by
            simpa [smul_eq_mul, ind] using
              (condExp_smul (μ := (P i : Measure Ω)) (m := ℱ n) (f j) (ind j))
    _ =ᵐ[(P i : Measure Ω)]
        ∑ j : Fin (N + 1), fun ω ↦ f j * (moranTransitionMatrix N (X n ω) j).toReal := by
          exact eventuallyEq_sum fun j _ ↦ by
            exact Filter.EventuallyEq.rfl.mul
              (moranOneStepConditionalProb_eq_transitionMatrix
                (N := N) (P := P) (X := X) i n j)
    _ =ᵐ[(P i : Measure Ω)]
        fun ω ↦ ∑ j : Fin (N + 1), f j * (moranTransitionMatrix N (X n ω) j).toReal := by
          exact Filter.EventuallyEq.of_eq <| by
            funext ω
            simp

/-- Helper for Example 17.22: the `toReal` row sum of the Moran transition matrix is `1`. -/
private theorem moranTransitionMatrix_rowSum_toReal
    (i : Fin (N + 1)) :
    ∑ j : Fin (N + 1), (moranTransitionMatrix N i j).toReal = 1 := by
  have hrow := moranWeightedRowToReal (N := N) (i := i) (g := fun _ ↦ (1 : ℝ))
  by_cases hzero : (i : ℕ) = 0
  · have hi : i = 0 := Fin.ext hzero
    have hsucc : (i : ℕ) + 1 < N + 1 := by
      simp [hzero]
    have hstay :
        (moranStayProb N i).toReal = 1 := by
      have hmass := moranLocalMass_sum_one_toReal (N := N) i
      simpa [hi, moranMoveProb_zero] using hmass
    calc
      ∑ j : Fin (N + 1), (moranTransitionMatrix N i j).toReal
          = (moranStayProb N i).toReal := by
              simpa [hzero, hsucc, hi, moranMoveProb_zero] using hrow
      _ = 1 := hstay
  · by_cases hsucc : (i : ℕ) + 1 < N + 1
    · calc
        ∑ j : Fin (N + 1), (moranTransitionMatrix N i j).toReal
            = (moranMoveProb N i).toReal +
                ((moranStayProb N i).toReal + (moranMoveProb N i).toReal) := by
                  simpa [hzero, hsucc] using hrow
        _ = 1 := by simpa [add_assoc] using moranLocalMass_sum_one_toReal (N := N) i
    · have hiVal : (i : ℕ) = N := by omega
      have hi : i = Fin.last N := Fin.ext hiVal
      have hstay :
          (moranStayProb N i).toReal = 1 := by
        have hmass := moranLocalMass_sum_one_toReal (N := N) i
        simpa [hi, moranMoveProb_last] using hmass
      calc
        ∑ j : Fin (N + 1), (moranTransitionMatrix N i j).toReal
            = (moranStayProb N i).toReal := by
                simpa [hzero, hsucc, hi, moranMoveProb_last] using hrow
        _ = 1 := hstay

/-- Helper for Example 17.22: the next-step conditional second moment of the Moran frequency is
the current square plus the explicit compensator density. -/
private theorem moranFrequencySquareMeanStep
    (i : Fin (N + 1)) :
    ∑ j : Fin (N + 1),
        (moranFrequency N j) ^ (2 : ℕ) * (moranTransitionMatrix N i j).toReal =
      moranFrequency N i ^ (2 : ℕ) +
        ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) * moranFrequency N i * (1 - moranFrequency N i) := by
  have hCenteredMean :
      ∑ j : Fin (N + 1),
          (moranFrequency N j - moranFrequency N i) *
            (moranTransitionMatrix N i j).toReal = 0 := by
    -- Center the first moment around the current state and use the row-mean and row-sum formulas.
    calc
      ∑ j : Fin (N + 1),
          (moranFrequency N j - moranFrequency N i) *
            (moranTransitionMatrix N i j).toReal
        = ∑ j : Fin (N + 1),
            (moranFrequency N j * (moranTransitionMatrix N i j).toReal -
              moranFrequency N i * (moranTransitionMatrix N i j).toReal) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
      _ = ∑ j : Fin (N + 1),
            moranFrequency N j * (moranTransitionMatrix N i j).toReal -
          ∑ j : Fin (N + 1),
            moranFrequency N i * (moranTransitionMatrix N i j).toReal := by
              rw [Finset.sum_sub_distrib]
      _ = moranFrequency N i - moranFrequency N i *
            (∑ j : Fin (N + 1), (moranTransitionMatrix N i j).toReal) := by
              rw [moranFrequencyMeanStep, ← Finset.mul_sum]
      _ = moranFrequency N i - moranFrequency N i * 1 := by
              rw [moranTransitionMatrix_rowSum_toReal]
      _ = 0 := by ring
  have hLinearTerm :
      ∑ j : Fin (N + 1),
          (2 * moranFrequency N i * (moranFrequency N j - moranFrequency N i)) *
            (moranTransitionMatrix N i j).toReal = 0 := by
    -- The linear centered term vanishes because the centered first moment is zero.
    calc
      ∑ j : Fin (N + 1),
          (2 * moranFrequency N i * (moranFrequency N j - moranFrequency N i)) *
            (moranTransitionMatrix N i j).toReal
        = ∑ j : Fin (N + 1),
            (2 * moranFrequency N i) *
              ((moranFrequency N j - moranFrequency N i) *
                (moranTransitionMatrix N i j).toReal) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
      _ = (2 * moranFrequency N i) *
            ∑ j : Fin (N + 1),
              (moranFrequency N j - moranFrequency N i) *
                (moranTransitionMatrix N i j).toReal := by
              rw [Finset.mul_sum]
      _ = 0 := by rw [hCenteredMean]; ring
  have hConstantTerm :
      ∑ j : Fin (N + 1),
          (moranFrequency N i ^ (2 : ℕ)) * (moranTransitionMatrix N i j).toReal =
        moranFrequency N i ^ (2 : ℕ) := by
    -- The constant contribution is the current square times the row mass `1`.
    calc
      ∑ j : Fin (N + 1),
          (moranFrequency N i ^ (2 : ℕ)) * (moranTransitionMatrix N i j).toReal
        = moranFrequency N i ^ (2 : ℕ) *
            ∑ j : Fin (N + 1), (moranTransitionMatrix N i j).toReal := by
              rw [← Finset.mul_sum]
      _ = moranFrequency N i ^ (2 : ℕ) * 1 := by
            rw [moranTransitionMatrix_rowSum_toReal]
      _ = moranFrequency N i ^ (2 : ℕ) := by ring
  -- Expand the square into centered quadratic, linear, and constant pieces.
  calc
    ∑ j : Fin (N + 1),
        (moranFrequency N j) ^ (2 : ℕ) * (moranTransitionMatrix N i j).toReal
      = ∑ j : Fin (N + 1),
          (((moranFrequency N j - moranFrequency N i) ^ (2 : ℕ)) +
              (2 * moranFrequency N i * (moranFrequency N j - moranFrequency N i)) +
              moranFrequency N i ^ (2 : ℕ)) *
            (moranTransitionMatrix N i j).toReal := by
            refine Finset.sum_congr rfl ?_
            intro j _
            ring
    _ = ∑ j : Fin (N + 1),
          (moranFrequency N j - moranFrequency N i) ^ (2 : ℕ) *
            (moranTransitionMatrix N i j).toReal +
        (∑ j : Fin (N + 1),
            (2 * moranFrequency N i * (moranFrequency N j - moranFrequency N i)) *
              (moranTransitionMatrix N i j).toReal +
          ∑ j : Fin (N + 1),
            (moranFrequency N i ^ (2 : ℕ)) * (moranTransitionMatrix N i j).toReal) := by
            simp_rw [add_mul]
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            ring
    _ = ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) * moranFrequency N i * (1 - moranFrequency N i) +
        (0 + moranFrequency N i ^ (2 : ℕ)) := by
          rw [moranSquaredIncrementMeanStep, hLinearTerm, hConstantTerm]
    _ = moranFrequency N i ^ (2 : ℕ) +
        ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) * moranFrequency N i * (1 - moranFrequency N i) := by
          ring

/-- Helper for Example 17.22: every Moran frequency coordinate is square integrable under the
realization law, because the state space is finite and the frequency stays in `[0, 1]`. -/
private theorem moranFrequency_squareIntegrable
    (i : Fin (N + 1)) :
    ∀ n, Integrable (fun ω ↦ M n ω ^ (2 : ℕ)) (P i : Measure Ω) := by
  let f : Fin (N + 1) → ℝ := fun x ↦ moranFrequency N x ^ (2 : ℕ)
  have hf_bdd : Bornology.IsBounded (Set.range f) := by
    -- The state space is finite, so every real-valued observable on it has bounded range.
    simpa [f] using (Set.toFinite (Set.range f)).isBounded
  -- Repackage the squared frequency coordinate as a bounded observable sampled along the chain.
  change ∀ n, Integrable (fun ω ↦ moranFrequency N (X n ω) ^ (2 : ℕ)) (P i : Measure Ω)
  simpa [f] using
    (integrable_comp_process_of_boundedRange_realization
      (N := N) (P := P) (X := X) hf_bdd i)

-- Proof sketch: use the one-step transition probabilities of the Moran chain to show that the
-- conditional expectation of the next frequency equals the current one.
/-- Any realization of the discrete Moran chain makes the gene-frequency process a martingale. -/
theorem moranFrequency_martingale
    (i : Fin (N + 1)) :
    Martingale M ℱ (P i : Measure Ω) := by
  have hMsm : ∀ n, StronglyMeasurable (M n) := by
    let hReal :
        IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel (moranTransitionMatrix N) ^ n) P X := inferInstance
    have hmoran : Measurable (moranFrequency N) := Measurable.of_discrete
    intro n
    -- The frequency coordinate is a discrete measurable function of the Markov state.
    change StronglyMeasurable (fun ω ↦ moranFrequency N (X n ω))
    exact (hmoran.comp (hReal.measurable_process n)).stronglyMeasurable
  have hMad : StronglyAdapted ℱ M := by
    have hmoran : Measurable (moranFrequency N) := Measurable.of_discrete
    have hXad : Adapted (processFiltration X) X :=
      adapted_processFiltration_of_realization (N := N) (P := P) (X := X)
    have hMadapted : Adapted ℱ M := by
      intro n
      exact hmoran.comp (hXad n)
    exact hMadapted.stronglyAdapted
  have hMint : ∀ n, Integrable (M n) (P i : Measure Ω) := by
    -- The state space is finite, so the sampled frequency observable is integrable at every time.
    simpa using
      (integrable_comp_process_of_boundedRange_realization
        (N := N) (P := P) (X := X)
        (f := moranFrequency N) (moranFrequency_isBounded (N := N)) i)
  have hCondZero :
      ∀ n, (P i : Measure Ω)[fun ω ↦ M (n + 1) ω - M n ω | ℱ n] =ᵐ[(P i : Measure Ω)] 0 := by
    intro n
    -- Route correction: use the one-step conditional expectation formula in the exact row-average
    -- normal form, then collapse that row average with `moranFrequencyMeanStep`.
    calc
      (P i : Measure Ω)[fun ω ↦ M (n + 1) ω - M n ω | ℱ n] =ᵐ[(P i : Measure Ω)]
          (P i : Measure Ω)[M (n + 1) | ℱ n] - (P i : Measure Ω)[M n | ℱ n] := by
            exact condExp_sub (hMint (n + 1)) (hMint n) (ℱ n)
      _ =ᵐ[(P i : Measure Ω)]
          (fun ω ↦ ∑ j : Fin (N + 1),
            moranFrequency N j * (moranTransitionMatrix N (X n ω) j).toReal) -
            (P i : Measure Ω)[M n | ℱ n] := by
              exact
                (moranCondExp_nextFunction
                  (N := N) (P := P) (X := X) i n (moranFrequency N)).sub
                  Filter.EventuallyEq.rfl
      _ =ᵐ[(P i : Measure Ω)] M n - (P i : Measure Ω)[M n | ℱ n] := by
            refine (Filter.EventuallyEq.of_eq <| by
              funext ω
              exact moranFrequencyMeanStep (N := N) (i := X n ω)).sub Filter.EventuallyEq.rfl
      _ =ᵐ[(P i : Measure Ω)] M n - M n := by
            refine Filter.EventuallyEq.rfl.sub ?_
            exact Filter.EventuallyEq.of_eq
              (MeasureTheory.condExp_of_stronglyMeasurable
                ((processFiltration X).le n) (hMad n) (hMint n))
      _ =ᵐ[(P i : Measure Ω)] 0 := by
            simp
  -- The zero conditional expectation of each increment is the martingale constructor hypothesis.
  exact martingale_of_condExp_sub_eq_zero_nat hMad hMint hCondZero

/-- Helper for Example 17.22: the conditional expectation of the squared Moran increment is the
explicit compensator density from formula `(17.12)`. -/
private theorem moranSquaredIncrement_condExp
    (i : Fin (N + 1)) (n : ℕ) :
    (P i : Measure Ω)[fun ω ↦ (M (n + 1) ω - M n ω) ^ (2 : ℕ) | ℱ n] =ᵐ[(P i : Measure Ω)]
      fun ω ↦ ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) * M n ω * (1 - M n ω) := by
  have hMmart : Martingale M ℱ (P i : Measure Ω) :=
    moranFrequency_martingale (N := N) (P := P) (X := X) i
  have hMsq : ∀ k, Integrable (fun ω ↦ M k ω ^ (2 : ℕ)) (P i : Measure Ω) :=
    moranFrequency_squareIntegrable (N := N) (P := P) (X := X) i
  have hMnSqMeas : StronglyMeasurable[ℱ n] (fun ω ↦ M n ω ^ (2 : ℕ)) := by
    -- The current square is already measurable with respect to the time-`n` history.
    simpa [pow_two] using (hMmart.stronglyMeasurable n).mul (hMmart.stronglyMeasurable n)
  have hSquareCond :
      (P i : Measure Ω)[fun ω ↦ M (n + 1) ω ^ (2 : ℕ) | ℱ n] =ᵐ[(P i : Measure Ω)]
        fun ω ↦ M n ω ^ (2 : ℕ) +
          ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) * M n ω * (1 - M n ω) := by
    -- First identify the conditional expectation of the next square via the finite-state row
    -- average, then collapse that row average with `moranFrequencySquareMeanStep`.
    calc
      (P i : Measure Ω)[fun ω ↦ M (n + 1) ω ^ (2 : ℕ) | ℱ n] =ᵐ[(P i : Measure Ω)]
          fun ω ↦ ∑ j : Fin (N + 1),
            (moranFrequency N j) ^ (2 : ℕ) * (moranTransitionMatrix N (X n ω) j).toReal := by
              simpa using
                moranCondExp_nextFunction
                  (N := N) (P := P) (X := X) i n
                  (fun j ↦ moranFrequency N j ^ (2 : ℕ))
      _ =ᵐ[(P i : Measure Ω)]
          fun ω ↦ M n ω ^ (2 : ℕ) +
            ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) * M n ω * (1 - M n ω) := by
              exact Filter.EventuallyEq.of_eq <| by
                funext ω
                exact moranFrequencySquareMeanStep (N := N) (i := X n ω)
  -- Rewrite the squared increment into the square-moment difference and subtract the present
  -- square, which is already `ℱ n`-measurable.
  calc
    (P i : Measure Ω)[fun ω ↦ (M (n + 1) ω - M n ω) ^ (2 : ℕ) | ℱ n] =ᵐ[(P i : Measure Ω)]
        (P i : Measure Ω)[fun ω ↦ M (n + 1) ω ^ (2 : ℕ) - M n ω ^ (2 : ℕ) | ℱ n] := by
          exact (condExp_sqMomentDiff_eq_condExp_sqIncrement hMmart hMsq n).symm
    _ =ᵐ[(P i : Measure Ω)]
        (P i : Measure Ω)[fun ω ↦ M (n + 1) ω ^ (2 : ℕ) | ℱ n] -
          (P i : Measure Ω)[fun ω ↦ M n ω ^ (2 : ℕ) | ℱ n] := by
            exact condExp_sub (hMsq (n + 1)) (hMsq n) (ℱ n)
    _ =ᵐ[(P i : Measure Ω)]
        (fun ω ↦ M n ω ^ (2 : ℕ) +
          ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) * M n ω * (1 - M n ω)) -
          (P i : Measure Ω)[fun ω ↦ M n ω ^ (2 : ℕ) | ℱ n] := by
            exact hSquareCond.sub Filter.EventuallyEq.rfl
    _ =ᵐ[(P i : Measure Ω)]
        (fun ω ↦ M n ω ^ (2 : ℕ) +
          ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) * M n ω * (1 - M n ω)) -
          fun ω ↦ M n ω ^ (2 : ℕ) := by
            refine Filter.EventuallyEq.rfl.sub ?_
            exact Filter.EventuallyEq.of_eq
              (MeasureTheory.condExp_of_stronglyMeasurable
                ((processFiltration X).le n) hMnSqMeas (hMsq n))
    _ =ᵐ[(P i : Measure Ω)] fun ω ↦
        ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) * M n ω * (1 - M n ω) := by
          exact Filter.EventuallyEq.of_eq <| by
            funext ω
            change
              (moranFrequency N (X n ω) ^ (2 : ℕ) +
                  ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) * moranFrequency N (X n ω) *
                    (1 - moranFrequency N (X n ω)) -
                moranFrequency N (X n ω) ^ (2 : ℕ)) =
                ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) * moranFrequency N (X n ω) *
                  (1 - moranFrequency N (X n ω))
            ring

-- Proof sketch: verify the Chapter 10 square-variation witness axioms for the explicit Moran sum
-- process by using the frequency martingale and the one-step increment computation from Example
-- 17.22.
/-- The square-variation witness in Example 17.22 is the explicit Moran sum process for the
frequency martingale. This is the
source-facing bridge to the chapter owner object `⟨M⟩[ℱ, μ]`. -/
theorem moranPredictableQuadraticVariation_isSquareVariationProcess
    (i : Fin (N + 1)) :
    IsSquareVariationProcess ℱ (P i : Measure Ω) M (moranPredictableQuadraticVariation N X) :=
  by
    let A : ℕ → Ω → ℝ := moranPredictableQuadraticVariation N X
    let density : ℕ → Ω → ℝ :=
      fun n ω ↦ ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) * M n ω * (1 - M n ω)
    have hA_zero : A 0 = fun _ : Ω ↦ (0 : ℝ) := by
      funext ω
      simp [A, moranPredictableQuadraticVariation]
    have hMsm : ∀ n, StronglyMeasurable (M n) := by
      let hReal :
          IsMarkovProcessRealization
            (fun n : ℕ ↦ discreteMatrixKernel (moranTransitionMatrix N) ^ n) P X := inferInstance
      have hmoran : Measurable (moranFrequency N) := Measurable.of_discrete
      intro n
      -- The frequency process is a discrete measurable function of the chain state.
      change StronglyMeasurable (fun ω ↦ moranFrequency N (X n ω))
      exact (hmoran.comp (hReal.measurable_process n)).stronglyMeasurable
    have hMad : StronglyAdapted ℱ M := by
      have hmoran : Measurable (moranFrequency N) := Measurable.of_discrete
      have hXad : Adapted (processFiltration X) X :=
        adapted_processFiltration_of_realization (N := N) (P := P) (X := X)
      have hMadapted : Adapted ℱ M := by
        intro n
        exact hmoran.comp (hXad n)
      exact hMadapted.stronglyAdapted
    have hMmart : Martingale M ℱ (P i : Measure Ω) :=
      moranFrequency_martingale (N := N) (P := P) (X := X) i
    have hMsq : ∀ n, Integrable (fun ω ↦ M n ω ^ (2 : ℕ)) (P i : Measure Ω) :=
      moranFrequency_squareIntegrable (N := N) (P := P) (X := X) i
    have hDensityStrong : ∀ n, StronglyMeasurable[ℱ n] (density n) := by
      intro n
      -- The compensator density depends only on the current state `X n`.
      have hOneMinus : StronglyMeasurable[ℱ n] (fun ω ↦ 1 - M n ω) := by
        exact stronglyMeasurable_const.sub (hMad n)
      simpa [density, mul_assoc] using stronglyMeasurable_const.mul ((hMad n).mul hOneMinus)
    have hATimeStrong : ∀ n, StronglyMeasurable[ℱ n] (A n) := by
      intro n
      induction n with
      | zero =>
          -- The compensator starts from the zero process.
          rw [hA_zero]
          simpa using
            (stronglyMeasurable_const : StronglyMeasurable[ℱ 0] (fun _ : Ω ↦ (0 : ℝ)))
      | succ n ih =>
          have hPrev : StronglyMeasurable[ℱ (n + 1)] (A n) := by
            exact ih.mono (Filtration.mono ℱ (Nat.le_succ n))
          have hTerm : StronglyMeasurable[ℱ (n + 1)] (density n) := by
            exact (hDensityStrong n).mono (Filtration.mono ℱ (Nat.le_succ n))
          have hStep : A (n + 1) = A n + density n := by
            simpa [density] using moranPredictableQuadraticVariation_succ (N := N) (X := X) n
          -- The recursion adds the current density to the previous compensator.
          simpa [hStep] using hPrev.add hTerm
    have hA0Meas : Measurable[ℱ 0] (A 0) := by
      rw [hA_zero]
      simp
    have hAAddOneMeas : ∀ n, Measurable[ℱ n] (A (n + 1)) := by
      intro n
      have hStep : A (n + 1) = A n + density n := by
        simpa [density] using moranPredictableQuadraticVariation_succ (N := N) (X := X) n
      -- Predictability only needs the one-step compensator to be measurable at time `n`.
      simpa [hStep] using ((hATimeStrong n).add (hDensityStrong n)).measurable
    have hAPredictable : IsPredictable ℱ A := by
      exact isPredictable_of_measurable_add_one hA0Meas hAAddOneMeas
    have hAad : StronglyAdapted ℱ A := hATimeStrong
    let densityState : Fin (N + 1) → ℝ :=
      fun x ↦ ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) * moranFrequency N x * (1 - moranFrequency N x)
    have hDensityStateBdd : Bornology.IsBounded (Set.range densityState) := by
      -- Any real-valued function on the finite Moran state space has bounded range.
      simpa [densityState] using (Set.toFinite (Set.range densityState)).isBounded
    have hDensityInt : ∀ n, Integrable (density n) (P i : Measure Ω) := by
      intro n
      change Integrable (fun ω ↦ densityState (X n ω)) (P i : Measure Ω)
      simpa [densityState] using
        (integrable_comp_process_of_boundedRange_realization
          (N := N) (P := P) (X := X)
          (f := densityState) hDensityStateBdd i n)
    have hAint : ∀ n, Integrable (A n) (P i : Measure Ω) := by
      intro n
      induction n with
      | zero =>
          -- The initial compensator is the zero process.
          rw [hA_zero]
          simp
      | succ n ih =>
          have hStep : A (n + 1) = A n + density n := by
            simpa [density] using moranPredictableQuadraticVariation_succ (N := N) (X := X) n
          -- The recursion turns integrability of the compensator into integrability of the next
          -- density increment.
          rw [hStep]
          exact ih.add (hDensityInt n)
    have hSquareAd : StronglyAdapted ℱ (fun n ω ↦ M n ω ^ (2 : ℕ)) := by
      intro n
      simpa [pow_two] using (hMad n).mul (hMad n)
    have hMadiff : StronglyAdapted ℱ (fun n ω ↦ M n ω ^ (2 : ℕ) - A n ω) := by
      intro n
      exact (hSquareAd n).sub (hAad n)
    have hCondZero :
        ∀ n, (P i : Measure Ω)[fun ω ↦ M (n + 1) ω ^ (2 : ℕ) - A (n + 1) ω -
            (M n ω ^ (2 : ℕ) - A n ω) | ℱ n] =ᵐ[(P i : Measure Ω)] 0 := by
      intro n
      have hAdiff : A (n + 1) - A n = density n := by
        have hStep : A (n + 1) = A n + density n := by
          simpa [density] using moranPredictableQuadraticVariation_succ (N := N) (X := X) n
        funext ω
        exact sub_eq_iff_eq_add'.2 (congrFun hStep ω)
      have hSqDiffInt :
          Integrable (fun ω ↦ M (n + 1) ω ^ (2 : ℕ) - M n ω ^ (2 : ℕ)) (P i : Measure Ω) :=
        (hMsq (n + 1)).sub (hMsq n)
      have hAdiffInt : Integrable (A (n + 1) - A n) (P i : Measure Ω) := by
        rw [hAdiff]
        exact hDensityInt n
      -- Route correction: rewrite the compensated-square increment into the square increment minus
      -- the explicit density, then use the already-proved conditional squared-increment formula.
      calc
        (P i : Measure Ω)[fun ω ↦ M (n + 1) ω ^ (2 : ℕ) - A (n + 1) ω -
            (M n ω ^ (2 : ℕ) - A n ω) | ℱ n] =ᵐ[(P i : Measure Ω)]
            (P i : Measure Ω)[fun ω ↦
              (M (n + 1) ω ^ (2 : ℕ) - M n ω ^ (2 : ℕ)) - (A (n + 1) ω - A n ω) | ℱ n] := by
                refine condExp_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
                ring
        _ =ᵐ[(P i : Measure Ω)]
            (P i : Measure Ω)[fun ω ↦ M (n + 1) ω ^ (2 : ℕ) - M n ω ^ (2 : ℕ) | ℱ n] -
              (P i : Measure Ω)[A (n + 1) - A n | ℱ n] := by
                exact condExp_sub hSqDiffInt hAdiffInt (ℱ n)
        _ =ᵐ[(P i : Measure Ω)]
            (P i : Measure Ω)[fun ω ↦ (M (n + 1) ω - M n ω) ^ (2 : ℕ) | ℱ n] -
              (P i : Measure Ω)[A (n + 1) - A n | ℱ n] := by
                exact (condExp_sqMomentDiff_eq_condExp_sqIncrement hMmart hMsq n).sub
                  Filter.EventuallyEq.rfl
        _ =ᵐ[(P i : Measure Ω)] density n - (P i : Measure Ω)[A (n + 1) - A n | ℱ n] := by
              exact (moranSquaredIncrement_condExp (N := N) (P := P) (X := X) i n).sub
                Filter.EventuallyEq.rfl
        _ =ᵐ[(P i : Measure Ω)] density n - density n := by
              rw [hAdiff]
              refine Filter.EventuallyEq.rfl.sub ?_
              exact Filter.EventuallyEq.of_eq
                (MeasureTheory.condExp_of_stronglyMeasurable
                  ((processFiltration X).le n) (hDensityStrong n) (hDensityInt n))
        _ =ᵐ[(P i : Measure Ω)] 0 := by
              simp [density]
    -- Assemble the explicit compensator from its initial value, predictability, and the
    -- compensated-square martingale.
    refine ⟨?_, hAPredictable, martingale_of_condExp_sub_eq_zero_nat hMadiff ?_ hCondZero⟩
    · ext ω
      simp [moranPredictableQuadraticVariation]
    · intro n
      exact (hMsq n).sub (hAint n)

-- Proof sketch: apply the Chapter 10 uniqueness bridge from any square-variation witness to the
-- canonical square variation of the martingale `M`.
/-- Example 17.22: for a realization of the discrete Moran chain, the canonical square variation
of the frequency martingale agrees almost everywhere with the explicit Moran formula `(17.12)` at
each fixed time. -/
theorem moranPredictableQuadraticVariation_eq
    (i : Fin (N + 1)) (n : ℕ) :
    ⟨M⟩[ℱ, (P i : Measure Ω)] n =ᵐ[(P i : Measure Ω)]
      moranPredictableQuadraticVariation N X n := by
  -- The source-facing witness identifies the canonical square variation with the explicit Moran
  -- compensator at every fixed time.
  exact
    IsSquareVariationProcess.predictablePart_sq_ae_eq
      (moranPredictableQuadraticVariation_isSquareVariationProcess
        (N := N) (P := P) (X := X) i)
      (moranFrequency_squareIntegrable (N := N) (P := P) (X := X) i)
      n

end

end ProbabilityTheory
