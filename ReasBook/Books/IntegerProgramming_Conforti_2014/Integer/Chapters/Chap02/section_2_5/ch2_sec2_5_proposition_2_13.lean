/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_5.ch2_sec2_5_definition_2_29.SAT
public import Mathlib.Data.Real.Basic

public section

namespace SAT.Clause

/-- Expanding the clause with positive index set `P` and negative index set `N` rewrites
clause satisfaction as the expected literalwise disjunction. -/
theorem indexSets_satisfiedBy_iff
    {n : ℕ} (P N : Finset (Fin n)) (β : Fin n → Bool) :
    SAT.Clause.satisfiedBy (P.image SAT.Literal.pos ∪ N.image SAT.Literal.neg) β ↔
      (∃ j ∈ P, β j = true) ∨ ∃ j ∈ N, β j = false := by
  -- Expand clause satisfaction, then sort the witnessing literal by its sign.
  rw [satisfiedBy_iff_exists_mem]
  constructor
  · rintro ⟨l, hl, hsatisfied⟩
    rw [Finset.mem_union] at hl
    rcases hl with hpos | hneg
    · rw [Finset.mem_image] at hpos
      obtain ⟨j, hj, rfl⟩ := hpos
      left
      use j
      constructor
      · exact hj
      · exact (SAT.Literal.satisfiedBy_pos_iff β j).mp hsatisfied
    · rw [Finset.mem_image] at hneg
      obtain ⟨j, hj, rfl⟩ := hneg
      right
      use j
      constructor
      · exact hj
      · exact (SAT.Literal.satisfiedBy_neg_iff β j).mp hsatisfied
  · rintro (⟨j, hj, hβ⟩ | ⟨j, hj, hβ⟩)
    · use SAT.Literal.pos j
      constructor
      · rw [Finset.mem_union]
        left
        rw [Finset.mem_image]
        use j
      · exact (SAT.Literal.satisfiedBy_pos_iff β j).mpr hβ
    · use SAT.Literal.neg j
      constructor
      · rw [Finset.mem_union]
        right
        rw [Finset.mem_image]
        use j
      · exact (SAT.Literal.satisfiedBy_neg_iff β j).mpr hβ

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_proposition_2_13.lean`: both real-valued
Boolean indicators are nonnegative. -/
private lemma boolIndicators_nonneg (b : Bool) :
    (0 ≤ if b then (1 : ℝ) else 0) ∧ (0 ≤ if b then (0 : ℝ) else 1) := by
  -- Both Boolean cases reduce the indicators to zero or one.
  cases b <;> simp

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_proposition_2_13.lean`: a true
entry in `P` or a false entry in `N` is equivalent to the combined real indicator sum being at
least one. -/
private lemma existsTrueOrFalse_iff_one_le_indicatorSums
    {α : Type*} (P N : Finset α) (β : α → Bool) :
    ((∃ j ∈ P, β j = true) ∨ ∃ j ∈ N, β j = false) ↔
      1 ≤ P.sum (fun j ↦ if β j then (1 : ℝ) else 0) +
        N.sum (fun j ↦ if β j then (0 : ℝ) else 1) := by
  constructor
  · intro hexists
    -- A witnessing coordinate contributes one, while every other contribution is nonnegative.
    rcases hexists with ⟨j, hj, hβ⟩ | ⟨j, hj, hβ⟩
    · have hP : 1 ≤ P.sum (fun i ↦ if β i then (1 : ℝ) else 0) := by
        calc
          1 = (if β j then (1 : ℝ) else 0) := by simp [hβ]
          _ ≤ P.sum (fun i ↦ if β i then (1 : ℝ) else 0) :=
            Finset.single_le_sum
              (f := fun i ↦ if β i then (1 : ℝ) else 0)
              (fun i _hi ↦ (boolIndicators_nonneg (β i)).1) hj
      have hN : 0 ≤ N.sum (fun i ↦ if β i then (0 : ℝ) else 1) := by
        exact Finset.sum_nonneg fun i _hi ↦ (boolIndicators_nonneg (β i)).2
      calc
        1 = 1 + 0 := (add_zero 1).symm
        _ ≤ P.sum (fun i ↦ if β i then (1 : ℝ) else 0) +
            N.sum (fun i ↦ if β i then (0 : ℝ) else 1) := add_le_add hP hN
    · have hN : 1 ≤ N.sum (fun i ↦ if β i then (0 : ℝ) else 1) := by
        calc
          1 = (if β j then (0 : ℝ) else 1) := by simp [hβ]
          _ ≤ N.sum (fun i ↦ if β i then (0 : ℝ) else 1) :=
            Finset.single_le_sum
              (f := fun i ↦ if β i then (0 : ℝ) else 1)
              (fun i _hi ↦ (boolIndicators_nonneg (β i)).2) hj
      have hP : 0 ≤ P.sum (fun i ↦ if β i then (1 : ℝ) else 0) := by
        exact Finset.sum_nonneg fun i _hi ↦ (boolIndicators_nonneg (β i)).1
      calc
        1 = 0 + 1 := (zero_add 1).symm
        _ ≤ P.sum (fun i ↦ if β i then (1 : ℝ) else 0) +
            N.sum (fun i ↦ if β i then (0 : ℝ) else 1) := add_le_add hP hN
  · intro hsum
    -- If neither kind of witness exists, both indicator sums vanish, contradicting the bound.
    by_contra hnone
    have hPnone : ¬ ∃ j ∈ P, β j = true := by
      intro h
      exact hnone (Or.inl h)
    have hNnone : ¬ ∃ j ∈ N, β j = false := by
      intro h
      exact hnone (Or.inr h)
    have hPzero : P.sum (fun i ↦ if β i then (1 : ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      cases hβ : β i with
      | false => simp
      | true =>
          exfalso
          apply hPnone
          use i
    have hNzero : N.sum (fun i ↦ if β i then (0 : ℝ) else 1) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      cases hβ : β i with
      | false =>
          exfalso
          apply hNnone
          use i
      | true => simp
    have himpossible : (1 : ℝ) ≤ 0 := by
      simpa [hPzero, hNzero] using hsum
    exact (not_le_of_gt zero_lt_one) himpossible

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_proposition_2_13.lean`: the true and false
real indicators over a finite set sum to its cardinality. -/
private lemma sumBoolIndicators_eq_card
    {α : Type*} (S : Finset α) (β : α → Bool) :
    S.sum (fun j ↦ if β j then (1 : ℝ) else 0) +
        S.sum (fun j ↦ if β j then (0 : ℝ) else 1) = (S.card : ℝ) := by
  -- Combine the sums pointwise; each Boolean value contributes exactly one.
  rw [← Finset.sum_add_distrib]
  calc
    S.sum (fun j ↦ (if β j then (1 : ℝ) else 0) + (if β j then 0 else 1)) =
        S.sum (fun _j ↦ (1 : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro j _hj
      cases β j <;> simp
    _ = (S.card : ℝ) := by simp

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_proposition_2_13.lean.
Proposition 2.13. For disjoint index sets `P` and `N`, the clause built from the positive and
negative literals is satisfied by a Boolean assignment exactly when the corresponding `0/1`
vector satisfies
`P.sum (fun j ↦ if β j then (1 : ℝ) else 0) - N.sum (fun j ↦ if β j then (1 : ℝ) else 0) ≥
1 - (N.card : ℝ)`. -/
theorem fromIndexSets_satisfiedBy_iff_clauseInequality
    {n : ℕ} (P N : Finset (Fin n)) (hdisj : Disjoint P N) (β : Fin n → Bool) :
    SAT.Clause.satisfiedBy (P.image SAT.Literal.pos ∪ N.image SAT.Literal.neg) β ↔
      P.sum (fun j ↦ if β j then (1 : ℝ) else 0) -
          N.sum (fun j ↦ if β j then (1 : ℝ) else 0) ≥
        1 - (N.card : ℝ) := by
  -- Retain the stated disjointness assumption while proving the stronger underlying equivalence.
  by_cases hPN : Disjoint P N
  · -- First replace satisfaction by the corresponding positive-or-negative witness.
    rw [indexSets_satisfiedBy_iff, existsTrueOrFalse_iff_one_le_indicatorSums]
    -- Complementary Boolean indicators turn the clause inequality into the normalized sum bound.
    rw [← sumBoolIndicators_eq_card N β]
    rw [add_comm (N.sum fun j ↦ if β j then (1 : ℝ) else 0)]
    rw [sub_add_eq_sub_sub]
    constructor
    · intro hsum
      exact sub_le_sub_right ((sub_le_iff_le_add).mpr hsum) _
    · intro hineq
      exact (sub_le_iff_le_add).mp ((sub_le_sub_iff_right _).mp hineq)
  · exact (hPN hdisj).elim

end SAT.Clause
