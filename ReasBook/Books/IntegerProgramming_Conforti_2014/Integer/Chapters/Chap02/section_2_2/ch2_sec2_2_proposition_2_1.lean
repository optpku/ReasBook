/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_2.ch2_sec2_2_definition_2_4.KnapsackSet
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_2.ch2_sec2_2_definition_2_4.Closure

public section

namespace ZeroOneKnapsack

open scoped BigOperators

/-- Helper for Proposition 2.1: on a binary vector, the weighted sum over a finite set keeps only
the coordinates equal to `1`. -/
private lemma weightedSum_eq_sum_filter_eq_one {ι : Type*}
    (weights : ι → ℕ) {x : ι → ℝ}
    (hBinary : ∀ i, x i = 0 ∨ x i = 1) (s : Finset ι) :
    s.sum (fun i ↦ (weights i : ℝ) * x i) =
      (s.filter (fun i ↦ x i = 1)).sum (fun i ↦ (weights i : ℝ)) := by
  classical
  -- Induct over the indexing set so each binary coordinate contributes either `0` or its weight.
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi hs
    rcases hBinary i with hxi | hxi
    · calc
        (insert i s).sum (fun j ↦ (weights j : ℝ) * x j)
            = (weights i : ℝ) * x i + s.sum (fun j ↦ (weights j : ℝ) * x j) := by
              simp [hi]
        _ = s.sum (fun j ↦ (weights j : ℝ) * x j) := by
              simp [hxi]
        _ = (s.filter (fun j ↦ x j = 1)).sum (fun j ↦ (weights j : ℝ)) := hs
        _ = ((insert i s).filter (fun j ↦ x j = 1)).sum (fun j ↦ (weights j : ℝ)) := by
              simp [Finset.filter_insert, hxi]
    · calc
        (insert i s).sum (fun j ↦ (weights j : ℝ) * x j)
            = (weights i : ℝ) * x i + s.sum (fun j ↦ (weights j : ℝ) * x j) := by
              simp [hi]
        _ = (weights i : ℝ) + s.sum (fun j ↦ (weights j : ℝ) * x j) := by
              simp [hxi]
        _ = (weights i : ℝ) + (s.filter (fun j ↦ x j = 1)).sum (fun j ↦ (weights j : ℝ)) := by
              rw [hs]
        _ = ((insert i s).filter (fun j ↦ x j = 1)).sum (fun j ↦ (weights j : ℝ)) := by
              simp [Finset.filter_insert, hi, hxi]

/-- Helper for Proposition 2.1: if every coordinate of `x` on `C` equals `1`, then the cover sum
counts the cardinality of `C`. -/
private lemma sum_eq_card_of_eq_one_on {ι : Type*} {x : ι → ℝ} {C : Finset ι}
    (hOne : ∀ i ∈ C, x i = 1) :
    C.sum x = C.card := by
  -- Replace each summand by `1`, then evaluate the constant finite sum.
  calc
    C.sum x = C.sum (fun _ ↦ (1 : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact hOne i hi
    _ = C.card := by
      simp

/-- Helper for Proposition 2.1: a binary sum over a cover with at least one zero entry satisfies
the corresponding cover inequality. -/
private lemma coverSum_le_rhs_of_binary_zero {ι : Type*}
    {x : ι → ℝ} {C : Finset ι}
    (hBinary : ∀ i, x i = 0 ∨ x i = 1)
    (hZero : ∃ i ∈ C, x i = 0) :
    C.sum x ≤ cover_inequality_rhs C := by
  classical
  rcases hZero with ⟨i, hiC, hxi0⟩
  have hEraseEq : (C.erase i).sum x = C.sum x := by
    -- Removing a zero-valued coordinate does not change the sum on the cover.
    simpa [hxi0] using C.sum_erase_add x hiC
  have hEraseLe : (C.erase i).sum x ≤ (C.erase i).card := by
    -- Every remaining binary coordinate is at most `1`, so the sum is bounded by the card.
    calc
      (C.erase i).sum x ≤ (C.erase i).sum (fun _ ↦ (1 : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        rcases hBinary j with hxj | hxj
        · simp [hxj]
        · simp [hxj]
      _ = (C.erase i).card := by
        simp
  calc
    C.sum x = (C.erase i).sum x := hEraseEq.symm
    _ ≤ (C.erase i).card := hEraseLe
    _ = (C.card : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem hiC]
      rw [Nat.cast_sub]
      · norm_num
      · exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨i, hiC⟩)
    _ = cover_inequality_rhs C := by
      rw [cover_inequality_rhs_eq]

/-- Proposition 2.1. For natural knapsack data `(weights, capacity)`, the `0`--`1` knapsack set
equals the binary set cut out by all minimal-cover inequalities. -/
theorem zero_one_knapsack_set_eq_cover_inequality_closure
    {ι : Type*} [Fintype ι] [DecidableEq ι] (weights : ι → ℕ) (capacity : ℕ) :
    zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) =
      cover_inequality_closure weights capacity := by
  ext x
  rw [mem_zero_one_knapsack_set_iff, mem_cover_inequality_closure_iff]
  constructor
  · rintro ⟨hBinary, hKnapsack⟩
    refine ⟨hBinary, ?_⟩
    intro C hCmin
    have hZero : ∃ i ∈ C, x i = 0 := by
      -- A feasible binary point cannot take the value `1` on every element of a minimal cover.
      by_contra hNoZero
      have hAllOne : ∀ i ∈ C, x i = 1 := by
        intro i hi
        rcases hBinary i with hxi | hxi
        · exfalso
          exact hNoZero ⟨i, hi, hxi⟩
        · exact hxi
      have hCoverReal : (capacity : ℝ) < C.sum (fun i ↦ (weights i : ℝ) * x i) := by
        -- On the cover itself, all binary coordinates are `1`, so the weighted sum is overweight.
        let coverWeightSum : ℕ := C.sum weights
        have hCoverNat : capacity < coverWeightSum := by
          simpa [coverWeightSum] using
            (isKnapsackCover_iff weights capacity C).mp hCmin.toIsKnapsackCover
        have hCoverNatCast : (capacity : ℝ) < (coverWeightSum : ℝ) := by
          exact_mod_cast hCoverNat
        calc
          (capacity : ℝ) < (coverWeightSum : ℝ) := hCoverNatCast
          _ = C.sum (fun i ↦ (weights i : ℝ)) := by
            rw [show coverWeightSum = C.sum weights by rfl]
            exact Nat.cast_sum C weights
          _ = C.sum (fun i ↦ (weights i : ℝ) * x i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hAllOne i hi]
      have hTermNonneg : ∀ i, 0 ≤ (weights i : ℝ) * x i := by
        -- Nonnegative weights and binary coordinates make every knapsack term nonnegative.
        intro i
        rcases hBinary i with hxi | hxi
        · simp [hxi]
        · simp [hxi]
      have hCoverLeKnapsack :
          C.sum (fun i ↦ (weights i : ℝ) * x i) ≤
            Finset.univ.sum (fun i ↦ (weights i : ℝ) * x i) := by
        -- The full knapsack sum dominates the partial sum over the minimal cover.
        simpa using Finset.sum_le_univ_sum_of_nonneg hTermNonneg
      exact (not_lt_of_ge hKnapsack) (lt_of_lt_of_le hCoverReal hCoverLeKnapsack)
    -- Once one coordinate on the cover is zero, the cover inequality follows by counting ones.
    exact coverSum_le_rhs_of_binary_zero hBinary hZero
  · rintro ⟨hBinary, hClosure⟩
    refine ⟨hBinary, ?_⟩
    by_contra hKnapsack
    let J : Finset ι := Finset.univ.filter (fun i ↦ x i = 1)
    have hJCoverReal : (capacity : ℝ) < J.sum (fun i ↦ (weights i : ℝ)) := by
      -- Rewriting the violated knapsack inequality on the support of the `1` coordinates
      -- produces an overweight candidate cover.
      calc
        (capacity : ℝ) < ∑ i, (weights i : ℝ) * x i := lt_of_not_ge hKnapsack
        _ = J.sum (fun i ↦ (weights i : ℝ)) := by
          simp [J, weightedSum_eq_sum_filter_eq_one, hBinary]
    have hJCoverNat : capacity < J.sum weights := by
      let supportWeightSum : ℕ := J.sum weights
      have hJCoverRealCast : (capacity : ℝ) < (supportWeightSum : ℝ) := by
        calc
          (capacity : ℝ) < J.sum (fun i ↦ (weights i : ℝ)) := hJCoverReal
          _ = (supportWeightSum : ℝ) := by
            rw [show supportWeightSum = J.sum weights by rfl]
            symm
            exact Nat.cast_sum J weights
      have hJCoverNat' : capacity < supportWeightSum := by
        exact_mod_cast hJCoverRealCast
      simpa [supportWeightSum] using hJCoverNat'
    have hJCover : IsKnapsackCover weights capacity J := by
      exact (isKnapsackCover_iff weights capacity J).2 hJCoverNat
    obtain ⟨C, hCJ, hCmin⟩ :=
      hJCover.exists_isMinimalKnapsackCover_subset
    have hOneOnC : ∀ i ∈ C, x i = 1 := by
      -- Every element of the extracted minimal cover lies in the support of ones.
      intro i hi
      exact (Finset.mem_filter.mp (hCJ hi)).2
    have hCardLeRhs : (C.card : ℝ) ≤ cover_inequality_rhs C := by
      -- The closure inequality contradicts the fact that all entries on `C` equal `1`.
      calc
        (C.card : ℝ) = C.sum x := by
          symm
          exact sum_eq_card_of_eq_one_on hOneOnC
        _ ≤ cover_inequality_rhs C := hClosure C hCmin
    rw [cover_inequality_rhs_eq] at hCardLeRhs
    exact (not_le_of_gt (sub_lt_self (C.card : ℝ) zero_lt_one)) hCardLeRhs

end ZeroOneKnapsack
