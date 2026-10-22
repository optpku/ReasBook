/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped ENNReal

universe u

variable {Ω : Type u} {C : Set (Set Ω)} {μ : AddContent ℝ≥0∞ C}

-- Proof sketch: write `A ∪ B` as the disjoint union of `A` and `B \ A`, and write `B` as the
-- disjoint union of `A ∩ B` and `B \ A`; additivity on the ring gives the two equalities whose
-- common `μ (B \ A)` term cancels.
/-- Lemma 1.31 (1): Part (i). On a ring of sets, a content satisfies the inclusion-exclusion
identity `μ (A ∪ B) + μ (A ∩ B) = μ A + μ B`. -/
lemma addContent_union_add_inter (hC : IsSetRing C) {A B : Set Ω} (hA : A ∈ C) (hB : B ∈ C) :
    μ (A ∪ B) + μ (A ∩ B) = μ A + μ B := by
  let D := B \ A
  have hD : D ∈ C := hC.diff_mem hB hA
  have hInter : A ∩ B ∈ C := hC.inter_mem hA hB
  have h_union_decomp : μ (A ∪ B) = μ A + μ D := by
    -- Rewrite `A ∪ B` as the disjoint union of `A` and `B \ A`.
    calc
      μ (A ∪ B) = μ (A ∪ D) := by
        congr 1
        ext x
        by_cases hxA : x ∈ A
        · simp [D, hxA]
        · simp [D, hxA]
      _ = μ A + μ D := MeasureTheory.addContent_union hC hA hD Set.disjoint_sdiff_right
  have h_right_decomp : μ B = μ (A ∩ B) + μ D := by
    -- Rewrite `B` as the disjoint union of `A ∩ B` and `B \ A`.
    calc
      μ B = μ ((A ∩ B) ∪ D) := by
        congr 1
        ext x
        by_cases hxA : x ∈ A
        · simp [D, hxA]
        · simp [D, hxA]
      _ = μ (A ∩ B) + μ D := by
        refine MeasureTheory.addContent_union hC hInter hD ?_
        rw [Set.disjoint_left]
        intro x hxInter hxD
        exact hxD.2 hxInter.1
  -- Combine the two decompositions and reassociate the `ENNReal` sums.
  calc
    μ (A ∪ B) + μ (A ∩ B) = (μ A + μ D) + μ (A ∩ B) := by rw [h_union_decomp]
    _ = μ A + (μ (A ∩ B) + μ D) := by
      rw [add_assoc, add_comm (μ D) (μ (A ∩ B))]
    _ = μ A + μ B := by rw [h_right_decomp]

/-- Lemma 1.31 (2): Part (ii). A content on a semiring of sets is monotone. -/
recall MeasureTheory.addContent_mono

-- Proof sketch: in a ring of sets one has the disjoint decomposition `B = A ∪ (B \ A)` whenever
-- `A ⊆ B`; apply additivity to this union.
/-- Lemma 1.31 (3): Part (ii). On a ring of sets, if `A ⊆ B`, then `μ B = μ A + μ (B \ A)`. -/
lemma addContent_eq_add_diff_of_subset (hC : IsSetRing C) {A B : Set Ω}
    (hA : A ∈ C) (hB : B ∈ C) (hAB : A ⊆ B) :
    μ B = μ A + μ (B \ A) := by
  have hDiff : B \ A ∈ C := hC.diff_mem hB hA
  -- Apply additivity to the disjoint decomposition `B = A ⊔ (B \ A)`.
  simpa [Set.union_diff_cancel hAB] using
    (MeasureTheory.addContent_union hC hA hDiff Set.disjoint_sdiff_right : μ (A ∪ (B \ A)) = _)

/-- Lemma 1.31 (4): Part (iii). A content on a semiring of sets is finitely subadditive on finite
semiring covers. -/
recall MeasureTheory.addContent_le_sum_of_subset_sUnion

/-- Lemma 1.31 (5): Part (iii). On a ring of sets, countable additivity on pairwise disjoint
sequences implies sigma-subadditivity. -/
recall MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum

-- Proof sketch: every finite partial sum equals the content of the corresponding finite disjoint
-- union, and this finite union is contained in the full union; monotonicity bounds each partial
-- sum by `μ (⋃ n, A n)`, then pass to the `tsum`.
/-- Helper for Lemma 1.31: every finite partial sum of a pairwise disjoint sequence is bounded by
the content of the full union. -/
lemma sum_addContent_range_le_iUnion (hC : IsSetRing C) {A : ℕ → Set Ω}
    (hA : ∀ n, A n ∈ C) (hdisj : Pairwise fun i j ↦ Disjoint (A i) (A j))
    (hUnion : (⋃ n, A n) ∈ C) (n : ℕ) :
    ∑ i ∈ Finset.range n, μ (A i) ≤ μ (⋃ i, A i) := by
  classical
  have hFiniteUnion_mem : (⋃ i ∈ Finset.range n, A i) ∈ C := by
    exact hC.biUnion_mem (Finset.range n) (fun i _ ↦ hA i)
  have hFiniteUnion_eq :
      μ (⋃ i ∈ Finset.range n, A i) = ∑ i ∈ Finset.range n, μ (A i) := by
    -- The finite union is disjoint because the whole sequence is pairwise disjoint.
    exact MeasureTheory.addContent_biUnion_eq hC
      (fun i _ ↦ hA i)
      (by
        intro i hi j hj hij
        exact hdisj hij)
  have hsubset : (⋃ i ∈ Finset.range n, A i) ⊆ ⋃ i, A i := by
    -- Every point in the finite-stage union already lies in the full union.
    intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    rcases hx with ⟨i, hi, hxi⟩
    exact ⟨i, hxi⟩
  have hmono : μ (⋃ i ∈ Finset.range n, A i) ≤ μ (⋃ i, A i) := by
    exact MeasureTheory.addContent_mono (m := μ) hC.isSetSemiring hFiniteUnion_mem hUnion hsubset
  -- Rewrite the left-hand side by the finite disjoint-union formula.
  rw [hFiniteUnion_eq] at hmono
  exact hmono

/-- Lemma 1.31 (6): Part (iv). On a ring of sets, the sum of the values of a pairwise disjoint
sequence is bounded above by the value of its union whenever that union belongs to the ring. -/
lemma tsum_addContent_le_of_disjoint_iUnion (hC : IsSetRing C) {A : ℕ → Set Ω}
    (hA : ∀ n, A n ∈ C) (hdisj : Pairwise fun i j ↦ Disjoint (A i) (A j))
    (hUnion : (⋃ n, A n) ∈ C) :
    (∑' n, μ (A n)) ≤ μ (⋃ n, A n) := by
  -- Bound each finite partial sum by the content of the full union.
  refine ENNReal.tsum_le_of_sum_range_le fun n ↦ ?_
  exact sum_addContent_range_le_iUnion hC hA hdisj hUnion n
