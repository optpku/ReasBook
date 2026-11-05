/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3.ch4_sec4_3_definition_4_3_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_corollary_4_8

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: this file reuses the chapter owner `digraph_incidence_matrix` together
-- with Mathlib's canonical `Matrix.IsTotallyUnimodular` API.

open scoped BigOperators Matrix

section Theorem49

variable {V A : Type}

/-- The chapter digraph incidence matrix is a `(0, ±1)`-matrix. -/
theorem digraph_incidence_matrix_hasZeroOneNegOneEntries
    (tail head : A → V) :
    HasZeroOneNegOneEntries (digraph_incidence_matrix ℤ tail head) := by
  rw [hasZeroOneNegOneEntries_iff]
  intro v a
  by_cases hhead : v = head a
  · by_cases htail : v = tail a
    · left
      have hloop : head a = tail a := hhead.symm.trans htail
      simp [digraph_incidence_matrix, hhead, hloop]
    · right
      left
      have hne : tail a ≠ head a := fun h ↦ htail (hhead.trans h.symm)
      simpa [hhead] using digraph_incidence_matrix_head ℤ tail head a hne
  · by_cases htail : v = tail a
    · right
      right
      have hne : tail a ≠ head a := fun h ↦ hhead (htail.trans h)
      simpa [htail] using digraph_incidence_matrix_tail ℤ tail head a hne
    · left
      simpa using
        digraph_incidence_matrix_eq_zero_of_ne_endpoints ℤ tail head htail hhead

private lemma digraph_incidence_matrix_submatrix_nonzero_eq_head_or_tail
    (tail head : A → V)
    {k : ℕ} {f : Fin k → V} {g : Fin k → A} {i j : Fin k}
    (hij :
      ((digraph_incidence_matrix ℤ tail head).submatrix f g) i j ≠ 0) :
    f i = head (g j) ∨ f i = tail (g j) := by
  by_cases hhead : f i = head (g j)
  · exact Or.inl hhead
  · by_cases htail : f i = tail (g j)
    · exact Or.inr htail
    · exact (hij (by simp [digraph_incidence_matrix, hhead, htail])).elim

private lemma digraph_incidence_matrix_submatrix_hasAtMostTwoNonzeroEntriesPerColumn
    (tail head : A → V)
    {k : ℕ} {f : Fin k → V} {g : Fin k → A}
    (hf : Function.Injective f) :
    HasAtMostTwoNonzeroEntriesPerColumn ((digraph_incidence_matrix ℤ tail head).submatrix f g) := by
  classical
  intro j
  let s : Finset (Fin k) :=
    Finset.univ.filter fun i ↦ ((digraph_incidence_matrix ℤ tail head).submatrix f g) i j ≠ 0
  have hs :
      s.image f ⊆ ({tail (g j), head (g j)} : Finset V) := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    rcases digraph_incidence_matrix_submatrix_nonzero_eq_head_or_tail tail head
        (Finset.mem_filter.mp hi).2 with h | h
    · simp [h]
    · simp [h]
  calc
    s.card = (s.image f).card := by
      symm
      exact Finset.card_image_of_injective s hf
    _ ≤ ({tail (g j), head (g j)} : Finset V).card := Finset.card_le_card hs
    _ ≤ 2 := by
      have hcard :
          ({tail (g j), head (g j)} : Finset V).card = 1 ∨
            ({tail (g j), head (g j)} : Finset V).card = 2 :=
        Finset.card_pair_eq_one_or_two
      omega

private lemma digraph_incidence_matrix_submatrix_is_equitable_row_bicoloring
    (tail head : A → V)
    {k : ℕ} {f : Fin k → V} {g : Fin k → A}
    (hf : Function.Injective f) :
    is_equitable_row_bicoloring
      ((digraph_incidence_matrix ℤ tail head).submatrix f g) Finset.univ ∅ := by
  classical
  rw [is_equitable_row_bicoloring_iff]
  refine ⟨Finset.disjoint_empty_right _, by simp, ?_⟩
  intro j
  rw [row_bicoloring_difference_apply, Finset.sum_empty, sub_zero]
  have hsum :
      (∑ i, ((digraph_incidence_matrix ℤ tail head).submatrix f g) i j) =
        (Finset.univ.image f).sum (fun v ↦ digraph_incidence_matrix ℤ tail head v (g j)) := by
    symm
    exact Finset.sum_image hf.injOn
  have hvalue :
    ∑ i, ((digraph_incidence_matrix ℤ tail head).submatrix f g) i j
        = (Finset.univ.image f).sum (fun v ↦ digraph_incidence_matrix ℤ tail head v (g j)) := hsum
  have hdiff :
      ∑ i, ((digraph_incidence_matrix ℤ tail head).submatrix f g) i j
        = (if head (g j) ∈ Finset.univ.image f then (1 : ℤ) else 0) -
            (if tail (g j) ∈ Finset.univ.image f then 1 else 0) := by
    exact hvalue.trans (by simp [digraph_incidence_matrix, Finset.sum_sub_distrib])
  rw [hdiff]
  by_cases hhead : head (g j) ∈ Finset.univ.image f <;>
    by_cases htail : tail (g j) ∈ Finset.univ.image f <;>
    simp [hhead, htail]

/-- Theorem 4.9. Incidence matrices of digraphs are totally unimodular. -/
theorem digraph_incidence_matrix_is_totally_unimodular
    (tail head : A → V) :
    (digraph_incidence_matrix ℤ tail head).IsTotallyUnimodular := by
  unfold Matrix.IsTotallyUnimodular
  intro k f g hf hg
  let B : Matrix (Fin k) (Fin k) ℤ := (digraph_incidence_matrix ℤ tail head).submatrix f g
  have hB01 : HasZeroOneNegOneEntries B := by
    dsimp [B]
    exact (digraph_incidence_matrix_hasZeroOneNegOneEntries tail head).submatrix f g
  have hBcol : HasAtMostTwoNonzeroEntriesPerColumn B := by
    dsimp [B]
    exact digraph_incidence_matrix_submatrix_hasAtMostTwoNonzeroEntriesPerColumn tail head hf
  have hBcolor : ∃ red blue : Finset (Fin k), is_equitable_row_bicoloring B red blue := by
    refine ⟨Finset.univ, ∅, ?_⟩
    dsimp [B]
    exact digraph_incidence_matrix_submatrix_is_equitable_row_bicoloring tail head hf
  have hBTU : B.IsTotallyUnimodular :=
    (totally_unimodular_iff_admits_equitable_row_bicoloring_of_column_support_card_le_two
      B hB01 hBcol).2 hBcolor
  simpa [B] using ((Matrix.isTotallyUnimodular_iff B).1 hBTU) k id id

end Theorem49
