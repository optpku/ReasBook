/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_11.ch2_sec2_11_proposition_2_20

open scoped BigOperators Matrix

section Definition249

variable {n k : ℕ}
variable (m : Fin k → ℕ)
variable (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
variable (b : ∀ i : Fin k, Fin (m i) → ℝ)
variable (u : Fin k → Fin n → ℝ)

/-- Helper for Definition 2.49: a binary vector of total mass one has one active coordinate,
and every other coordinate vanishes. -/
private lemma exists_activeSelector_of_binary_sum_eq_one
    (x : Fin k → ℝ)
    (hBinary : ∀ i : Fin k, x i = 0 ∨ x i = 1)
    (hSum : ∑ i : Fin k, x i = (1 : ℝ)) :
    ∃ i : Fin k, x i = 1 ∧ ∀ j : Fin k, j ≠ i → x j = 0 := by
  classical
  have hNonneg : ∀ i : Fin k, 0 ≤ x i := by
    intro i
    rcases hBinary i with hi | hi
    · simp [hi]
    · simp [hi]
  have hActive : ∃ i : Fin k, x i = 1 := by
    by_contra hNoActive
    push Not at hNoActive
    have hZero : ∀ i : Fin k, x i = 0 := by
      intro i
      rcases hBinary i with hi | hi
      · exact hi
      · exact (hNoActive i hi).elim
    have hZeroSum : ∑ i : Fin k, x i = 0 := by
      simp [hZero]
    exact zero_ne_one (hZeroSum.symm.trans hSum)
  obtain ⟨i, hi⟩ := hActive
  refine ⟨i, hi, ?_⟩
  intro j hji
  have hEraseSum : (Finset.univ.erase i).sum x = 0 := by
    have hDecompose :
        (Finset.univ.erase i).sum x + x i = ∑ j : Fin k, x j :=
      Finset.sum_erase_add _ _ (Finset.mem_univ i)
    rw [hi] at hDecompose
    have hCancel : (Finset.univ.erase i).sum x + 1 = 0 + 1 := by
      calc
        (Finset.univ.erase i).sum x + 1 = ∑ j : Fin k, x j := hDecompose
        _ = 1 := hSum
        _ = 0 + 1 := (zero_add 1).symm
    exact add_right_cancel hCancel
  exact
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun l _ ↦ hNonneg l)).1 hEraseSum j (by simp [hji])

/-- Helper for Definition 2.49: a vector in a selector-scaled box vanishes when its selector
vanishes. -/
private lemma block_eq_zero_of_mem_scaledBox_of_selector_eq_zero
    (v u : Fin n → ℝ) (x : ℝ)
    (hv : v ∈ Set.Icc (0 : Fin n → ℝ) (x • u))
    (hx : x = 0) :
    v = 0 := by
  subst x
  -- The scaled upper endpoint is zero, so the two box inequalities squeeze the block to zero.
  exact le_antisymm (by simpa using hv.2) hv.1

/-- Helper for Definition 2.49: membership in one bounded branch supplies the corresponding
one-hot lifted witness. -/
private lemma oneHotBinaryWitness_of_mem_boundedBranch
    (y : Fin n → ℝ) (i : Fin k)
    (hy : y ∈ polyhedron_le_set (A i) (b i) ∩ Set.Icc (0 : Fin n → ℝ) (u i)) :
    ∃ x : Fin k → ℝ, ∃ yParts : Fin k → Fin n → ℝ,
      (∑ j : Fin k, yParts j, ∑ j : Fin k, x j) = (y, (1 : ℝ)) ∧
        (∀ j : Fin k,
          yParts j ∈ polyhedron_le_set (A j) (x j • b j) ∩
            Set.Icc (0 : Fin n → ℝ) (x j • u j)) ∧
        (∀ j : Fin k, x j ∈ ({0, 1} : Set ℝ)) := by
  classical
  refine ⟨Pi.single i 1, Pi.single i y, ?_, ?_, ?_⟩
  · -- Both finite sums retain only the active coordinate.
    apply Prod.ext
    · simp
    · simp
  · -- The active block is the given branch point; every inactive block is identically zero.
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hy
    · simp [polyhedron_le_set, hji]
  · -- A one-hot selector takes only the values zero and one.
    intro j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_11/ch2_sec2_11_definition_2_49.lean

Definition 2.49: a point belongs to the union of the bounded branch polyhedra
`polyhedron_le_set (A i) (b i) ∩ Set.Icc 0 (u i)` exactly when it admits binary selector
variables and block vectors satisfying the explicit bounded lifted system. -/
theorem mem_iUnion_boundedPolyhedra_iff_exists_binary_witness
    (y : Fin n → ℝ) :
    y ∈ ⋃ i : Fin k, polyhedron_le_set (A i) (b i) ∩ Set.Icc (0 : Fin n → ℝ) (u i) ↔
      ∃ x : Fin k → ℝ, ∃ yParts : Fin k → Fin n → ℝ,
        (∑ i : Fin k, yParts i, ∑ i : Fin k, x i) = (y, (1 : ℝ)) ∧
          (∀ i : Fin k,
            yParts i ∈ polyhedron_le_set (A i) (x i • b i) ∩
              Set.Icc (0 : Fin n → ℝ) (x i • u i)) ∧
          (∀ i : Fin k, x i ∈ ({0, 1} : Set ℝ)) := by
  constructor
  · intro hy
    -- Choose the branch containing `y` and use its canonical one-hot witness.
    rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
    exact oneHotBinaryWitness_of_mem_boundedBranch m A b u y i hi
  · rintro ⟨x, yParts, hSum, hBlocks, hBinarySet⟩
    -- Split the paired normalization equation and convert set membership to binary equations.
    have hySum : ∑ i : Fin k, yParts i = y := congrArg Prod.fst hSum
    have hxSum : ∑ i : Fin k, x i = (1 : ℝ) := congrArg Prod.snd hSum
    have hBinary : ∀ i : Fin k, x i = 0 ∨ x i = 1 := by
      intro i
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hBinarySet i
    obtain ⟨i, hi, hInactive⟩ :=
      exists_activeSelector_of_binary_sum_eq_one x hBinary hxSum
    have hInactiveBlocks : ∀ j : Fin k, j ≠ i → yParts j = 0 := by
      intro j hji
      exact block_eq_zero_of_mem_scaledBox_of_selector_eq_zero
        (yParts j) (u j) (x j) (hBlocks j).2 (hInactive j hji)
    have hPartsSum : (∑ j : Fin k, yParts j) = yParts i := by
      rw [Finset.sum_eq_single i]
      · intro j _ hji
        exact hInactiveBlocks j hji
      · simp
    have hiPart : yParts i = y := hPartsSum.symm.trans hySum
    have hiBlock :
        y ∈ polyhedron_le_set (A i) (b i) ∩ Set.Icc (0 : Fin n → ℝ) (u i) := by
      simpa [hi, hiPart] using hBlocks i
    -- The unique active block recovers `y`, hence witnesses membership in the union.
    exact Set.mem_iUnion.mpr ⟨i, hiBlock⟩

/-- The bounded-union membership statement is equivalently membership in the canonical
`Disjunctive.boundedLiftedSet` for some block decomposition and selector vector. -/
theorem mem_iUnion_boundedPolyhedra_iff_mem_boundedLiftedSet
    (y : Fin n → ℝ) :
    y ∈ ⋃ i : Fin k, polyhedron_le_set (A i) (b i) ∩ Set.Icc (0 : Fin n → ℝ) (u i) ↔
      ∃ yParts : Fin k → Fin n → ℝ, ∃ x : Fin k → ℝ,
        (y, yParts, x) ∈ Disjunctive.boundedLiftedSet m A b u := by
  constructor
  · intro hy
    -- Repackage the explicit binary witness through the lifted-set membership theorem.
    rcases (mem_iUnion_boundedPolyhedra_iff_exists_binary_witness m A b u y).1 hy with
      ⟨x, yParts, hSum, hBlocks, hBinarySet⟩
    have hySum : ∑ i : Fin k, yParts i = y := congrArg Prod.fst hSum
    have hxSum : ∑ i : Fin k, x i = (1 : ℝ) := congrArg Prod.snd hSum
    have hBinary : ∀ i : Fin k, x i = 0 ∨ x i = 1 := by
      intro i
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hBinarySet i
    refine ⟨yParts, x, (Disjunctive.mem_boundedLiftedSet_iff m A b u y yParts x).2 ?_⟩
    exact ⟨hySum, fun i ↦ (hBlocks i).1, fun i ↦ (hBlocks i).2, hBinary, hxSum⟩
  · rintro ⟨yParts, x, hLifted⟩
    -- Expand canonical lifted-set membership and restore the paired explicit witness equation.
    rcases (Disjunctive.mem_boundedLiftedSet_iff m A b u y yParts x).1 hLifted with
      ⟨hySum, hPolyhedra, hBoxes, hBinary, hxSum⟩
    refine (mem_iUnion_boundedPolyhedra_iff_exists_binary_witness m A b u y).2 ?_
    refine ⟨x, yParts, Prod.ext hySum hxSum, ?_, ?_⟩
    · intro i
      exact ⟨hPolyhedra i, hBoxes i⟩
    · intro i
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hBinary i

end Definition249
