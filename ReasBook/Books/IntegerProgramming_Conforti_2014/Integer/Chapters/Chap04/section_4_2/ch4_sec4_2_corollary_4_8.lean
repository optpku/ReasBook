/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_corollary_4_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_definition_4_2_extra_4
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_definition_4_2_extra_3

-- Declarations for this item will be appended below by the statement pipeline.

-- Core/canonical owner: `Matrix.IsTotallyUnimodular`.
-- Bridge/view owner: `is_equitable_row_bicoloring`.
-- Source-facing extra hypothesis owner: `HasZeroOneNegOneEntries`.

open scoped BigOperators

universe u v w

section Corollary48

variable {m : Type u} {n : Type v}

variable [Fintype m] [DecidableEq m]

/-- An integer matrix has at most two nonzero entries in each column when every column support has
cardinality at most `2`. -/
def HasAtMostTwoNonzeroEntriesPerColumn (A : Matrix m n ℤ) : Prop :=
  ∀ j, (Finset.univ.filter fun i ↦ A i j ≠ 0).card ≤ 2

namespace HasAtMostTwoNonzeroEntriesPerColumn

/-- Helper for Corollary 4.8: the two-nonzero-per-column condition is preserved by restricting to
any row submatrix. -/
theorem submatrix
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    {A : Matrix m n ℤ}
    (hcol : HasAtMostTwoNonzeroEntriesPerColumn A)
    (row : ι ↪ m) :
    HasAtMostTwoNonzeroEntriesPerColumn (A.submatrix row id) := by
  intro j
  let s : Finset ι := Finset.univ.filter fun i ↦ A (row i) j ≠ 0
  let t : Finset m := Finset.univ.filter fun i ↦ A i j ≠ 0
  have hs : s.image row ⊆ t := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨i', hi', rfl⟩
    exact Finset.mem_filter.mpr ⟨by simp, (Finset.mem_filter.mp hi').2⟩
  -- Count the restricted support by embedding it into the original support.
  calc
    (Finset.univ.filter fun i ↦ (A.submatrix row id) i j ≠ 0).card = s.card := by
      simp [s]
    _ = (s.image row).card := by
      symm
      exact Finset.card_image_of_injective s row.injective
    _ ≤ t.card := Finset.card_le_card hs
    _ = (Finset.univ.filter fun i ↦ A i j ≠ 0).card := by
      simp [t]
    _ ≤ 2 := hcol j

end HasAtMostTwoNonzeroEntriesPerColumn

/-- Helper for Corollary 4.8: a finite sum collapses to one term when every other index
contributes `0`. -/
lemma sum_eq_if_mem_of_eq_zero_off_singleton
    {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (s : Finset α) (f : α → β) (a : α)
    (hzero : ∀ x ∈ s, x ≠ a → f x = 0) :
    s.sum f = if a ∈ s then f a else 0 := by
  by_cases ha : a ∈ s
  · -- When `a` is present, every other summand vanishes.
    rw [if_pos ha, Finset.sum_eq_single_of_mem a ha]
    intro b hb hba
    exact hzero b hb hba
  · -- When `a` is absent, all summands vanish.
    rw [if_neg ha]
    refine Finset.sum_eq_zero ?_
    intro b hb
    exact hzero b hb (fun hba ↦ ha (hba ▸ hb))

/-- Helper for Corollary 4.8: if every nonzero row of a fixed column lies in the row embedding
image, then restricting the red and blue row sets along that embedding preserves the column
difference. -/
lemma row_bicoloring_difference_submatrix_restrict_eq_of_nonzero_mem_image
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    {A : Matrix m n ℤ}
    (row : ι ↪ m) (red blue : Finset m) (j : n)
    (himg : ∀ i : m, A i j ≠ 0 → i ∈ Set.range row) :
    row_bicoloring_difference (A.submatrix row id)
        (red.preimage row row.injective.injOn)
        (blue.preimage row row.injective.injOn) j
      = row_bicoloring_difference A red blue j := by
  classical
  rw [row_bicoloring_difference_apply, row_bicoloring_difference_apply]
  simp only [Matrix.submatrix_apply]
  have hred :
      (red.preimage row row.injective.injOn).sum (fun i ↦ A (row i) j) =
        red.sum (fun i ↦ A i j) := by
    -- First push the sum forward along the embedding.
    calc
      (red.preimage row row.injective.injOn).sum (fun i ↦ A (row i) j)
          = ((red.preimage row row.injective.injOn).image row).sum (fun i ↦ A i j) := by
              symm
              exact Finset.sum_image row.injective.injOn
      _ = ({i ∈ red | i ∈ Set.range row}).sum (fun i ↦ A i j) := by
            rw [Finset.image_preimage row red row.injective.injOn]
      _ = red.sum (fun i ↦ A i j) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hir : i ∈ Set.range row
            · simp [hir]
            · have hzero : A i j = 0 := by
                by_contra hne
                exact hir (himg i hne)
              simp [hir, hzero]
  have hblue :
      (blue.preimage row row.injective.injOn).sum (fun i ↦ A (row i) j) =
        blue.sum (fun i ↦ A i j) := by
    -- The same pushforward argument applies to the blue rows.
    calc
      (blue.preimage row row.injective.injOn).sum (fun i ↦ A (row i) j)
          = ((blue.preimage row row.injective.injOn).image row).sum (fun i ↦ A i j) := by
              symm
              exact Finset.sum_image row.injective.injOn
      _ = ({i ∈ blue | i ∈ Set.range row}).sum (fun i ↦ A i j) := by
            rw [Finset.image_preimage row blue row.injective.injOn]
      _ = blue.sum (fun i ↦ A i j) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hir : i ∈ Set.range row
            · simp [hir]
            · have hzero : A i j = 0 := by
                by_contra hne
                exact hir (himg i hne)
              simp [hir, hzero]
  -- Both red and blue sums match the original column sums.
  simpa using congrArg₂ (fun a b : ℤ ↦ a - b) hred hblue

/-- Helper for Corollary 4.8: restricting an equitable row-bicoloring along a row embedding keeps
each column balanced when every column has support of size at most two. -/
lemma restricted_row_bicoloring_balance_of_column_support_card_le_two
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    {A : Matrix m n ℤ}
    (hA : HasZeroOneNegOneEntries A)
    (hcol : HasAtMostTwoNonzeroEntriesPerColumn A)
    {red blue : Finset m}
    (hColor : is_equitable_row_bicoloring A red blue)
    (row : ι ↪ m) :
    ∀ j : n,
      row_bicoloring_difference (A.submatrix row id)
          (red.preimage row row.injective.injOn)
          (blue.preimage row row.injective.injOn) j = 0 ∨
        row_bicoloring_difference (A.submatrix row id)
            (red.preimage row row.injective.injOn)
            (blue.preimage row row.injective.injOn) j = 1 ∨
          row_bicoloring_difference (A.submatrix row id)
              (red.preimage row row.injective.injOn)
              (blue.preimage row row.injective.injOn) j = -1 := by
  classical
  have hDisj := hColor.disjoint
  rw [Finset.disjoint_left] at hDisj
  intro j
  let support : Finset ι := Finset.univ.filter fun i ↦ A (row i) j ≠ 0
  have hsupportCard : support.card ≤ 2 := by
    simpa [support] using (HasAtMostTwoNonzeroEntriesPerColumn.submatrix hcol row) j
  have hcases : support.card = 0 ∨ support.card = 1 ∨ support.card = 2 := by
    omega
  rcases hcases with hzero | hone | htwo
  · have hsupport : support = ∅ := Finset.card_eq_zero.mp hzero
    have hsZero : ∀ i : ι, A (row i) j = 0 := by
      intro i
      by_contra hne
      have hi : i ∈ support := by
        simp [support, hne]
      simp [hsupport] at hi
    -- When the restricted support is empty, the column difference is `0`.
    left
    rw [row_bicoloring_difference_apply]
    simp [hsZero]
  · obtain ⟨i, hsupport⟩ := Finset.card_eq_one.mp hone
    have hiSupport : i ∈ support := by
      simp [hsupport]
    have hnonzero : A (row i) j ≠ 0 := (Finset.mem_filter.mp hiSupport).2
    have hsZero : ∀ i' : ι, i' ≠ i → A (row i') j = 0 := by
      intro i' hi'
      by_contra hne
      have hi'Support : i' ∈ support := by
        simp [support, hne]
      have : i' = i := by
        simpa [hsupport] using hi'Support
      exact hi' this
    have hentry : A (row i) j = 1 ∨ A (row i) j = -1 := by
      rcases HasZeroOneNegOneEntries.apply hA (row i) j with hzero0 | hone0 | hneg0
      · exact False.elim (hnonzero hzero0)
      · exact Or.inl hone0
      · exact Or.inr hneg0
    rcases is_equitable_row_bicoloring.mem_red_or_mem_blue hColor (row i) with hred | hblue
    · have hnotBlue : row i ∉ blue := fun hmem ↦ hDisj hred hmem
      have hredSum :
          (red.preimage row row.injective.injOn).sum (fun i' ↦ A (row i') j) = A (row i) j := by
        -- A singleton support leaves only the selected red row contribution.
        simpa [hred] using
          sum_eq_if_mem_of_eq_zero_off_singleton
            (red.preimage row row.injective.injOn)
            (fun i' ↦ A (row i') j) i
            (fun i' _ hi' ↦ hsZero i' hi')
      have hblueSum :
          (blue.preimage row row.injective.injOn).sum (fun i' ↦ A (row i') j) = 0 := by
        -- No blue row contributes at the unique nonzero position.
        simpa [hnotBlue] using
          sum_eq_if_mem_of_eq_zero_off_singleton
            (blue.preimage row row.injective.injOn)
            (fun i' ↦ A (row i') j) i
            (fun i' _ hi' ↦ hsZero i' hi')
      rw [row_bicoloring_difference_apply]
      simp [Matrix.submatrix_apply]
      rw [hredSum, hblueSum, sub_zero]
      rcases hentry with hone' | hneg'
      · exact Or.inr (Or.inl hone')
      · exact Or.inr (Or.inr hneg')
    · have hnotRed : row i ∉ red := fun hmem ↦ hDisj hmem hblue
      have hredSum :
          (red.preimage row row.injective.injOn).sum (fun i' ↦ A (row i') j) = 0 := by
        -- No red row contributes at the unique nonzero position.
        simpa [hnotRed] using
          sum_eq_if_mem_of_eq_zero_off_singleton
            (red.preimage row row.injective.injOn)
            (fun i' ↦ A (row i') j) i
            (fun i' _ hi' ↦ hsZero i' hi')
      have hblueSum :
          (blue.preimage row row.injective.injOn).sum (fun i' ↦ A (row i') j) = A (row i) j := by
        -- A singleton support leaves only the selected blue row contribution.
        simpa [hblue] using
          sum_eq_if_mem_of_eq_zero_off_singleton
            (blue.preimage row row.injective.injOn)
            (fun i' ↦ A (row i') j) i
            (fun i' _ hi' ↦ hsZero i' hi')
      rw [row_bicoloring_difference_apply]
      simp [Matrix.submatrix_apply]
      rw [hredSum, hblueSum]
      rcases hentry with hone' | hneg'
      · right
        right
        simpa [hone']
      · right
        left
        simpa [hneg']
  · let supportM : Finset m := Finset.univ.filter fun i ↦ A i j ≠ 0
    have hsubset : support.image row ⊆ supportM := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨i', hi', rfl⟩
      exact Finset.mem_filter.mpr ⟨by simp, (Finset.mem_filter.mp hi').2⟩
    have himageCard : (support.image row).card = 2 := by
      rw [Finset.card_image_of_injective support row.injective, htwo]
    have hsupportEq : support.image row = supportM := by
      apply Finset.eq_of_subset_of_card_le hsubset
      rw [himageCard]
      exact hcol j
    have himg : ∀ i : m, A i j ≠ 0 → i ∈ Set.range row := by
      intro i hi
      have hiMem : i ∈ supportM := by
        exact Finset.mem_filter.mpr ⟨by simp, hi⟩
      have hiImage : i ∈ support.image row := by
        simpa [hsupportEq] using hiMem
      rcases Finset.mem_image.mp hiImage with ⟨i', _, hi'⟩
      exact ⟨i', hi'⟩
    -- When both possible nonzero rows survive the restriction, the column difference is unchanged.
    rw [row_bicoloring_difference_submatrix_restrict_eq_of_nonzero_mem_image row red blue j himg]
    exact hColor.column_balance j

/-- Helper for Corollary 4.8: restricting an equitable row-bicoloring along a row embedding
produces an equitable row-bicoloring of the row submatrix. -/
lemma is_equitable_row_bicoloring.submatrix_of_column_support_card_le_two
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    {A : Matrix m n ℤ}
    (hA : HasZeroOneNegOneEntries A)
    (hcol : HasAtMostTwoNonzeroEntriesPerColumn A)
    {red blue : Finset m}
    (hColor : is_equitable_row_bicoloring A red blue)
    (row : ι ↪ m) :
    ∃ red' blue' : Finset ι,
      is_equitable_row_bicoloring (A.submatrix row id) red' blue' := by
  classical
  let red' : Finset ι := red.preimage row row.injective.injOn
  let blue' : Finset ι := blue.preimage row row.injective.injOn
  have hDisj := hColor.disjoint
  have hCover := hColor.cover
  refine ⟨red', blue', ?_⟩
  rw [is_equitable_row_bicoloring_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- Disjointness survives by taking preimages along the embedding.
    simpa [red', blue'] using
      (Finset.disjoint_preimage (f := row) (s := red) (t := blue) hDisj)
  · -- The restricted red and blue sets still cover all rows of the submatrix.
    calc
      red' ∪ blue'
          = (red ∪ blue).preimage row row.injective.injOn := by
              symm
              simpa [red', blue'] using
                (Finset.preimage_union (f := row) (s := red) (t := blue) row.injective.injOn)
      _ = Finset.univ := by
            rw [hCover, Finset.preimage_univ]
  · -- The balance condition is exactly the restricted-balance lemma above.
    exact restricted_row_bicoloring_balance_of_column_support_card_le_two hA hcol hColor row

/-- Corollary 4.8. A `(0, ±1)` matrix `A` with at most two nonzero elements in each column is
totally unimodular if and only if `A` admits an equitable row-bicoloring. -/
theorem totally_unimodular_iff_admits_equitable_row_bicoloring_of_column_support_card_le_two
    (A : Matrix m n ℤ)
    (hA : HasZeroOneNegOneEntries A)
    (hcol : HasAtMostTwoNonzeroEntriesPerColumn A) :
    A.IsTotallyUnimodular ↔
      ∃ red blue : Finset m, is_equitable_row_bicoloring A red blue := by
  constructor
  · intro hTU
    let row : m ↪ m := Function.Embedding.refl m
    obtain ⟨red, blue, hColor⟩ :=
      (totally_unimodular_iff_every_row_submatrix_admits_equitable_row_bicoloring A).1 hTU row
    -- Apply Corollary 4.7 to the identity row embedding to recover a coloring of `A` itself.
    refine ⟨red, blue, ?_⟩
    simpa [row, Matrix.submatrix_id_id] using hColor
  · rintro ⟨red, blue, hColor⟩
    -- Route correction: use Corollary 4.7's row-submatrix criterion and restrict the given
    -- coloring along each row embedding, rather than switching to a determinant-by-determinant
    -- argument.
    have hRow :
        ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (row : ι ↪ m),
          ∃ red' blue' : Finset ι,
            is_equitable_row_bicoloring (A.submatrix row id) red' blue' := by
      intro ι _ _ row
      exact
        is_equitable_row_bicoloring.submatrix_of_column_support_card_le_two
          hA hcol hColor row
    exact
      (totally_unimodular_iff_every_row_submatrix_admits_equitable_row_bicoloring.{u, v, u}
        A).2 hRow

end Corollary48
