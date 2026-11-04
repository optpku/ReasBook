/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_corollary_4_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_definition_4_2_extra_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix

universe u v w x

-- The statements below use mathlib's canonical `Matrix.IsTotallyUnimodular` API together with the
-- Chapter 4 owners `HasZeroOneNegOneEntries` and `is_equitable_row_bicoloring`, plus a
-- source-facing square-submatrix obstruction phrased in the chapter's standard finite-index
-- embedding language.

section Theorem59

variable {m : Type u} {n : Type v}

/-- A square integer matrix has even nonzero support in every row and column when each row and
each column contains an even number of nonzero entries. -/
def HasEvenNonzeroSupportInRowsAndCols {ι : Type*} [Fintype ι] (B : Matrix ι ι ℤ) : Prop :=
  (∀ i, Even (Function.support (B i)).ncard) ∧
    ∀ j, Even (Function.support fun i ↦ B i j).ncard

/-- The half-sum of the entries of a square integer matrix is odd when the total sum of its
entries is twice an odd integer. -/
def HasOddHalfEntrySum {ι : Type*} [Fintype ι] (B : Matrix ι ι ℤ) : Prop :=
  ∃ t : ℤ, (∑ i, ∑ j, B i j) = 2 * t ∧ Odd t

/-- Helper for Theorem 4.59: `HasOddHalfEntrySum B` is equivalent to the total entry sum of `B`
being congruent to `2` modulo `4`. -/
lemma hasOddHalfEntrySum_iff_totalEqTwoModFour
    {ι : Type*} [Fintype ι] (B : Matrix ι ι ℤ) :
    HasOddHalfEntrySum B ↔ ∃ u : ℤ, (∑ i, ∑ j, B i j) = 2 + 4 * u := by
  constructor
  · rintro ⟨t, ht, hOdd⟩
    rcases hOdd with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    calc
      (∑ i, ∑ j, B i j) = 2 * t := ht
      _ = 2 * (u + u + 1) := by
        rw [hu]
        ring
      _ = 2 + 4 * u := by ring
  · rintro ⟨u, hu⟩
    refine ⟨2 * u + 1, ?_, ?_⟩
    · calc
        (∑ i, ∑ j, B i j) = 2 + 4 * u := hu
        _ = 2 * (2 * u + 1) := by ring
    · refine ⟨u, ?_⟩
      ring

/-- A matrix contains an even-support odd-half-sum square submatrix when some square submatrix has
an even number of nonzero entries in each row and column and has odd half entry sum. -/
def HasEvenSupportOddHalfSumSquareSubmatrix
    (A : Matrix m n ℤ) : Prop :=
  ∃ (ι : Type*) (_ : Fintype ι) (row : ι ↪ m) (col : ι ↪ n),
    HasEvenNonzeroSupportInRowsAndCols (A.submatrix row col) ∧
      HasOddHalfEntrySum (A.submatrix row col)

/-- Helper for Theorem 4.59: multiplying a `(0, ±1)` entry by a sign keeps it in `{0, 1, -1}`. -/
lemma signed_zero_one_neg_one
    (s : Bool) {z : ℤ} (hz : z = 0 ∨ z = 1 ∨ z = -1) :
    (if s then (1 : ℤ) else -1) * z = 0 ∨
      (if s then (1 : ℤ) else -1) * z = 1 ∨
      (if s then (1 : ℤ) else -1) * z = -1 := by
  -- Reduce to the three possible values of `z`.
  rcases hz with rfl | rfl | rfl <;> cases s <;> norm_num

/-- Helper for Theorem 4.59: modulo `2`, the values `1` and `-1` both reduce to `1`. -/
lemma zmod_two_cast_eq_indicator_of_zero_one_neg_one
    {z : ℤ} (hz : z = 0 ∨ z = 1 ∨ z = -1) :
    ((z : ℤ) : ZMod 2) = if z = 0 then 0 else 1 := by
  -- Reduce to the three allowed integer values.
  rcases hz with rfl | rfl | rfl
  · norm_num
  · norm_num
  · simpa using (ZMod.neg_eq_self_mod_two (1 : ZMod 2))

/-- Helper for Theorem 4.59: a finite sum of `(0, ±1)` integers
with even nonzero support is even. -/
lemma even_sum_of_zero_one_neg_one_even_support
    {ι : Type*} [Fintype ι] (f : ι → ℤ)
    (hf : ∀ i, f i = 0 ∨ f i = 1 ∨ f i = -1)
    (hs : Even (Function.support f).ncard) :
    Even (∑ i, f i) := by
  classical
  have hIndicator :
      (∑ i, if f i = 0 then (0 : ZMod 2) else 1) =
        ∑ i, if f i ≠ 0 then (1 : ZMod 2) else 0 := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hfi : f i = 0 <;> simp [hfi]
  have hsToFinset : Even ({i | f i ≠ 0}.toFinset.card) := by
    rw [← Set.ncard_eq_toFinset_card']
    simpa [Function.support] using hs
  have hs' : Even ((Finset.univ.filter fun i ↦ f i ≠ 0).card) := by
    simpa [Set.toFinset_setOf] using hsToFinset
  -- Work modulo `2`, where every nonzero `(0, ±1)` entry becomes `1`.
  rw [← ZMod.intCast_eq_zero_iff_even]
  calc
    ((∑ i, f i : ℤ) : ZMod 2)
        = ∑ i, (((f i : ℤ) : ZMod 2)) := by
            simp
    _ = ∑ i, (if f i = 0 then 0 else 1) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using zmod_two_cast_eq_indicator_of_zero_one_neg_one (hf i)
    _ = ∑ i, if f i ≠ 0 then (1 : ZMod 2) else 0 := hIndicator
    _ = Finset.sum (Finset.univ.filter (fun i ↦ f i ≠ 0)) (fun _ ↦ (1 : ZMod 2)) := by
          rw [← Finset.sum_filter]
    _ = (((Finset.univ.filter fun i ↦ f i ≠ 0).card : ℕ) : ZMod 2) := by
          symm
          rw [Finset.card_eq_sum_ones]
          simp
    _ = 0 := Even.natCast_zmod_two hs'

/-- Helper for Theorem 4.59: every row of an even-support `(0, ±1)` square matrix has even sum. -/
lemma even_row_sum_of_even_support
    {ι : Type*} [Fintype ι] {B : Matrix ι ι ℤ}
    (hB : HasZeroOneNegOneEntries B)
    (hEven : HasEvenNonzeroSupportInRowsAndCols B) :
    ∀ i, Even (∑ j, B i j) := by
  -- Apply the finite-family parity lemma to each row.
  intro i
  exact
    even_sum_of_zero_one_neg_one_even_support
      (B i) (fun j ↦ HasZeroOneNegOneEntries.apply hB i j) (hEven.1 i)

/-- Helper for Theorem 4.59: an equitable row-bicoloring on an even-support square matrix forces
every row-bicoloring difference to vanish. -/
lemma row_bicoloring_difference_eq_zero_of_even_column_support
    {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℤ}
    (hB : HasZeroOneNegOneEntries B)
    (hEven : HasEvenNonzeroSupportInRowsAndCols B)
    {red blue : Finset ι}
    (hColor : is_equitable_row_bicoloring B red blue) :
    ∀ j, row_bicoloring_difference B red blue j = 0 := by
  -- Each column-difference is one of `0`, `1`, `-1`; even column support forces it to be even.
  rcases (is_equitable_row_bicoloring_iff.1 hColor) with ⟨hDisj, hCover, hBalance⟩
  intro j
  have hColumnEven :
      Even (∑ i, B i j) := by
    exact
      even_sum_of_zero_one_neg_one_even_support
        (fun i ↦ B i j) (fun i ↦ HasZeroOneNegOneEntries.apply hB i j) (hEven.2 j)
  have hDiffEven :
      Even (row_bicoloring_difference B red blue j) := by
    have hSum :
        red.sum (fun i ↦ B i j) + blue.sum (fun i ↦ B i j) = ∑ i, B i j := by
      rw [← hCover, Finset.sum_union hDisj]
    rw [row_bicoloring_difference_apply]
    have hTwoBlue : Even (2 * blue.sum (fun i ↦ B i j)) := by
      exact even_two_mul _
    have hRewrite :
        red.sum (fun i ↦ B i j) - blue.sum (fun i ↦ B i j) =
          (∑ i, B i j) - 2 * blue.sum (fun i ↦ B i j) := by
      linarith
    rw [hRewrite]
    exact hColumnEven.sub hTwoBlue
  rcases hBalance j with hZero | hOne | hNegOne
  · exact hZero
  · exfalso
    have : Even (1 : ℤ) := hOne ▸ hDiffEven
    norm_num at this
  · exfalso
    have : Even (-1 : ℤ) := hNegOne ▸ hDiffEven
    norm_num at this

/-- Helper for Theorem 4.59: an equitable row-bicoloring rules out odd half entry sum on an
even-support `(0, ±1)` square matrix. -/
lemma odd_half_entry_sum_not_of_equitable_row_bicoloring
    {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℤ}
    (hB : HasZeroOneNegOneEntries B)
    (hEven : HasEvenNonzeroSupportInRowsAndCols B)
    (hColor : ∃ red blue : Finset ι, is_equitable_row_bicoloring B red blue) :
    ¬ HasOddHalfEntrySum B := by
  -- The column balances force the red and blue total row sums to agree.
  rintro ⟨t, ht, hOddt⟩
  rcases hColor with ⟨red, blue, hColor⟩
  rcases (is_equitable_row_bicoloring_iff.1 hColor) with ⟨hDisj, hCover, _hBalance⟩
  have hDiffZero := row_bicoloring_difference_eq_zero_of_even_column_support hB hEven hColor
  have hRowEven := even_row_sum_of_even_support hB hEven
  have hPartition :
      (∑ i, ∑ j, B i j) =
        red.sum (fun i ↦ ∑ j, B i j) + blue.sum (fun i ↦ ∑ j, B i j) := by
    -- Split the total row-sum according to the red/blue partition of the rows.
    rw [← hCover, Finset.sum_union hDisj]
  have hRedEqBlue :
      red.sum (fun i ↦ ∑ j, B i j) = blue.sum (fun i ↦ ∑ j, B i j) := by
    -- Summing the zero column-differences over all columns identifies the two totals.
    have hSumDiff :
        ∑ j, row_bicoloring_difference B red blue j =
          red.sum (fun i ↦ ∑ j, B i j) - blue.sum (fun i ↦ ∑ j, B i j) := by
      calc
        ∑ j, row_bicoloring_difference B red blue j
            = ∑ j, (red.sum (fun i ↦ B i j) - blue.sum (fun i ↦ B i j)) := by
                simp [row_bicoloring_difference_apply]
        _ = (∑ j, red.sum (fun i ↦ B i j)) - ∑ j, blue.sum (fun i ↦ B i j) := by
              rw [Finset.sum_sub_distrib]
        _ = red.sum (fun i ↦ ∑ j, B i j) - ∑ j, blue.sum (fun i ↦ B i j) := by
              rw [Finset.sum_comm]
        _ = red.sum (fun i ↦ ∑ j, B i j) - blue.sum (fun i ↦ ∑ j, B i j) := by
              congr 1
              rw [Finset.sum_comm]
    have hZeroDiff : ∑ j, row_bicoloring_difference B red blue j = 0 := by
      -- Every summand vanishes because each column-difference is zero.
      refine Finset.sum_eq_zero ?_
      intro j hj
      exact hDiffZero j
    linarith
  have hRedEven :
      Even (red.sum (fun i ↦ ∑ j, B i j)) := by
    -- The sum of even row-sums over the red rows is again even.
    refine Finset.induction_on red ?_ ?_
    · simpa using (show Even (0 : ℤ) by simp)
    · intro i s hi hsEven
      simpa [Finset.sum_insert hi] using (hRowEven i).add hsEven
  have hTotalTwo :
      (∑ i, ∑ j, B i j) = 2 * red.sum (fun i ↦ ∑ j, B i j) := by
    -- Replacing the blue total by the red total makes the total sum twice the red total.
    calc
      (∑ i, ∑ j, B i j)
          = red.sum (fun i ↦ ∑ j, B i j) + blue.sum (fun i ↦ ∑ j, B i j) := hPartition
      _ = red.sum (fun i ↦ ∑ j, B i j) + red.sum (fun i ↦ ∑ j, B i j) := by rw [hRedEqBlue]
      _ = 2 * red.sum (fun i ↦ ∑ j, B i j) := by ring
  have htEq :
      t = red.sum (fun i ↦ ∑ j, B i j) := by
    linarith [ht, hTotalTwo]
  have hEvenT : Even t := by
    rw [htEq]
    exact hRedEven
  exact ((Int.not_even_iff_odd).2 hOddt) hEvenT

/-- Helper for Theorem 4.59: an even-support square submatrix of a totally unimodular matrix
cannot have odd half entry sum. -/
lemma odd_half_entry_sum_not_of_totally_unimodular_square
    {ι : Type*} [Fintype ι] {B : Matrix ι ι ℤ}
    (hTU : B.IsTotallyUnimodular)
    (hEven : HasEvenNonzeroSupportInRowsAndCols B) :
    ¬ HasOddHalfEntrySum B := by
  classical
  have hEntries : HasZeroOneNegOneEntries B :=
    Matrix.IsTotallyUnimodular.hasZeroOneNegOneEntries hTU
  have hColor :
      ∃ red blue : Finset ι, is_equitable_row_bicoloring B red blue := by
    -- Apply Corollary 4.7 to the square matrix itself through the identity row embedding.
    simpa using
      ((totally_unimodular_iff_every_row_submatrix_admits_equitable_row_bicoloring B).1 hTU)
        (Function.Embedding.refl ι)
  -- The previously proved parity contradiction finishes once the equitable coloring exists.
  exact odd_half_entry_sum_not_of_equitable_row_bicoloring hEntries hEven hColor

/-- Helper for Theorem 4.59: a forbidden square submatrix inside a row submatrix is already a
forbidden square submatrix of the ambient matrix. -/
lemma even_support_odd_half_sum_square_submatrix_of_row_submatrix
    {ρ : Type w} {A : Matrix m n ℤ} (row : ρ ↪ m)
    (hSub : HasEvenSupportOddHalfSumSquareSubmatrix.{w, v, x} (A.submatrix row id)) :
    HasEvenSupportOddHalfSumSquareSubmatrix.{u, v, x} A := by
  -- Reuse the same square witness and compose its row embedding with the ambient row embedding.
  rcases hSub with ⟨ι, _, row', col, hEven, hOdd⟩
  refine ⟨ι, inferInstance, row'.trans row, col, ?_, ?_⟩
  · simpa [Matrix.submatrix_submatrix, Function.comp_id] using hEven
  · simpa [Matrix.submatrix_submatrix, Function.comp_id] using hOdd

/-- Helper for Theorem 4.59: the Boolean `±1` signing induced by a red/blue partition computes the
row-bicoloring difference. -/
lemma boolean_signed_sum_eq_row_bicoloring_difference
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) {red blue : Finset ι}
    (hDisj : Disjoint red blue) (hCover : red ∪ blue = Finset.univ) :
    ∀ j,
      (∑ i, (if i ∈ red then (1 : ℤ) else -1) * B i j) =
        row_bicoloring_difference B red blue j := by
  -- Split the universal row sum along the red/blue partition and simplify each side separately.
  intro j
  calc
    (∑ i, (if i ∈ red then (1 : ℤ) else -1) * B i j)
        = (red ∪ blue).sum (fun i ↦ (if i ∈ red then (1 : ℤ) else -1) * B i j) := by
            rw [hCover]
    _ = red.sum (fun i ↦ (if i ∈ red then (1 : ℤ) else -1) * B i j) +
          blue.sum (fun i ↦ (if i ∈ red then (1 : ℤ) else -1) * B i j) := by
            rw [Finset.sum_union hDisj]
    _ = red.sum (fun i ↦ B i j) + blue.sum (fun i ↦ -B i j) := by
          -- On red rows the sign is `+1`, while disjointness forces blue rows to contribute `-1`.
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hi]
          · refine Finset.sum_congr rfl ?_
            intro i hi
            have hNotRed : i ∉ red := fun hiRed ↦ Finset.disjoint_left.mp hDisj hiRed hi
            simp [hNotRed]
    _ = red.sum (fun i ↦ B i j) - blue.sum (fun i ↦ B i j) := by
          rw [show blue.sum (fun i ↦ -B i j) = -(blue.sum (fun i ↦ B i j)) by
            rw [Finset.sum_neg_distrib]]
          ring
    _ = row_bicoloring_difference B red blue j := by
          rw [row_bicoloring_difference_apply]

/-- Helper for Theorem 4.59: row-bicoloring differences are invariant under row reindexing. -/
lemma row_bicoloring_difference_reindex_rows
    {ι κ : Type*}
    (B : Matrix κ n ℤ) (e : ι ≃ κ) (red blue : Finset ι) (j : n) :
    row_bicoloring_difference (B.reindex e.symm (Equiv.refl n)) red blue j =
      row_bicoloring_difference B (red.map e.toEmbedding) (blue.map e.toEmbedding) j := by
  -- Both transported row sums are the original sums rewritten along the row equivalence.
  rw [row_bicoloring_difference_apply, row_bicoloring_difference_apply]
  simp [Matrix.reindex_apply, Finset.sum_map]

/-- Helper for Theorem 4.59: an equitable row-bicoloring transports across a row reindexing
equivalence. -/
lemma is_equitable_row_bicoloring_reindex_rows
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix κ n ℤ) (e : ι ≃ κ) {red blue : Finset ι}
    (hColor : is_equitable_row_bicoloring (B.reindex e.symm (Equiv.refl n)) red blue) :
    is_equitable_row_bicoloring B (red.map e.toEmbedding) (blue.map e.toEmbedding) := by
  -- Unfold the predicate so disjointness, coverage, and each column balance transport separately.
  rw [is_equitable_row_bicoloring_iff] at hColor ⊢
  rcases hColor with ⟨hDisj, hCover, hBalance⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (Finset.disjoint_map e.toEmbedding).2 hDisj
  · calc
      red.map e.toEmbedding ∪ blue.map e.toEmbedding
          = (red ∪ blue).map e.toEmbedding := by
              rw [Finset.map_union]
      _ = Finset.univ.map e.toEmbedding := by rw [hCover]
      _ = Finset.univ := Finset.map_univ_equiv e
  · intro j
    -- The column-balance condition is exactly the reindexed difference identity above.
    rw [← row_bicoloring_difference_reindex_rows B e red blue j]
    exact hBalance j

/-- Helper for Theorem 4.59: existence of an equitable row-bicoloring is invariant under a row
reindexing equivalence. -/
lemma exists_equitable_row_bicoloring_reindex_rows_iff
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix κ n ℤ) (e : ι ≃ κ) :
    (∃ red blue : Finset ι,
      is_equitable_row_bicoloring (B.reindex e.symm (Equiv.refl n)) red blue) ↔
      ∃ red blue : Finset κ, is_equitable_row_bicoloring B red blue := by
  constructor
  · rintro ⟨red, blue, hColor⟩
    -- Map a coloring of the reindexed matrix forward along the row equivalence.
    exact
      ⟨red.map e.toEmbedding, blue.map e.toEmbedding,
        is_equitable_row_bicoloring_reindex_rows B e hColor⟩
  · rintro ⟨red, blue, hColor⟩
    let B' : Matrix ι n ℤ := B.reindex e.symm (Equiv.refl n)
    have hColor' :
        is_equitable_row_bicoloring (B'.reindex e (Equiv.refl n)) red blue := by
      -- Reindexing `B'` back along the inverse equivalence recovers `B`.
      simpa [B', Matrix.reindex_apply] using hColor
    refine ⟨red.map e.symm.toEmbedding, blue.map e.symm.toEmbedding, ?_⟩
    -- Now transport the recovered coloring forward to the once-reindexed matrix.
    exact is_equitable_row_bicoloring_reindex_rows B' e.symm hColor'

/-- Helper for Theorem 4.59: equitable row-bicolorings are equivalent to Boolean `±1` row-signings
whose signed column sums lie in `{0, 1, -1}`. -/
lemma equitable_row_bicoloring_iff_exists_row_signing
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) :
    (∃ red blue : Finset ι, is_equitable_row_bicoloring B red blue) ↔
      ∃ s : ι → Bool,
        ∀ j,
          (∑ i, (if s i then (1 : ℤ) else -1) * B i j) = 0 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) * B i j) = 1 ∨
              (∑ i, (if s i then (1 : ℤ) else -1) * B i j) = -1 := by
  constructor
  · rintro ⟨red, blue, hColor⟩
    rcases (is_equitable_row_bicoloring_iff.1 hColor) with ⟨hDisj, hCover, hBalance⟩
    refine ⟨fun i ↦ i ∈ red, ?_⟩
    intro j
    -- Rewrite the signed column sum back to the row-bicoloring difference from the equitable
    -- partition, then reuse the balance clause already present in `hColor`.
    have hRewrite :
        (∑ i, (if i ∈ red then (1 : ℤ) else -1) * B i j) =
          row_bicoloring_difference B red blue j :=
      boolean_signed_sum_eq_row_bicoloring_difference B hDisj hCover j
    have hRewrite' :
        (∑ i, if i ∈ red then B i j else -B i j) =
          row_bicoloring_difference B red blue j := by
      simpa using hRewrite
    simpa [hRewrite'] using hBalance j
  · rintro ⟨s, hSigned⟩
    let red : Finset ι := Finset.univ.filter fun i ↦ s i
    let blue : Finset ι := Finset.univ.filter fun i ↦ ¬ s i
    refine ⟨red, blue, ?_⟩
    rw [is_equitable_row_bicoloring_iff]
    have hDisj : Disjoint red blue := by
      -- The Boolean choice prevents a row from being both red and blue.
      rw [Finset.disjoint_left]
      intro i hiRed hiBlue
      have hs : s i := by simpa [red] using hiRed
      have hns : ¬ s i := by simpa [blue] using hiBlue
      exact hns hs
    have hCover : red ∪ blue = Finset.univ := by
      -- Every row is colored by its Boolean sign.
      ext i
      by_cases hs : s i
      · simp [red, blue, hs]
      · simp [red, blue, hs]
    refine ⟨?_, ?_, ?_⟩
    · exact hDisj
    · exact hCover
    · intro j
      -- Replace the row-bicoloring difference by the Boolean signed sum supplied by `hSigned`.
      have hSignRewrite :
          (∑ i, (if i ∈ red then (1 : ℤ) else -1) * B i j) =
            ∑ i, (if s i then (1 : ℤ) else -1) * B i j := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hs : s i <;> simp [red, hs]
      have hRewrite :
          row_bicoloring_difference B red blue j =
            ∑ i, (if s i then (1 : ℤ) else -1) * B i j := by
        calc
          row_bicoloring_difference B red blue j
              = ∑ i, (if i ∈ red then (1 : ℤ) else -1) * B i j := by
                  symm
                  exact
                    boolean_signed_sum_eq_row_bicoloring_difference B hDisj hCover j
          _ = ∑ i, (if s i then (1 : ℤ) else -1) * B i j := hSignRewrite
      rw [hRewrite]
      exact hSigned j

/-- Helper for Theorem 4.59: an equitable row-bicoloring on a fixed matrix can be used directly
as a Boolean `±1` row-signing on that same matrix spelling. -/
lemma exists_row_signing_of_equitable_row_bicoloring
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ)
    {red blue : Finset ι}
    (hColor : is_equitable_row_bicoloring B red blue) :
    ∃ s : ι → Bool,
      ∀ j,
        (∑ i, (if s i then (1 : ℤ) else -1) * B i j) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) * B i j) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) * B i j) = -1 := by
  -- Repackage the given coloring through the signing equivalence without changing the matrix.
  exact (equitable_row_bicoloring_iff_exists_row_signing B).1 ⟨red, blue, hColor⟩

/-- Helper for Theorem 4.59: `BadRowSet B R` means the row restriction of `B` to `R` admits no
equitable row-bicoloring. -/
def BadRowSet {ρ : Type*} [DecidableEq ρ] (B : Matrix ρ n ℤ) (R : Finset ρ) : Prop :=
  ¬ ∃ red blue : Finset {i // i ∈ R},
      is_equitable_row_bicoloring
        (B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R) id) red blue

/-- Helper for Theorem 4.59: the full row set is bad exactly when the original matrix has no
equitable row-bicoloring. -/
lemma bad_row_set_univ_iff
    {ρ : Type u} [Fintype ρ] [DecidableEq ρ] (B : Matrix ρ n ℤ) :
    BadRowSet B (Finset.univ : Finset ρ) ↔
      ¬ ∃ red blue : Finset ρ, is_equitable_row_bicoloring B red blue := by
  let e : {i // i ∈ (Finset.univ : Finset ρ)} ≃ ρ :=
    Equiv.subtypeUnivEquiv fun _ ↦ Finset.mem_univ _
  -- Reindex the universal-row restriction back to `B` and then compare the existential statements.
  simpa [BadRowSet, e, Matrix.reindex_apply] using
    not_congr (exists_equitable_row_bicoloring_reindex_rows_iff B e)

/-- Helper for Theorem 4.59: among the bad row sets of `B`, there is one of minimal cardinality,
and every one-row deletion of that minimal bad row set is colorable. -/
lemma exists_minimal_bad_row_set_with_colorable_row_deletions
    {ρ : Type u} [Fintype ρ] [DecidableEq ρ] (B : Matrix ρ n ℤ)
    (hNoColor : ¬ ∃ red blue : Finset ρ, is_equitable_row_bicoloring B red blue) :
    ∃ R : Finset ρ,
      BadRowSet B R ∧
        (∀ ⦃S : Finset ρ⦄, BadRowSet B S → R.card ≤ S.card) ∧
        ∀ r : {i // i ∈ R},
          ∃ red blue : Finset {i // i ∈ R.erase r.1},
            is_equitable_row_bicoloring
              (B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R.erase r.1) id)
              red blue := by
  classical
  let s : Set (Finset ρ) := {R | BadRowSet B R}
  have hsNonempty : s.Nonempty := by
    -- The full row set is bad because the original matrix was assumed to have no coloring.
    exact ⟨Finset.univ, (bad_row_set_univ_iff B).2 hNoColor⟩
  let R : Finset ρ := Function.argminOn Finset.card s hsNonempty
  refine ⟨R, ?_, ?_, ?_⟩
  · -- Record that the chosen row set is indeed bad.
    exact Function.argminOn_mem Finset.card s hsNonempty
  · intro S hBadS
    -- Cardinal minimality is built into the `argminOn` choice of `R`.
    exact Function.argminOn_le Finset.card s hBadS
  · intro r
    by_contra hNoDeletedColor
    have hBadErase : BadRowSet B (R.erase r.1) := by
      simpa [BadRowSet] using hNoDeletedColor
    have hMinCard : R.card ≤ (R.erase r.1).card := by
      exact Function.argminOn_le Finset.card s hBadErase
    have hStrictCard : (R.erase r.1).card < R.card := by
      -- Erasing a row from the chosen row set strictly decreases its cardinality.
      rw [Finset.card_erase_of_mem r.2]
      have hPos : 0 < R.card := Finset.card_pos.mpr ⟨r.1, r.2⟩
      omega
    exact (not_lt_of_ge hMinCard) hStrictCard

/-- Helper for Theorem 4.59: every proper subset of a cardinal-minimal bad row set is colorable. -/
lemma proper_row_subset_colorable_of_minimal_bad_row_set
    {ρ : Type u} [Fintype ρ] [DecidableEq ρ] (B : Matrix ρ n ℤ) {R : Finset ρ}
    (hMinBad : ∀ ⦃S : Finset ρ⦄, BadRowSet B S → R.card ≤ S.card)
    {S : Finset ρ} (hSub : S ⊂ R) :
    ∃ red blue : Finset {i // i ∈ S},
      is_equitable_row_bicoloring
        (B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ S) id) red blue := by
  by_contra hNoColor
  have hBadS : BadRowSet B S := by
    -- The definition of `BadRowSet` is exactly the negated coloring statement.
    simpa [BadRowSet] using hNoColor
  have hCardLe : R.card ≤ S.card := hMinBad hBadS
  have hCardLt : S.card < R.card := Finset.card_lt_card hSub
  exact (not_lt_of_ge hCardLe) hCardLt

/-- Helper for Theorem 4.59: deleting `r` from the ambient row set `R` is equivalent to deleting
`r` from the restricted row type `R.attach`. -/
def erased_row_subtype_equiv
    {ρ : Type u} [DecidableEq ρ] {R : Finset ρ} (r : {i // i ∈ R}) :
    {i // i ∈ R.erase r.1} ≃ {i : {j // j ∈ R} // i ≠ r} where
  toFun i :=
    ⟨⟨i.1, (Finset.mem_erase.mp i.2).2⟩,
      fun h ↦ (Finset.mem_erase.mp i.2).1 (congrArg (fun x : {j // j ∈ R} ↦ x.1) h)⟩
  invFun i :=
    ⟨i.1.1, Finset.mem_erase.mpr ⟨fun h ↦ i.2 (Subtype.ext h), i.1.2⟩⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Helper for Theorem 4.59: the deleted-row restriction `R.erase r.1` is just a row-reindexing
of the bad restriction `B.submatrix rowR id` with the distinguished row removed. -/
lemma deleted_row_submatrix_eq_reindex
    {ρ : Type u} [DecidableEq ρ] {R : Finset ρ} (B : Matrix ρ n ℤ)
    (r : {i // i ∈ R}) :
    B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R.erase r.1) id =
      (((B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R) id).submatrix
          (Function.Embedding.subtype fun i : {j // j ∈ R} ↦ i ≠ r) id)).reindex
        (erased_row_subtype_equiv r).symm (Equiv.refl n) := by
  -- Both matrices read off the same ambient entry of `B`.
  ext i j
  rfl

/-- Helper for Theorem 4.59: rows of `A.image Subtype.val` are exactly the rows of `A`, viewed
inside the ambient restriction to `R`. -/
private noncomputable def imageSubtypeRowsEquiv
    {ρ : Type u} [DecidableEq ρ] {R : Finset ρ}
    (A : Finset {i // i ∈ R}) :
    {i // i ∈ A.image Subtype.val} ≃ {i : {j // j ∈ R} // i ∈ A} where
  toFun i := by
    classical
    let hmem : ∃ r ∈ A, (r : ρ) = i.1 := Finset.mem_image.mp i.2
    let r : {i // i ∈ R} := Classical.choose hmem
    have hrA : r ∈ A := (Classical.choose_spec hmem).1
    have hrEq : (r : ρ) = i.1 := (Classical.choose_spec hmem).2
    refine ⟨⟨i.1, ?_⟩, ?_⟩
    · simpa [hrEq] using r.2
    · have hEqSubtype :
          (⟨i.1, by simpa [hrEq] using r.2⟩ : {j // j ∈ R}) = r := by
        apply Subtype.ext
        exact hrEq.symm
      simpa [hEqSubtype] using hrA
  invFun i :=
    ⟨i.1.1, Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Helper for Theorem 4.59: restricting the ambient matrix directly to `A.image Subtype.val`
matches restricting the `R`-row submatrix further to `A`. -/
private lemma imageSubtypeRowsSubmatrixEqReindex
    {ρ : Type u} [DecidableEq ρ] {R : Finset ρ} (B : Matrix ρ n ℤ)
    (A : Finset {i // i ∈ R}) :
    B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ A.image Subtype.val) id =
      (((B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R) id).submatrix
          (Function.Embedding.subtype fun i : {j // j ∈ R} ↦ i ∈ A) id)).reindex
        (imageSubtypeRowsEquiv A).symm (Equiv.refl n) := by
  -- Both row restrictions evaluate the same ambient entry of `B`.
  ext i j
  have hRow :
      ((imageSubtypeRowsEquiv A i).1 : ρ) = i.1 := rfl
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, hRow]

/-- Helper for Theorem 4.59: equitable row-bicolorings transport between the direct restriction to
`A.image Subtype.val` and the corresponding row submatrix inside the `R`-restriction. -/
private lemma existsEquitableRowBicoloringImageSubtypeRows_iff
    {ρ : Type u} [DecidableEq ρ] {R : Finset ρ} (B : Matrix ρ n ℤ)
    (A : Finset {i // i ∈ R}) :
    (∃ red blue : Finset {i // i ∈ A.image Subtype.val},
      is_equitable_row_bicoloring
        (B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ A.image Subtype.val) id)
        red blue) ↔
      ∃ red blue : Finset {i : {j // j ∈ R} // i ∈ A},
        is_equitable_row_bicoloring
          ((B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R) id).submatrix
            (Function.Embedding.subtype fun i : {j // j ∈ R} ↦ i ∈ A) id)
          red blue := by
  let B_A : Matrix {i : {j // j ∈ R} // i ∈ A} n ℤ :=
    (B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R) id).submatrix
      (Function.Embedding.subtype fun i : {j // j ∈ R} ↦ i ∈ A) id
  let e : {i // i ∈ A.image Subtype.val} ≃ {i : {j // j ∈ R} // i ∈ A} :=
    imageSubtypeRowsEquiv A
  have hMatrix :
      B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ A.image Subtype.val) id =
        B_A.reindex e.symm (Equiv.refl n) := by
    simpa [B_A, e] using imageSubtypeRowsSubmatrixEqReindex B A
  constructor
  · rintro ⟨red, blue, hColor⟩
    have hColor' :
        is_equitable_row_bicoloring (B_A.reindex e.symm (Equiv.refl n)) red blue := by
      -- Rewrite the direct ambient restriction to the `B_A`-reindexed spelling used by the
      -- row-reindexing transport lemma.
      rw [← hMatrix]
      exact hColor
    exact (exists_equitable_row_bicoloring_reindex_rows_iff B_A e).1 ⟨red, blue, hColor'⟩
  · rintro ⟨red, blue, hColor⟩
    rcases (exists_equitable_row_bicoloring_reindex_rows_iff B_A e).2 ⟨red, blue, hColor⟩ with
      ⟨red', blue', hColor'⟩
    refine ⟨red', blue', ?_⟩
    -- Undo the same matrix rewrite to return to the ambient direct restriction.
    rw [hMatrix]
    exact hColor'

/-- Helper for Theorem 4.59: a coloring of the deleted ambient rows becomes a Boolean signing on
the deleted rows of the bad restriction itself. -/
lemma exists_deleted_row_signing_of_colorable_row_deletion
    {ρ : Type u} [DecidableEq ρ] (B : Matrix ρ n ℤ)
    {R : Finset ρ} (r : {i // i ∈ R})
    (hDeleted :
      ∃ red blue : Finset {i // i ∈ R.erase r.1},
        is_equitable_row_bicoloring
          (B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R.erase r.1) id)
          red blue) :
    ∃ s : {i : {j // j ∈ R} // i ≠ r} → Bool,
      ∀ j,
        (∑ i, (if s i then (1 : ℤ) else -1) *
            (((B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R) id).submatrix
              (Function.Embedding.subtype fun i : {j // j ∈ R} ↦ i ≠ r) id) i j)) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            (((B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R) id).submatrix
              (Function.Embedding.subtype fun i : {j // j ∈ R} ↦ i ≠ r) id) i j)) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              (((B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R) id).submatrix
                (Function.Embedding.subtype fun i : {j // j ∈ R} ↦ i ≠ r) id) i j)) = -1 := by
  let Bdel : Matrix {i : {j // j ∈ R} // i ≠ r} n ℤ :=
    ((B.submatrix (Function.Embedding.subtype fun i : ρ ↦ i ∈ R) id).submatrix
      (Function.Embedding.subtype fun i : {j // j ∈ R} ↦ i ≠ r) id)
  have hColorReindexed :
      ∃ red blue : Finset {i // i ∈ R.erase r.1},
        is_equitable_row_bicoloring
          (Bdel.reindex (erased_row_subtype_equiv r).symm (Equiv.refl n))
          red blue := by
    -- Rewrite the ambient deleted-row matrix as the reindexed restriction matrix.
    simpa [Bdel, deleted_row_submatrix_eq_reindex B r] using hDeleted
  have hColorBdel :
      ∃ red blue : Finset {i : {j // j ∈ R} // i ≠ r},
        is_equitable_row_bicoloring Bdel red blue :=
    (exists_equitable_row_bicoloring_reindex_rows_iff Bdel
      (erased_row_subtype_equiv r)).1 hColorReindexed
  -- Convert the deleted-row coloring into the equivalent Boolean `±1` signing.
  simpa [Bdel] using (equitable_row_bicoloring_iff_exists_row_signing Bdel).1 hColorBdel

/-- Helper for Theorem 4.59: extend a deleted-row signing by assigning the missing row the sign
`σ`. -/
def extend_deleted_row_signing
    {ι : Type*} [DecidableEq ι] (r : ι) (σ : Bool) (s : {i // i ≠ r} → Bool) :
    ι → Bool :=
  fun i ↦ if h : i = r then σ else s ⟨i, h⟩

/-- Helper for Theorem 4.59: the extension really assigns the chosen sign to the missing row. -/
lemma extend_deleted_row_signing_apply_self
    {ι : Type*} [DecidableEq ι] (r : ι) (σ : Bool) (s : {i // i ≠ r} → Bool) :
    extend_deleted_row_signing r σ s r = σ := by
  -- Unfold the extension at the distinguished row.
  simp [extend_deleted_row_signing]

/-- Helper for Theorem 4.59: away from the missing row, the extension agrees with the deleted-row
signing. -/
lemma extend_deleted_row_signing_apply_ne
    {ι : Type*} [DecidableEq ι] (r : ι) (σ : Bool) (s : {i // i ≠ r} → Bool)
    {i : ι} (hi : i ≠ r) :
    extend_deleted_row_signing r σ s i = s ⟨i, hi⟩ := by
  -- Unfold the extension away from the distinguished row.
  simp [extend_deleted_row_signing, hi]

/-- Helper for Theorem 4.59: a row distinct from `r₁` and `r₂` belongs to the exact
double-deleted finset `((Finset.univ : Finset ι).erase r₁).erase r₂`. -/
lemma mem_double_erase_univ_of_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r₁ r₂ i : ι}
    (hi₂ : i ≠ r₂) (hi₁ : i ≠ r₁) :
    i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂ := by
  simp [hi₂, hi₁]

/-- Helper for Theorem 4.59: the exact double-deleted row set is equivalent to deleting `r₂`
inside the once-deleted row subtype `{i // i ≠ r₁}`. -/
private def doubleErasedRowsEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r₁ r₂ : ι) (hNe : r₁ ≠ r₂) :
    {i // i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂} ≃
      {i : {j // j ≠ r₁} // i ≠ ⟨r₂, Ne.symm hNe⟩} where
  toFun i :=
    ⟨⟨i.1, by
        exact (Finset.mem_erase.mp ((Finset.mem_erase.mp i.2).2)).1⟩,
      fun h ↦ (Finset.mem_erase.mp i.2).1 (congrArg Subtype.val h)⟩
  invFun i :=
    ⟨i.1.1, by
      refine Finset.mem_erase.mpr ?_
      refine ⟨?_, ?_⟩
      · intro hEq
        exact i.2 (Subtype.ext hEq)
      · exact Finset.mem_erase.mpr ⟨i.1.2, Finset.mem_univ _⟩⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Helper for Theorem 4.59: extend a signing on the exact double-deleted row set by prescribing
the signs on the two deleted rows. -/
def extend_double_deleted_row_signing
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r₁ r₂ : ι) (σ₁ σ₂ : Bool)
    (tA : {i // i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂} → Bool) :
    ι → Bool :=
  fun i ↦
    if hi₁ : i = r₁ then σ₁ else
      if hi₂ : i = r₂ then σ₂ else
        tA ⟨i, mem_double_erase_univ_of_ne hi₂ hi₁⟩

/-- Helper for Theorem 4.59: the double-deleted extension uses the prescribed sign on `r₁`. -/
lemma extend_double_deleted_row_signing_apply_left
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r₁ r₂ : ι) (σ₁ σ₂ : Bool)
    (tA : {i // i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂} → Bool) :
    extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA r₁ = σ₁ := by
  -- Unfold the extension at the first deleted row.
  simp [extend_double_deleted_row_signing]

/-- Helper for Theorem 4.59: the double-deleted extension uses the prescribed sign on `r₂`. -/
lemma extend_double_deleted_row_signing_apply_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r₁ r₂ : ι) (hNe : r₂ ≠ r₁) (σ₁ σ₂ : Bool)
    (tA : {i // i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂} → Bool) :
    extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA r₂ = σ₂ := by
  -- Unfold the extension at the second deleted row and use `r₂ ≠ r₁`.
  simp [extend_double_deleted_row_signing, hNe]

/-- Helper for Theorem 4.59: away from `r₁` and `r₂`, the double-deleted extension agrees with the
signing on the exact double-deleted row set. -/
lemma extend_double_deleted_row_signing_apply_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r₁ r₂ i : ι} (σ₁ σ₂ : Bool)
    (tA : {i // i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂} → Bool)
    (hi₁ : i ≠ r₁) (hi₂ : i ≠ r₂) :
    extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA i =
      tA ⟨i, mem_double_erase_univ_of_ne hi₂ hi₁⟩ := by
  -- Unfold the extension away from both deleted rows.
  simp [extend_double_deleted_row_signing, hi₁, hi₂]

/-- Helper for Theorem 4.59: extending a signing on the exact double-deleted row set splits the
full signed column sum into the double-deleted core and the two prescribed row terms. -/
private lemma extendDoubleDeletedSigning_sum_eq_core_plus_pivots
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (r₁ r₂ : ι) (hNe : r₂ ≠ r₁) (σ₁ σ₂ : Bool)
    (tA : {i // i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂} → Bool) (j : κ) :
    (∑ i, (if extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA i then (1 : ℤ) else -1) * B i j) =
      (∑ i : {x // x ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂},
        (if tA i then (1 : ℤ) else -1) *
          ((B.submatrix
            (Function.Embedding.subtype
              fun i : ι ↦ i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂) id) i j)) +
        ((if σ₂ then (1 : ℤ) else -1) * B r₂ j) +
        ((if σ₁ then (1 : ℤ) else -1) * B r₁ j) := by
  let A : Finset ι := ((Finset.univ : Finset ι).erase r₁).erase r₂
  let f : ι → ℤ := fun i ↦
    (if extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA i then (1 : ℤ) else -1) * B i j
  have hSplit₁ :
      (∑ i, f i) = Finset.sum (Finset.univ.erase r₁) f + f r₁ := by
    -- Separate the first deleted row from the ambient finite sum.
    have hr₁ : r₁ ∈ (Finset.univ : Finset ι) := by simp
    exact ((Finset.univ : Finset ι).sum_erase_add f hr₁).symm
  have hSplit₂ :
      Finset.sum (Finset.univ.erase r₁) f = Finset.sum A f + f r₂ := by
    -- Remove the second deleted row from the once-deleted sum.
    have hr₂ : r₂ ∈ Finset.univ.erase r₁ := by simp [hNe]
    exact ((Finset.univ.erase r₁).sum_erase_add f hr₂).symm
  have hCore :
      Finset.sum A f =
        ∑ i : {x // x ∈ A},
          (if tA i then (1 : ℤ) else -1) *
            ((B.submatrix
              (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j) := by
    -- Away from the two deleted rows, the full extension agrees with the `A`-signing itself.
    rw [← Finset.sum_attach, Finset.attach_eq_univ]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi₂ : i.1 ≠ r₂ := by
      exact (Finset.mem_erase.mp i.2).1
    have hi₁ : i.1 ≠ r₁ := by
      exact (Finset.mem_erase.mp ((Finset.mem_erase.mp i.2).2)).1
    have ht_mem :
        extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA i.1 = tA i := by
      simpa [A] using
        (extend_double_deleted_row_signing_apply_mem σ₁ σ₂ tA hi₁ hi₂)
    simp [f, Matrix.submatrix_apply, ht_mem]
  calc
    (∑ i, f i) = Finset.sum (Finset.univ.erase r₁) f + f r₁ := hSplit₁
    _ = (Finset.sum A f + f r₂) + f r₁ := by rw [hSplit₂]
    _ = (Finset.sum A f + ((if σ₂ then (1 : ℤ) else -1) * B r₂ j)) +
          ((if σ₁ then (1 : ℤ) else -1) * B r₁ j) := by
      rw [show f r₂ = ((if σ₂ then (1 : ℤ) else -1) * B r₂ j) by
        simp [f, extend_double_deleted_row_signing_apply_right, hNe]]
      rw [show f r₁ = ((if σ₁ then (1 : ℤ) else -1) * B r₁ j) by
        simp [f, extend_double_deleted_row_signing_apply_left]]
    _ = ((∑ i : {x // x ∈ A},
          (if tA i then (1 : ℤ) else -1) *
            ((B.submatrix
              (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
          ((if σ₂ then (1 : ℤ) else -1) * B r₂ j)) +
          ((if σ₁ then (1 : ℤ) else -1) * B r₁ j) := by
      rw [hCore]
    _ = (∑ i : {x // x ∈ A},
          (if tA i then (1 : ℤ) else -1) *
            ((B.submatrix
              (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
          ((if σ₂ then (1 : ℤ) else -1) * B r₂ j) +
          ((if σ₁ then (1 : ℤ) else -1) * B r₁ j) := by
      ring

/-- Helper for Theorem 4.59: on a shared critical column, the two normalized pivot contributions
collapse the double-deleted extension sum to the `A`-core plus `2`. -/
private lemma extendDoubleDeletedSigning_sharedColumn_sum_eq_core_plus_two
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (r₁ r₂ : ι) (hNe : r₂ ≠ r₁) (σ₁ σ₂ : Bool)
    (tA : {i // i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂} → Bool) (j : κ)
    (hRow₁ : ((if σ₁ then (1 : ℤ) else -1) * B r₁ j) = 1)
    (hRow₂ : ((if σ₂ then (1 : ℤ) else -1) * B r₂ j) = 1) :
    (∑ i, (if extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA i then (1 : ℤ) else -1) * B i j) =
      (∑ i : {x // x ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂},
        (if tA i then (1 : ℤ) else -1) *
          ((B.submatrix
            (Function.Embedding.subtype
              fun i : ι ↦ i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂) id) i j)) + 2 := by
  -- Rewrite the full sum through the double-deleted core and substitute the two forced pivots.
  rw [extendDoubleDeletedSigning_sum_eq_core_plus_pivots B r₁ r₂ hNe σ₁ σ₂ tA j, hRow₂, hRow₁]
  ring

/-- Helper for Theorem 4.59: on an even-support column, the signed sum over the exact
double-deleted row set is even whenever the two deleted entries are nonzero. -/
private lemma doubleDeletedCore_even_of_evenSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r₁ r₂ : ι) (hNe : r₂ ≠ r₁) (σ₁ σ₂ : Bool)
    (tA : {i // i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂} → Bool) (j : κ)
    (hEvenSupport : Even (Function.support fun i ↦ B i j).ncard)
    (hr₁ : B r₁ j ≠ 0) (hr₂ : B r₂ j ≠ 0) :
    Even (∑ i : {x // x ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂},
      (if tA i then (1 : ℤ) else -1) *
        ((B.submatrix
          (Function.Embedding.subtype
            fun i : ι ↦ i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂) id) i j)) := by
  let A : Finset ι := ((Finset.univ : Finset ι).erase r₁).erase r₂
  let fullSigned : ι → ℤ := fun i ↦
    (if extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA i then (1 : ℤ) else -1) * B i j
  let core : ℤ :=
    ∑ i : {x // x ∈ A},
      (if tA i then (1 : ℤ) else -1) *
        ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)
  have hFullValues :
      ∀ i, fullSigned i = 0 ∨ fullSigned i = 1 ∨ fullSigned i = -1 := by
    intro i
    -- Each signed ambient column entry is still a `(0, ±1)` value.
    simpa [fullSigned] using
      signed_zero_one_neg_one (extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA i)
        (HasZeroOneNegOneEntries.apply hB i j)
  have hSupportEq :
      Function.support fullSigned = Function.support fun i ↦ B i j := by
    ext i
    -- Multiplying by a Boolean sign does not change whether a column entry is zero.
    dsimp [fullSigned]
    cases hsi : extend_double_deleted_row_signing r₁ r₂ σ₁ σ₂ tA i <;>
      by_cases hBij : B i j = 0 <;> simp [hsi, hBij]
  have hFullEven : Even (∑ i, fullSigned i) := by
    -- The ambient signed column inherits even parity from the even support of the original column.
    apply even_sum_of_zero_one_neg_one_even_support fullSigned hFullValues
    simpa [hSupportEq] using hEvenSupport
  have hRow₁Value :
      ((if σ₁ then (1 : ℤ) else -1) * B r₁ j) = 1 ∨
        ((if σ₁ then (1 : ℤ) else -1) * B r₁ j) = -1 := by
    rcases HasZeroOneNegOneEntries.apply hB r₁ j with hZero | hOne | hNegOne
    · exact (hr₁ hZero).elim
    · cases σ₁ <;> simp [hOne]
    · cases σ₁ <;> simp [hNegOne]
  have hRow₂Value :
      ((if σ₂ then (1 : ℤ) else -1) * B r₂ j) = 1 ∨
        ((if σ₂ then (1 : ℤ) else -1) * B r₂ j) = -1 := by
    rcases HasZeroOneNegOneEntries.apply hB r₂ j with hZero | hOne | hNegOne
    · exact (hr₂ hZero).elim
    · cases σ₂ <;> simp [hOne]
    · cases σ₂ <;> simp [hNegOne]
  have hPivotsEven :
      Even (((if σ₂ then (1 : ℤ) else -1) * B r₂ j) +
        ((if σ₁ then (1 : ℤ) else -1) * B r₁ j)) := by
    rcases hRow₂Value with hRow₂One | hRow₂NegOne
    · rcases hRow₁Value with hRow₁One | hRow₁NegOne
      · rw [hRow₂One, hRow₁One]
        norm_num
      · rw [hRow₂One, hRow₁NegOne]
        norm_num
    · rcases hRow₁Value with hRow₁One | hRow₁NegOne
      · rw [hRow₂NegOne, hRow₁One]
        norm_num
      · rw [hRow₂NegOne, hRow₁NegOne]
        norm_num
  have hSplit :
      (∑ i, fullSigned i) =
        core + ((if σ₂ then (1 : ℤ) else -1) * B r₂ j) +
          ((if σ₁ then (1 : ℤ) else -1) * B r₁ j) := by
    -- Rewrite the ambient signed column into the exact double-deleted core plus the two pivots.
    simpa [A, core, fullSigned] using
      extendDoubleDeletedSigning_sum_eq_core_plus_pivots B r₁ r₂ hNe σ₁ σ₂ tA j
  have hCorePlusPivotsEven :
      Even (core + (((if σ₂ then (1 : ℤ) else -1) * B r₂ j) +
        ((if σ₁ then (1 : ℤ) else -1) * B r₁ j))) := by
    -- Reassociate the split so the even pivot contribution can be subtracted in one step.
    have hFullEven' :
        Even
          (core + ((if σ₂ then (1 : ℤ) else -1) * B r₂ j) +
            ((if σ₁ then (1 : ℤ) else -1) * B r₁ j)) := by
      rw [← hSplit]
      exact hFullEven
    simpa [add_assoc] using hFullEven'
  -- Subtract the even two-pivot contribution from the even ambient signed sum.
  simpa [A, core] using hCorePlusPivotsEven.sub hPivotsEven

/-- Helper for Theorem 4.59: on an even-support shared critical column, any balanced signing of the
exact double-deleted row set has core sum `0`. -/
private lemma doubleDeletedCore_eq_zero_of_balanced_evenSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r₁ r₂ : ι) (hNe : r₂ ≠ r₁) (σ₁ σ₂ : Bool)
    (tA : {i // i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂} → Bool) (j : κ)
    (htA :
      (∑ i : {x // x ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂},
        (if tA i then (1 : ℤ) else -1) *
          ((B.submatrix
            (Function.Embedding.subtype
              fun i : ι ↦ i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂) id) i j)) = 0 ∨
        (∑ i : {x // x ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂},
          (if tA i then (1 : ℤ) else -1) *
            ((B.submatrix
              (Function.Embedding.subtype
                fun i : ι ↦ i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂) id) i j)) = 1 ∨
          (∑ i : {x // x ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂},
            (if tA i then (1 : ℤ) else -1) *
              ((B.submatrix
                (Function.Embedding.subtype
                  fun i : ι ↦ i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂) id) i j)) = -1)
    (hEvenSupport : Even (Function.support fun i ↦ B i j).ncard)
    (hr₁ : B r₁ j ≠ 0) (hr₂ : B r₂ j ≠ 0) :
    (∑ i : {x // x ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂},
      (if tA i then (1 : ℤ) else -1) *
        ((B.submatrix
          (Function.Embedding.subtype
            fun i : ι ↦ i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂) id) i j)) = 0 := by
  have hCoreEven :
      Even (∑ i : {x // x ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂},
        (if tA i then (1 : ℤ) else -1) *
          ((B.submatrix
            (Function.Embedding.subtype
              fun i : ι ↦ i ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂) id) i j)) :=
    doubleDeletedCore_even_of_evenSupport hB r₁ r₂ hNe σ₁ σ₂ tA j hEvenSupport hr₁ hr₂
  rcases htA with hZero | hOne | hNegOne
  · exact hZero
  · exfalso
    rw [hOne] at hCoreEven
    norm_num at hCoreEven
  · exfalso
    rw [hNegOne] at hCoreEven
    norm_num at hCoreEven

/-- Helper for Theorem 4.59: flipping every Boolean sign flips the value of the extension as well. -/
lemma extend_deleted_row_signing_compl
    {ι : Type*} [DecidableEq ι] (r : ι) (σ : Bool) (s : {i // i ≠ r} → Bool) :
    extend_deleted_row_signing r (!σ) (fun i ↦ !(s i)) =
      fun i ↦ !(extend_deleted_row_signing r σ s i) := by
  -- Check the distinguished row and the deleted rows separately.
  funext i
  by_cases hi : i = r
  · simp [extend_deleted_row_signing, hi]
  · simp [extend_deleted_row_signing, hi]

/-- Helper for Theorem 4.59: negating a value in `{0, 1, -1}` keeps it in `{0, 1, -1}`. -/
lemma neg_eq_zero_one_neg_one_of_zero_one_neg_one
    {z : ℤ} (hz : z = 0 ∨ z = 1 ∨ z = -1) :
    -z = 0 ∨ -z = 1 ∨ -z = -1 := by
  -- Reduce to the three allowed values of `z`.
  rcases hz with rfl | rfl | rfl <;> norm_num

/-- Helper for Theorem 4.59: complementing every Boolean sign negates the signed column sum. -/
lemma signed_column_sum_compl_eq_neg
    {ι : Type*} [Fintype ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (s : ι → Bool) (j : κ) :
    (∑ i, (if !s i then (1 : ℤ) else -1) * B i j) =
      -∑ i, (if s i then (1 : ℤ) else -1) * B i j := by
  -- Rewrite each complemented term as the negative of the original term and sum.
  calc
    (∑ i, (if !s i then (1 : ℤ) else -1) * B i j)
        = ∑ i, -((if s i then (1 : ℤ) else -1) * B i j) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            cases hs : s i <;> simp [hs]
    _ = -∑ i, (if s i then (1 : ℤ) else -1) * B i j := by
          rw [Finset.sum_neg_distrib]

/-- Helper for Theorem 4.59: complementing a deleted-row signing preserves the
`{0, 1, -1}`-valued deleted-column balance family. -/
private lemma deletedRowBalanceFamily_compl
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} {r : ι} (s : {i // i ≠ r} → Bool)
    (hs :
      ∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1) :
    ∀ j',
      (∑ i, (if (!s i) then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
        (∑ i, (if (!s i) then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
          (∑ i, (if (!s i) then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1 := by
  intro j'
  have hNegDeleted :
      (∑ i, (if (!s i) then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) =
        -(∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) := by
    -- Complementing every deleted-row sign negates the deleted signed column sum.
    simpa using
      signed_column_sum_compl_eq_neg
        (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) s j'
  rcases hs j' with hZero | hOne | hNegOne
  · left
    calc
      (∑ i, (if (!s i) then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) =
        -(∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) :=
          hNegDeleted
      _ = 0 := by rw [hZero]; norm_num
  · right
    right
    calc
      (∑ i, (if (!s i) then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) =
        -(∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) :=
          hNegDeleted
      _ = -1 := by rw [hOne]
  · right
    left
    calc
      (∑ i, (if (!s i) then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) =
        -(∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) :=
          hNegDeleted
      _ = 1 := by rw [hNegOne]; norm_num

/-- Helper for Theorem 4.59: extending across the missing row splits the full signed column sum
into the deleted-row contribution plus the missing-row term. -/
lemma extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (r : ι) (σ : Bool) (s : {i // i ≠ r} → Bool) (j : κ) :
    (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) =
      (∑ i : {i // i ≠ r},
        (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) +
        ((if σ then (1 : ℤ) else -1) * B r j) := by
  let f : ι → ℤ := fun i ↦
    (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j
  -- Split the finite row sum into the distinguished row and the deleted-row subtype.
  calc
    (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j)
        = ((if extend_deleted_row_signing r σ s r then (1 : ℤ) else -1) * B r j) +
            ∑ i : {i // i ≠ r},
              (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j := by
            simpa [f] using Fintype.sum_eq_add_sum_subtype_ne f r
    _ = ((if σ then (1 : ℤ) else -1) * B r j) +
          ∑ i : {i // i ≠ r},
            (if s i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j := by
          congr 1
          · simp [extend_deleted_row_signing]
          · refine Finset.sum_congr rfl ?_
            intro i hi
            simp [extend_deleted_row_signing, Matrix.submatrix_apply, i.2]
    _ = (∑ i : {i // i ≠ r},
          (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) +
          ((if σ then (1 : ℤ) else -1) * B r j) := by
            rw [add_comm]

/-- Helper for Theorem 4.59: a signing on a bad row restriction must be unbalanced in some
column. -/
lemma exists_unbalanced_column_of_signing_of_no_equitable_row_bicoloring
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ)
    (hBad : ¬ ∃ red blue : Finset ι, is_equitable_row_bicoloring B red blue)
    (s : ι → Bool) :
    ∃ j,
      ¬ ((∑ i, (if s i then (1 : ℤ) else -1) * B i j) = 0 ∨
        (∑ i, (if s i then (1 : ℤ) else -1) * B i j) = 1 ∨
        (∑ i, (if s i then (1 : ℤ) else -1) * B i j) = -1) := by
  -- Otherwise the signing itself would produce an equitable row-bicoloring.
  by_contra hNoColumn
  apply hBad
  refine (equitable_row_bicoloring_iff_exists_row_signing B).2 ?_
  refine ⟨s, ?_⟩
  intro j
  by_contra hj
  exact hNoColumn ⟨j, hj⟩

/-- Helper for Theorem 4.59: every deleted-row signing extension on a bad row restriction is
unbalanced in some column. -/
lemma exists_unbalanced_column_of_extended_deleted_row_signing
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ)
    (hBad : ¬ ∃ red blue : Finset ι, is_equitable_row_bicoloring B red blue)
    (r : ι) (σ : Bool) (s : {i // i ≠ r} → Bool) :
    ∃ j,
      ¬ ((∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 0 ∨
        (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 1 ∨
        (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = -1) := by
  -- Apply the bad-column witness to the extended full-row signing.
  exact
    exists_unbalanced_column_of_signing_of_no_equitable_row_bicoloring B hBad
      (extend_deleted_row_signing r σ s)

/-- Helper for Theorem 4.59: once two `{0, 1, -1}` contributions add to an unbalanced value, the
sum must already be `2` or `-2`. -/
lemma full_signed_sum_eq_two_or_neg_two_of_zero_one_neg_one
    {a b : ℤ}
    (ha : a = 0 ∨ a = 1 ∨ a = -1)
    (hb : b = 0 ∨ b = 1 ∨ b = -1)
    (hBad : ¬ (a + b = 0 ∨ a + b = 1 ∨ a + b = -1)) :
    a + b = 2 ∨ a + b = -2 := by
  -- Exhaust the nine possible `(0, ±1)` pairs.
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals
    first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exfalso; simpa using hBad

/-- Helper for Theorem 4.59: if two `{0, 1, -1}` integers add up to `2`, then both are `1`. -/
lemma summands_eq_one_of_zero_one_neg_one_add_eq_two
    {a b : ℤ}
    (ha : a = 0 ∨ a = 1 ∨ a = -1)
    (hb : b = 0 ∨ b = 1 ∨ b = -1)
    (h : a + b = 2) :
    a = 1 ∧ b = 1 := by
  -- Exhaust the finitely many possible `{0, 1, -1}` pairs.
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> norm_num at h
  exact ⟨rfl, rfl⟩

/-- Helper for Theorem 4.59: if two `{0, 1, -1}` integers add up to `-2`, then both are `-1`. -/
lemma summands_eq_neg_one_of_zero_one_neg_one_add_eq_neg_two
    {a b : ℤ}
    (ha : a = 0 ∨ a = 1 ∨ a = -1)
    (hb : b = 0 ∨ b = 1 ∨ b = -1)
    (h : a + b = -2) :
    a = -1 ∧ b = -1 := by
  -- Exhaust the finitely many possible `{0, 1, -1}` pairs.
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> norm_num at h
  exact ⟨rfl, rfl⟩

/-- Helper for Theorem 4.59: a bad column for an extended deleted-row signing can be normalized,
possibly by complementing the signing, into a genuine critical column with signed pivot value `1`.
-/
private lemma normalizeUnbalancedDeletedRowExtensionAtColumn
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r : ι) (s : {i // i ≠ r} → Bool) (σ : Bool) {j : κ}
    (hs :
      ∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1)
    (hBad :
      ¬ ((∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 0 ∨
        (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 1 ∨
        (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = -1)) :
    ∃ s' : {i // i ≠ r} → Bool, ∃ σ' : Bool,
      (∀ j',
        (∑ i, (if s' i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
          (∑ i, (if s' i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
            (∑ i, (if s' i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1) ∧
      (∑ i, (if extend_deleted_row_signing r σ' s' i then (1 : ℤ) else -1) * B i j) = 2 ∧
      (((if σ' then (1 : ℤ) else -1) * B r j) = 1) := by
  let deletedSum : ℤ :=
    ∑ i, (if s i then (1 : ℤ) else -1) *
      ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j)
  let rowTerm : ℤ := (if σ then (1 : ℤ) else -1) * B r j
  have hSplit :
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) =
        deletedSum + rowTerm := by
    -- Split the bad full sum into its deleted contribution and the distinguished row term.
    simpa [deletedSum, rowTerm] using
      extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term B r σ s j
  have hDeletedValue :
      deletedSum = 0 ∨ deletedSum = 1 ∨ deletedSum = -1 := by
    simpa [deletedSum] using hs j
  have hRowValue :
      rowTerm = 0 ∨ rowTerm = 1 ∨ rowTerm = -1 := by
    -- The distinguished row contribution is still a signed `(0, ±1)` entry.
    simpa [rowTerm] using signed_zero_one_neg_one σ (HasZeroOneNegOneEntries.apply hB r j)
  have hBadSplit :
      ¬ (deletedSum + rowTerm = 0 ∨ deletedSum + rowTerm = 1 ∨ deletedSum + rowTerm = -1) := by
    intro hBalanced
    apply hBad
    rcases hBalanced with hZero | hOne | hNegOne
    · left
      rw [hSplit]
      exact hZero
    · right
      left
      rw [hSplit]
      exact hOne
    · right
      right
      rw [hSplit]
      exact hNegOne
  have hTwoOrNegTwo :
      deletedSum + rowTerm = 2 ∨ deletedSum + rowTerm = -2 := by
    exact
      full_signed_sum_eq_two_or_neg_two_of_zero_one_neg_one
        hDeletedValue hRowValue hBadSplit
  rcases hTwoOrNegTwo with hTwo | hNegTwo
  · have hPair :
        deletedSum = 1 ∧ rowTerm = 1 := by
      -- Exhaust the finitely many `{0, 1, -1}` possibilities for the two summands.
      rcases hDeletedValue with hDeletedZero | hDeletedOne | hDeletedNegOne
      · rcases hRowValue with hRowZero | hRowOne | hRowNegOne
        · rw [hDeletedZero, hRowZero] at hTwo
          norm_num at hTwo
        · rw [hDeletedZero, hRowOne] at hTwo
          norm_num at hTwo
        · rw [hDeletedZero, hRowNegOne] at hTwo
          norm_num at hTwo
      · rcases hRowValue with hRowZero | hRowOne | hRowNegOne
        · rw [hDeletedOne, hRowZero] at hTwo
          norm_num at hTwo
        · exact ⟨hDeletedOne, hRowOne⟩
        · rw [hDeletedOne, hRowNegOne] at hTwo
          norm_num at hTwo
      · rcases hRowValue with hRowZero | hRowOne | hRowNegOne
        · rw [hDeletedNegOne, hRowZero] at hTwo
          norm_num at hTwo
        · rw [hDeletedNegOne, hRowOne] at hTwo
          norm_num at hTwo
        · rw [hDeletedNegOne, hRowNegOne] at hTwo
          norm_num at hTwo
    refine ⟨s, σ, hs, ?_, ?_⟩
    · rw [hSplit]
      exact hTwo
    · simpa [rowTerm] using hPair.2
  · let s' : {i // i ≠ r} → Bool := fun i ↦ !(s i)
    have hs' :
        ∀ j',
          (∑ i, (if s' i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
            (∑ i, (if s' i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
              (∑ i, (if s' i then (1 : ℤ) else -1) *
                ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1 := by
      -- Complement the deleted witness once so the same bad column becomes positive.
      simpa [s'] using deletedRowBalanceFamily_compl s hs
    have hPair :
        deletedSum = -1 ∧ rowTerm = -1 := by
      -- The same finite case split isolates the unique way to sum to `-2`.
      rcases hDeletedValue with hDeletedZero | hDeletedOne | hDeletedNegOne
      · rcases hRowValue with hRowZero | hRowOne | hRowNegOne
        · rw [hDeletedZero, hRowZero] at hNegTwo
          norm_num at hNegTwo
        · rw [hDeletedZero, hRowOne] at hNegTwo
          norm_num at hNegTwo
        · rw [hDeletedZero, hRowNegOne] at hNegTwo
          norm_num at hNegTwo
      · rcases hRowValue with hRowZero | hRowOne | hRowNegOne
        · rw [hDeletedOne, hRowZero] at hNegTwo
          norm_num at hNegTwo
        · rw [hDeletedOne, hRowOne] at hNegTwo
          norm_num at hNegTwo
        · rw [hDeletedOne, hRowNegOne] at hNegTwo
          norm_num at hNegTwo
      · rcases hRowValue with hRowZero | hRowOne | hRowNegOne
        · rw [hDeletedNegOne, hRowZero] at hNegTwo
          norm_num at hNegTwo
        · rw [hDeletedNegOne, hRowOne] at hNegTwo
          norm_num at hNegTwo
        · exact ⟨hDeletedNegOne, hRowNegOne⟩
    have hCompl :
        extend_deleted_row_signing r (!σ) s' =
          fun i ↦ !(extend_deleted_row_signing r σ s i) := by
      -- Flipping both the deleted signs and the distinguished-row sign flips the full extension.
      simpa [s'] using extend_deleted_row_signing_compl r σ s
    refine ⟨s', !σ, hs', ?_, ?_⟩
    · calc
        (∑ i, (if extend_deleted_row_signing r (!σ) s' i then (1 : ℤ) else -1) * B i j)
            = ∑ i, (if !(extend_deleted_row_signing r σ s i) then (1 : ℤ) else -1) * B i j := by
                simp [hCompl]
        _ = -(∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) := by
              simpa using signed_column_sum_compl_eq_neg B (extend_deleted_row_signing r σ s) j
        _ = -(deletedSum + rowTerm) := by rw [hSplit]
        _ = -(-2 : ℤ) := by rw [hNegTwo]
        _ = 2 := by norm_num
    · have hRowCompl :
          ((if !σ then (1 : ℤ) else -1) * B r j) = -(rowTerm) := by
        cases σ <;> simp [rowTerm]
      calc
        ((if !σ then (1 : ℤ) else -1) * B r j) = -(rowTerm) := hRowCompl
        _ = -(-1 : ℤ) := by rw [hPair.2]
        _ = 1 := by norm_num

/-- Helper for Theorem 4.59: a bad extended deleted-row signing can be normalized using either the
original deleted witness or its global complement, and the chosen branch is recorded explicitly. -/
private lemma normalizeUnbalancedDeletedRowExtensionAtColumn_withOrigin
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r : ι) (s : {i // i ≠ r} → Bool) (σ : Bool) {j : κ}
    (hs :
      ∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1)
    (hBad :
      ¬ ((∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 0 ∨
        (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 1 ∨
        (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = -1)) :
    ∃ s' : {i // i ≠ r} → Bool, ∃ σ' : Bool,
      ((s' = s ∧ σ' = σ) ∨ (s' = (fun i ↦ !s i) ∧ σ' = !σ)) ∧
      (∀ j',
        (∑ i, (if s' i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
          (∑ i, (if s' i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
            (∑ i, (if s' i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1) ∧
      (∑ i, (if extend_deleted_row_signing r σ' s' i then (1 : ℤ) else -1) * B i j) = 2 ∧
      (((if σ' then (1 : ℤ) else -1) * B r j) = 1) := by
  let deletedSum : ℤ :=
    ∑ i, (if s i then (1 : ℤ) else -1) *
      ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j)
  let rowTerm : ℤ := (if σ then (1 : ℤ) else -1) * B r j
  have hSplit :
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) =
        deletedSum + rowTerm := by
    -- Split the bad full-column sum into the deleted contribution and the distinguished row term.
    simpa [deletedSum, rowTerm] using
      extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term B r σ s j
  have hDeletedValue :
      deletedSum = 0 ∨ deletedSum = 1 ∨ deletedSum = -1 := by
    -- The deleted-row witness constrains the deleted contribution to `{0, 1, -1}`.
    simpa [deletedSum] using hs j
  have hRowValue :
      rowTerm = 0 ∨ rowTerm = 1 ∨ rowTerm = -1 := by
    -- The distinguished-row contribution is still a signed `(0, ±1)` entry.
    simpa [rowTerm] using signed_zero_one_neg_one σ (HasZeroOneNegOneEntries.apply hB r j)
  have hBadSplit :
      ¬ (deletedSum + rowTerm = 0 ∨ deletedSum + rowTerm = 1 ∨ deletedSum + rowTerm = -1) := by
    intro hBalanced
    apply hBad
    rcases hBalanced with hZero | hOne | hNegOne
    · left
      rw [hSplit]
      exact hZero
    · right
      left
      rw [hSplit]
      exact hOne
    · right
      right
      rw [hSplit]
      exact hNegOne
  have hTwoOrNegTwo :
      deletedSum + rowTerm = 2 ∨ deletedSum + rowTerm = -2 := by
    -- A bad full column has to take one of the two exceptional values `±2`.
    exact
      full_signed_sum_eq_two_or_neg_two_of_zero_one_neg_one
        hDeletedValue hRowValue hBadSplit
  rcases hTwoOrNegTwo with hTwo | hNegTwo
  · have hPair : deletedSum = 1 ∧ rowTerm = 1 := by
      -- The positive branch forces both summands to be `1`.
      exact summands_eq_one_of_zero_one_neg_one_add_eq_two hDeletedValue hRowValue hTwo
    refine ⟨s, σ, ?_⟩
    refine ⟨Or.inl ⟨rfl, rfl⟩, hs, ?_, ?_⟩
    · rw [hSplit]
      exact hTwo
    · simpa [rowTerm] using hPair.2
  · let s' : {i // i ≠ r} → Bool := fun i ↦ !s i
    have hs' :
        ∀ j',
          (∑ i, (if s' i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
            (∑ i, (if s' i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
              (∑ i, (if s' i then (1 : ℤ) else -1) *
                ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1 := by
      -- Complementing the deleted-row signs preserves the balance family.
      simpa [s'] using deletedRowBalanceFamily_compl s hs
    have hPair : deletedSum = -1 ∧ rowTerm = -1 := by
      -- The negative branch forces both summands to be `-1`.
      exact
        summands_eq_neg_one_of_zero_one_neg_one_add_eq_neg_two hDeletedValue hRowValue hNegTwo
    have hCompl :
        extend_deleted_row_signing r (!σ) s' =
          fun i ↦ !(extend_deleted_row_signing r σ s i) := by
      -- Flipping the deleted signs and the distinguished-row sign flips the whole extension.
      simpa [s'] using extend_deleted_row_signing_compl r σ s
    have hFlippedSum :
        (∑ i, (if extend_deleted_row_signing r (!σ) s' i then (1 : ℤ) else -1) * B i j) =
          -(∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) := by
      -- The complemented extension negates the bad full-column sum.
      calc
        (∑ i, (if extend_deleted_row_signing r (!σ) s' i then (1 : ℤ) else -1) * B i j)
            = ∑ i, (if !(extend_deleted_row_signing r σ s i) then (1 : ℤ) else -1) * B i j := by
                simp [hCompl]
        _ = -(∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) := by
              simpa using signed_column_sum_compl_eq_neg B (extend_deleted_row_signing r σ s) j
    have hRowCompl :
        ((if !σ then (1 : ℤ) else -1) * B r j) = -(rowTerm) := by
      cases σ <;> simp [rowTerm]
    refine ⟨s', !σ, ?_⟩
    refine ⟨Or.inr ⟨rfl, rfl⟩, hs', ?_, ?_⟩
    · calc
        (∑ i, (if extend_deleted_row_signing r (!σ) s' i then (1 : ℤ) else -1) * B i j)
            = -(∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) :=
              hFlippedSum
        _ = -(deletedSum + rowTerm) := by rw [hSplit]
        _ = -(-2 : ℤ) := by rw [hNegTwo]
        _ = 2 := by norm_num
    · calc
        ((if !σ then (1 : ℤ) else -1) * B r j) = -(rowTerm) := hRowCompl
        _ = -(-1 : ℤ) := by rw [hPair.2]
        _ = 1 := by norm_num

/-- Helper for Theorem 4.59: a deleted-row signing on a bad row restriction can be normalized so
that some extended signed column sum is exactly `2`. -/
lemma exists_normalized_critical_column_of_deleted_row_signing
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (hB : HasZeroOneNegOneEntries B)
    (hBad : ¬ ∃ red blue : Finset ι, is_equitable_row_bicoloring B red blue)
    (r : ι)
    (hDeleted :
      ∃ s : {i // i ≠ r} → Bool,
        ∀ j,
          (∑ i, (if s i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 0 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1 ∨
              (∑ i, (if s i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = -1) :
    ∃ s : {i // i ≠ r} → Bool, ∃ σ : Bool, ∃ j : κ,
      (∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') = -1) ∧
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 2 := by
  classical
  rcases hDeleted with ⟨s, hs⟩
  rcases exists_unbalanced_column_of_extended_deleted_row_signing B hBad r true s with
    ⟨j, hj⟩
  have hSplit :
      (∑ i, (if extend_deleted_row_signing r true s i then (1 : ℤ) else -1) * B i j) =
        (∑ i : {i // i ≠ r},
          (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) + B r j := by
    -- With `σ = true`, the missing-row term is exactly the original matrix entry.
    simpa using
      extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term B r true s j
  have hRowValue :
      B r j = 0 ∨ B r j = 1 ∨ B r j = -1 := by
    -- The distinguished row entry is still a `(0, ±1)` value.
    simpa using HasZeroOneNegOneEntries.apply hB r j
  have hTwoOrNegTwo :
      (∑ i, (if extend_deleted_row_signing r true s i then (1 : ℤ) else -1) * B i j) = 2 ∨
        (∑ i, (if extend_deleted_row_signing r true s i then (1 : ℤ) else -1) * B i j) = -2 := by
    -- Rewrite the bad full sum as deleted contribution plus the missing-row term.
    have hBadSum :
        ¬ (((∑ i : {i // i ≠ r},
              (if s i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) + B r j) = 0 ∨
          ((∑ i : {i // i ≠ r},
              (if s i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) + B r j) = 1 ∨
          ((∑ i : {i // i ≠ r},
              (if s i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) + B r j) = -1) := by
      -- Transfer the bad-column witness through the previously established sum split.
      intro hBalanced
      apply hj
      rw [hSplit]
      exact hBalanced
    have hDeletedValue :
        (∑ i : {i // i ≠ r},
          (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 0 ∨
          (∑ i : {i // i ≠ r},
            (if s i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1 ∨
            (∑ i : {i // i ≠ r},
              (if s i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = -1 :=
      hs j
    have hSum :=
      full_signed_sum_eq_two_or_neg_two_of_zero_one_neg_one hDeletedValue hRowValue hBadSum
    rcases hSum with hSum | hSum
    · left
      rw [hSplit]
      exact hSum
    · right
      rw [hSplit]
      exact hSum
  rcases hTwoOrNegTwo with hTwo | hNegTwo
  · -- The positive critical column already has the desired normalization.
    exact ⟨s, true, j, hs, hTwo⟩
  · let s' : {i // i ≠ r} → Bool := fun i ↦ !(s i)
    have hs' :
        ∀ j',
          (∑ i, (if s' i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') = 0 ∨
            (∑ i, (if s' i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') = 1 ∨
              (∑ i, (if s' i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') = -1 := by
      intro j'
      -- Complementing all deleted-row signs negates the deleted signed sum.
      have hNegDeleted :
          (∑ i, (if s' i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') =
            -(∑ i, (if s i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') := by
        simpa [s'] using
          signed_column_sum_compl_eq_neg
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) s j'
      rcases hs j' with hZero | hOne | hNegOne
      · left
        calc
          (∑ i, (if s' i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') =
            -(∑ i, (if s i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') :=
              hNegDeleted
          _ = 0 := by rw [hZero]; norm_num
      · right
        right
        calc
          (∑ i, (if s' i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') =
            -(∑ i, (if s i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') :=
              hNegDeleted
          _ = -1 := by rw [hOne]
      · right
        left
        calc
          (∑ i, (if s' i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') =
            -(∑ i, (if s i then (1 : ℤ) else -1) *
                (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j') :=
              hNegDeleted
          _ = 1 := by rw [hNegOne]; norm_num
    have hCompl :
        extend_deleted_row_signing r false s' =
          fun i ↦ !(extend_deleted_row_signing r true s i) := by
      -- Flipping the deleted-row signs and the missing-row sign flips the whole extension.
      simpa [s'] using extend_deleted_row_signing_compl r true s
    have hFlippedSum :
        (∑ i, (if extend_deleted_row_signing r false s' i then (1 : ℤ) else -1) * B i j) =
          -(∑ i, (if extend_deleted_row_signing r true s i then (1 : ℤ) else -1) * B i j) := by
      -- Apply the global sign-flip identity to the extended signing itself.
      calc
        (∑ i, (if extend_deleted_row_signing r false s' i then (1 : ℤ) else -1) * B i j)
            = ∑ i, (if !(extend_deleted_row_signing r true s i) then (1 : ℤ) else -1) * B i j := by
                simp [hCompl]
        _ = -(∑ i, (if extend_deleted_row_signing r true s i then (1 : ℤ) else -1) * B i j) := by
              simpa using signed_column_sum_compl_eq_neg B (extend_deleted_row_signing r true s) j
    refine ⟨s', false, j, hs', ?_⟩
    -- The complemented full signing turns the `-2` witness into the required `2`.
    calc
      (∑ i, (if extend_deleted_row_signing r false s' i then (1 : ℤ) else -1) * B i j)
          = -(∑ i, (if extend_deleted_row_signing r true s i then (1 : ℤ) else -1) * B i j) :=
            hFlippedSum
      _ = -(-2 : ℤ) := by rw [hNegTwo]
      _ = 2 := by norm_num

/-- Helper for Theorem 4.59: a finite `(0, ±1)`-family with even total sum has even nonzero
support. -/
lemma even_support_of_zero_one_neg_one_even_sum
    {ι : Type*} [Fintype ι] (f : ι → ℤ)
    (hf : ∀ i, f i = 0 ∨ f i = 1 ∨ f i = -1)
    (hs : Even (∑ i, f i)) :
    Even (Function.support f).ncard := by
  classical
  have hIndicator :
      (∑ i, (((f i : ℤ) : ZMod 2))) =
        ∑ i, if f i ≠ 0 then (1 : ZMod 2) else 0 := by
    calc
      (∑ i, (((f i : ℤ) : ZMod 2)))
          = ∑ i, (if f i = 0 then 0 else 1) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa using zmod_two_cast_eq_indicator_of_zero_one_neg_one (hf i)
      _ = ∑ i, if f i ≠ 0 then (1 : ZMod 2) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hfi : f i = 0 <;> simp [hfi]
  have hCardZero :
      ((((Finset.univ.filter fun i ↦ f i ≠ 0).card : ℕ) : ZMod 2)) = 0 := by
    calc
      ((((Finset.univ.filter fun i ↦ f i ≠ 0).card : ℕ) : ZMod 2))
          = Finset.sum (Finset.univ.filter (fun i ↦ f i ≠ 0)) (fun _ ↦ (1 : ZMod 2)) := by
              symm
              rw [Finset.card_eq_sum_ones]
              simp
      _ = ∑ i, if f i ≠ 0 then (1 : ZMod 2) else 0 := by
            rw [Finset.sum_filter]
      _ = ∑ i, (((f i : ℤ) : ZMod 2)) := hIndicator.symm
      _ = (((∑ i, f i : ℤ) : ZMod 2)) := by simp
      _ = 0 := Even.intCast_zmod_two hs
  have hEvenToFinset : Even ({i | f i ≠ 0}.toFinset.card) := by
    simpa [Set.toFinset_setOf] using (ZMod.natCast_eq_zero_iff_even.1 hCardZero)
  -- Convert the finitary support cardinality back to `Function.support`.
  simpa [Function.support, Set.ncard_eq_toFinset_card'] using hEvenToFinset

/-- Helper for Theorem 4.59: signing a full column by an extended deleted-row Boolean assignment
preserves even column sums when the underlying column has even nonzero support. -/
lemma even_extended_signed_column_sum_of_even_support
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r : ι) (σ : Bool) (s : {i // i ≠ r} → Bool) (j : κ)
    (hEvenSupport : Even (Function.support fun i ↦ B i j).ncard) :
    Even (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) := by
  let signedColumn : ι → ℤ := fun i ↦
    (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j
  have hValues : ∀ i, signedColumn i = 0 ∨ signedColumn i = 1 ∨ signedColumn i = -1 := by
    intro i
    -- Each signed entry is still a `(0, ±1)` value.
    simpa [signedColumn] using
      signed_zero_one_neg_one (extend_deleted_row_signing r σ s i)
        (HasZeroOneNegOneEntries.apply hB i j)
  have hSupport :
      Function.support signedColumn = Function.support fun i ↦ B i j := by
    ext i
    -- Multiplying by the Boolean sign does not change whether the entry is zero.
    by_cases hi : extend_deleted_row_signing r σ s i
    · simp [signedColumn, hi]
    · simp [signedColumn, hi]
  -- Transfer the even-support parity lemma to the signed full column.
  simpa [signedColumn, hSupport] using
    even_sum_of_zero_one_neg_one_even_support signedColumn hValues
      (by simpa [hSupport] using hEvenSupport)

/-- Helper for Theorem 4.59: for a fixed deleted-row signing on an even-support column, the
deleted signed sum vanishes exactly when the distinguished row entry vanishes. -/
lemma deleted_signed_column_sum_eq_zero_iff_entry_eq_zero_of_even_support
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r : ι) (σ : Bool) (s : {i // i ≠ r} → Bool) (j : κ)
    (hDeleted :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 0 ∨
        (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = -1)
    (hEvenSupport : Even (Function.support fun i ↦ B i j).ncard) :
    (∑ i, (if s i then (1 : ℤ) else -1) *
        (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 0 ↔
      B r j = 0 := by
  let deletedSum : ℤ :=
    ∑ i, (if s i then (1 : ℤ) else -1) *
      (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j
  let rowTerm : ℤ := (if σ then (1 : ℤ) else -1) * B r j
  have hFullEven :
      Even (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) := by
    -- The extended signed full column inherits even parity from the original even-support column.
    exact even_extended_signed_column_sum_of_even_support hB r σ s j hEvenSupport
  have hSplit :
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) =
        deletedSum + rowTerm := by
    -- Split the full signed column into the deleted part and the distinguished-row contribution.
    simpa [deletedSum, rowTerm] using
      extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term B r σ s j
  have hDeletedValue :
      deletedSum = 0 ∨ deletedSum = 1 ∨ deletedSum = -1 := by
    -- The deleted witness already restricts the deleted sum to `{0, 1, -1}`.
    simpa [deletedSum] using hDeleted
  have hRowValue :
      rowTerm = 0 ∨ rowTerm = 1 ∨ rowTerm = -1 := by
    -- The distinguished-row contribution is a signed `(0, ±1)` entry.
    simpa [rowTerm] using signed_zero_one_neg_one σ (HasZeroOneNegOneEntries.apply hB r j)
  constructor
  · intro hZero
    have hZero' : deletedSum = 0 := by
      simpa [deletedSum] using hZero
    have hRowEven : Even rowTerm := by
      -- If the deleted part vanishes, the full even sum is exactly the row term.
      have hFullEq :
          (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = rowTerm := by
        rw [hSplit, hZero', zero_add]
      rw [← hFullEq]
      exact hFullEven
    rcases hRowValue with hRowZero | hRowOne | hRowNegOne
    · have hEntryValue : B r j = 0 ∨ B r j = 1 ∨ B r j = -1 := HasZeroOneNegOneEntries.apply hB r j
      rcases hEntryValue with hEntryZero | hEntryOne | hEntryNegOne
      · exact hEntryZero
      · exfalso
        cases σ <;> simp [rowTerm, hEntryOne] at hRowZero
      · exfalso
        cases σ <;> simp [rowTerm, hEntryNegOne] at hRowZero
    · rw [hRowOne] at hRowEven
      norm_num at hRowEven
    · rw [hRowNegOne] at hRowEven
      norm_num at hRowEven
  · intro hEntryZero
    have hRowZero : rowTerm = 0 := by
      simp [rowTerm, hEntryZero]
    have hDeletedEven : Even deletedSum := by
      -- If the row entry vanishes, the deleted sum is the full even signed column sum.
      have hFullEq :
          (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = deletedSum := by
        rw [hSplit, hRowZero, add_zero]
      rw [← hFullEq]
      exact hFullEven
    rcases hDeletedValue with hDeletedZero | hDeletedOne | hDeletedNegOne
    · simpa [deletedSum] using hDeletedZero
    · rw [hDeletedOne] at hDeletedEven
      norm_num at hDeletedEven
    · rw [hDeletedNegOne] at hDeletedEven
      norm_num at hDeletedEven

/-- Helper for Theorem 4.59: on an even-support column, a deleted-row witness with deleted sum
`1` or `-1` forces the distinguished row entry to be nonzero. -/
private lemma missingRow_nonzero_of_deletedSum_eq_one_or_negOne_of_evenSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r : ι) (σ : Bool) (s : {i // i ≠ r} → Bool) (j : κ)
    (hDeletedEq :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1 ∨
        (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = -1)
    (hEvenSupport : Even (Function.support fun i ↦ B i j).ncard) :
    B r j ≠ 0 := by
  intro hZero
  have hDeletedZero :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 0 := by
    have hDeletedValue :
        (∑ i, (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = -1 := by
      rcases hDeletedEq with hOne | hNegOne
      · exact Or.inr (Or.inl hOne)
      · exact Or.inr (Or.inr hNegOne)
    -- Convert the zero row entry into a vanishing deleted sum through the even-support parity API.
    exact
      (deleted_signed_column_sum_eq_zero_iff_entry_eq_zero_of_even_support
        hB r σ s j hDeletedValue hEvenSupport).2 hZero
  rcases hDeletedEq with hOne | hNegOne
  · rw [hOne] at hDeletedZero
    norm_num at hDeletedZero
  · rw [hNegOne] at hDeletedZero
    norm_num at hDeletedZero

/-- Helper for Theorem 4.59: any nonzero `(0, ±1)` entry admits a Boolean sign making its signed
contribution equal to `1`. -/
private lemma exists_bool_sign_mul_eq_one_of_zeroOneNegOne_nonzero
    {z : ℤ} (hz : z = 0 ∨ z = 1 ∨ z = -1) (hne : z ≠ 0) :
    ∃ σ : Bool, ((if σ then (1 : ℤ) else -1) * z) = 1 := by
  rcases hz with hZero | hOne | hNegOne
  · exact (hne hZero).elim
  · refine ⟨true, ?_⟩
    simp [hOne]
  · refine ⟨false, ?_⟩
    simp [hNegOne]

/-- Helper for Theorem 4.59: if a deleted-row balance with signed kept-row contribution `1`
vanishes, then the exact common-core contribution is `-1`. -/
private lemma commonCore_eq_neg_one_of_deleted_eq_zero_and_signedKeep_eq_one
    {core rowTerm : ℤ}
    (hDeleted : core + rowTerm = 0)
    (hRow : rowTerm = 1) :
    core = -1 := by
  -- Solve the common-core value by subtracting the normalized kept-row contribution.
  linarith

/-- Helper for Theorem 4.59: complementing a signing on an exact row-restricted submatrix negates
its signed column sum. -/
private lemma restrictedSignedColumnSum_compl_eq_neg
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (A : Finset ι) (s : {i // i ∈ A} → Bool) (j : κ) :
    (∑ i : {x // x ∈ A},
        (if !s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) =
      -(∑ i : {x // x ∈ A},
          (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) := by
  -- This is the exact-core version of the global complement identity, specialized once so later
  -- bad-column arguments can stay in the stable `A`-restricted spelling.
  simpa using
    signed_column_sum_compl_eq_neg
      (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) s j

/-- Helper for Theorem 4.59: `sharedCriticalOverlapCoeffEqOnBadSupport B A s₁ s₂ j` records the
fixed-column common-core overlap premise that the two signings have the same `±1` coefficient on
every supported row of the exact `A`-restricted column. -/
private def sharedCriticalOverlapCoeffEqOnBadSupport
    {ι : Type*} [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (A : Finset ι)
    (s₁ s₂ : {i // i ∈ A} → Bool) (j : κ) : Prop :=
  ∀ i : {x // x ∈ A},
    ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j) ≠ 0 →
      (if s₁ i then (1 : ℤ) else -1) = (if s₂ i then (1 : ℤ) else -1)

/-- Helper for Theorem 4.59: `sharedCriticalBadSupport B A j` is the support of the fixed column
`j`, viewed inside the exact common-core row type `{i // i ∈ A}`. -/
private def sharedCriticalBadSupport
    {ι : Type*} [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (A : Finset ι) (j : κ) :=
  {i : {x // x ∈ A} //
    ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j) ≠ 0}

/-- Helper for Theorem 4.59: proving sign agreement on the support subtype of a fixed
exact-common-core column is equivalent to proving it rowwise with the support hypothesis as an
explicit premise. -/
private lemma sharedCriticalSignEqOnBadSupport_of_restricted
    {ι : Type*} [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (A : Finset ι) (j : κ)
    (s₁ s₂ : {i // i ∈ A} → Bool)
    (hRestricted :
      ∀ i : sharedCriticalBadSupport B A j, s₁ i.1 = s₂ i.1) :
    ∀ i : {x // x ∈ A},
      ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j) ≠ 0 →
        s₁ i = s₂ i := by
  intro i hBij
  -- Package the supported row into the fixed support subtype, then project the restricted
  -- sign-equality statement back to the original rowwise formulation.
  exact hRestricted ⟨i, hBij⟩

/-- Helper for Theorem 4.59: two exact-row-restricted signings give the same signed column sum
whenever their coefficients agree on every row where the column entry is nonzero. -/
private lemma restrictedSignedColumnSum_eq_of_coeffEq_on_support
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (A : Finset ι)
    (s₁ s₂ : {i // i ∈ A} → Bool) (j : κ)
    (hCoeff :
      ∀ i : {x // x ∈ A},
        ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j) ≠ 0 →
          (if s₁ i then (1 : ℤ) else -1) =
            (if s₂ i then (1 : ℤ) else -1)) :
    (∑ i : {x // x ∈ A},
        (if s₁ i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) =
      (∑ i : {x // x ∈ A},
        (if s₂ i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) := by
  -- Reduce the restricted signed-sum equality to the rows where the fixed column is actually
  -- supported; zero entries contribute `0` regardless of the chosen Boolean sign.
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hBij :
      ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j) = 0
  · have hBij' : B i j = 0 := by
      simpa [Matrix.submatrix_apply] using hBij
    simp [hBij']
  · rw [hCoeff i hBij]

/-- Helper for Theorem 4.59: agreement of two Boolean signings on the supported rows of a fixed
exact-common-core column upgrades immediately to agreement of their `±1` coefficients there. -/
private lemma sharedCriticalOverlapCoeffEqOnBadSupport_of_signEq
    {ι : Type*} [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (A : Finset ι)
    (s₁ s₂ : {i // i ∈ A} → Bool) (j : κ)
    (hSignEq :
      ∀ i : {x // x ∈ A},
        ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j) ≠ 0 →
          s₁ i = s₂ i) :
    sharedCriticalOverlapCoeffEqOnBadSupport B A s₁ s₂ j := by
  intro i hBij
  -- Once the Boolean signs agree on the supported rows, the corresponding `±1` coefficients are
  -- literally the same.
  simp [hSignEq i hBij]

/-- Helper for Theorem 4.59: the packaged fixed-column overlap premise upgrades immediately to the
corresponding equality of exact-common-core signed sums. -/
private lemma sharedCriticalCoreSumsEq_of_overlapCoeffEqOnBadSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (A : Finset ι)
    (s₁ s₂ : {i // i ∈ A} → Bool) (j : κ)
    (hCoeff : sharedCriticalOverlapCoeffEqOnBadSupport B A s₁ s₂ j) :
    (∑ i : {x // x ∈ A},
        (if s₁ i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) =
      (∑ i : {x // x ∈ A},
        (if s₂ i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) := by
  -- This is the exact-core wrapper around the supportwise coefficient premise.
  exact restrictedSignedColumnSum_eq_of_coeffEq_on_support B A s₁ s₂ j hCoeff

/-- Helper for Theorem 4.59: once the bad and aligned exact-core sums are identified, the zero
branch values `1` and `-1` are incompatible. -/
private lemma sharedCriticalZeroBranchContradiction
    {badCore alignedCore : ℤ}
    (hEq : badCore = alignedCore)
    (hBad : badCore = 1)
    (hAligned : alignedCore = -1) :
    False := by
  -- Equal exact-core sums cannot simultaneously take the normalized zero-branch values `1` and
  -- `-1`.
  linarith

/-- Helper for Theorem 4.59: if two exact-common-core signings have the same `±1` coefficients on
the supported rows of the fixed bad column, then the aligned zero branch contradicts the
normalized core values `1` and `-1`. -/
private lemma sharedCriticalAlignedZeroBranchImpossible_of_overlapCoeffEq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (A : Finset ι)
    (sBad sAligned : {i // i ∈ A} → Bool) (j : κ)
    (hCoeff : sharedCriticalOverlapCoeffEqOnBadSupport B A sBad sAligned j)
    (hBadCore :
      (∑ i : {x // x ∈ A},
          (if sBad i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) = 1)
    (hAlignedCore :
      (∑ i : {x // x ∈ A},
          (if sAligned i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) = -1) :
    False := by
  have hCoreEq :
      (∑ i : {x // x ∈ A},
          (if sBad i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) =
        (∑ i : {x // x ∈ A},
          (if sAligned i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) := by
    -- Upgrade the fixed-column overlap premise to equality of the two exact-core signed sums.
    exact
      sharedCriticalCoreSumsEq_of_overlapCoeffEqOnBadSupport
        B A sBad sAligned j hCoeff
  -- The generic zero-branch contradiction now closes the normalized `1 = -1` clash.
  exact sharedCriticalZeroBranchContradiction hCoreEq hBadCore hAlignedCore

/-- Helper for Theorem 4.59: if a deleted-row balance with signed kept-row contribution `1`
equals `1` or `-1`, then the exact common-core contribution is `0` or `-2`. -/
private lemma commonCore_eq_zero_or_negTwo_of_deleted_eq_one_or_negOne_and_signedKeep_eq_one
    {core rowTerm : ℤ}
    (hDeleted : core + rowTerm = 1 ∨ core + rowTerm = -1)
    (hRow : rowTerm = 1) :
    core = 0 ∨ core = -2 := by
  -- Normalize the deleted-row value against the fixed kept-row contribution `1`.
  rcases hDeleted with hDeleted | hDeleted
  · left
    linarith
  · right
    linarith

/-- Helper for Theorem 4.59: if a deleted-row balance with signed kept-row contribution `1`
has exact common-core contribution `-2`, then the deleted-row sum itself is `-1`. -/
private lemma deleted_eq_neg_one_of_commonCore_eq_negTwo_and_signedKeep_eq_one
    {core rowTerm : ℤ}
    (hCore : core = -2)
    (hRow : rowTerm = 1) :
    core + rowTerm = -1 := by
  -- Substitute the normalized common-core and kept-row values and simplify.
  linarith

/-- Helper for Theorem 4.59: once the deleted-row sum is `1`, a nonzero distinguished row entry
can be signed so that the full extended signed column sum becomes `2`. -/
private lemma exists_missingRow_sign_sum_eq_two_of_deletedSum_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r : ι) (s : {i // i ≠ r} → Bool) (j : κ)
    (hDeletedEq :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1)
    (hne : B r j ≠ 0) :
    ∃ σ : Bool,
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 2 := by
  rcases
      exists_bool_sign_mul_eq_one_of_zeroOneNegOne_nonzero
        (HasZeroOneNegOneEntries.apply hB r j) hne with
    ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  -- Split the full signed column into the deleted-row contribution and the chosen pivot term.
  calc
    (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j)
        =
      (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) +
        ((if σ then (1 : ℤ) else -1) * B r j) := by
            simpa using extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term B r σ s j
    _ = 1 + 1 := by rw [hDeletedEq, hσ]
    _ = 2 := by norm_num

/-- Helper for Theorem 4.59: if a deleted-row sum is `-1`, then complementing the deleted-row
signing turns it into a normalized critical full-column witness. -/
private lemma exists_missingRow_sign_sum_eq_two_of_deletedSum_eq_negOne
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r : ι) (s : {i // i ≠ r} → Bool) (j : κ)
    (hDeletedEq :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = -1)
    (hne : B r j ≠ 0) :
    ∃ σ : Bool,
      (∑ i, (if extend_deleted_row_signing r σ (fun i ↦ !s i) i then (1 : ℤ) else -1) * B i j) = 2 := by
  have hDeletedComplEq :
      (∑ i, (if (!s i) then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1 := by
    -- Complementing every deleted-row sign negates the deleted signed column sum.
    calc
      (∑ i, (if (!s i) then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j)
          =
        -(∑ i, (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) := by
              simpa using
                signed_column_sum_compl_eq_neg
                  (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) s j
      _ = 1 := by
        rw [hDeletedEq]
        norm_num
  -- After the complement rewrite, reuse the existing `deleted sum = 1` witness API.
  exact
    exists_missingRow_sign_sum_eq_two_of_deletedSum_eq_one
      hB r (fun i ↦ !s i) j hDeletedComplEq hne

/-- Helper for Theorem 4.59: a normalized critical column has a nonzero pivot entry and even full
column support. -/
lemma criticalColumn_deletedSum_and_signedPivot_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r : ι) (s : {i // i ≠ r} → Bool) (σ : Bool) (j : κ)
    (hDeleted :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 0 ∨
        (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = -1)
    (hCritical :
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 2) :
    (∑ i, (if s i then (1 : ℤ) else -1) *
        (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1 ∧
      ((if σ then (1 : ℤ) else -1) * B r j) = 1 := by
  let deletedSum : ℤ :=
    ∑ i, (if s i then (1 : ℤ) else -1) *
      (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j
  let rowTerm : ℤ := (if σ then (1 : ℤ) else -1) * B r j
  have hSplit :
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) =
        deletedSum + rowTerm := by
    -- Split the critical full-column sum into the deleted-row part and the pivot-row term.
    simpa [deletedSum, rowTerm] using
      extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term B r σ s j
  have hDeletedValue :
      deletedSum = 0 ∨ deletedSum = 1 ∨ deletedSum = -1 := by
    -- The deleted-row witness already constrains the deleted contribution to `{0, 1, -1}`.
    simpa [deletedSum] using hDeleted
  have hRowTermValue :
      rowTerm = 0 ∨ rowTerm = 1 ∨ rowTerm = -1 := by
    -- The pivot term is still a signed `(0, ±1)` entry.
    simpa [rowTerm] using signed_zero_one_neg_one σ (HasZeroOneNegOneEntries.apply hB r j)
  have hPair : deletedSum = 1 ∧ rowTerm = 1 := by
    -- Since the full signed critical column sums to `2`, both summands must be `1`.
    apply summands_eq_one_of_zero_one_neg_one_add_eq_two hDeletedValue hRowTermValue
    calc
      deletedSum + rowTerm
          = ∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j := by
              rw [hSplit]
      _ = 2 := hCritical
  simpa [deletedSum, rowTerm] using hPair

/-- Helper for Theorem 4.59: a normalized critical column has a nonzero pivot entry and even full
column support. -/
lemma criticalColumn_hasNonzeroPivot_and_evenColumnSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    (r : ι) (s : {i // i ≠ r} → Bool) (σ : Bool) (j : κ)
    (hDeleted :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 0 ∨
        (∑ i, (if s i then (1 : ℤ) else -1) *
          (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = 1 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j) = -1)
    (hCritical :
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j) = 2) :
    B r j ≠ 0 ∧ Even (Function.support fun i ↦ B i j).ncard := by
  let deletedSum : ℤ :=
    ∑ i, (if s i then (1 : ℤ) else -1) *
      (B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j
  let rowTerm : ℤ := (if σ then (1 : ℤ) else -1) * B r j
  let signedColumn : ι → ℤ :=
    fun i ↦ (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j
  have hSplit :
      (∑ i, signedColumn i) = deletedSum + rowTerm := by
    -- Split the full signed sum into the deleted-row contribution and the pivot-row term.
    simpa [deletedSum, rowTerm, signedColumn] using
      extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term B r σ s j
  have hDeletedValue :
      deletedSum = 0 ∨ deletedSum = 1 ∨ deletedSum = -1 := by
    simpa [deletedSum] using hDeleted
  have hRowTermValue :
      rowTerm = 0 ∨ rowTerm = 1 ∨ rowTerm = -1 := by
    -- The pivot contribution is still a signed `(0, ±1)` entry.
    simpa [rowTerm] using signed_zero_one_neg_one σ (HasZeroOneNegOneEntries.apply hB r j)
  have hOnePair : deletedSum = 1 ∧ rowTerm = 1 := by
    -- Reuse the extracted `1 + 1` split for this critical column.
    simpa [deletedSum, rowTerm] using
      criticalColumn_deletedSum_and_signedPivot_eq_one hB r s σ j hDeleted hCritical
  have hNonzero : B r j ≠ 0 := by
    -- A pivot contribution equal to `1` cannot come from a zero matrix entry.
    intro hZero
    have hRowTermZero : rowTerm = 0 := by simp [rowTerm, hZero]
    rw [hRowTermZero] at hOnePair
    norm_num at hOnePair
  have hSignedValues :
      ∀ i, signedColumn i = 0 ∨ signedColumn i = 1 ∨ signedColumn i = -1 := by
    intro i
    -- Every full signed-column entry is still in `{0, 1, -1}`.
    simpa [signedColumn] using
      signed_zero_one_neg_one (extend_deleted_row_signing r σ s i)
        (HasZeroOneNegOneEntries.apply hB i j)
  have hEvenSignedSupport :
      Even (Function.support signedColumn).ncard := by
    -- The normalized sum `2` is even, so the signed-column support has even cardinality.
    apply even_support_of_zero_one_neg_one_even_sum signedColumn hSignedValues
    rw [show (∑ i, signedColumn i) = 2 by simpa [signedColumn] using hCritical]
    norm_num
  have hSupportEq :
      Function.support signedColumn = Function.support (fun i ↦ B i j) := by
    -- Multiplying by a Boolean sign does not change which entries are zero.
    ext i
    dsimp [signedColumn]
    cases hsi : extend_deleted_row_signing r σ s i <;> by_cases hBij : B i j = 0 <;>
      simp [hsi, hBij]
  exact ⟨hNonzero, by simpa [hSupportEq] using hEvenSignedSupport⟩

/-- Helper for Theorem 4.59: encode a `(0, ±1)` column entry in a three-valued finite pattern
codomain. -/
def zeroOneNegOneCode (z : ℤ) : Fin 3 :=
  if z = 0 then 0 else if z = 1 then 1 else 2

/-- Helper for Theorem 4.59: the row-restricted pattern of a column is a finite object, so Hall's
theorem can be applied without assuming the ambient column type is finite. -/
def zeroOneNegOneColumnPattern
    {ι : Type*} {κ : Type*} (B : Matrix ι κ ℤ) (j : κ) : ι → Fin 3 :=
  fun i ↦ zeroOneNegOneCode (B i j)

/-- Helper for Theorem 4.59: on `{0, 1, -1}`, the finite code `zeroOneNegOneCode` loses no
information. -/
lemma zeroOneNegOneCode_eq_iff_of_zero_one_neg_one
    {a b : ℤ}
    (ha : a = 0 ∨ a = 1 ∨ a = -1)
    (hb : b = 0 ∨ b = 1 ∨ b = -1) :
    zeroOneNegOneCode a = zeroOneNegOneCode b ↔ a = b := by
  -- Exhaust the nine possible `{0, 1, -1}` pairs.
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp [zeroOneNegOneCode]

/-- Helper for Theorem 4.59: two `(0, ±1)` columns have the same finite pattern exactly when they
agree entrywise. -/
lemma zeroOneNegOneColumnPattern_eq_iff
    {ι : Type*} {κ : Type*} {B : Matrix ι κ ℤ}
    (hB : HasZeroOneNegOneEntries B) {j₁ j₂ : κ} :
    zeroOneNegOneColumnPattern B j₁ = zeroOneNegOneColumnPattern B j₂ ↔
      ∀ i, B i j₁ = B i j₂ := by
  constructor
  · intro hPattern i
    -- Evaluate the pattern equality at row `i` and decode the resulting three-valued code.
    have hi : zeroOneNegOneCode (B i j₁) = zeroOneNegOneCode (B i j₂) :=
      congrArg (fun f ↦ f i) hPattern
    exact
      (zeroOneNegOneCode_eq_iff_of_zero_one_neg_one
        (HasZeroOneNegOneEntries.apply hB i j₁)
        (HasZeroOneNegOneEntries.apply hB i j₂)).mp hi
  · intro hEntries
    -- Re-encode the entrywise equality row by row.
    funext i
    simp [zeroOneNegOneColumnPattern, hEntries i]

/-- Helper for Theorem 4.59: a critical witness can be transported across two actual columns with
the same three-valued row pattern. -/
lemma criticalWitness_of_columnPatternEq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    {r : ι} {j₁ j₂ : κ}
    (hCritical :
      ∃ s : {i // i ≠ r} → Bool, ∃ σ : Bool,
        (∀ j',
          (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
              (∑ i, (if s i then (1 : ℤ) else -1) *
                ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1) ∧
        (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j₁) = 2)
    (hPattern : zeroOneNegOneColumnPattern B j₂ = zeroOneNegOneColumnPattern B j₁) :
    ∃ s : {i // i ≠ r} → Bool, ∃ σ : Bool,
      (∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j')) = -1) ∧
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j₂) = 2 := by
  rcases hCritical with ⟨s, σ, hs, hSumTwo⟩
  refine ⟨s, σ, hs, ?_⟩
  have hEntries : ∀ i, B i j₂ = B i j₁ :=
    (zeroOneNegOneColumnPattern_eq_iff hB).1 hPattern
  -- Rewrite the critical full-column sum entrywise along the pattern equality.
  calc
    (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j₂)
        = ∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i j₁ := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hEntries i]
    _ = 2 := hSumTwo

/-- Helper for Theorem 4.59: deleting a second row from a deleted-row witness splits the original
deleted-row sum into the exact double-deleted core plus the second row term. -/
private lemma sharedCriticalWitnessCoreSplit
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) {r₁ r₂ : ι} (hNe : r₁ ≠ r₂)
    (s : {i // i ≠ r₁} → Bool) (j : κ) :
    let A : Finset ι := ((Finset.univ : Finset ι).erase r₁).erase r₂
    let sA : {i // i ∈ A} → Bool := fun i ↦ s ((doubleErasedRowsEquiv r₁ r₂ hNe) i).1
    (∑ i : {i // i ≠ r₁},
        (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j)) =
      (∑ i : {i // i ∈ A},
        (if sA i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
        ((if s ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B r₂ j) := by
  let A : Finset ι := ((Finset.univ : Finset ι).erase r₁).erase r₂
  let r₂' : {i // i ≠ r₁} := ⟨r₂, Ne.symm hNe⟩
  let coreNested : {i : {k // k ≠ r₁} // i ≠ r₂'} → ℤ := fun i ↦
    (if s i.1 then (1 : ℤ) else -1) *
      ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i.1 j)
  have hSplit :
      (∑ i : {i // i ≠ r₁},
          (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j)) =
        ((if s r₂' then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) r₂' j)) +
          ∑ i : {x : {k // k ≠ r₁} // x ≠ r₂'}, coreNested i := by
    -- Separate the `r₂` row from the once-deleted witness sum.
    simpa [r₂', coreNested] using
      (Fintype.sum_eq_add_sum_subtype_ne
        (fun i : {i // i ≠ r₁} ↦
          (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j))
        r₂')
  have hCore :
      (∑ i : {x : {k // k ≠ r₁} // x ≠ r₂'}, coreNested i) =
        ∑ i : {x // x ∈ A},
          (if s ((doubleErasedRowsEquiv r₁ r₂ hNe) i).1 then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j) := by
    -- Reindex the exact double-deleted core through the canonical equivalence of row types.
    symm
    refine Fintype.sum_equiv (doubleErasedRowsEquiv r₁ r₂ hNe) _ _ ?_
    intro i
    rfl
  -- Combine the `r₂` split with the exact-core reindexing.
  calc
    (∑ i : {i // i ≠ r₁},
        (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j))
        = ((if s r₂' then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) r₂' j)) +
            ∑ i : {x : {k // k ≠ r₁} // x ≠ r₂'}, coreNested i := hSplit
    _ = ((if s ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B r₂ j) +
          (∑ i : {x // x ∈ A},
            (if (fun i ↦ s ((doubleErasedRowsEquiv r₁ r₂ hNe) i).1) i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) := by
      rw [hCore]
      simp [r₂', Matrix.submatrix_apply]
    _ = (∑ i : {x // x ∈ A},
          (if (fun i ↦ s ((doubleErasedRowsEquiv r₁ r₂ hNe) i).1) i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
          ((if s ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B r₂ j) := by
      rw [add_comm]

/-- Helper for Theorem 4.59: on a shared critical column, the witness for `r₁` rewrites on the
exact double-deleted row set to a core-plus-`r₂` equation equal to `1`, while the `r₁` pivot term
itself is also `1`. -/
private lemma sharedCriticalWitnessNormalizedSplit
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    {r₁ r₂ : ι} (hNe : r₁ ≠ r₂) {j : κ}
    (s : {i // i ≠ r₁} → Bool) (σ : Bool)
    (hDeleted :
      ∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j')) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j')) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j')) = -1)
    (hCritical :
      (∑ i, (if extend_deleted_row_signing r₁ σ s i then (1 : ℤ) else -1) * B i j) = 2) :
    let A : Finset ι := ((Finset.univ : Finset ι).erase r₁).erase r₂
    let sA : {i // i ∈ A} → Bool := fun i ↦ s ((doubleErasedRowsEquiv r₁ r₂ hNe) i).1
    ((∑ i : {x // x ∈ A},
        (if sA i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
        ((if s ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B r₂ j) = 1) ∧
      (((if σ then (1 : ℤ) else -1) * B r₁ j) = 1) := by
  let A : Finset ι := ((Finset.univ : Finset ι).erase r₁).erase r₂
  let sA : {i // i ∈ A} → Bool := fun i ↦ s ((doubleErasedRowsEquiv r₁ r₂ hNe) i).1
  have hPair :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j)) = 1 ∧
        ((if σ then (1 : ℤ) else -1) * B r₁ j) = 1 := by
    -- Normalize the critical witness on its own deleted-row domain first.
    simpa using
      criticalColumn_deletedSum_and_signedPivot_eq_one hB r₁ s σ j (hDeleted j) hCritical
  constructor
  · -- Rewrite the deleted-row equation onto the exact double-deleted core plus the `r₂` term.
    calc
      (∑ i : {x // x ∈ A},
          (if sA i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
          ((if s ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B r₂ j)
          =
        ∑ i : {x // x ≠ r₁},
          (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j) := by
              simpa [A, sA] using (sharedCriticalWitnessCoreSplit B hNe s j).symm
      _ = 1 := hPair.1
  · -- Keep the `r₁` pivot normalization in its explicit ambient-row form.
    exact hPair.2

/-- Helper for Theorem 4.59: the deleted-row balance family for a shared witness rewrites on the
exact double-deleted row set to the common-core sum plus the opposite-row term. -/
private lemma sharedCriticalWitnessDeletedBalanceOnCommonCore
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) {r₁ r₂ : ι} (hNe : r₁ ≠ r₂)
    (s : {i // i ≠ r₁} → Bool)
    (hDeleted :
      ∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j')) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j')) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j')) = -1) :
    let A : Finset ι := ((Finset.univ : Finset ι).erase r₁).erase r₂
    let sA : {i // i ∈ A} → Bool := fun i ↦ s ((doubleErasedRowsEquiv r₁ r₂ hNe) i).1
    ∀ j',
      ((∑ i : {x // x ∈ A},
          (if sA i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j')) +
          ((if s ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B r₂ j')) = 0 ∨
        ((∑ i : {x // x ∈ A},
            (if sA i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j')) +
            ((if s ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B r₂ j')) = 1 ∨
          ((∑ i : {x // x ∈ A},
              (if sA i then (1 : ℤ) else -1) *
                ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j')) +
              ((if s ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B r₂ j')) = -1 := by
  intro A sA j'
  -- Rewrite the deleted-row sum once onto the exact double-deleted core spelling, then reuse the
  -- existing deleted balance hypothesis without any further transport.
  have hRewrite :
      ((∑ i : {x // x ∈ A},
          (if sA i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j')) +
          ((if s ⟨r₂, Ne.symm hNe⟩ then (1 : ℤ) else -1) * B r₂ j')) =
        ∑ i : {x // x ≠ r₁},
          (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₁) id) i j') := by
    simpa [A, sA] using (sharedCriticalWitnessCoreSplit B hNe s j').symm
  -- After the rewrite, the target is exactly the original deleted witness balance statement.
  rw [hRewrite]
  exact hDeleted j'

/-- Helper for Theorem 4.59: after aligning the kept-row sign with `τ`, the deleted-row balance
family for the second witness specializes at a fixed column on the exact
`A := ((Finset.univ : Finset ι).erase r₁).erase r₂` spelling. -/
private lemma sharedCriticalAlignedDeletedBalanceAtColumn
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) {r₁ r₂ : ι} (hNe : r₁ ≠ r₂)
    (s : {i // i ≠ r₂} → Bool) (τ : Bool)
    (hDeleted :
      ∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₂) id) i j')) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₂) id) i j')) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₂) id) i j')) = -1)
    (hτ : τ = s ⟨r₁, hNe⟩) (j : κ) :
    let A : Finset ι := ((Finset.univ : Finset ι).erase r₂).erase r₁
    let sA : {i // i ∈ A} → Bool := fun i ↦
      s ((doubleErasedRowsEquiv r₂ r₁ (Ne.symm hNe)) i).1
    ((∑ i : {x // x ∈ A},
        (if sA i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
        ((if τ then (1 : ℤ) else -1) * B r₁ j)) = 0 ∨
      ((∑ i : {x // x ∈ A},
          (if sA i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
          ((if τ then (1 : ℤ) else -1) * B r₁ j)) = 1 ∨
        ((∑ i : {x // x ∈ A},
            (if sA i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
            ((if τ then (1 : ℤ) else -1) * B r₁ j)) = -1 := by
  -- Rewrite the second deleted witness onto its canonical exact common core and align the
  -- kept-row sign by substitution.
  simpa [doubleErasedRowsEquiv, hτ] using
    sharedCriticalWitnessDeletedBalanceOnCommonCore B (Ne.symm hNe) s hDeleted j

/-- Helper for Theorem 4.59: in the aligned zero branch on the exact common core, the deleted row
entry must vanish on the chosen column. -/
private lemma sharedCriticalAlignedDeletedZeroGivesMissingRowZero
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    {r₁ r₂ : ι} (hNe : r₁ ≠ r₂)
    (s : {i // i ≠ r₂} → Bool) (τ : Bool) (j : κ)
    (hDeleted :
      ∀ j',
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₂) id) i j')) = 0 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₂) id) i j')) = 1 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₂) id) i j')) = -1)
    (hτ : τ = s ⟨r₁, hNe⟩)
    (hEvenSupport : Even (Function.support fun i ↦ B i j).ncard)
    (hZero :
      let A : Finset ι := ((Finset.univ : Finset ι).erase r₂).erase r₁
      let sA : {i // i ∈ A} → Bool := fun i ↦
        s ((doubleErasedRowsEquiv r₂ r₁ (Ne.symm hNe)) i).1
      ((∑ i : {x // x ∈ A},
          (if sA i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
          ((if τ then (1 : ℤ) else -1) * B r₁ j)) = 0) :
    B r₂ j = 0 := by
  have hDeletedZero :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₂) id) i j)) = 0 := by
    have hSplit := sharedCriticalWitnessCoreSplit B (Ne.symm hNe) s j
    -- Move the zero branch back through the common-core split before applying the parity API.
    calc
      (∑ i, (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r₂) id) i j)) =
          (∑ i : {x // x ∈ ((Finset.univ : Finset ι).erase r₂).erase r₁},
              (if s ((doubleErasedRowsEquiv r₂ r₁ (Ne.symm hNe)) i).1 then
                  (1 : ℤ) else -1) *
                ((B.submatrix
                  (Function.Embedding.subtype
                    fun i : ι ↦ i ∈ ((Finset.univ : Finset ι).erase r₂).erase r₁) id) i j)) +
            ((if s ⟨r₁, hNe⟩ then (1 : ℤ) else -1) * B r₁ j) := hSplit
      _ = 0 := by
        simpa [doubleErasedRowsEquiv, hτ] using hZero
  exact
    (deleted_signed_column_sum_eq_zero_iff_entry_eq_zero_of_even_support
      hB r₂ τ s j (hDeleted j) hEvenSupport).1 hDeletedZero

/-- Helper for Theorem 4.59: a nonzero aligned common-core branch rewrites back to a nonzero
deleted-row witness. -/
private lemma deletedRow_nonzero_of_commonCore_eq_one_or_negOne
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    {B : Matrix ι κ ℤ} (hB : HasZeroOneNegOneEntries B)
    {rKeep rDel : ι} (hNe : rKeep ≠ rDel)
    (s : {i // i ≠ rDel} → Bool) (τ : Bool) (j : κ)
    (hτ : τ = s ⟨rKeep, hNe⟩)
    (hCommonCore :
      let A : Finset ι := ((Finset.univ : Finset ι).erase rDel).erase rKeep
      let sA : {i // i ∈ A} → Bool := fun i ↦
        s ⟨i.1, (Finset.mem_erase.mp ((Finset.mem_erase.mp i.2).2)).1⟩
      ((∑ i : {x // x ∈ A},
          (if sA i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
          ((if τ then (1 : ℤ) else -1) * B rKeep j) = 1) ∨
        ((∑ i : {x // x ∈ A},
            (if sA i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
            ((if τ then (1 : ℤ) else -1) * B rKeep j) = -1))
    (hEvenSupport : Even (Function.support fun i ↦ B i j).ncard) :
    B rDel j ≠ 0 := by
  subst τ
  let A : Finset ι := ((Finset.univ : Finset ι).erase rDel).erase rKeep
  let sA : {i // i ∈ A} → Bool := fun i ↦
    s ⟨i.1, (Finset.mem_erase.mp ((Finset.mem_erase.mp i.2).2)).1⟩
  have hRewrite :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ rDel) id) i j)) =
        ((∑ i : {x // x ∈ A},
            (if sA i then (1 : ℤ) else -1) *
              ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
          ((if s ⟨rKeep, hNe⟩ then (1 : ℤ) else -1) * B rKeep j)) := by
    -- Rewrite the deleted-row sum through the exact common core plus the kept-row term.
    simpa [A, sA, doubleErasedRowsEquiv] using
      sharedCriticalWitnessCoreSplit B (Ne.symm hNe) s j
  have hDeletedEq :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ rDel) id) i j)) = 1 ∨
        (∑ i, (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ rDel) id) i j)) = -1 := by
    -- Rewrite the common-core branch back to the once-deleted witness before applying parity.
    rcases hCommonCore with hOne | hNegOne
    · left
      calc
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ rDel) id) i j))
            =
          ((∑ i : {x // x ∈ A},
              (if sA i then (1 : ℤ) else -1) *
                ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
            ((if s ⟨rKeep, hNe⟩ then (1 : ℤ) else -1) * B rKeep j)) := hRewrite
        _ = 1 := hOne
    · right
      calc
        (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ rDel) id) i j))
            =
          ((∑ i : {x // x ∈ A},
              (if sA i then (1 : ℤ) else -1) *
                ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ∈ A) id) i j)) +
            ((if s ⟨rKeep, hNe⟩ then (1 : ℤ) else -1) * B rKeep j)) := hRewrite
        _ = -1 := hNegOne
  -- Even-support parity turns a nonzero deleted witness into a nonzero deleted-row entry.
  exact
    missingRow_nonzero_of_deletedSum_eq_one_or_negOne_of_evenSupport
      hB rDel (s ⟨rKeep, hNe⟩) s j hDeletedEq hEvenSupport

/-- Helper for Theorem 4.59: a Hall matching on finite row-restricted column patterns can be
realized by an injective choice of actual columns with distinct selected patterns. -/
lemma exists_injective_columnChoice_of_patternHall
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (B : Matrix ι κ ℤ) (criticalPattern : ι → (ι → Fin 3) → Prop)
    (criticalWitness : ι → κ → Prop)
    (hHall :
      ∀ A : Finset ι,
        Nat.card A ≤ Nat.card {p // ∃ r ∈ A, criticalPattern r p})
    (hRealize :
      ∀ r p, criticalPattern r p →
        ∃ j : κ, zeroOneNegOneColumnPattern B j = p ∧ criticalWitness r j) :
    ∃ col : ι ↪ κ,
      Function.Injective (fun r ↦ zeroOneNegOneColumnPattern B (col r)) ∧
      ∀ r,
        criticalPattern r (zeroOneNegOneColumnPattern B (col r)) ∧ criticalWitness r (col r) := by
  classical
  have hPatternChoice :
      ∃ f : ι → (ι → Fin 3), Function.Injective f ∧ ∀ r, criticalPattern r (f r) := by
    -- Apply finite Hall directly to the pattern codomain rather than the ambient column type.
    let t : ι → Finset (ι → Fin 3) := fun r ↦ {p | criticalPattern r p}
    have hHall' : ∀ A : Finset ι, A.card ≤ (A.biUnion t).card := by
      intro A
      have hUnion :
          ({p | ∃ r ∈ A, criticalPattern r p} : Finset (ι → Fin 3)) = A.biUnion t := by
        ext p
        simp [t]
      have hHallA :
          A.card ≤ ({p | ∃ r ∈ A, criticalPattern r p} : Finset (ι → Fin 3)).card := by
        calc
          A.card = Fintype.card A := by
            exact (Fintype.card_ofFinset A (fun _ ↦ Iff.rfl)).symm
          _ = Nat.card A := by
            rw [Nat.card_eq_fintype_card]
          _ ≤ Nat.card {p // ∃ r ∈ A, criticalPattern r p} := hHall A
          _ = ({p | ∃ r ∈ A, criticalPattern r p} : Finset (ι → Fin 3)).card := by
            classical
            exact Nat.subtype_card _ (by intro p; simp)
      simpa [hUnion] using hHallA
    simpa [t] using (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hHall'
  rcases hPatternChoice with ⟨f, hf, hfRel⟩
  choose col hcolPattern hcolWitness using
    fun r ↦ hRealize r (f r) (hfRel r)
  have hcol_injective : Function.Injective col := by
    -- If two realized columns coincide, their selected patterns coincide, so Hall injectivity
    -- forces the corresponding rows to be equal.
    intro r₁ r₂ hEq
    apply hf
    calc
      f r₁ = zeroOneNegOneColumnPattern B (col r₁) := (hcolPattern r₁).symm
      _ = zeroOneNegOneColumnPattern B (col r₂) := by rw [hEq]
      _ = f r₂ := hcolPattern r₂
  have hpattern_injective :
      Function.Injective (fun r ↦ zeroOneNegOneColumnPattern B (col r)) := by
    -- Rewriting through the realized patterns reduces distinctness of selected patterns to the
    -- Hall-selected injective pattern family.
    intro r₁ r₂ hEq
    apply hf
    calc
      f r₁ = zeroOneNegOneColumnPattern B (col r₁) := (hcolPattern r₁).symm
      _ = zeroOneNegOneColumnPattern B (col r₂) := hEq
      _ = f r₂ := hcolPattern r₂
  refine ⟨⟨col, hcol_injective⟩, hpattern_injective, ?_⟩
  intro r
  constructor
  · -- Rewriting through the realized pattern restores the Hall-selected relation.
    simpa [hcolPattern r] using hfRel r
  · exact hcolWitness r

/-- Helper for Theorem 4.59: after Hall chooses the columns, each critical witness rewrites
directly into the fixed square `C := B.submatrix id col`. -/
lemma selectedCriticalSquare_hasCriticalDiagonalWitness
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} {B : Matrix ι κ ℤ}
    (col : ι ↪ κ)
    (hcolCritical :
      ∀ r : ι,
        ∃ s : {i // i ≠ r} → Bool, ∃ σ : Bool,
          (∀ j : κ,
            (∑ i, (if s i then (1 : ℤ) else -1) *
                ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j)) = 0 ∨
              (∑ i, (if s i then (1 : ℤ) else -1) *
                ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j)) = 1 ∨
                (∑ i, (if s i then (1 : ℤ) else -1) *
                  ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j)) = -1) ∧
          (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i (col r)) = 2) :
    let C : Matrix ι ι ℤ := B.submatrix id col
    ∀ r : ι,
      ∃ s : {i // i ≠ r} → Bool, ∃ σ : Bool,
        (∀ j : ι,
          (∑ i, (if s i then (1 : ℤ) else -1) *
              ((C.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j)) = 0 ∨
            (∑ i, (if s i then (1 : ℤ) else -1) *
              ((C.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j)) = 1 ∨
              (∑ i, (if s i then (1 : ℤ) else -1) *
                ((C.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i j)) = -1) ∧
        (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * C i r) = 2 := by
  intro C r
  rcases hcolCritical r with ⟨s, σ, hs, hSumTwo⟩
  refine ⟨s, σ, ?_, ?_⟩
  · intro j
    -- The deleted-row balance statement is unchanged after rewriting the chosen column `col j`
    -- into the fixed square `C`.
    simpa [C, Matrix.submatrix_apply] using hs (col j)
  · -- The distinguished critical column becomes the diagonal column of the fixed square.
    simpa [C, Matrix.submatrix_apply] using hSumTwo

/-- Helper for Theorem 4.59: on the distinguished diagonal column of a normalized critical
witness, the deleted-row contribution and the signed diagonal entry are both equal to `1`. -/
lemma normalizedCriticalDiagonal_deletedSum_and_signedPivot_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℤ}
    (hB : HasZeroOneNegOneEntries B)
    (r : ι) (s : {i // i ≠ r} → Bool) (σ : Bool)
    (hDeleted :
      (∑ i, (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i r)) = 0 ∨
        (∑ i, (if s i then (1 : ℤ) else -1) *
          ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i r)) = 1 ∨
          (∑ i, (if s i then (1 : ℤ) else -1) *
            ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i r)) = -1)
    (hCritical :
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i r) = 2) :
    (∑ i, (if s i then (1 : ℤ) else -1) *
        ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i r)) = 1 ∧
      ((if σ then (1 : ℤ) else -1) * B r r) = 1 := by
  let deletedSum : ℤ :=
    ∑ i, (if s i then (1 : ℤ) else -1) *
      ((B.submatrix (Function.Embedding.subtype fun i : ι ↦ i ≠ r) id) i r)
  let rowTerm : ℤ := (if σ then (1 : ℤ) else -1) * B r r
  have hSplit :
      (∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i r) =
        deletedSum + rowTerm := by
    -- Split the critical full-column sum into the deleted-row part and the diagonal entry.
    simpa [deletedSum, rowTerm] using
      extended_deleted_row_signing_sum_eq_deleted_sum_add_row_term B r σ s r
  have hDeletedValue :
      deletedSum = 0 ∨ deletedSum = 1 ∨ deletedSum = -1 := by
    -- The deleted-row witness already constrains the deleted contribution to `{0, 1, -1}`.
    simpa [deletedSum] using hDeleted
  have hRowTermValue :
      rowTerm = 0 ∨ rowTerm = 1 ∨ rowTerm = -1 := by
    -- The diagonal term is still a signed `(0, ±1)` entry.
    simpa [rowTerm] using signed_zero_one_neg_one σ (HasZeroOneNegOneEntries.apply hB r r)
  have hPair : deletedSum = 1 ∧ rowTerm = 1 := by
    -- Since the full signed diagonal column sums to `2`, both summands must be `1`.
    apply summands_eq_one_of_zero_one_neg_one_add_eq_two hDeletedValue hRowTermValue
    calc
      deletedSum + rowTerm
          = ∑ i, (if extend_deleted_row_signing r σ s i then (1 : ℤ) else -1) * B i r := by
              rw [hSplit]
      _ = 2 := hCritical
  simpa [deletedSum, rowTerm] using hPair

/-- Helper for Theorem 4.59: divisibility of a vector-matrix product can be cancelled when the
matrix is unimodular. -/
lemma dvd_vec_of_dvd_vecMul_of_det_eq_one_or_negOne
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) (x : ι → ℤ) (d : ℤ)
    (hdet : M.det = 1 ∨ M.det = -1)
    (hdiv : ∀ j, d ∣ (x ᵥ* M) j) :
    ∀ i, d ∣ x i := by
  intro i
  have hAdjDiv : d ∣ ((x ᵥ* M) ᵥ* M.adjugate) i := by
    dsimp [Matrix.vecMul, dotProduct]
    refine Finset.dvd_sum ?_
    intro j hj
    exact dvd_mul_of_dvd_left (hdiv j) _
  rw [Matrix.vecMul_vecMul] at hAdjDiv
  rw [Matrix.mul_adjugate] at hAdjDiv
  rcases hdet with hOne | hNegOne
  · simpa [hOne, Matrix.vecMul, dotProduct, Matrix.one_apply] using hAdjDiv
  · have hNeg : d ∣ -x i := by
      simpa [hNegOne, Matrix.vecMul, dotProduct, Matrix.one_apply] using hAdjDiv
    simpa using hNeg

/-- Helper for Theorem 4.59: a deleted adjugate-row combination expands against the deleted
matrix as the corresponding combination of rows of the adjugate product. -/
lemma deletedAdjugateRowCombination_vecMul {k : ℕ}
    (C : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ)
    (a b s p : Fin (k + 2)) (q : Fin (k + 1)) :
    ((fun i : Fin (k + 1) ↦
      C.adjugate a s * C.adjugate b (s.succAbove i) -
        C.adjugate b s * C.adjugate a (s.succAbove i)) ᵥ*
        C.submatrix s.succAbove p.succAbove) q =
      C.adjugate a s * (C.adjugate * C) b (p.succAbove q) -
        C.adjugate b s * (C.adjugate * C) a (p.succAbove q) := by
  -- Expand the deleted product, split the difference, and restore the omitted `s` coordinate.
  simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, Matrix.mul_apply]
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp only [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hsumB := Fin.sum_univ_succAbove
    (fun j : Fin (k + 2) ↦ C.adjugate b j * C j (p.succAbove q)) s
  have hsumA := Fin.sum_univ_succAbove
    (fun j : Fin (k + 2) ↦ C.adjugate a j * C j (p.succAbove q)) s
  rw [hsumB, hsumA]
  ring

/-- Helper for Theorem 4.59: when the adjugate has `(0, ±1)` entries, the determinant divides
every cross-product of two adjugate rows and two adjugate columns. -/
lemma det_dvd_adjugateCross_of_signEntries {k : ℕ}
    (C : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ)
    (hdet : C.det ≠ 0) (hAdj : HasZeroOneNegOneEntries C.adjugate)
    (a b s p : Fin (k + 2)) :
    C.det ∣ C.adjugate a s * C.adjugate b p -
      C.adjugate b s * C.adjugate a p := by
  classical
  by_cases hps : p = s
  · -- A repeated selected column makes the cross-product vanish.
    rw [hps]
    ring_nf
    exact dvd_zero C.det
  have hpivot : ∃ t : Fin (k + 2), C.adjugate t s ≠ 0 := by
    -- The `s`-th column of the adjugate cannot vanish because `C * adjugate C = det C • 1`.
    by_contra hNoPivot
    push Not at hNoPivot
    have hDiagonal := congrArg (fun M : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ ↦ M s s)
      (Matrix.mul_adjugate C)
    have hDetZero : C.det = 0 := by
      simpa [Matrix.mul_apply, Matrix.one_apply, hNoPivot] using hDiagonal.symm
    exact hdet hDetZero
  obtain ⟨t, ht⟩ := hpivot
  let M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    C.submatrix s.succAbove t.succAbove
  have hMdet : M.det = 1 ∨ M.det = -1 := by
    -- The chosen nonzero cofactor is a sign, so its deleted minor is unimodular.
    have hCofactor := Matrix.adjugate_fin_succ_eq_det_submatrix C t s
    have hAdjValue := HasZeroOneNegOneEntries.apply hAdj t s
    have hPow : (-1 : ℤ) ^ (s + t : ℕ) = 1 ∨ (-1 : ℤ) ^ (s + t : ℕ) = -1 :=
      neg_one_pow_eq_or ℤ (s + t : ℕ)
    rcases hAdjValue with hZero | hOne | hNegOne
    · exact (ht hZero).elim
    · rcases hPow with hPow | hPow
      · left
        simpa [M, hPow] using hCofactor.symm.trans hOne
      · right
        have : -M.det = 1 := by simpa [M, hPow] using hCofactor.symm.trans hOne
        linarith
    · rcases hPow with hPow | hPow
      · right
        simpa [M, hPow] using hCofactor.symm.trans hNegOne
      · left
        have : -M.det = -1 := by simpa [M, hPow] using hCofactor.symm.trans hNegOne
        linarith
  let x : Fin (k + 1) → ℤ := fun i ↦
    C.adjugate a s * C.adjugate b (s.succAbove i) -
      C.adjugate b s * C.adjugate a (s.succAbove i)
  have hProductDiv : ∀ q, C.det ∣ (x ᵥ* M) q := by
    intro q
    -- The deleted-product formula reduces every coordinate to entries of `adjugate C * C`.
    rw [deletedAdjugateRowCombination_vecMul C a b s t q]
    rw [Matrix.adjugate_mul]
    by_cases hb : b = t.succAbove q
    · by_cases ha : a = t.succAbove q <;> simp [Matrix.one_apply, hb, ha]
    · by_cases ha : a = t.succAbove q <;> simp [Matrix.one_apply, hb, ha]
  have hxDiv : ∀ q, C.det ∣ x q :=
    dvd_vec_of_dvd_vecMul_of_det_eq_one_or_negOne M x C.det hMdet hProductDiv
  obtain ⟨q, hq⟩ := Fin.exists_succAbove_eq hps
  -- The coordinate corresponding to `p` is the requested cross-product.
  simpa [x, hq] using hxDiv q

/-- Helper for Theorem 4.59: a non-colorable matrix has a cardinal-minimal square submatrix whose
determinant is outside the sign range, and every smaller square submatrix has sign determinant. -/
lemma exists_minimal_bad_square_submatrix
    {ρ : Type u} [Fintype ρ] [DecidableEq ρ] {n : Type v}
    (B : Matrix ρ n ℤ) (hB : HasZeroOneNegOneEntries B)
    (hNoColor : ¬ ∃ red blue : Finset ρ, is_equitable_row_bicoloring B red blue) :
    ∃ k : ℕ, ∃ f : Fin k → ρ, ∃ g : Fin k → n,
      (B.submatrix f g).det ∉ Set.range (SignType.cast : SignType → ℤ) ∧
      ∀ j < k, ∀ f' : Fin j → ρ, ∀ g' : Fin j → n,
        (B.submatrix f' g').det ∈ Set.range (SignType.cast : SignType → ℤ) := by
  classical
  have hNotTU : ¬ B.IsTotallyUnimodular := by
    intro hTU
    apply hNoColor
    exact (totally_unimodular_iff_every_row_submatrix_admits_equitable_row_bicoloring B).1
      hTU (Function.Embedding.refl ρ)
  rw [Matrix.isTotallyUnimodular_iff] at hNotTU
  push Not at hNotTU
  let bad : ℕ → Prop := fun k ↦ ∃ f : Fin k → ρ, ∃ g : Fin k → n,
    (B.submatrix f g).det ∉ Set.range (SignType.cast : SignType → ℤ)
  have hbad : ∃ k, bad k := by
    simpa [bad] using hNotTU
  let k : ℕ := Nat.find hbad
  obtain ⟨f, g, hdet⟩ := Nat.find_spec hbad
  refine ⟨k, f, g, hdet, ?_⟩
  intro j hj f' g'
  by_contra hNot
  exact (Nat.find_min hbad (by simpa [k] using hj)) ⟨f', g', hNot⟩

/-- Helper for Theorem 4.59: proper-minor sign control makes every entry of the adjugate a
`(0, ±1)` integer. -/
lemma minimal_bad_square_adjugate_hasZeroOneNegOneEntries {k : ℕ}
    (C : Matrix (Fin k) (Fin k) ℤ) (hk : 0 < k)
    (hmin : ∀ j < k, ∀ f : Fin j → Fin k, ∀ g : Fin j → Fin k,
      (C.submatrix f g).det ∈ Set.range (SignType.cast : SignType → ℤ)) :
    HasZeroOneNegOneEntries C.adjugate := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  intro i j
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hminor := hmin l (Nat.lt_succ_self l) j.succAbove i.succAbove
  rcases hminor with ⟨z, hz⟩
  have hpow : (-1 : ℤ) ^ (j + i : ℕ) = 1 ∨ (-1 : ℤ) ^ (j + i : ℕ) = -1 := by
    exact neg_one_pow_eq_or ℤ (j + i : ℕ)
  rcases hpow with hpow | hpow
  · rw [hpow]
    refine ⟨z, ?_⟩
    simpa using hz
  · rw [hpow]
    cases z with
    | zero => exact ⟨0, by simpa using hz.symm⟩
    | neg => exact ⟨SignType.pos, by rw [← hz]; norm_num⟩
    | pos => exact ⟨SignType.neg, by simpa using hz⟩

/-- Helper for Theorem 4.59: a nonzero cross-product of four signs is `2` or `-2`. -/
lemma signCross_eq_two_or_negTwo
    {a b c d : ℤ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1)
    (hNonzero : a * b - c * d ≠ 0) :
    a * b - c * d = 2 ∨ a * b - c * d = -2 := by
  -- There are only sixteen sign combinations; the equal-product cases contradict nonvanishing.
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
  all_goals norm_num at hNonzero
  all_goals norm_num

/-- Helper for Theorem 4.59: an integer of absolute value at most one lies in the sign range. -/
lemma mem_signTypeRange_of_natAbs_le_one (z : ℤ) (hAbs : z.natAbs ≤ 1) :
    z ∈ Set.range (SignType.cast : SignType → ℤ) := by
  rw [SignType.range_eq (SignType.cast : SignType → ℤ)]
  have hCases : z.natAbs = 0 ∨ z.natAbs = 1 := by omega
  rcases hCases with hZero | hOne
  · left
    exact Int.natAbs_eq_zero.mp hZero
  · obtain hPos | hNeg := Int.natAbs_eq z
    · right
      right
      simpa [hOne] using hPos
    · right
      left
      simpa [hOne] using hNeg

/-- Helper for Theorem 4.59: an integer of absolute value two is `2` or `-2`. -/
lemma eq_two_or_negTwo_of_natAbs_eq_two (z : ℤ) (hAbs : z.natAbs = 2) :
    z = 2 ∨ z = -2 := by
  obtain hPos | hNeg := Int.natAbs_eq z
  · left
    simpa [hAbs] using hPos
  · right
    simpa [hAbs] using hNeg

/-- Helper for Theorem 4.59: an even sign-weighted sum of `(0, ±1)` integers has even nonzero
support. -/
lemma even_support_of_sign_weighted_sum_even
    {ι : Type*} [Fintype ι] (f s : ι → ℤ)
    (hf : ∀ i, f i = 0 ∨ f i = 1 ∨ f i = -1)
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hEven : Even (∑ i, s i * f i)) :
    Even (Function.support f).ncard := by
  classical
  rw [← ZMod.natCast_eq_zero_iff_even]
  calc
    (((Function.support f).ncard : ℕ) : ZMod 2) =
        (((Finset.univ.filter fun i ↦ f i ≠ 0).card : ℕ) : ZMod 2) := by
          congr 1
          rw [Set.ncard_eq_toFinset_card']
          simp [Function.support, Set.toFinset_setOf]
    _ = ∑ i, if f i ≠ 0 then (1 : ZMod 2) else 0 := by
          rw [← Finset.sum_filter]
          rw [Finset.card_eq_sum_ones]
          simp
    _ = ∑ i, ((((s i * f i : ℤ)) : ZMod 2)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hsCast : ((s i : ℤ) : ZMod 2) = 1 := by
            rcases hs i with hSignOne | hSignNegOne
            · rw [hSignOne]
              norm_num
            · rw [hSignNegOne]
              simpa using (ZMod.neg_eq_self_mod_two (1 : ZMod 2))
          by_cases hfi : f i = 0
          · simp [hfi]
          · have hfCast := zmod_two_cast_eq_indicator_of_zero_one_neg_one (hf i)
            simp [hfi, hsCast] at hfCast ⊢
            exact hfCast.symm
    _ = (((∑ i, s i * f i : ℤ)) : ZMod 2) := by simp
    _ = 0 := Even.intCast_zmod_two hEven

/-- Helper for Theorem 4.59: a bad determinant with sign-valued cofactors in dimension at least
two yields a signed adjugate that is a two-sided inverse scaled by `2`. -/
lemma exists_signedScaledInverse_of_signAdjugate {k : ℕ}
    (C : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ)
    (hBadDet : C.det ∉ Set.range (SignType.cast : SignType → ℤ))
    (hAdj : HasZeroOneNegOneEntries C.adjugate) :
    ∃ S : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ,
      (∀ i j, S i j = 1 ∨ S i j = -1) ∧
        S * C = (2 : ℤ) • 1 ∧ C * S = (2 : ℤ) • 1 := by
  classical
  have hDetNotZero : C.det ≠ 0 := by
    intro hZero
    apply hBadDet
    rw [SignType.range_eq (SignType.cast : SignType → ℤ)]
    exact Or.inl hZero
  have hColumnNonzero : ∀ s, ∃ t, C.adjugate t s ≠ 0 := by
    intro s
    by_contra hNoPivot
    push Not at hNoPivot
    have hDiagonal := congrArg (fun M : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ ↦ M s s)
      (Matrix.mul_adjugate C)
    have hDetZero : C.det = 0 := by
      simpa [Matrix.mul_apply, Matrix.one_apply, hNoPivot] using hDiagonal.symm
    exact hDetNotZero hDetZero
  have hRowNonzero : ∀ a, ∃ p, C.adjugate a p ≠ 0 := by
    intro a
    by_contra hNoPivot
    push Not at hNoPivot
    have hDiagonal := congrArg (fun M : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ ↦ M a a)
      (Matrix.adjugate_mul C)
    have hDetZero : C.det = 0 := by
      simpa [Matrix.mul_apply, Matrix.one_apply, hNoPivot] using hDiagonal.symm
    exact hDetNotZero hDetZero
  have hAdjNonzero : ∀ a s, C.adjugate a s ≠ 0 := by
    intro a s hZero
    obtain ⟨b, hb⟩ := hColumnNonzero s
    obtain ⟨p, hp⟩ := hRowNonzero a
    have hDiv := det_dvd_adjugateCross_of_signEntries C hDetNotZero hAdj a b s p
    have hbValue := HasZeroOneNegOneEntries.apply hAdj b s
    have hpValue := HasZeroOneNegOneEntries.apply hAdj a p
    have hUnit :
        -(C.adjugate b s * C.adjugate a p) = 1 ∨
          -(C.adjugate b s * C.adjugate a p) = -1 := by
      rcases hbValue with hbZero | hbOne | hbNegOne
      · exact (hb hbZero).elim
      · rcases hpValue with hpZero | hpOne | hpNegOne
        · exact (hp hpZero).elim
        · right
          rw [hbOne, hpOne]
          norm_num
        · left
          rw [hbOne, hpNegOne]
          norm_num
      · rcases hpValue with hpZero | hpOne | hpNegOne
        · exact (hp hpZero).elim
        · left
          rw [hbNegOne, hpOne]
          norm_num
        · right
          rw [hbNegOne, hpNegOne]
          norm_num
    have hDvdOne : C.det ∣ 1 := by
      rw [hZero, zero_mul, zero_sub] at hDiv
      rcases hUnit with hUnit | hUnit
      · simpa [hUnit] using hDiv
      · simpa [hUnit] using hDiv
    have hOneNeZero : (1 : ℤ) ≠ 0 := one_ne_zero
    have hAbsLe : C.det.natAbs ≤ 1 :=
      Int.natAbs_le_of_dvd_ne_zero hDvdOne hOneNeZero
    exact hBadDet (mem_signTypeRange_of_natAbs_le_one C.det hAbsLe)
  have hAdjSign : ∀ a s, C.adjugate a s = 1 ∨ C.adjugate a s = -1 := by
    intro a s
    rcases HasZeroOneNegOneEntries.apply hAdj a s with hZero | hOne | hNegOne
    · exact (hAdjNonzero a s hZero).elim
    · exact Or.inl hOne
    · exact Or.inr hNegOne
  have hCrossNonzero :
      ∃ p : Fin (k + 2),
        C.adjugate 0 0 * C.adjugate 1 p - C.adjugate 1 0 * C.adjugate 0 p ≠ 0 := by
    by_contra hNoCross
    push Not at hNoCross
    have h00' := hAdjSign 0 0
    have h10' := hAdjSign 1 0
    have hRows :
        C.adjugate 1 = C.adjugate 0 ∨ C.adjugate 1 = -C.adjugate 0 := by
      rcases h00' with h00One | h00NegOne
      · rcases h10' with h10One | h10NegOne
        · left
          funext p
          have hp := hNoCross p
          simp [h00One, h10One] at hp
          exact sub_eq_zero.mp hp
        · right
          funext p
          have hp := hNoCross p
          simp [h00One, h10NegOne] at hp
          rw [Pi.neg_apply]
          linarith
      · rcases h10' with h10One | h10NegOne
        · right
          funext p
          have hp := hNoCross p
          simp [h00NegOne, h10One] at hp
          rw [Pi.neg_apply]
          linarith
        · left
          funext p
          have hp := hNoCross p
          simp [h00NegOne, h10NegOne] at hp
          linarith
    have h00Product := congrArg
      (fun M : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ ↦ M 0 0) (Matrix.adjugate_mul C)
    have h10Product := congrArg
      (fun M : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ ↦ M 1 0) (Matrix.adjugate_mul C)
    have h00Product' : (C.adjugate * C) 0 0 = C.det := by
      simpa [Matrix.one_apply] using h00Product
    have h10Product' : (C.adjugate * C) 1 0 = 0 := by
      simpa [Matrix.one_apply] using h10Product
    rcases hRows with hRows | hRows
    · have hProductsEqual : (C.adjugate * C) 1 0 = (C.adjugate * C) 0 0 := by
        simp only [Matrix.mul_apply]
        rw [hRows]
      rw [h10Product', h00Product'] at hProductsEqual
      exact hDetNotZero hProductsEqual.symm
    · have hProductsNeg : (C.adjugate * C) 1 0 = -(C.adjugate * C) 0 0 := by
        simp only [Matrix.mul_apply]
        rw [hRows]
        simp [Finset.sum_neg_distrib]
      rw [h10Product', h00Product'] at hProductsNeg
      exact hDetNotZero (neg_eq_zero.mp hProductsNeg.symm)
  obtain ⟨p, hp⟩ := hCrossNonzero
  have hDiv := det_dvd_adjugateCross_of_signEntries C hDetNotZero hAdj 0 1 0 p
  have hCrossTwo :
      C.adjugate 0 0 * C.adjugate 1 p - C.adjugate 1 0 * C.adjugate 0 p = 2 ∨
        C.adjugate 0 0 * C.adjugate 1 p - C.adjugate 1 0 * C.adjugate 0 p = -2 := by
    exact signCross_eq_two_or_negTwo
      (hAdjSign 0 0) (hAdjSign 1 p) (hAdjSign 1 0) (hAdjSign 0 p) hp
  have hDvdTwo : C.det ∣ 2 := by
    rcases hCrossTwo with hTwo | hNegTwo
    · simpa [hTwo] using hDiv
    · simpa [hNegTwo] using hDiv
  have hTwoNeZero : (2 : ℤ) ≠ 0 := by norm_num
  have hAbsLeTwo : C.det.natAbs ≤ 2 :=
    Int.natAbs_le_of_dvd_ne_zero hDvdTwo hTwoNeZero
  have hDetTwo : C.det = 2 ∨ C.det = -2 := by
    have hAbsNotLeOne : ¬ C.det.natAbs ≤ 1 := by
      intro hAbs
      exact hBadDet (mem_signTypeRange_of_natAbs_le_one C.det hAbs)
    have hAbsEqTwo : C.det.natAbs = 2 := by omega
    exact eq_two_or_negTwo_of_natAbs_eq_two C.det hAbsEqTwo
  rcases hDetTwo with hDetTwo | hDetNegTwo
  · refine ⟨C.adjugate, ?_, ?_, ?_⟩
    · intro i j
      rcases HasZeroOneNegOneEntries.apply hAdj i j with hZero | hOne | hNegOne
      · exact (hAdjNonzero i j hZero).elim
      · exact Or.inl hOne
      · exact Or.inr hNegOne
    · simpa [hDetTwo] using Matrix.adjugate_mul C
    · simpa [hDetTwo] using Matrix.mul_adjugate C
  · refine ⟨-C.adjugate, ?_, ?_, ?_⟩
    · intro i j
      rcases HasZeroOneNegOneEntries.apply hAdj i j with hZero | hOne | hNegOne
      · exact (hAdjNonzero i j hZero).elim
      · right
        simp [hOne]
      · left
        simp [hNegOne]
    · rw [neg_mul, Matrix.adjugate_mul, hDetNegTwo]
      simp
    · rw [mul_neg, Matrix.mul_adjugate, hDetNegTwo]
      simp

/-- Helper for Theorem 4.59: a `(0, ±1)` square matrix with a signed two-sided inverse scaled by
`2` has even row and column support and odd half entry sum. -/
lemma signedScaledInverse_hasEvenSupportOddHalfSum
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (C S : Matrix ι ι ℤ)
    (hC : HasZeroOneNegOneEntries C)
    (hS : ∀ i j, S i j = 1 ∨ S i j = -1)
    (hLeft : S * C = (2 : ℤ) • 1)
    (hRight : C * S = (2 : ℤ) • 1) :
    HasEvenNonzeroSupportInRowsAndCols C ∧ HasOddHalfEntrySum C := by
  classical
  let r : ι := Classical.choice inferInstance
  have hColumnEven : ∀ j, Even (Function.support fun i ↦ C i j).ncard := by
    intro j
    have hWeightedEven : Even (∑ i, S r i * C i j) := by
      have hEntry := congrArg (fun M : Matrix ι ι ℤ ↦ M r j) hLeft
      by_cases hrj : r = j
      · have hSumTwo : (∑ i, S r i * C i j) = 2 := by
          simpa [Matrix.mul_apply, Matrix.one_apply, hrj] using hEntry
        rw [hSumTwo]
        norm_num
      · have hSumZero : (∑ i, S r i * C i j) = 0 := by
          simpa [Matrix.mul_apply, Matrix.one_apply, hrj] using hEntry
        rw [hSumZero]
        norm_num
    -- Modulo two every entry of the selected signed row is `1`.
    exact even_support_of_sign_weighted_sum_even
      (fun i ↦ C i j) (fun i ↦ S r i)
      (fun i ↦ HasZeroOneNegOneEntries.apply hC i j) (fun i ↦ hS r i) hWeightedEven
  have hRowEven : ∀ i, Even (Function.support (C i)).ncard := by
    intro i
    have hWeightedEven : Even (∑ j, S j r * C i j) := by
      have hEntry := congrArg (fun M : Matrix ι ι ℤ ↦ M i r) hRight
      have hReorder : (∑ j, S j r * C i j) = (C * S) i r := by
        simp only [Matrix.mul_apply]
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring
      by_cases hir : i = r
      · have hSumTwo : (∑ j, S j r * C i j) = 2 := by
          rw [hReorder]
          simpa [Matrix.one_apply, hir] using hEntry
        rw [hSumTwo]
        norm_num
      · have hSumZero : (∑ j, S j r * C i j) = 0 := by
          rw [hReorder]
          simpa [Matrix.one_apply, hir] using hEntry
        rw [hSumZero]
        norm_num
    -- The right scaled-inverse equation gives the analogous signed sum along each row.
    exact even_support_of_sign_weighted_sum_even
      (C i) (fun j ↦ S j r)
      (fun j ↦ HasZeroOneNegOneEntries.apply hC i j) (fun j ↦ hS j r) hWeightedEven
  have hEvenSupport : HasEvenNonzeroSupportInRowsAndCols C := ⟨hRowEven, hColumnEven⟩
  have hRowSumEven : ∀ i, Even (∑ j, C i j) :=
    even_row_sum_of_even_support hC hEvenSupport
  choose halfRowSum hHalfRowSum using hRowSumEven
  have hHalfRowSumEq : ∀ i, (∑ j, C i j) = 2 * halfRowSum i := by
    intro i
    -- Rewrite the additive evenness witness as multiplication by `2`.
    calc
      (∑ j, C i j) = halfRowSum i + halfRowSum i := hHalfRowSum i
      _ = 2 * halfRowSum i := by ring
  have hSignedHalfSum : (∑ i, S r i * halfRowSum i) = 1 := by
    have hScaledRowSum : (∑ i, S r i * (∑ j, C i j)) = 2 := by
      calc
        (∑ i, S r i * (∑ j, C i j)) = ∑ i, ∑ j, S r i * C i j := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.mul_sum]
        _ = ∑ j, ∑ i, S r i * C i j := Finset.sum_comm
        _ = ∑ j, (S * C) r j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [Matrix.mul_apply]
        _ = ∑ j, ((2 : ℤ) • (1 : Matrix ι ι ℤ)) r j := by rw [hLeft]
        _ = 2 := by simp [Matrix.one_apply]
    have hDoubleSignedHalf : 2 * (∑ i, S r i * halfRowSum i) = 2 := by
      calc
        2 * (∑ i, S r i * halfRowSum i) =
            ∑ i, S r i * (2 * halfRowSum i) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ = ∑ i, S r i * (∑ j, C i j) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hHalfRowSumEq i]
        _ = 2 := hScaledRowSum
    linarith
  have hHalfOdd : Odd (∑ i, halfRowSum i) := by
    rw [← ZMod.intCast_eq_one_iff_odd]
    calc
      (((∑ i, halfRowSum i : ℤ)) : ZMod 2) =
          ∑ i, (((halfRowSum i : ℤ)) : ZMod 2) := by simp
      _ = ∑ i, (((S r i * halfRowSum i : ℤ)) : ZMod 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rcases hS r i with hOne | hNegOne
            · rw [hOne]
              norm_num
            · rw [hNegOne]
              simpa using (ZMod.neg_eq_self_mod_two (((halfRowSum i : ℤ)) : ZMod 2))
      _ = (((∑ i, S r i * halfRowSum i : ℤ)) : ZMod 2) := by simp
      _ = 1 := by rw [hSignedHalfSum]; norm_num
  have hOddHalf : HasOddHalfEntrySum C := by
    refine ⟨∑ i, halfRowSum i, ?_, hHalfOdd⟩
    -- Summing the row decompositions reconstructs the full entry sum.
    calc
      (∑ i, ∑ j, C i j) = ∑ i, 2 * halfRowSum i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hHalfRowSumEq i]
      _ = 2 * ∑ i, halfRowSum i := by rw [Finset.mul_sum]
  exact ⟨hEvenSupport, hOddHalf⟩

/-- Helper for Theorem 4.59: a row submatrix without an equitable row-bicoloring contains the
Camion parity obstruction as a square submatrix. -/
lemma exists_even_support_odd_half_sum_square_submatrix_of_not_equitable_row_bicoloring
    {ρ : Type u} [Fintype ρ] [DecidableEq ρ] (B : Matrix ρ n ℤ)
    (hB : HasZeroOneNegOneEntries B)
    (hNoColor : ¬ ∃ red blue : Finset ρ, is_equitable_row_bicoloring B red blue) :
    HasEvenSupportOddHalfSumSquareSubmatrix.{u, v, u} B := by
  classical
  -- Route correction: select a dimension-minimal bad square and use the deleted-minor
  -- divisibility interface above, avoiding the unsupported shared-signing compatibility route.
  obtain ⟨k, f, g, hBadDet, hMinimal⟩ :=
    exists_minimal_bad_square_submatrix B hB hNoColor
  have hkZero : k ≠ 0 := by
    intro hk
    subst k
    apply hBadDet
    rw [Matrix.det_fin_zero]
    have hPosCast : SignType.cast SignType.pos = (1 : ℤ) := by simp
    exact ⟨SignType.pos, hPosCast⟩
  have hkOne : k ≠ 1 := by
    intro hk
    subst k
    apply hBadDet
    rw [Matrix.det_fin_one]
    exact hB (f 0) (g 0)
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 2 := by
    use k - 2
    omega
  let C : Matrix (Fin (l + 2)) (Fin (l + 2)) ℤ := B.submatrix f g
  have hCMinimal :
      ∀ j < l + 2, ∀ f' : Fin j → Fin (l + 2), ∀ g' : Fin j → Fin (l + 2),
        (C.submatrix f' g').det ∈ Set.range (SignType.cast : SignType → ℤ) := by
    intro j hj f' g'
    have hMinor := hMinimal j hj (fun i ↦ f (f' i)) (fun i ↦ g (g' i))
    simpa [C, Matrix.submatrix_submatrix, Function.comp_def] using hMinor
  have hCAdj : HasZeroOneNegOneEntries C.adjugate := by
    -- Every cofactor is a proper minor of the chosen minimal bad square.
    have hkPositive : 0 < l + 2 := by omega
    exact minimal_bad_square_adjugate_hasZeroOneNegOneEntries C hkPositive hCMinimal
  obtain ⟨S, hS, hLeft, hRight⟩ :=
    exists_signedScaledInverse_of_signAdjugate C hBadDet hCAdj
  have hCEntries : HasZeroOneNegOneEntries C := by
    simpa [C] using hB.submatrix f g
  have hCDetNotZero : C.det ≠ 0 := by
    intro hZero
    apply hBadDet
    rw [SignType.range_eq (SignType.cast : SignType → ℤ)]
    have hZero' : (B.submatrix f g).det = 0 := by simpa [C] using hZero
    exact Or.inl hZero'
  have hfInjective : Function.Injective f := by
    intro i j hij
    by_contra hNe
    have hRows : C i = C j := by
      funext q
      simp [C, hij]
    exact hCDetNotZero (Matrix.det_zero_of_row_eq hNe hRows)
  have hgInjective : Function.Injective g := by
    intro i j hij
    by_contra hNe
    have hColumns : ∀ q, C q i = C q j := by
      intro q
      simp [C, hij]
    exact hCDetNotZero (Matrix.det_zero_of_column_eq hNe hColumns)
  let liftEquiv : Fin (l + 2) ≃ ULift.{u} (Fin (l + 2)) := Equiv.ulift.symm
  let rowFun : ULift.{u} (Fin (l + 2)) → ρ := f ∘ Equiv.ulift
  let colFun : ULift.{u} (Fin (l + 2)) → n := g ∘ Equiv.ulift
  have hRowFunInjective : Function.Injective rowFun :=
    hfInjective.comp Equiv.ulift.injective
  have hColFunInjective : Function.Injective colFun :=
    hgInjective.comp Equiv.ulift.injective
  let row : ULift.{u} (Fin (l + 2)) ↪ ρ := ⟨rowFun, hRowFunInjective⟩
  let col : ULift.{u} (Fin (l + 2)) ↪ n := ⟨colFun, hColFunInjective⟩
  let C' : Matrix (ULift.{u} (Fin (l + 2))) (ULift.{u} (Fin (l + 2))) ℤ :=
    Matrix.reindex liftEquiv liftEquiv C
  let S' : Matrix (ULift.{u} (Fin (l + 2))) (ULift.{u} (Fin (l + 2))) ℤ :=
    Matrix.reindex liftEquiv liftEquiv S
  have hSelectedMatrix : B.submatrix row col = C' := by
    -- The universe lift changes only the index presentation of the minimal square.
    ext i j
    rfl
  have hC'Entries : HasZeroOneNegOneEntries C' := by
    intro i j
    simpa [C', Matrix.reindex_apply] using
      hCEntries (liftEquiv.symm i) (liftEquiv.symm j)
  have hS' : ∀ i j, S' i j = 1 ∨ S' i j = -1 := by
    intro i j
    simpa [S', Matrix.reindex_apply] using hS (liftEquiv.symm i) (liftEquiv.symm j)
  have hLeft' : S' * C' = (2 : ℤ) • 1 := by
    calc
      S' * C' = Matrix.reindexAlgEquiv ℤ ℤ liftEquiv (S * C) := by
        simpa [S', C'] using (Matrix.reindexAlgEquiv_mul liftEquiv S C).symm
      _ = Matrix.reindexAlgEquiv ℤ ℤ liftEquiv ((2 : ℤ) • 1) := by rw [hLeft]
      _ = (2 : ℤ) • Matrix.reindexAlgEquiv ℤ ℤ liftEquiv 1 := by
        rw [map_smul]
      _ = (2 : ℤ) • 1 := by rw [map_one]
  have hRight' : C' * S' = (2 : ℤ) • 1 := by
    calc
      C' * S' = Matrix.reindexAlgEquiv ℤ ℤ liftEquiv (C * S) := by
        simpa [S', C'] using (Matrix.reindexAlgEquiv_mul liftEquiv C S).symm
      _ = Matrix.reindexAlgEquiv ℤ ℤ liftEquiv ((2 : ℤ) • 1) := by rw [hRight]
      _ = (2 : ℤ) • Matrix.reindexAlgEquiv ℤ ℤ liftEquiv 1 := by
        rw [map_smul]
      _ = (2 : ℤ) • 1 := by rw [map_one]
  have hParity' :
      HasEvenNonzeroSupportInRowsAndCols C' ∧ HasOddHalfEntrySum C' := by
    -- Apply the square-local parity interface after lifting the finite index into universe `u`.
    exact signedScaledInverse_hasEvenSupportOddHalfSum C' S' hC'Entries hS' hLeft' hRight'
  refine ⟨ULift.{u} (Fin (l + 2)), inferInstance, row, col, ?_, ?_⟩
  · rw [hSelectedMatrix]
    exact hParity'.1
  · rw [hSelectedMatrix]
    exact hParity'.2

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_11/ch4_sec4_11_theorem_4_59.lean.

Theorem 4.59. A `(0, ±1)` matrix `A` is totally unimodular if and only if `A` does not contain
a square submatrix with an even number of nonzero entries in each row and column whose sum of the
entries divided by `2` is odd. -/
theorem totally_unimodular_iff_no_even_support_odd_half_sum_square_submatrix
    (A : Matrix m n ℤ) (hA : HasZeroOneNegOneEntries A) :
    A.IsTotallyUnimodular ↔ ¬ HasEvenSupportOddHalfSumSquareSubmatrix.{u, v, u} A := by
  classical
  constructor
  · intro hTU hObstruction
    -- Specialize total unimodularity to the obstructing square submatrix.
    rcases hObstruction with ⟨ι, _, row, col, hEven, hOdd⟩
    have hSubTU : (A.submatrix row col).IsTotallyUnimodular := hTU.submatrix row col
    exact (odd_half_entry_sum_not_of_totally_unimodular_square hSubTU hEven) hOdd
  · intro hNoObstruction
    -- Route correction: the reverse implication stays on Corollary 4.7 and uses the row-submatrix
    -- transport lemma to lift any Camion obstruction back to the ambient matrix.
    have hRow :
        ∀ {ρ : Type u} [Fintype ρ] [DecidableEq ρ] (row : ρ ↪ m),
          ∃ red blue : Finset ρ, is_equitable_row_bicoloring (A.submatrix row id) red blue := by
      intro ρ _ _ row
      by_cases hColor :
          ∃ red blue : Finset ρ, is_equitable_row_bicoloring (A.submatrix row id) red blue
      · exact hColor
      · have hSubObstruction :
            HasEvenSupportOddHalfSumSquareSubmatrix.{u, v, u} (A.submatrix row id) :=
            exists_even_support_odd_half_sum_square_submatrix_of_not_equitable_row_bicoloring
              (A.submatrix row id) (hA.submatrix row id) hColor
        have hObstruction :
            HasEvenSupportOddHalfSumSquareSubmatrix.{u, v, u} A :=
          even_support_odd_half_sum_square_submatrix_of_row_submatrix row hSubObstruction
        exact False.elim (hNoObstruction hObstruction)
    exact
      (totally_unimodular_iff_every_row_submatrix_admits_equitable_row_bicoloring.{u, v, u}
        A).2 hRow

end Theorem59

#print axioms totally_unimodular_iff_every_column_submatrix_admits_equitable_bicoloring
#print axioms totally_unimodular_iff_every_row_submatrix_admits_equitable_row_bicoloring
#print axioms totally_unimodular_iff_no_even_support_odd_half_sum_square_submatrix
