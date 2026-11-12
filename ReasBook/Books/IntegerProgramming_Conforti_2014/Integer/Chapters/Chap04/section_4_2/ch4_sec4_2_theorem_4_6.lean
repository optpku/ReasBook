/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_definition_4_2_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_theorem_4_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix Pointwise

-- The primitive Chapter 4.2 owner is `is_equitable_bicoloring`; this theorem keeps only the
-- source statement's existence form.

universe u v w

section Theorem46

variable {m : Type u} {n : Type v}

/-- Helper for Theorem 4.6: restricting the rows of a matrix preserves an equitable
bicoloring on its columns. -/
private lemma is_equitable_bicoloring.submatrixRows
    {α : Type*} {A : Matrix m n ℤ} [Fintype n] [DecidableEq n]
    {red blue : Finset n} (h : is_equitable_bicoloring A red blue) (row : α → m) :
    is_equitable_bicoloring (A.submatrix row id) red blue := by
  -- Unfold the predicate so the row-balance field can be checked rowwise after restriction.
  rw [is_equitable_bicoloring_iff] at h ⊢
  rcases h with ⟨hDisj, hCover, hBalance⟩
  refine ⟨hDisj, hCover, ?_⟩
  intro i
  simpa [column_bicoloring_difference, Matrix.submatrix_apply] using hBalance (row i)

/-- Helper for Theorem 4.6: a column-bicoloring difference is unchanged when the column type is
reindexed by an equivalence. -/
private lemma column_bicoloring_difference_reindex_columns
    {κ ι ν : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (B : Matrix ν κ ℤ)
    (e : ι ≃ κ)
    (red blue : Finset κ)
    (i : ν) :
    column_bicoloring_difference
        (Matrix.reindex (Equiv.refl _) e.symm B)
        (red.map e.symm.toEmbedding)
        (blue.map e.symm.toEmbedding)
        i =
      column_bicoloring_difference B red blue i := by
  -- Both transported sums are just the original sums rewritten along the column equivalence.
  rw [column_bicoloring_difference_apply, column_bicoloring_difference_apply]
  simp [Matrix.reindex_apply, Finset.sum_map]

/-- Helper for Theorem 4.6: an equitable bicoloring transports across a column reindexing
equivalence. -/
private lemma is_equitable_bicoloring_reindex_columns
    {κ ι ν : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (B : Matrix ν κ ℤ)
    (e : ι ≃ κ)
    (red blue : Finset κ)
    (hColor : is_equitable_bicoloring B red blue) :
    is_equitable_bicoloring
        (Matrix.reindex (Equiv.refl _) e.symm B)
        (red.map e.symm.toEmbedding)
        (blue.map e.symm.toEmbedding) := by
  -- Transport disjointness, coverage, and each row-balance field along the same column
  -- equivalence.
  rw [is_equitable_bicoloring_iff] at hColor ⊢
  rcases hColor with ⟨hDisj, hCover, hBalance⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (Finset.disjoint_map e.symm.toEmbedding).2 hDisj
  · calc
      red.map e.symm.toEmbedding ∪ blue.map e.symm.toEmbedding
          = (red ∪ blue).map e.symm.toEmbedding := by
              rw [Finset.map_union]
      _ = Finset.univ.map e.symm.toEmbedding := by rw [hCover]
      _ = Finset.univ := Finset.map_univ_equiv e.symm
  · intro i
    rw [column_bicoloring_difference_reindex_columns B e red blue i]
    exact hBalance i

/-- Helper for Theorem 4.6: an equitable bicoloring transports across a row reindexing
equivalence. -/
private lemma is_equitable_bicoloring_reindex_rows
    {ι κ ν : Type*} [Fintype ν] [DecidableEq ν]
    (B : Matrix κ ν ℤ) (e : ι ≃ κ) {red blue : Finset ν}
    (hColor : is_equitable_bicoloring (Matrix.reindex e.symm (Equiv.refl _) B) red blue) :
    is_equitable_bicoloring B red blue := by
  -- Only the row-balance field changes, and it is exactly the same sum evaluated at `e.symm i`.
  rw [is_equitable_bicoloring_iff] at hColor ⊢
  rcases hColor with ⟨hDisj, hCover, hBalance⟩
  refine ⟨hDisj, hCover, ?_⟩
  intro i
  simpa [column_bicoloring_difference, Matrix.reindex_apply] using hBalance (e.symm i)

/-- Helper for Theorem 4.6: if an integer row sum lies strictly between half a total sum minus
`1` and half that total sum plus `1`, then the centered difference is `0`, `1`, or `-1`. -/
private lemma two_mul_sub_mem_sign_of_half_open_bounds
    (t y : ℤ)
    (hl : (((t : ℤ) : ℝ) / 2) - 1 < y)
    (hu : (y : ℝ) < (((t : ℤ) : ℝ) / 2) + 1) :
    2 * y - t = 0 ∨ 2 * y - t = 1 ∨ 2 * y - t = -1 := by
  -- Normalize the real bounds into the integer window `-2 < 2 * y - t < 2`.
  have hltAux : t - 2 < 2 * y := by
    have hltReal : ((t : ℤ) : ℝ) - 2 < (2 : ℝ) * y := by
      nlinarith
    exact_mod_cast hltReal
  have hgtAux : 2 * y < t + 2 := by
    have hgtReal : (2 : ℝ) * y < ((t : ℤ) : ℝ) + 2 := by
      nlinarith
    exact_mod_cast hgtReal
  omega

/-- Helper for Theorem 4.6: for a `0/1`-valued integer vector, the red-minus-blue row sum over
its `1`- and `0`-supports is the centered quantity `2 * (B * z) - B * 1`. -/
private lemma columnBicoloringDifference_eq_twoMulSub_of_zeroOneSupport
    {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) ℤ)
    (z : Fin n → ℤ)
    (hz01 : ∀ j, z j = 0 ∨ z j = 1)
    (i : Fin m) :
    let red : Finset (Fin n) := Finset.univ.filter (fun j ↦ z j = 1)
    let blue : Finset (Fin n) := Finset.univ.filter (fun j ↦ z j = 0)
    column_bicoloring_difference B red blue i =
      2 * (B *ᵥ z) i - (B *ᵥ fun _ ↦ (1 : ℤ)) i := by
  classical
  let red : Finset (Fin n) := Finset.univ.filter (fun j ↦ z j = 1)
  let blue : Finset (Fin n) := Finset.univ.filter (fun j ↦ z j = 0)
  have hDisj : Disjoint red blue := by
    -- A coordinate cannot be simultaneously `0` and `1`.
    refine Finset.disjoint_left.2 ?_
    intro j hjRed hjBlue
    have hRed : z j = 1 := by simpa [red] using hjRed
    have hBlue : z j = 0 := by simpa [blue] using hjBlue
    omega
  have hCover : red ∪ blue = Finset.univ := by
    -- The `0/1` hypothesis partitions the whole column set into the red and blue supports.
    ext j
    constructor
    · intro hj
      simp
    · intro hj
      rcases hz01 j with hZero | hOne
      · simp [red, blue, hZero]
      · simp [red, blue, hOne]
  have hRedSum :
      red.sum (fun j ↦ B i j) = (B *ᵥ z) i := by
    -- Rewrite the red support sum as the matrix-vector product against the `0/1` vector `z`.
    calc
      red.sum (fun j ↦ B i j)
          = Finset.sum Finset.univ (fun j ↦ if z j = 1 then B i j else 0) := by
              simp [red, Finset.sum_filter]
      _ = Finset.sum Finset.univ (fun j ↦ B i j * z j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rcases hz01 j with hZero | hOne
            · simp [hZero]
            · simp [hOne]
      _ = (B *ᵥ z) i := by
            simp [Matrix.mulVec, dotProduct]
  have hTotalSum :
      (B *ᵥ fun _ ↦ (1 : ℤ)) i =
        red.sum (fun j ↦ B i j) + blue.sum (fun j ↦ B i j) := by
    -- The total row sum splits across the disjoint red/blue partition of all columns.
    calc
      (B *ᵥ fun _ ↦ (1 : ℤ)) i
          = Finset.sum Finset.univ (fun j ↦ B i j) := by
              simp [Matrix.mulVec, dotProduct]
      _ = Finset.sum (red ∪ blue) (fun j ↦ B i j) := by
            rw [hCover]
      _ = red.sum (fun j ↦ B i j) + blue.sum (fun j ↦ B i j) := by
            simpa using (Finset.sum_union hDisj (f := fun j : Fin n ↦ B i j))
  -- Combine the partitioned total sum with the red-support product identity.
  have hGoal :
      column_bicoloring_difference B red blue i =
        2 * (B *ᵥ z) i - (B *ᵥ fun _ ↦ (1 : ℤ)) i := by
    rw [column_bicoloring_difference_apply]
    omega
  simpa [red, blue] using hGoal

/-- Helper for Theorem 4.6: an integral point of the half-sum interval polyhedron gives an
equitable bicoloring by coloring the `1`-coordinates red and the `0`-coordinates blue. -/
private lemma equitableBicoloringOfIntegralPointInHalfSumPolyhedron
    {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) ℤ)
    {x : Fin n → ℝ}
    (hxP :
      x ∈ integer_interval_matrix_polyhedron B
        (fun i ↦ ⌊(((B *ᵥ fun _ ↦ (1 : ℤ)) i : ℝ) / 2)⌋)
        (fun i ↦ ⌈(((B *ᵥ fun _ ↦ (1 : ℤ)) i : ℝ) / 2)⌉)
        (fun _ ↦ 0)
        (fun _ ↦ 1))
    (hxInt : x ∈ integerVectors n) :
    ∃ red blue : Finset (Fin n), is_equitable_bicoloring B red blue := by
  -- Extract the interval inequalities and box constraints from the polyhedron membership.
  rcases
      (mem_integer_interval_matrix_polyhedron_iff
        B
        (fun i ↦ ⌊(((B *ᵥ fun _ ↦ (1 : ℤ)) i : ℝ) / 2)⌋)
        (fun i ↦ ⌈(((B *ᵥ fun _ ↦ (1 : ℤ)) i : ℝ) / 2)⌉)
        (fun _ ↦ 0)
        (fun _ ↦ 1)
        x).1 hxP with
    ⟨hLowerRows, hUpperRows, hLowerBox, hUpperBox⟩
  -- Route correction: extract the integer witness before any row-balance rewriting so the
  -- remaining equalities stay in the integer spelling world.
  rcases (mem_integerVectors_iff (n := n) (x := x)).1 hxInt with ⟨z, rfl⟩
  let red : Finset (Fin n) := Finset.univ.filter (fun j ↦ z j = 1)
  let blue : Finset (Fin n) := Finset.univ.filter (fun j ↦ z j = 0)
  have hz01 : ∀ j, z j = 0 ∨ z j = 1 := by
    -- The integral box constraints force each coordinate to be either `0` or `1`.
    intro j
    have h0Real : (0 : ℝ) ≤ z j := by
      simpa using hLowerBox j
    have h1Real : (z j : ℝ) ≤ 1 := by
      simpa using hUpperBox j
    have h0 : 0 ≤ z j := by
      exact_mod_cast h0Real
    have h1 : z j ≤ 1 := by
      exact_mod_cast h1Real
    omega
  have hDisj : Disjoint red blue := by
    -- The red and blue supports are disjoint because no integer is both `0` and `1`.
    refine Finset.disjoint_left.2 ?_
    intro j hjRed hjBlue
    have hRed : z j = 1 := by simpa [red] using hjRed
    have hBlue : z j = 0 := by simpa [blue] using hjBlue
    omega
  have hCover : red ∪ blue = Finset.univ := by
    -- Every column lies in exactly one support because the coordinates are `0/1`.
    ext j
    constructor
    · intro hj
      simp
    · intro hj
      rcases hz01 j with hZero | hOne
      · simp [red, blue, hZero]
      · simp [red, blue, hOne]
  have hCastMulVec :
      (B.map (Int.castRingHom ℝ)) *ᵥ (Int.cast ∘ z) =
        fun i ↦ ((B *ᵥ z) i : ℝ) := by
    -- Cast the integer matrix-vector product once so each row bound can be read over `ℤ`.
    ext i
    simpa using (RingHom.map_mulVec (Int.castRingHom ℝ) B z i).symm
  refine ⟨red, blue, ?_⟩
  rw [is_equitable_bicoloring_iff]
  refine ⟨hDisj, hCover, ?_⟩
  intro i
  let t : ℤ := (B *ᵥ fun _ ↦ (1 : ℤ)) i
  let y : ℤ := (B *ᵥ z) i
  have hLowerRowReal : (⌊((t : ℝ) / 2)⌋ : ℝ) ≤ (y : ℝ) := by
    -- Rewrite the lower row bound through the casted integer matrix-vector product.
    have hLower := hLowerRows i
    rw [hCastMulVec] at hLower
    simpa [t, y]
      using hLower
  have hUpperRowReal : (y : ℝ) ≤ (⌈((t : ℝ) / 2)⌉ : ℝ) := by
    -- Rewrite the upper row bound through the same cast identity.
    have hUpper := hUpperRows i
    rw [hCastMulVec] at hUpper
    simpa [t, y]
      using hUpper
  have hLowerOpen : (((t : ℤ) : ℝ) / 2) - 1 < y := by
    -- The floor lower bound places `y` inside the open interval required by the arithmetic
    -- companion lemma.
    exact (Int.sub_one_lt_floor (((t : ℤ) : ℝ) / 2)).trans_le hLowerRowReal
  have hUpperOpen : (y : ℝ) < (((t : ℤ) : ℝ) / 2) + 1 := by
    -- The ceil upper bound gives the matching open upper inequality.
    exact hUpperRowReal.trans_lt (Int.ceil_lt_add_one (((t : ℤ) : ℝ) / 2))
  have hCentered :
      column_bicoloring_difference B red blue i = 2 * y - t := by
    -- Normalize the red/blue support difference to the centered integer expression.
    simpa [red, blue, t, y] using
      columnBicoloringDifference_eq_twoMulSub_of_zeroOneSupport B z hz01 i
  rcases two_mul_sub_mem_sign_of_half_open_bounds t y hLowerOpen hUpperOpen with
    hZero | hOne | hNegOne
  · left
    exact hCentered.trans hZero
  · right
    left
    exact hCentered.trans hOne
  · right
    right
    exact hCentered.trans hNegOne

/-- Helper for Theorem 4.6: a totally unimodular square-indexed integer matrix admits an
equitable bicoloring of its columns. -/
private lemma finEquitableBicoloringOfIsTotallyUnimodular
    {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) ℤ)
    (hB : B.IsTotallyUnimodular) :
    ∃ red blue : Finset (Fin n), is_equitable_bicoloring B red blue := by
  let c : Fin m → ℤ := fun i ↦ ⌊(((B *ᵥ fun _ ↦ (1 : ℤ)) i : ℝ) / 2)⌋
  let d : Fin m → ℤ := fun i ↦ ⌈(((B *ᵥ fun _ ↦ (1 : ℤ)) i : ℝ) / 2)⌉
  let l : Fin n → ℤ := fun _ ↦ 0
  let u : Fin n → ℤ := fun _ ↦ 1
  let P := integer_interval_matrix_polyhedron B c d l u
  let xHalf : Fin n → ℝ := fun _ ↦ (1 / 2 : ℝ)
  have hIntegral : is_integral P := by
    -- Theorem 4.5 gives integrality of every integer interval system cut out by a TU matrix.
    exact
      ((integer_interval_matrix_polyhedron_integral_iff_totally_unimodular B).2 hB)
        c d l u
  have hHalfMulVec :
      (B.map (Int.castRingHom ℝ)) *ᵥ xHalf =
        fun i ↦ (((B *ᵥ fun _ ↦ (1 : ℤ)) i : ℤ) : ℝ) / 2 := by
    -- Compute each row directly: every coordinate of the midpoint vector is `1/2`.
    ext i
    have hOnesRow :
        Finset.sum Finset.univ (fun j : Fin n ↦ (B i j : ℝ)) =
          (((B *ᵥ fun _ ↦ (1 : ℤ)) i : ℤ) : ℝ) := by
      simpa [Matrix.mulVec, dotProduct] using
        (RingHom.map_mulVec (Int.castRingHom ℝ) B (fun _ ↦ (1 : ℤ)) i).symm
    calc
      ((B.map (Int.castRingHom ℝ)) *ᵥ xHalf) i
          = Finset.sum Finset.univ (fun j : Fin n ↦ (B i j : ℝ) * (1 / 2 : ℝ)) := by
              simp [xHalf, Matrix.mulVec, dotProduct]
      _ = (Finset.sum Finset.univ (fun j : Fin n ↦ (B i j : ℝ))) * (1 / 2 : ℝ) := by
            rw [Finset.sum_mul]
      _ = (((B *ᵥ fun _ ↦ (1 : ℤ)) i : ℤ) : ℝ) / 2 := by
            rw [hOnesRow]
            ring
  have hxHalf : xHalf ∈ P := by
    -- The midpoint satisfies the box constraints and sits between the floor and ceiling bounds
    -- rowwise by construction.
    refine (mem_integer_interval_matrix_polyhedron_iff B c d l u xHalf).2 ?_
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rw [hHalfMulVec]
      simpa [c] using Int.floor_le ((((B *ᵥ fun _ ↦ (1 : ℤ)) i : ℤ) : ℝ) / 2)
    · intro i
      rw [hHalfMulVec]
      simpa [d] using Int.le_ceil ((((B *ᵥ fun _ ↦ (1 : ℤ)) i : ℤ) : ℝ) / 2)
    · intro j
      norm_num [l, xHalf]
    · intro j
      norm_num [u, xHalf]
  have hHullNonempty :
      (convexHull ℝ (P ∩ Set.range (fun z : Fin n → ℤ ↦ Int.cast ∘ z))).Nonempty := by
    -- The integral description of `P` shows that the convex hull of its integer points contains
    -- the midpoint witness.
    rw [← (is_integral_iff).1 hIntegral]
    exact ⟨xHalf, hxHalf⟩
  have hIntegerPoint :
      (P ∩ Set.range (fun z : Fin n → ℤ ↦ Int.cast ∘ z)).Nonempty := by
    -- Nonemptiness of a convex hull reflects nonemptiness of the generating set.
    exact convexHull_nonempty_iff.mp hHullNonempty
  rcases hIntegerPoint with ⟨x, hxMem⟩
  have hxP : x ∈ P := hxMem.1
  have hxIntRange : x ∈ Set.range (fun z : Fin n → ℤ ↦ Int.cast ∘ z) := hxMem.2
  have hxInt : x ∈ integerVectors n := by
    simpa [P, integerVectors] using hxIntRange
  -- Feed the extracted integral witness to the Fin-indexed bridge proved above.
  exact equitableBicoloringOfIntegralPointInHalfSumPolyhedron B hxP hxInt

/-- Helper for Theorem 4.6: a totally unimodular matrix on arbitrary finite row and column types
admits an equitable bicoloring. -/
private lemma finiteEquitableBicoloringOfIsTotallyUnimodular
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (B : Matrix α β ℤ) (hB : B.IsTotallyUnimodular) :
    ∃ red blue : Finset β, is_equitable_bicoloring B red blue := by
  classical
  let rowEquiv : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let colEquiv : β ≃ Fin (Fintype.card β) := Fintype.equivFin β
  let Brow : Matrix (Fin (Fintype.card α)) β ℤ := Matrix.reindex rowEquiv (Equiv.refl _) B
  let Bfin : Matrix (Fin (Fintype.card α)) (Fin (Fintype.card β)) ℤ :=
    Matrix.reindex (Equiv.refl _) colEquiv Brow
  have hBrow : Brow.IsTotallyUnimodular := by
    -- First move the row index to `Fin`; this is the row-only transport used later in reverse.
    simpa [Brow, rowEquiv] using
      (Matrix.reindex_isTotallyUnimodular B rowEquiv (Equiv.refl β)).2 hB
  have hBfin : Bfin.IsTotallyUnimodular := by
    -- Then move the column index to `Fin`, producing the finite canonical matrix.
    simpa [Bfin, Brow, colEquiv] using
      (Matrix.reindex_isTotallyUnimodular Brow (Equiv.refl _) colEquiv).2 hBrow
  obtain ⟨redFin, blueFin, hColorFin⟩ :=
    finEquitableBicoloringOfIsTotallyUnimodular Bfin hBfin
  let red : Finset β := redFin.map colEquiv.symm.toEmbedding
  let blue : Finset β := blueFin.map colEquiv.symm.toEmbedding
  have hColorBrow : is_equitable_bicoloring Brow red blue := by
    -- Transport the finished coloring back across the column equivalence only.
    simpa [Bfin, Brow, red, blue, colEquiv, Matrix.reindex_apply] using
      is_equitable_bicoloring_reindex_columns Bfin colEquiv redFin blueFin hColorFin
  refine ⟨red, blue, ?_⟩
  -- Finally transport the row-reindexed coloring back to the original matrix.
  simpa [Brow, red, blue, rowEquiv, Matrix.reindex_apply] using
    is_equitable_bicoloring_reindex_rows B rowEquiv.symm hColorBrow

/-- Helper for Theorem 4.6: if an admissible red/blue partition is not equitable, then some row
already violates the row-balance clause. -/
private lemma admissiblePartitionHasBadRow
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (B : Matrix m ι ℤ)
    {red blue : Finset ι}
    (hDisj : Disjoint red blue)
    (hCover : red ∪ blue = Finset.univ)
    (hNotColor : ¬ is_equitable_bicoloring B red blue) :
    ∃ r : m,
      ¬ (column_bicoloring_difference B red blue r = 0 ∨
        column_bicoloring_difference B red blue r = 1 ∨
        column_bicoloring_difference B red blue r = -1) := by
  classical
  by_contra hNoBadRow
  apply hNotColor
  rw [is_equitable_bicoloring_iff]
  refine ⟨hDisj, hCover, ?_⟩
  intro r
  -- If no witness row exists, every row satisfies the required trichotomy.
  by_contra hBad
  exact hNoBadRow ⟨r, hBad⟩

/-- Helper for Theorem 4.6: if every finite row restriction of a matrix with finitely many columns
admits an equitable bicoloring, then the full matrix does as well. -/
private lemma existsEquitableBicoloringOfAllFiniteRowRestrictions
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (B : Matrix m ι ℤ)
    (hfinite :
      ∀ {α : Type u} [Fintype α] [DecidableEq α] (row : α ↪ m),
        ∃ red blue : Finset ι,
          is_equitable_bicoloring (B.submatrix row id) red blue) :
    ∃ red blue : Finset ι, is_equitable_bicoloring B red blue := by
  classical
  let BadPartition :=
    {p : Finset ι × Finset ι //
      Disjoint p.1 p.2 ∧ p.1 ∪ p.2 = Finset.univ ∧ ¬ is_equitable_bicoloring B p.1 p.2}
  let witnessRow : BadPartition → m := fun p ↦
    Classical.choose
      (admissiblePartitionHasBadRow B p.2.1 p.2.2.1 p.2.2.2)
  let α := ↥(Set.range witnessRow)
  let row : α ↪ m := Function.Embedding.subtype (Set.range witnessRow)
  have hαfinite : (Set.range witnessRow).Finite := Set.finite_range witnessRow
  let _ : Fintype α := hαfinite.fintype
  let _ : DecidableEq α := Classical.decEq α
  obtain ⟨red, blue, hColorRestricted⟩ := hfinite (α := α) row
  have hRestrictedData :
      Disjoint red blue ∧
        red ∪ blue = Finset.univ ∧
        ∀ i : α,
          column_bicoloring_difference (B.submatrix row id) red blue i = 0 ∨
            column_bicoloring_difference (B.submatrix row id) red blue i = 1 ∨
            column_bicoloring_difference (B.submatrix row id) red blue i = -1 := by
    -- Unpack the coloring on the chosen finite row restriction once.
    exact (is_equitable_bicoloring_iff (B.submatrix row id) red blue).1 hColorRestricted
  by_cases hColor : is_equitable_bicoloring B red blue
  · exact ⟨red, blue, hColor⟩
  · let bad : BadPartition := ⟨(red, blue), hRestrictedData.1, hRestrictedData.2.1, hColor⟩
    let badRow : α := ⟨witnessRow bad, ⟨bad, rfl⟩⟩
    have hWitness :
        ¬ (column_bicoloring_difference B red blue (witnessRow bad) = 0 ∨
          column_bicoloring_difference B red blue (witnessRow bad) = 1 ∨
          column_bicoloring_difference B red blue (witnessRow bad) = -1) := by
      -- The chosen row for a bad partition is exactly a violating row.
      exact
        Classical.choose_spec
          (admissiblePartitionHasBadRow B bad.2.1 bad.2.2.1 bad.2.2.2)
    have hRestrictedBalance :=
      hRestrictedData.2.2 badRow
    have hLiftedBalance :
        column_bicoloring_difference B red blue (witnessRow bad) = 0 ∨
          column_bicoloring_difference B red blue (witnessRow bad) = 1 ∨
          column_bicoloring_difference B red blue (witnessRow bad) = -1 := by
      -- Evaluating the restricted row at the witness subtype gives the same ambient row sum.
      simpa [row, badRow, witnessRow, column_bicoloring_difference, Matrix.submatrix_apply] using
        hRestrictedBalance
    exact (hWitness hLiftedBalance).elim

/-- Helper for Theorem 4.6: multiplying a sign-valued integer by `(-1)^t` stays in the sign
range. -/
private lemma negOnePow_mul_mem_signTypeRange
    (t : ℕ) {z : ℤ} (hz : z ∈ Set.range (SignType.cast : SignType → ℤ)) :
    (-1 : ℤ) ^ t * z ∈ Set.range (SignType.cast : SignType → ℤ) := by
  -- The factor `(-1)^t` is either `1` or `-1`, so it only possibly flips the sign witness.
  rcases neg_one_pow_eq_or ℤ t with hpow | hpow
  · rw [hpow, one_mul]
    exact hz
  · rw [hpow, neg_mul]
    rcases hz with ⟨s, rfl⟩
    cases s
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨-1, by simp⟩

/-- Helper for Theorem 4.6: for disjoint red and blue classes, the red-minus-blue row sum is a
single matrix-vector product against the signed indicator vector. -/
private lemma columnBicoloringDifference_eq_mulVec_signedIndicator
    {ρ ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ρ ι ℤ) (red blue : Finset ι) (hDisj : Disjoint red blue) :
    column_bicoloring_difference S red blue =
      S *ᵥ (fun j ↦ if j ∈ red then (1 : ℤ) else if j ∈ blue then (-1 : ℤ) else 0) := by
  ext i
  have hRed :
      ∑ j : ι, (if j ∈ red then S i j else 0) = red.sum (fun j ↦ S i j) := by
    -- The red contribution is the usual filtered sum over the red support.
    simp
  have hBlue :
      ∑ j : ι, (if j ∈ blue then S i j else 0) = blue.sum (fun j ↦ S i j) := by
    -- The blue contribution is the analogous filtered sum over the blue support.
    simp
  rw [column_bicoloring_difference_apply, Matrix.mulVec, dotProduct]
  symm
  calc
    ∑ j : ι, S i j *
        (if j ∈ red then (1 : ℤ) else if j ∈ blue then (-1 : ℤ) else 0)
      = ∑ j : ι, ((if j ∈ red then S i j else 0) - (if j ∈ blue then S i j else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          by_cases hjRed : j ∈ red
          · have hjBlue : j ∉ blue := by
              exact fun hjBlue ↦ (Finset.disjoint_left.1 hDisj) hjRed hjBlue
            simp [hjRed, hjBlue]
          · by_cases hjBlue : j ∈ blue
            · simp [hjRed, hjBlue]
            · simp [hjRed, hjBlue]
    _ = (∑ j : ι, if j ∈ red then S i j else 0) - ∑ j : ι, if j ∈ blue then S i j else 0 := by
          rw [Finset.sum_sub_distrib]
    _ = red.sum (fun j ↦ S i j) - blue.sum (fun j ↦ S i j) := by
          rw [hRed, hBlue]

/-- Helper for Theorem 4.6: if every deleted minor determinant lies in the sign range, then every
coordinate of the first Cramer column does too. -/
private lemma firstCramer_mem_signTypeRange_of_minorDetMemSign
    {k : ℕ}
    (C : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)
    (hminor : ∀ i j : Fin (k + 1),
      (C.submatrix i.succAbove j.succAbove).det ∈ Set.range (SignType.cast : SignType → ℤ)) :
    ∀ i : Fin (k + 1),
      Matrix.cramer C (Pi.single 0 (1 : ℤ)) i ∈ Set.range (SignType.cast : SignType → ℤ) := by
  intro i
  -- The first Cramer column is the first adjugate column, so each coordinate is a signed deleted
  -- minor determinant.
  rw [Matrix.cramer_eq_adjugate_mulVec]
  have hEntry : (C.adjugate *ᵥ Pi.single 0 (1 : ℤ)) i = C.adjugate i 0 := by
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro hzero
      exact (hzero (by simp)).elim
  rw [hEntry, Matrix.adjugate_fin_succ_eq_det_submatrix]
  simpa using negOnePow_mul_mem_signTypeRange i.1 (hminor 0 i)

/-- Helper for Theorem 4.6: specialize the ambient column-colorability hypothesis once to
`Fin`-indexed column embeddings. -/
private lemma ambientFinColumnColorability
    {A : Matrix m n ℤ}
    (hColor :
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (col : ι ↪ n),
        ∃ red blue : Finset ι,
          is_equitable_bicoloring (A.submatrix id col) red blue) :
    ∀ {ℓ : ℕ} (col : Fin ℓ ↪ n),
      ∃ red blue : Finset (Fin ℓ),
        is_equitable_bicoloring (A.submatrix id col) red blue := by
  -- Route correction: specialize the theorem hypothesis on a single `ULift` of `Fin ℓ`, then
  -- transport the resulting coloring back across `Equiv.ulift`. This pays the universe conversion
  -- once and keeps the rest of the converse purely `Fin`-indexed.
  intro ℓ col
  let colUp : ULift (Fin ℓ) ↪ n :=
    ⟨fun j ↦ col j.down, by
      intro x y h
      cases x
      cases y
      simp at h
      simpa [h]⟩
  let e : Fin ℓ ≃ ULift (Fin ℓ) :=
    { toFun := ULift.up
      invFun := ULift.down
      left_inv := fun _ ↦ rfl
      right_inv := by
        intro x
        cases x
        rfl }
  obtain ⟨redUp, blueUp, hColorUp⟩ := hColor (ι := ULift (Fin ℓ)) colUp
  refine ⟨redUp.map e.symm.toEmbedding, blueUp.map e.symm.toEmbedding, ?_⟩
  -- The matrix itself is the same column selection after reindexing the `ULift`ed columns back to
  -- `Fin ℓ`.
  simpa [colUp, Matrix.reindex_apply] using
    (is_equitable_bicoloring_reindex_columns
      (A.submatrix id colUp) e redUp blueUp hColorUp)

/-- Helper for Theorem 4.6: ambient column-colorability restricts to every column submatrix of a
square submatrix by composing the chosen column embeddings and then restricting rows. -/
private lemma squareSubmatrixColumnColorabilityOfAmbientColumnColorability
    {k : ℕ} {A : Matrix m n ℤ}
    (hColorFin :
      ∀ {ℓ : ℕ} (col : Fin ℓ ↪ n),
        ∃ red blue : Finset (Fin ℓ),
          is_equitable_bicoloring (A.submatrix id col) red blue)
    (row : Fin k → m) (col : Fin k ↪ n)
    {ℓ : ℕ} (g : Fin ℓ ↪ Fin k) :
    ∃ red blue : Finset (Fin ℓ),
      is_equitable_bicoloring ((A.submatrix row col).submatrix id g) red blue := by
  obtain ⟨red, blue, hAmbient⟩ := hColorFin (g.trans col)
  refine ⟨red, blue, ?_⟩
  -- First color the composed ambient column embedding, then restrict the rows to the square
  -- submatrix.
  have hRestricted := is_equitable_bicoloring.submatrixRows hAmbient row
  simpa [Matrix.submatrix_submatrix, Function.comp_apply] using hRestricted

/-- Helper for Theorem 4.6: deleted minors inherit the column-colorability hypothesis from the
ambient square matrix through the direct `succAbove` embeddings. -/
private lemma deletedMinorColumnColorabilityOfSquareColorability
    {k : ℕ}
    (C : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)
    (hColorFin :
      ∀ {ℓ : ℕ} (col : Fin ℓ ↪ Fin (k + 1)),
        ∃ red blue : Finset (Fin ℓ),
          is_equitable_bicoloring (C.submatrix id col) red blue)
    (i j : Fin (k + 1))
    {ℓ : ℕ} (g : Fin ℓ ↪ Fin k) :
    ∃ red blue : Finset (Fin ℓ),
      is_equitable_bicoloring ((C.submatrix i.succAbove j.succAbove).submatrix id g) red blue := by
  -- The deleted minor is a square submatrix, so the generic transport bridge applies directly.
  simpa using
    squareSubmatrixColumnColorabilityOfAmbientColumnColorability
      hColorFin i.succAbove j.succAboveEmb g

/-- Helper for Theorem 4.6: if a vector vanishes outside the range of a column embedding, then the
ambient matrix-vector product equals the corresponding product on the column submatrix. -/
private lemma submatrixMulVec_eq_mulVec_of_eq_zero_outside
    {ρ ι ν : Type*} [Fintype ι] [Fintype ν] [DecidableEq ν]
    (A : Matrix ρ ν ℤ) (g : ι ↪ ν) {y : ν → ℤ}
    (hy : ∀ t : ν, t ∉ Set.range g → y t = 0) :
    A *ᵥ y = (A.submatrix id g) *ᵥ (fun s : ι ↦ y (g s)) := by
  ext i
  have hfilter :
      Finset.univ.filter (fun t : ν ↦ t ∈ Set.range g) = Finset.univ.map g := by
    ext t
    simp [Set.mem_range]
  -- Drop the zero coordinates outside the chosen range, then reindex the remaining sum by `g`.
  calc
    (A *ᵥ y) i = ∑ t : ν, A i t * y t := by
      simp [Matrix.mulVec, dotProduct]
    _ =
        Finset.sum (Finset.univ.filter (fun t : ν ↦ t ∈ Set.range g))
          (fun t : ν ↦ A i t * y t) := by
            symm
            refine Finset.sum_subset (Finset.filter_subset _ _) ?_
            intro t _ ht
            have ht' : t ∉ Set.range g := by
              simpa using ht
            simp [hy t ht']
    _ = Finset.sum (Finset.univ.map g) (fun t : ν ↦ A i t * y t) := by
          rw [hfilter]
    _ = ∑ s : ι, A i (g s) * y (g s) := by
          simp
    _ = (((A.submatrix id g) *ᵥ fun s : ι ↦ y (g s)) i) := by
          simp [Matrix.mulVec, dotProduct]

/-- Helper for Theorem 4.6: a nonzero determinant makes the square matrix-vector map injective. -/
private lemma eq_of_mulVec_eq_of_det_ne_zero
    {k : ℕ} {M : Matrix (Fin k) (Fin k) ℤ} (hM : M.det ≠ 0)
    {x y : Fin k → ℤ} (hxy : M *ᵥ x = M *ᵥ y) :
    x = y := by
  -- Subtract the two systems and use nonsingularity to kill the difference vector.
  have hsub : M *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hzero : x - y = 0 := Matrix.eq_zero_of_mulVec_eq_zero hM hsub
  exact sub_eq_zero.mp hzero

/-- Helper for Theorem 4.6: when the total row sum is even, an equitable row balance can only be
`0`. -/
private lemma rowBalance_eq_zero_of_even_total
    {ρ ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ρ ι ℤ) {red blue : Finset ι}
    (hDisj : Disjoint red blue) (hCover : red ∪ blue = Finset.univ)
    {i : ρ}
    (hEven : Even ((S *ᵥ fun _ ↦ (1 : ℤ)) i))
    (hBalance :
      column_bicoloring_difference S red blue i = 0 ∨
        column_bicoloring_difference S red blue i = 1 ∨
        column_bicoloring_difference S red blue i = -1) :
    column_bicoloring_difference S red blue i = 0 := by
  let r : ℤ := red.sum (fun j ↦ S i j)
  let b : ℤ := blue.sum (fun j ↦ S i j)
  have hTotal : (S *ᵥ fun _ ↦ (1 : ℤ)) i = r + b := by
    -- The total row sum splits across the disjoint red/blue partition of the columns.
    calc
      (S *ᵥ fun _ ↦ (1 : ℤ)) i = ∑ j : ι, S i j := by
        simp [Matrix.mulVec, dotProduct]
      _ = Finset.sum (red ∪ blue) (fun j ↦ S i j) := by
            rw [hCover]
      _ = r + b := by
            simpa [r, b] using (Finset.sum_union hDisj (f := fun j : ι ↦ S i j))
  rcases hEven with ⟨t, ht⟩
  rcases hBalance with hZero | hOne | hNegOne
  · exact hZero
  · have hOne' : r - b = 1 := by
      simpa [r, b, column_bicoloring_difference_apply] using hOne
    rw [hTotal] at ht
    omega
  · have hNegOne' : r - b = -1 := by
      simpa [r, b, column_bicoloring_difference_apply] using hNegOne
    rw [hTotal] at ht
    omega

/-- Helper for Theorem 4.6: when the total row sum is odd, an equitable row balance must be
`1` or `-1`. -/
private lemma rowBalance_eq_pos_or_neg_of_odd_total
    {ρ ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ρ ι ℤ) {red blue : Finset ι}
    (hDisj : Disjoint red blue) (hCover : red ∪ blue = Finset.univ)
    {i : ρ}
    (hOdd : Odd ((S *ᵥ fun _ ↦ (1 : ℤ)) i))
    (hBalance :
      column_bicoloring_difference S red blue i = 0 ∨
        column_bicoloring_difference S red blue i = 1 ∨
        column_bicoloring_difference S red blue i = -1) :
    column_bicoloring_difference S red blue i = 1 ∨
      column_bicoloring_difference S red blue i = -1 := by
  let r : ℤ := red.sum (fun j ↦ S i j)
  let b : ℤ := blue.sum (fun j ↦ S i j)
  have hTotal : (S *ᵥ fun _ ↦ (1 : ℤ)) i = r + b := by
    -- As above, the total row sum is the sum of the red and blue contributions.
    calc
      (S *ᵥ fun _ ↦ (1 : ℤ)) i = ∑ j : ι, S i j := by
        simp [Matrix.mulVec, dotProduct]
      _ = Finset.sum (red ∪ blue) (fun j ↦ S i j) := by
            rw [hCover]
      _ = r + b := by
            simpa [r, b] using (Finset.sum_union hDisj (f := fun j : ι ↦ S i j))
  rcases hOdd with ⟨t, ht⟩
  rcases hBalance with hZero | hOne | hNegOne
  · have hZero' : r - b = 0 := by
      simpa [r, b, column_bicoloring_difference_apply] using hZero
    rw [hTotal] at ht
    omega
  · exact Or.inl hOne
  · exact Or.inr hNegOne

/-- Helper for Theorem 4.6: on the support of the first Cramer column, the unweighted row sum and
the Cramer-weighted row sum have the same parity. -/
private lemma supportRowSumsParity_ofFirstCramerSupport
    {k : ℕ}
    (C : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)
    (hd :
      ∀ i : Fin (k + 1),
        Matrix.cramer C (Pi.single 0 (1 : ℤ)) i ∈ Set.range (SignType.cast : SignType → ℤ))
    (i : Fin (k + 1)) :
    let d : Fin (k + 1) → ℤ := Matrix.cramer C (Pi.single 0 (1 : ℤ))
    let support : Finset (Fin (k + 1)) := Finset.univ.filter (fun j ↦ d j ≠ 0)
    let supportEmb : Fin support.card ↪ Fin (k + 1) := (support.orderEmbOfFin rfl).toEmbedding
    let S : Matrix (Fin (k + 1)) (Fin support.card) ℤ := C.submatrix id supportEmb
    Even (((S *ᵥ fun _ ↦ (1 : ℤ)) i) - (C *ᵥ d) i) := by
  classical
  let d : Fin (k + 1) → ℤ := Matrix.cramer C (Pi.single 0 (1 : ℤ))
  let support : Finset (Fin (k + 1)) := Finset.univ.filter (fun j ↦ d j ≠ 0)
  let supportEmb : Fin support.card ↪ Fin (k + 1) := (support.orderEmbOfFin rfl).toEmbedding
  let S : Matrix (Fin (k + 1)) (Fin support.card) ℤ := C.submatrix id supportEmb
  have hdZeroOutside :
      ∀ t : Fin (k + 1), t ∉ Set.range supportEmb → d t = 0 := by
    -- Outside the support embedding range, the Cramer coordinate must vanish by definition of the
    -- support set.
    intro t ht
    by_contra hdt
    have htSupport : t ∈ support := by
      simp [support, d, hdt]
    have htRange : t ∈ Set.range supportEmb := by
      have htRange' : t ∈ Set.range (support.orderEmbOfFin rfl) := by
        rwa [support.range_orderEmbOfFin rfl]
      simpa [supportEmb] using htRange'
    exact ht htRange
  have hMulVecSupport :
      C *ᵥ d = S *ᵥ fun s : Fin support.card ↦ d (supportEmb s) := by
    -- Restrict the ambient product to the nonzero support once; all off-support coordinates are
    -- already zero.
    simpa [S] using
      (submatrixMulVec_eq_mulVec_of_eq_zero_outside C supportEmb (y := d) hdZeroOutside)
  have hTermEven :
      ∀ s : Fin support.card, Even (C i (supportEmb s) * (1 - d (supportEmb s))) := by
    -- On the support, each Cramer coordinate is `1` or `-1`, so `1 - d_j` is `0` or `2`.
    intro s
    have hsMem : supportEmb s ∈ support := by
      simpa [supportEmb] using Finset.orderEmbOfFin_mem support rfl s
    have hsNonzero : d (supportEmb s) ≠ 0 := by
      exact (Finset.mem_filter.1 hsMem).2
    have hsSign := hd (supportEmb s)
    rw [SignType.range_eq (SignType.cast : SignType → ℤ)] at hsSign
    rcases hsSign with hsZero | hsNeg | hsPos
    · exact (hsNonzero hsZero).elim
    · refine ⟨C i (supportEmb s), ?_⟩
      have hsNeg' : d (supportEmb s) = -1 := by simpa [d] using hsNeg
      rw [hsNeg']
      ring
    · refine ⟨0, ?_⟩
      have hsPos' : d (supportEmb s) = 1 := by simpa [d] using hsPos
      rw [hsPos']
      ring
  have hSumEvenUniv :
      Even ((Finset.univ : Finset (Fin support.card)).sum
        (fun s ↦ C i (supportEmb s) * (1 - d (supportEmb s)))) := by
    -- Summing even terms preserves evenness.
    refine Finset.induction_on (s := (Finset.univ : Finset (Fin support.card))) ?_ ?_
    · exact ⟨0, by simp⟩
    · intro a s ha hs
      simpa [Finset.sum_insert, ha] using (hTermEven a).add hs
  have hSumEven :
      Even (∑ s : Fin support.card, C i (supportEmb s) * (1 - d (supportEmb s))) := by
    simpa using hSumEvenUniv
  have hRewrite :
      ((S *ᵥ fun _ ↦ (1 : ℤ)) i) - (C *ᵥ d) i =
        ∑ s : Fin support.card, C i (supportEmb s) * (1 - d (supportEmb s)) := by
    -- Rewrite both row sums over the same support index set and combine them termwise.
    have hMulVecAt : (C *ᵥ d) i = (S *ᵥ fun s : Fin support.card ↦ d (supportEmb s)) i :=
      congrFun hMulVecSupport i
    rw [hMulVecAt]
    calc
      ((S *ᵥ fun _ ↦ (1 : ℤ)) i) - (S *ᵥ fun s : Fin support.card ↦ d (supportEmb s)) i
          = (∑ s : Fin support.card, C i (supportEmb s) * (1 : ℤ)) -
              ∑ s : Fin support.card, C i (supportEmb s) * d (supportEmb s) := by
                simp [S, Matrix.mulVec, dotProduct]
      _ =
          ∑ s : Fin support.card,
            (C i (supportEmb s) * (1 : ℤ) - C i (supportEmb s) * d (supportEmb s)) := by
              rw [Finset.sum_sub_distrib]
      _ = ∑ s : Fin support.card, C i (supportEmb s) * (1 - d (supportEmb s)) := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            ring
  have hFinal : Even (((S *ᵥ fun _ ↦ (1 : ℤ)) i) - (C *ᵥ d) i) := by
    -- The parity claim is now exactly the evenness of the support-indexed sum.
    rw [hRewrite]
    exact hSumEven
  simpa [d, support, supportEmb, S] using hFinal

/-- Helper for Theorem 4.6: on the support submatrix, the explicit `±1` indicator vector
reproduces the column-bicoloring difference. -/
private lemma supportIndicatorMulVec_eq_columnBicoloringDifference
    {ρ ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ρ ι ℤ) {red blue : Finset ι}
    (hColor : is_equitable_bicoloring S red blue) :
    S *ᵥ (fun s ↦ if s ∈ red then (1 : ℤ) else (-1 : ℤ)) =
      column_bicoloring_difference S red blue := by
  rw [is_equitable_bicoloring_iff] at hColor
  rcases hColor with ⟨hDisj, hCover, _⟩
  -- Replace the generic `0/±1` signed indicator by the support-side `±1` indicator using that
  -- every support index is colored.
  calc
    S *ᵥ (fun s ↦ if s ∈ red then (1 : ℤ) else (-1 : ℤ))
        =
          S *ᵥ (fun s ↦ if s ∈ red then (1 : ℤ) else if s ∈ blue then (-1 : ℤ) else 0) := by
            congr 1
            funext s
            by_cases hsRed : s ∈ red
            · simp [hsRed]
            · have hsBlue : s ∈ blue := by
                have hsMem : s ∈ red ∪ blue := by
                  simpa [hCover]
                simpa [Finset.mem_union, hsRed] using hsMem
              simp [hsRed, hsBlue]
    _ = column_bicoloring_difference S red blue := by
          symm
          exact columnBicoloringDifference_eq_mulVec_signedIndicator S red blue hDisj

/-- Helper for Theorem 4.6: an equitable bicoloring of the support-column submatrix extends to an
ambient signed indicator vector whose matrix product is the same row-balance function. -/
private lemma supportColumnSignedIndicatorSystem
    {k : ℕ}
    (C : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)
    (d : Fin (k + 1) → ℤ)
    (support : Finset (Fin (k + 1)))
    (supportEmb : Fin support.card ↪ Fin (k + 1))
    (hRange : Set.range supportEmb = support)
    (hSupport : ∀ t : Fin (k + 1), t ∈ support ↔ d t ≠ 0)
    {red blue : Finset (Fin support.card)}
    (hColor : is_equitable_bicoloring (C.submatrix id supportEmb) red blue) :
    ∃ x : Fin (k + 1) → ℤ,
      (∀ t : Fin (k + 1), d t = 0 → x t = 0) ∧
      (∀ t : Fin (k + 1), d t ≠ 0 → x t = 1 ∨ x t = -1) ∧
      C *ᵥ x = column_bicoloring_difference (C.submatrix id supportEmb) red blue := by
  classical
  let x : Fin (k + 1) → ℤ := fun t ↦
    if ht : t ∈ Set.range supportEmb then
      if Classical.choose ht ∈ red then 1 else -1
    else 0
  refine ⟨x, ?_, ?_, ?_⟩
  · intro t hdt
    -- A zero Cramer coordinate cannot lie in the declared support, so the ambient extension
    -- vanishes off support by construction.
    by_cases ht : t ∈ Set.range supportEmb
    · exfalso
      have htSupport : t ∈ support := by
        have htSupportSet : t ∈ (support : Set (Fin (k + 1))) := by
          simpa [hRange] using ht
        simpa using htSupportSet
      exact ((hSupport t).1 htSupport) hdt
    · unfold x
      exact dif_neg ht
  · intro t hdt
    -- On the support range, the ambient extension is the same `±1` indicator used on the support
    -- submatrix.
    have htSupport : t ∈ support := (hSupport t).2 hdt
    have htRange : t ∈ Set.range supportEmb := by
      have htSupportSet : t ∈ (support : Set (Fin (k + 1))) := by
        simpa using htSupport
      simpa [hRange] using htSupportSet
    by_cases hRed : Classical.choose htRange ∈ red
    · left
      unfold x
      rw [dif_pos htRange]
      simpa [hRed]
    · right
      unfold x
      rw [dif_pos htRange]
      simpa [hRed]
  · have hxZero :
        ∀ t : Fin (k + 1), t ∉ Set.range supportEmb → x t = 0 := by
        intro t ht
        unfold x
        exact dif_neg ht
    have hAmbient :
        C *ᵥ x =
          (C.submatrix id supportEmb) *ᵥ (fun s : Fin support.card ↦ x (supportEmb s)) := by
      -- The ambient product reduces to the support submatrix because the extension is zero off the
      -- support range.
      exact submatrixMulVec_eq_mulVec_of_eq_zero_outside C supportEmb hxZero
    have hRestricted :
        (fun s : Fin support.card ↦ x (supportEmb s)) =
          fun s ↦ if s ∈ red then (1 : ℤ) else (-1 : ℤ) := by
      -- Evaluating the extension on an embedded support index recovers the original support-side
      -- signed indicator exactly.
      funext s
      have hsRange : supportEmb s ∈ Set.range supportEmb := ⟨s, rfl⟩
      have hsChoose : Classical.choose hsRange = s := by
        apply supportEmb.injective
        exact Classical.choose_spec hsRange
      unfold x
      rw [dif_pos hsRange]
      simp [hsChoose]
    calc
      C *ᵥ x =
          (C.submatrix id supportEmb) *ᵥ (fun s : Fin support.card ↦ x (supportEmb s)) :=
        hAmbient
      _ =
          (C.submatrix id supportEmb) *ᵥ
            (fun s ↦ if s ∈ red then (1 : ℤ) else (-1 : ℤ)) := by
              rw [hRestricted]
      _ = column_bicoloring_difference (C.submatrix id supportEmb) red blue :=
        supportIndicatorMulVec_eq_columnBicoloringDifference _ hColor

/-- Helper for Theorem 4.6: a sign-valued solution of `C *ᵥ x = e₀` forces the determinant of `C`
to lie in `0, ±1` once the first Cramer column is already sign-valued. -/
private lemma oddDet_mem_signTypeRange_ofSupportSystem
    {k : ℕ}
    (C : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)
    (hdet_ne_zero : C.det ≠ 0)
    (hd :
      ∀ i : Fin (k + 1),
        Matrix.cramer C (Pi.single 0 (1 : ℤ)) i ∈ Set.range (SignType.cast : SignType → ℤ))
    {x : Fin (k + 1) → ℤ}
    (hxSign : ∀ i : Fin (k + 1), x i ∈ Set.range (SignType.cast : SignType → ℤ))
    (hxSystem : C *ᵥ x = Pi.single 0 (1 : ℤ)) :
    C.det ∈ Set.range (SignType.cast : SignType → ℤ) := by
  let d : Fin (k + 1) → ℤ := Matrix.cramer C (Pi.single 0 (1 : ℤ))
  have hdEq :
      d = C.det • x := by
    -- Compare the given unit-system solution with the first Cramer column using injectivity of
    -- multiplication by a nonsingular square matrix.
    apply eq_of_mulVec_eq_of_det_ne_zero hdet_ne_zero
    calc
      C *ᵥ d = C.det • Pi.single 0 (1 : ℤ) := Matrix.mulVec_cramer C (Pi.single 0 (1 : ℤ))
      _ = C *ᵥ (C.det • x) := by
            symm
            calc
              C *ᵥ (C.det • x) = C.det • (C *ᵥ x) := by
                simpa using (Matrix.mulVec_smul C C.det x)
              _ = C.det • Pi.single 0 (1 : ℤ) := by rw [hxSystem]
  have hx_ne_zero : x ≠ 0 := by
    -- The system `C *ᵥ x = e₀` forbids the zero vector.
    intro hxZero
    have hAtZero := congrFun hxSystem 0
    simp [hxZero] at hAtZero
  have hxExists : ∃ j : Fin (k + 1), x j ≠ 0 := by
    by_contra hxNone
    apply hx_ne_zero
    funext j
    by_contra hxj
    exact hxNone ⟨j, hxj⟩
  rcases hxExists with ⟨j, hjNonzero⟩
  have hxpm : x j = 1 ∨ x j = -1 := by
    -- A nonzero sign-valued coordinate must be `1` or `-1`.
    have hxj := hxSign j
    rw [SignType.range_eq (SignType.cast : SignType → ℤ)] at hxj
    rcases hxj with hZero | hNeg | hPos
    · exact (hjNonzero hZero).elim
    · exact Or.inr hNeg
    · exact Or.inl hPos
  cases hxpm with
  | inl hPos =>
      -- When a support coordinate of `x` is `1`, the matching Cramer coordinate is exactly
      -- `det C`.
      simpa [d, hdEq, hPos] using hd j
  | inr hNeg =>
      -- When the support coordinate is `-1`, the matching Cramer coordinate is `- det C`, so one
      -- more sign flip puts the determinant itself in the sign range.
      have hNegDet : -C.det ∈ Set.range (SignType.cast : SignType → ℤ) := by
        simpa [d, hdEq, hNeg] using hd j
      simpa using negOnePow_mul_mem_signTypeRange 1 hNegDet

/-- Helper for Theorem 4.6: a nonzero determinant forces the first Cramer column for `e₀` to have
some nonzero coordinate. -/
private lemma exists_nonzero_firstCramer_of_det_ne_zero
    {k : ℕ}
    (C : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)
    (hdet_ne_zero : C.det ≠ 0) :
    ∃ j : Fin (k + 1), Matrix.cramer C (Pi.single 0 (1 : ℤ)) j ≠ 0 := by
  by_contra hNone
  have hdZero : Matrix.cramer C (Pi.single 0 (1 : ℤ)) = 0 := by
    -- If no coordinate survives, the whole first Cramer column is zero.
    ext j
    by_contra hj
    exact hNone ⟨j, hj⟩
  have hAtZero := congrFun (Matrix.mulVec_cramer C (Pi.single 0 (1 : ℤ))) 0
  -- Evaluating Cramer's rule at row `0` turns the zero-column contradiction into `det C = 0`.
  have hdet_zero : C.det = 0 := by
    simpa [hdZero] using hAtZero.symm
  exact hdet_ne_zero hdet_zero

/-- Helper for Theorem 4.6: in the even determinant branch, a coloring of the nonzero first
Cramer support yields a nonzero kernel vector. -/
private lemma supportColoringKernelWitness_of_evenDet
    {k : ℕ}
    (C : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)
    (hdet_ne_zero : C.det ≠ 0)
    (hdetEven : Even C.det)
    (hd :
      ∀ i : Fin (k + 1),
        Matrix.cramer C (Pi.single 0 (1 : ℤ)) i ∈ Set.range (SignType.cast : SignType → ℤ))
    (hColorFin :
      ∀ {ℓ : ℕ} (col : Fin ℓ ↪ Fin (k + 1)),
        ∃ red blue : Finset (Fin ℓ),
          is_equitable_bicoloring (C.submatrix id col) red blue) :
    ∃ x : Fin (k + 1) → ℤ, x ≠ 0 ∧ C *ᵥ x = 0 := by
  classical
  let d : Fin (k + 1) → ℤ := Matrix.cramer C (Pi.single 0 (1 : ℤ))
  let support : Finset (Fin (k + 1)) := Finset.univ.filter (fun j ↦ d j ≠ 0)
  let supportEmb : Fin support.card ↪ Fin (k + 1) := (support.orderEmbOfFin rfl).toEmbedding
  let S : Matrix (Fin (k + 1)) (Fin support.card) ℤ := C.submatrix id supportEmb
  have hRange : Set.range supportEmb = support := by
    -- The canonical embedding enumerates exactly the chosen support finset.
    simpa [supportEmb] using (support.range_orderEmbOfFin rfl)
  have hSupport : ∀ t : Fin (k + 1), t ∈ support ↔ d t ≠ 0 := by
    -- Membership in the support finset is exactly nonvanishing of the Cramer coordinate.
    intro t
    simp [support]
  obtain ⟨red, blue, hColor⟩ := hColorFin supportEmb
  have hColorData := (is_equitable_bicoloring_iff S red blue).1 hColor
  obtain ⟨x, hxZero, hxNonzero, hSystem⟩ :=
    supportColumnSignedIndicatorSystem C d support supportEmb hRange hSupport hColor
  have hTotalEven : ∀ i : Fin (k + 1), Even ((S *ᵥ fun _ ↦ (1 : ℤ)) i) := by
    intro i
    have hParity :
        Even (((S *ᵥ fun _ ↦ (1 : ℤ)) i) - (C *ᵥ d) i) := by
      -- The support sum and the Cramer-weighted sum differ by an even quantity.
      simpa [d, support, supportEmb, S] using
        supportRowSumsParity_ofFirstCramerSupport C hd i
    have hCramerEven : Even ((C *ᵥ d) i) := by
      -- Cramer's rule makes each right-hand side entry either `0` or `det C`.
      have hAt := congrFun (Matrix.mulVec_cramer C (Pi.single 0 (1 : ℤ))) i
      by_cases hi0 : i = 0
      · subst hi0
        simpa [d] using hdetEven
      · have hZero : (C *ᵥ d) i = 0 := by
          simpa [d, Pi.single_eq_of_ne hi0] using hAt
        rw [hZero]
        exact ⟨0, by simp⟩
    rcases hParity with ⟨a, ha⟩
    rcases hCramerEven with ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    omega
  have hBalanceZero :
      ∀ i : Fin (k + 1), column_bicoloring_difference S red blue i = 0 := by
    intro i
    -- Even total row sums force the equitable balance to be exactly zero.
    exact
      rowBalance_eq_zero_of_even_total S hColorData.1 hColorData.2.1
        (hTotalEven i) (hColorData.2.2 i)
  have hKernel : C *ᵥ x = 0 := by
    -- The ambient support extension inherits the zero row-balance system.
    calc
      C *ᵥ x = column_bicoloring_difference S red blue := hSystem
      _ = 0 := by
            ext i
            exact hBalanceZero i
  obtain ⟨j, hjd⟩ := exists_nonzero_firstCramer_of_det_ne_zero C hdet_ne_zero
  have hxj : x j ≠ 0 := by
    -- A nonzero Cramer support index carries a `±1` entry in the ambient signed indicator.
    rcases hxNonzero j hjd with hOne | hNegOne
    · simpa [hOne]
    · simpa [hNegOne]
  refine ⟨x, ?_, hKernel⟩
  -- The ambient kernel vector is nontrivial because it is nonzero on some support index.
  intro hxZeroVec
  apply hxj
  simpa [hxZeroVec]

/-- Helper for Theorem 4.6: in the odd determinant branch, a coloring of the nonzero first
Cramer support yields a sign-valued solution of `C *ᵥ x = e₀`. -/
private lemma supportColoringUnitSystem_of_oddDet
    {k : ℕ}
    (C : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)
    (hdetOdd : Odd C.det)
    (hd :
      ∀ i : Fin (k + 1),
        Matrix.cramer C (Pi.single 0 (1 : ℤ)) i ∈ Set.range (SignType.cast : SignType → ℤ))
    (hColorFin :
      ∀ {ℓ : ℕ} (col : Fin ℓ ↪ Fin (k + 1)),
        ∃ red blue : Finset (Fin ℓ),
          is_equitable_bicoloring (C.submatrix id col) red blue) :
    ∃ x : Fin (k + 1) → ℤ,
      (∀ i : Fin (k + 1), x i ∈ Set.range (SignType.cast : SignType → ℤ)) ∧
      C *ᵥ x = Pi.single 0 (1 : ℤ) := by
  classical
  let d : Fin (k + 1) → ℤ := Matrix.cramer C (Pi.single 0 (1 : ℤ))
  let support : Finset (Fin (k + 1)) := Finset.univ.filter (fun j ↦ d j ≠ 0)
  let supportEmb : Fin support.card ↪ Fin (k + 1) := (support.orderEmbOfFin rfl).toEmbedding
  let S : Matrix (Fin (k + 1)) (Fin support.card) ℤ := C.submatrix id supportEmb
  have hRange : Set.range supportEmb = support := by
    -- The canonical embedding enumerates exactly the nonzero first-Cramer support.
    simpa [supportEmb] using (support.range_orderEmbOfFin rfl)
  have hSupport : ∀ t : Fin (k + 1), t ∈ support ↔ d t ≠ 0 := by
    -- Support membership is the same as Cramer nonvanishing.
    intro t
    simp [support]
  obtain ⟨red, blue, hColor⟩ := hColorFin supportEmb
  have hColorData := (is_equitable_bicoloring_iff S red blue).1 hColor
  obtain ⟨x, hxZero, hxNonzero, hSystem⟩ :=
    supportColumnSignedIndicatorSystem C d support supportEmb hRange hSupport hColor
  have hTotalEven :
      ∀ i : Fin (k + 1), i ≠ 0 → Even ((S *ᵥ fun _ ↦ (1 : ℤ)) i) := by
    intro i hi0
    have hParity :
        Even (((S *ᵥ fun _ ↦ (1 : ℤ)) i) - (C *ᵥ d) i) := by
      -- Away from row `0`, the Cramer right-hand side is zero, so parity transfers directly.
      simpa [d, support, supportEmb, S] using
        supportRowSumsParity_ofFirstCramerSupport C hd i
    have hAt := congrFun (Matrix.mulVec_cramer C (Pi.single 0 (1 : ℤ))) i
    have hZero : (C *ᵥ d) i = 0 := by
      simpa [d, Pi.single_eq_of_ne hi0] using hAt
    rw [hZero] at hParity
    simpa using hParity
  have hTotalOddZero : Odd ((S *ᵥ fun _ ↦ (1 : ℤ)) 0) := by
    have hParity :
        Even (((S *ᵥ fun _ ↦ (1 : ℤ)) 0) - (C *ᵥ d) 0) := by
      -- At row `0`, the support parity differs from the Cramer value by an even integer.
      simpa [d, support, supportEmb, S] using
        supportRowSumsParity_ofFirstCramerSupport C hd 0
    have hAtZero := congrFun (Matrix.mulVec_cramer C (Pi.single 0 (1 : ℤ))) 0
    have hCramerOdd : Odd ((C *ᵥ d) 0) := by
      simpa [d] using hdetOdd
    rcases hParity with ⟨a, ha⟩
    rcases hCramerOdd with ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    have hCramerAtZero : (C *ᵥ d) 0 = C.det := by
      simpa [d] using hAtZero
    rw [hCramerAtZero] at hb
    omega
  have hBalanceOffZero :
      ∀ i : Fin (k + 1), i ≠ 0 → column_bicoloring_difference S red blue i = 0 := by
    intro i hi0
    -- Even off-axis totals force zero row balance there.
    exact
      rowBalance_eq_zero_of_even_total S hColorData.1 hColorData.2.1
        (hTotalEven i hi0) (hColorData.2.2 i)
  have hBalanceAtZero :
      column_bicoloring_difference S red blue 0 = 1 ∨
        column_bicoloring_difference S red blue 0 = -1 := by
    -- The distinguished row has odd total sum, so its equitable balance is exactly `±1`.
    exact
      rowBalance_eq_pos_or_neg_of_odd_total S hColorData.1 hColorData.2.1
        hTotalOddZero (hColorData.2.2 0)
  have hxSign :
      ∀ i : Fin (k + 1), x i ∈ Set.range (SignType.cast : SignType → ℤ) := by
    intro i
    -- The ambient extension is zero off support and `±1` on support.
    rw [SignType.range_eq (SignType.cast : SignType → ℤ)]
    by_cases hdi : d i = 0
    · left
      exact hxZero i hdi
    · rcases hxNonzero i hdi with hOne | hNegOne
      · right
        right
        exact hOne
      · right
        left
        exact hNegOne
  cases hBalanceAtZero with
  | inl hPos =>
      refine ⟨x, hxSign, ?_⟩
      -- In the positive branch, the ambient support system already equals `e₀`.
      calc
        C *ᵥ x = column_bicoloring_difference S red blue := hSystem
        _ = Pi.single 0 (1 : ℤ) := by
              ext i
              by_cases hi0 : i = 0
              · subst hi0
                exact hPos
              · rw [Pi.single_eq_of_ne hi0]
                exact hBalanceOffZero i hi0
  | inr hNeg =>
      let x' : Fin (k + 1) → ℤ := fun i ↦ -x i
      have hx'Sign :
          ∀ i : Fin (k + 1), x' i ∈ Set.range (SignType.cast : SignType → ℤ) := by
        intro i
        -- Negating a sign-valued coordinate keeps it in the sign range.
        simpa [x'] using negOnePow_mul_mem_signTypeRange 1 (hxSign i)
      have hNegSystem :
          -column_bicoloring_difference S red blue = Pi.single 0 (1 : ℤ) := by
        -- Negating the `-e₀` balance vector normalizes it to `e₀`.
        ext i
        by_cases hi0 : i = 0
        · subst hi0
          have hNeg' := hNeg
          rw [column_bicoloring_difference_apply] at hNeg'
          simp [Pi.single_eq_same, column_bicoloring_difference_apply]
          omega
        · rw [Pi.single_eq_of_ne hi0]
          have hZero := hBalanceOffZero i hi0
          rw [column_bicoloring_difference_apply] at hZero
          simp [column_bicoloring_difference_apply]
          omega
      refine ⟨x', hx'Sign, ?_⟩
      -- In the negative branch, flip the ambient signed indicator once to normalize to `e₀`.
      calc
        C *ᵥ x' = -(C *ᵥ x) := by
          simpa [x'] using (Matrix.mulVec_neg x C)
        _ = -column_bicoloring_difference S red blue := by rw [hSystem]
        _ = Pi.single 0 (1 : ℤ) := hNegSystem

/-- Helper for Theorem 4.6: the converse is reduced to proving the determinant statement for a
square matrix whose every column submatrix is equitably bicolorable. -/
private lemma squareDet_mem_signTypeRange_ofEveryColumnSubmatrixColorable
    {k : ℕ} (C : Matrix (Fin k) (Fin k) ℤ)
    (hColorFin :
      ∀ {ℓ : ℕ} (col : Fin ℓ ↪ Fin k),
        ∃ red blue : Finset (Fin ℓ),
          is_equitable_bicoloring (C.submatrix id col) red blue) :
    C.det ∈ Set.range (SignType.cast : SignType → ℤ) := by
  induction k with
  | zero =>
      -- The `0 × 0` determinant is `1`, which is one of the sign values.
      refine ⟨1, ?_⟩
      simp
  | succ k ih =>
      -- Route correction: keep the converse purely `Fin`-indexed and close the parity branches
      -- through the two support-side helpers instead of rebuilding the branch assembly inline.
      have hminor :
          ∀ i j : Fin (k + 1),
            (C.submatrix i.succAbove j.succAbove).det ∈
              Set.range (SignType.cast : SignType → ℤ) := by
        intro i j
        exact
          ih
            (C.submatrix i.succAbove j.succAbove)
            (deletedMinorColumnColorabilityOfSquareColorability C hColorFin i j)
      have hd :
          ∀ i : Fin (k + 1),
            Matrix.cramer C (Pi.single 0 (1 : ℤ)) i ∈
              Set.range (SignType.cast : SignType → ℤ) :=
        firstCramer_mem_signTypeRange_of_minorDetMemSign C hminor
      by_cases hdet_zero : C.det = 0
      · exact ⟨0, hdet_zero.symm⟩
      · by_cases hdetEven : Even C.det
        · obtain ⟨x, hx_ne_zero, hx_system⟩ :=
            supportColoringKernelWitness_of_evenDet C hdet_zero hdetEven hd hColorFin
          have hx_zero : x = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet_zero hx_system
          exact (hx_ne_zero hx_zero).elim
        · have hdetOdd : Odd C.det := Int.not_even_iff_odd.mp hdetEven
          obtain ⟨x, hxSign, hxSystem⟩ :=
            supportColoringUnitSystem_of_oddDet C hdetOdd hd hColorFin
          exact oddDet_mem_signTypeRange_ofSupportSystem C hdet_zero hd hxSign hxSystem

/-- Theorem 4.6. A matrix `A` is totally unimodular if and only if every column submatrix of `A`
admits an equitable bicoloring. -/
theorem totally_unimodular_iff_every_column_submatrix_admits_equitable_bicoloring
    (A : Matrix m n ℤ) :
    A.IsTotallyUnimodular ↔
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (col : ι ↪ n),
        ∃ red blue : Finset ι,
          is_equitable_bicoloring (A.submatrix id col) red blue := by
  constructor
  · intro hA ι _ _ col
    -- First solve every finite row restriction by total unimodularity, then lift the coloring to
    -- all rows by the compactness lemma just proved.
    let B : Matrix m ι ℤ := A.submatrix (fun i : m ↦ i) col
    refine
      existsEquitableBicoloringOfAllFiniteRowRestrictions
        (ι := ι) (B := B) ?_
    intro (κ : Type u) _ _ row
    simpa [B, Matrix.submatrix_apply] using
      finiteEquitableBicoloringOfIsTotallyUnimodular
        (A.submatrix row col) (hA.submatrix row col)
  · intro hColor
    -- Route correction: the forward compactness argument is already complete above; the converse
    -- now reduces directly to the square determinant statement.
    rw [Matrix.isTotallyUnimodular_iff]
    intro k row col
    by_cases hrow : Function.Injective row
    · by_cases hcol : Function.Injective col
      · let colEmb : Fin k ↪ n := ⟨col, hcol⟩
        have hColorFin :
            ∀ {ℓ : ℕ} (col : Fin ℓ ↪ n),
              ∃ red blue : Finset (Fin ℓ),
                is_equitable_bicoloring (A.submatrix id col) red blue :=
          ambientFinColumnColorability hColor
        -- Once the chosen square columns are packaged as an embedding, the converse closes through
        -- the square determinant lemma applied to the square submatrix.
        simpa [colEmb] using
          squareDet_mem_signTypeRange_ofEveryColumnSubmatrixColorable
            (C := A.submatrix row colEmb)
            (hColorFin := squareSubmatrixColumnColorabilityOfAmbientColumnColorability
              hColorFin row colEmb)
      · rw [Function.not_injective_iff] at hcol
        obtain ⟨i, j, hcolEq, hij⟩ := hcol
        -- Repeated columns force the determinant to vanish.
        refine ⟨0, ?_⟩
        symm
        apply Matrix.det_zero_of_column_eq hij
        simp [hcolEq]
    · rw [Function.not_injective_iff] at hrow
      obtain ⟨i, j, hrowEq, hij⟩ := hrow
      -- Repeated rows force the determinant to vanish after transposing to a repeated-column
      -- statement.
      refine ⟨0, ?_⟩
      rw [← Matrix.det_transpose, Matrix.transpose_submatrix]
      symm
      apply Matrix.det_zero_of_column_eq hij.symm
      simp [hrowEq]

end Theorem46
