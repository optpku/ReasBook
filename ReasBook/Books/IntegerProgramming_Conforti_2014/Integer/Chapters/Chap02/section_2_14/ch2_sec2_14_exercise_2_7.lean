import Mathlib

-- Semantic recall note: `lean_leansearch` was unavailable in this session, so this item uses
-- explicit local `Matrix`/`Finset` formulations verified against mathlib surface APIs.

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A `0,1` matrix has only `0` and `1` as entries. -/
def IsZeroOneMatrix (A : Matrix m n ℤ) : Prop :=
  ∀ i j, A i j = 0 ∨ A i j = 1

/-- The support of a row of a matrix, viewed as the set of columns where the entry is nonzero. -/
def rowSupport (A : Matrix m n ℤ) (i : m) : Finset n :=
  Finset.univ.filter fun j ↦ A i j ≠ 0

/-- The finite set of distinct row supports of a matrix. -/
def rowSupports (A : Matrix m n ℤ) : Finset (Finset n) :=
  Finset.univ.image (rowSupport A)

/-- The inclusion-maximal row supports of a matrix. -/
def maximalRowSupports (A : Matrix m n ℤ) : Finset (Finset n) :=
  (rowSupports A).filter fun s ↦
    ∀ t ∈ rowSupports A, s ⊆ t → t ⊆ s

/-- The inclusion-minimal row supports of a matrix. -/
def minimalRowSupports (A : Matrix m n ℤ) : Finset (Finset n) :=
  (rowSupports A).filter fun s ↦
    ∀ t ∈ rowSupports A, t ⊆ s → s ⊆ t

/-- The canonical `0,1` row with prescribed support. -/
def rowOfSupport (s : Finset n) : n → ℤ :=
  fun j ↦ if j ∈ s then 1 else 0

/-- The matrix whose rows are the canonical `0,1` rows with the prescribed supports. -/
def matrixOfRowSupports (S : Finset (Finset n)) : Matrix S n ℤ :=
  fun s j ↦ rowOfSupport s.1 j

/-- Multiplying a support-row matrix by a vector evaluates the corresponding subset sum. -/
theorem matrixOfRowSupports_mulVec_apply
    {R : Type*} [Ring R]
    (S : Finset (Finset n)) (x : n → R) (s : S) :
    ((((matrixOfRowSupports S : Matrix S n ℤ).map (Int.castRingHom R)) *ᵥ x) s) =
      (s : Finset n).sum x := by
  simp [Matrix.mulVec, dotProduct, matrixOfRowSupports, rowOfSupport]

/-- The row-deduplicated matrix whose rows are exactly the inclusion-maximal row supports of `A`. -/
def Amax (A : Matrix m n ℤ) : Matrix (maximalRowSupports A) n ℤ :=
  matrixOfRowSupports (maximalRowSupports A)

/-- The row-deduplicated matrix whose rows are exactly the inclusion-minimal row supports of `A`. -/
def Amin (A : Matrix m n ℤ) : Matrix (minimalRowSupports A) n ℤ :=
  matrixOfRowSupports (minimalRowSupports A)

/-- A binary vector has only `0` and `1` as entries. -/
def IsZeroOneVector (x : n → ℤ) : Prop :=
  ∀ j, x j = 0 ∨ x j = 1

/-- The `i`-th row sum of `A` against an integer vector `x`. -/
def integerRowSum (A : Matrix m n ℤ) (i : m) (x : n → ℤ) : ℤ :=
  ∑ j, A i j * x j

/-- The `i`-th row sum of `A` against a real vector `x`. -/
def realRowSum (A : Matrix m n ℤ) (i : m) (x : n → ℝ) : ℝ :=
  ∑ j, (A i j : ℝ) * x j

/-- The packing set associated to a `0,1` matrix. -/
def packingSet (A : Matrix m n ℤ) : Set (n → ℤ) :=
  {x | IsZeroOneVector x ∧ ∀ i, integerRowSum A i x ≤ 1}

/-- The covering set associated to a `0,1` matrix. -/
def coveringSet (A : Matrix m n ℤ) : Set (n → ℤ) :=
  {x | IsZeroOneVector x ∧ ∀ i, 1 ≤ integerRowSum A i x}

/-- The standard linear relaxation of the packing set associated to a `0,1` matrix. -/
def packingLinearRelaxation (A : Matrix m n ℤ) : Set (n → ℝ) :=
  {x | (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧ ∀ i, realRowSum A i x ≤ 1}

/-- The standard linear relaxation of the covering set associated to a `0,1` matrix. -/
def coveringLinearRelaxation (A : Matrix m n ℤ) : Set (n → ℝ) :=
  {x | (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧ ∀ i, 1 ≤ realRowSum A i x}

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_7.lean`: a zero-one row
acts on a vector by summing precisely over its support. -/
lemma map_mulVec_apply_eq_sum_rowSupport
    {R : Type*} [Ring R] (A : Matrix m n ℤ) (hA : IsZeroOneMatrix A)
    (x : n → R) (i : m) :
    (((A.map (Int.castRingHom R)) *ᵥ x) i) = (rowSupport A i).sum x := by
  -- Split each matrix coefficient into its two allowed values.
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, rowSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  rcases hA i j with hij | hij
  · simp [hij]
  · simp [hij]

omit [DecidableEq m] in
/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_7.lean`: every row support
is contained in an inclusion-maximal row support. -/
lemma exists_maximalRowSupport_superset (A : Matrix m n ℤ) (i : m) :
    ∃ s : maximalRowSupports A, rowSupport A i ⊆ (s : Finset n) := by
  -- Extend the chosen support inside the finite poset of all row supports.
  have hi : rowSupport A i ∈ rowSupports A := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  obtain ⟨s, his, hs⟩ := (rowSupports A).exists_le_maximal hi
  refine ⟨⟨s, ?_⟩, his⟩
  exact Finset.mem_filter.mpr ⟨hs.1, hs.2⟩

omit [DecidableEq m] in
/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_7.lean`: every row support
contains an inclusion-minimal row support. -/
lemma exists_minimalRowSupport_subset (A : Matrix m n ℤ) (i : m) :
    ∃ s : minimalRowSupports A, (s : Finset n) ⊆ rowSupport A i := by
  -- Shrink the chosen support inside the finite poset of all row supports.
  have hi : rowSupport A i ∈ rowSupports A := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  obtain ⟨s, hsi, hs⟩ := (rowSupports A).exists_le_minimal hi
  refine ⟨⟨s, ?_⟩, hsi⟩
  exact Finset.mem_filter.mpr ⟨hs.1, hs.2⟩

omit [DecidableEq m] in
/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_7.lean`: membership among
the distinct row supports is witnessed by an original row. -/
lemma exists_rowSupport_eq_of_mem_rowSupports (A : Matrix m n ℤ) {s : Finset n}
    (hs : s ∈ rowSupports A) : ∃ i, rowSupport A i = s := by
  -- Unpack membership in the image defining the set of row supports.
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hs
  exact ⟨i, hi⟩

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_7.lean`: an integer row
sum of a zero-one matrix is the sum over that row's support. -/
lemma integerRowSum_eq_sum_rowSupport (A : Matrix m n ℤ) (hA : IsZeroOneMatrix A)
    (i : m) (x : n → ℤ) : integerRowSum A i x = (rowSupport A i).sum x := by
  -- Identify the integer row sum with the mapped matrix-vector product.
  simpa [integerRowSum, Matrix.mulVec, dotProduct] using
    (map_mulVec_apply_eq_sum_rowSupport A hA x i)

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_7.lean`: a real row
sum of a zero-one matrix is the sum over that row's support. -/
lemma realRowSum_eq_sum_rowSupport (A : Matrix m n ℤ) (hA : IsZeroOneMatrix A)
    (i : m) (x : n → ℝ) : realRowSum A i x = (rowSupport A i).sum x := by
  -- Identify the real row sum with the mapped matrix-vector product.
  simpa [realRowSum, Matrix.mulVec, dotProduct] using
    (map_mulVec_apply_eq_sum_rowSupport A hA x i)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_7.lean`: an integer row
sum in a canonical support matrix is its indexed subset sum. -/
lemma integerRowSum_matrixOfRowSupports (S : Finset (Finset n)) (s : S) (x : n → ℤ) :
    integerRowSum (matrixOfRowSupports S) s x = (s : Finset n).sum x := by
  -- Specialize the canonical matrix-vector computation to integer coefficients.
  simpa [integerRowSum, Matrix.mulVec, dotProduct] using
    (matrixOfRowSupports_mulVec_apply S x s)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_7.lean`: a real row
sum in a canonical support matrix is its indexed subset sum. -/
lemma realRowSum_matrixOfRowSupports (S : Finset (Finset n)) (s : S) (x : n → ℝ) :
    realRowSum (matrixOfRowSupports S) s x = (s : Finset n).sum x := by
  -- Specialize the canonical matrix-vector computation to real coefficients.
  simpa [realRowSum, Matrix.mulVec, dotProduct] using
    (matrixOfRowSupports_mulVec_apply S x s)

omit [DecidableEq m] in
/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_7.lean:
Exercise 2.7 (1), removing non-maximal row supports does not change the packing set. -/
theorem packingSet_eq_Amax_packingSet (A : Matrix m n ℤ) (hA : IsZeroOneMatrix A) :
    packingSet A = packingSet (Amax A) := by
  -- Compare the two feasible sets pointwise, using support sums as their common normal form.
  ext x
  constructor
  · rintro ⟨hx, hrows⟩
    refine ⟨hx, ?_⟩
    intro s
    have hs : (s : Finset n) ∈ rowSupports A := (Finset.mem_filter.mp s.property).1
    obtain ⟨i, hi⟩ := exists_rowSupport_eq_of_mem_rowSupports A hs
    calc
      integerRowSum (Amax A) s x = (s : Finset n).sum x := by
        simpa only [Amax] using integerRowSum_matrixOfRowSupports (maximalRowSupports A) s x
      _ = (rowSupport A i).sum x := congrArg (fun t : Finset n ↦ t.sum x) hi.symm
      _ = integerRowSum A i x := (integerRowSum_eq_sum_rowSupport A hA i x).symm
      _ ≤ 1 := hrows i
  · rintro ⟨hx, hrows⟩
    refine ⟨hx, ?_⟩
    intro i
    obtain ⟨s, his⟩ := exists_maximalRowSupport_superset A i
    have hxnonneg (j : n) : 0 ≤ x j := by
      rcases hx j with hj | hj
      · simp [hj]
      · simp [hj]
    calc
      integerRowSum A i x = (rowSupport A i).sum x :=
        integerRowSum_eq_sum_rowSupport A hA i x
      _ ≤ (s : Finset n).sum x :=
        Finset.sum_le_sum_of_subset_of_nonneg his (fun j _ _ ↦ hxnonneg j)
      _ = integerRowSum (Amax A) s x := by
        simpa only [Amax] using
          (integerRowSum_matrixOfRowSupports (maximalRowSupports A) s x).symm
      _ ≤ 1 := hrows s

omit [DecidableEq m] in
/-- Exercise 2.7 (2): removing non-maximal row supports does not change the linear relaxation of the
packing set. -/
theorem packingLinearRelaxation_eq_Amax (A : Matrix m n ℤ) (hA : IsZeroOneMatrix A) :
    packingLinearRelaxation A = packingLinearRelaxation (Amax A) := by
  -- Retained maximal rows are original rows, and omitted rows lie below a retained support.
  ext x
  constructor
  · rintro ⟨hx, hrows⟩
    refine ⟨hx, ?_⟩
    intro s
    have hs : (s : Finset n) ∈ rowSupports A := (Finset.mem_filter.mp s.property).1
    obtain ⟨i, hi⟩ := exists_rowSupport_eq_of_mem_rowSupports A hs
    calc
      realRowSum (Amax A) s x = (s : Finset n).sum x := by
        simpa only [Amax] using realRowSum_matrixOfRowSupports (maximalRowSupports A) s x
      _ = (rowSupport A i).sum x := congrArg (fun t : Finset n ↦ t.sum x) hi.symm
      _ = realRowSum A i x := (realRowSum_eq_sum_rowSupport A hA i x).symm
      _ ≤ 1 := hrows i
  · rintro ⟨hx, hrows⟩
    refine ⟨hx, ?_⟩
    intro i
    obtain ⟨s, his⟩ := exists_maximalRowSupport_superset A i
    calc
      realRowSum A i x = (rowSupport A i).sum x :=
        realRowSum_eq_sum_rowSupport A hA i x
      _ ≤ (s : Finset n).sum x :=
        Finset.sum_le_sum_of_subset_of_nonneg his (fun j _ _ ↦ (hx j).1)
      _ = realRowSum (Amax A) s x := by
        simpa only [Amax] using
          (realRowSum_matrixOfRowSupports (maximalRowSupports A) s x).symm
      _ ≤ 1 := hrows s

omit [DecidableEq m] in
/-- Exercise 2.7 (3): removing non-minimal row supports does not change the covering set. -/
theorem coveringSet_eq_Amin_coveringSet (A : Matrix m n ℤ) (hA : IsZeroOneMatrix A) :
    coveringSet A = coveringSet (Amin A) := by
  -- Compare covering constraints through the inclusion-minimal row supports.
  ext x
  constructor
  · rintro ⟨hx, hrows⟩
    refine ⟨hx, ?_⟩
    intro s
    have hs : (s : Finset n) ∈ rowSupports A := (Finset.mem_filter.mp s.property).1
    obtain ⟨i, hi⟩ := exists_rowSupport_eq_of_mem_rowSupports A hs
    calc
      1 ≤ integerRowSum A i x := hrows i
      _ = (rowSupport A i).sum x := integerRowSum_eq_sum_rowSupport A hA i x
      _ = (s : Finset n).sum x := congrArg (fun t : Finset n ↦ t.sum x) hi
      _ = integerRowSum (Amin A) s x := by
        simpa only [Amin] using
          (integerRowSum_matrixOfRowSupports (minimalRowSupports A) s x).symm
  · rintro ⟨hx, hrows⟩
    refine ⟨hx, ?_⟩
    intro i
    obtain ⟨s, hsi⟩ := exists_minimalRowSupport_subset A i
    have hxnonneg (j : n) : 0 ≤ x j := by
      rcases hx j with hj | hj
      · simp [hj]
      · simp [hj]
    calc
      1 ≤ integerRowSum (Amin A) s x := hrows s
      _ = (s : Finset n).sum x := by
        simpa only [Amin] using integerRowSum_matrixOfRowSupports (minimalRowSupports A) s x
      _ ≤ (rowSupport A i).sum x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsi (fun j _ _ ↦ hxnonneg j)
      _ = integerRowSum A i x := (integerRowSum_eq_sum_rowSupport A hA i x).symm

omit [DecidableEq m] in
/-- Exercise 2.7 (4): removing non-minimal row supports does not change the linear relaxation of the
covering set. -/
theorem coveringLinearRelaxation_eq_Amin (A : Matrix m n ℤ) (hA : IsZeroOneMatrix A) :
    coveringLinearRelaxation A = coveringLinearRelaxation (Amin A) := by
  -- Minimal supports give the weakest covering rows, while all coordinates remain nonnegative.
  ext x
  constructor
  · rintro ⟨hx, hrows⟩
    refine ⟨hx, ?_⟩
    intro s
    have hs : (s : Finset n) ∈ rowSupports A := (Finset.mem_filter.mp s.property).1
    obtain ⟨i, hi⟩ := exists_rowSupport_eq_of_mem_rowSupports A hs
    calc
      1 ≤ realRowSum A i x := hrows i
      _ = (rowSupport A i).sum x := realRowSum_eq_sum_rowSupport A hA i x
      _ = (s : Finset n).sum x := congrArg (fun t : Finset n ↦ t.sum x) hi
      _ = realRowSum (Amin A) s x := by
        simpa only [Amin] using
          (realRowSum_matrixOfRowSupports (minimalRowSupports A) s x).symm
  · rintro ⟨hx, hrows⟩
    refine ⟨hx, ?_⟩
    intro i
    obtain ⟨s, hsi⟩ := exists_minimalRowSupport_subset A i
    calc
      1 ≤ realRowSum (Amin A) s x := hrows s
      _ = (s : Finset n).sum x := by
        simpa only [Amin] using realRowSum_matrixOfRowSupports (minimalRowSupports A) s x
      _ ≤ (rowSupport A i).sum x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsi (fun j _ _ ↦ (hx j).1)
      _ = realRowSum A i x := (realRowSum_eq_sum_rowSupport A hA i x).symm

#print axioms packingSet_eq_Amax_packingSet
#print axioms packingLinearRelaxation_eq_Amax
#print axioms coveringSet_eq_Amin_coveringSet
#print axioms coveringLinearRelaxation_eq_Amin
