import Mathlib

open scoped BigOperators

universe u v w

attribute [local instance] Classical.propDecidable

/-- The support of a matrix, viewed as the set of index pairs where the entry is nonzero. -/
def matrix_support {m : Type u} {n : Type v} {α : Type w} [Zero α] (A : Matrix m n α) :
    Set (m × n) :=
  {p | A p.1 p.2 ≠ 0}

/-- Membership in `matrix_support A` means that the corresponding matrix entry is nonzero. -/
@[simp] theorem mem_matrix_support_iff
    {m : Type u} {n : Type v} {α : Type w} [Zero α] {A : Matrix m n α} {i : m} {j : n} :
    (i, j) ∈ matrix_support A ↔ A i j ≠ 0 :=
  Iff.rfl

/-- The `0,1` indicator matrix of a Cartesian product of row and column sets. -/
noncomputable def rectangle_indicator {m : Type u} {n : Type v} {α : Type w} [Zero α] [One α]
    (rowSet : Set m) (colSet : Set n) : Matrix m n α :=
  fun i j ↦ if i ∈ rowSet ∧ j ∈ colSet then 1 else 0

@[simp] theorem mem_matrix_support_rectangle_indicator_iff
    {m : Type u} {n : Type v} {α : Type w} [Zero α] [One α] [NeZero (1 : α)]
    {rowSet : Set m} {colSet : Set n} {i : m} {j : n} :
    (i, j) ∈ matrix_support (rectangle_indicator rowSet colSet : Matrix m n α) ↔
      i ∈ rowSet ∧ j ∈ colSet := by
  classical
  rw [mem_matrix_support_iff, rectangle_indicator]
  by_cases h : i ∈ rowSet ∧ j ∈ colSet
  · simp [h, one_ne_zero]
  · simp [h]

@[simp] theorem matrix_support_rectangle_indicator
    {m : Type u} {n : Type v} {α : Type w} [Zero α] [One α] [NeZero (1 : α)]
    (rowSet : Set m) (colSet : Set n) :
    matrix_support (rectangle_indicator rowSet colSet : Matrix m n α) = rowSet.prod colSet := by
  ext p
  rcases p with ⟨i, j⟩
  exact mem_matrix_support_rectangle_indicator_iff

/-- Definition 4.10.1-extra-1 (1). A rectangle matrix is a `0,1` matrix whose support is a product
of nonempty row and column index sets. -/
class is_rectangle_matrix {m : Type u} {n : Type v} {α : Type w} [Zero α] [One α]
    (R : Matrix m n α) : Prop where
  /-- Every entry of a rectangle matrix is either `0` or `1`. -/
  zero_one (i : m) (j : n) : R i j = 0 ∨ R i j = 1
  /-- The support of a rectangle matrix is a Cartesian product of nonempty row and column sets. -/
  support_eq :
    ∃ I : Set m, ∃ J : Set n,
      I.Nonempty ∧ J.Nonempty ∧ matrix_support R = I.prod J

/-- `is_rectangle_matrix` unfolds to `0,1` entries together with product support on nonempty row
and column sets. -/
theorem is_rectangle_matrix_iff
    {m : Type u} {n : Type v} {α : Type w} [Zero α] [One α] {R : Matrix m n α} :
    is_rectangle_matrix R ↔
      (∀ i j, R i j = 0 ∨ R i j = 1) ∧
        ∃ I : Set m, ∃ J : Set n,
          I.Nonempty ∧ J.Nonempty ∧ matrix_support R = I.prod J := by
  constructor
  · intro h
    exact ⟨h.zero_one, h.support_eq⟩
  · rintro ⟨hzero_one, hsupport⟩
    exact ⟨hzero_one, hsupport⟩

/-- A nontrivial rectangle indicator matrix is a rectangle matrix. -/
theorem rectangle_indicator_is_rectangle_matrix
    {m : Type u} {n : Type v} {α : Type w} [Zero α] [One α] [NeZero (1 : α)]
    {rowSet : Set m} {colSet : Set n} (hrowSet : rowSet.Nonempty) (hcolSet : colSet.Nonempty) :
    is_rectangle_matrix (rectangle_indicator rowSet colSet : Matrix m n α) := by
  refine (is_rectangle_matrix_iff).mpr ?_
  refine ⟨?_, rowSet, colSet, hrowSet, hcolSet, matrix_support_rectangle_indicator rowSet colSet⟩
  intro i j
  classical
  by_cases h : i ∈ rowSet ∧ j ∈ colSet <;> simp [rectangle_indicator, h]

/-- Rectangle matrices are exactly the `0,1` matrices of rank `1`. -/
theorem is_rectangle_matrix_iff_zero_one_and_rank_eq_one
    {m : Type u} {n : Type v} {K : Type w} [Field K] [Finite m] [Fintype n]
    {R : Matrix m n K} :
    is_rectangle_matrix R ↔ (∀ i j, R i j = 0 ∨ R i j = 1) ∧ Matrix.rank R = 1 := by
  constructor
  · intro hR
    classical
    rcases (is_rectangle_matrix_iff.mp hR) with ⟨hzero_one, I, J, hI, hJ, hsupport⟩
    refine ⟨hzero_one, ?_⟩
    obtain ⟨i₀, hi₀⟩ := hI
    obtain ⟨j₀, hj₀⟩ := hJ
    have hmem₀ : (i₀, j₀) ∈ matrix_support R := by
      rw [hsupport]
      exact ⟨hi₀, hj₀⟩
    have hentry₀_ne : R i₀ j₀ ≠ 0 := mem_matrix_support_iff.mp hmem₀
    have hentry₀_one : R i₀ j₀ = 1 := by
      rcases hzero_one i₀ j₀ with hzero | hone
      · exact False.elim (hentry₀_ne hzero)
      · exact hone
    have hvec :
        R =
          Matrix.vecMulVec
            (fun i ↦ if i ∈ I then (1 : K) else 0)
            (fun j ↦ if j ∈ J then (1 : K) else 0) := by
      ext i j
      by_cases hi : i ∈ I <;> by_cases hj : j ∈ J
      · have hmem : (i, j) ∈ matrix_support R := by
          rw [hsupport]
          exact ⟨hi, hj⟩
        have hentry_ne : R i j ≠ 0 := mem_matrix_support_iff.mp hmem
        rcases hzero_one i j with hzero | hone
        · exact False.elim (hentry_ne hzero)
        · simpa [Matrix.vecMulVec_apply, hi, hj, hone]
      · have hzero : R i j = 0 := by
          by_contra hentry_ne
          have hmem : (i, j) ∈ matrix_support R := mem_matrix_support_iff.mpr hentry_ne
          have hprod : i ∈ I ∧ j ∈ J := by simpa [hsupport] using hmem
          exact hj hprod.2
        simpa [Matrix.vecMulVec_apply, hj, hzero]
      · have hzero : R i j = 0 := by
          by_contra hentry_ne
          have hmem : (i, j) ∈ matrix_support R := mem_matrix_support_iff.mpr hentry_ne
          have hprod : i ∈ I ∧ j ∈ J := by simpa [hsupport] using hmem
          exact hi hprod.1
        simpa [Matrix.vecMulVec_apply, hi, hj, hzero]
      · have hzero : R i j = 0 := by
          by_contra hentry_ne
          have hmem : (i, j) ∈ matrix_support R := mem_matrix_support_iff.mpr hentry_ne
          have hprod : i ∈ I ∧ j ∈ J := by simpa [hsupport] using hmem
          exact hi hprod.1
        simpa [Matrix.vecMulVec_apply, hi, hj, hzero]
    have hrank_le : Matrix.rank R ≤ 1 := by
      rw [hvec]
      exact Matrix.rank_vecMulVec_le _ _
    have hrank_ne_zero : Matrix.rank R ≠ 0 := by
      intro hrank_zero
      have hspan_zero : Module.finrank K (Submodule.span K (Set.range R.row)) = 0 := by
        simpa [R.rank_eq_finrank_span_row] using hrank_zero
      have hspan_bot : Submodule.span K (Set.range R.row) = ⊥ :=
        Submodule.finrank_eq_zero.mp hspan_zero
      have hrow_mem : R.row i₀ ∈ Submodule.span K (Set.range R.row) :=
        Submodule.subset_span ⟨i₀, rfl⟩
      have hrow_zero : R.row i₀ = 0 := by
        simpa [hspan_bot] using hrow_mem
      have : R i₀ j₀ = 0 := by
        simpa [Matrix.row] using congrArg (fun f : n → K ↦ f j₀) hrow_zero
      exact hentry₀_ne this
    omega
  · rintro ⟨hzero_one, hrank⟩
    classical
    let _ := Fintype.ofFinite m
    let W : Submodule K (n → K) := Submodule.span K (Set.range R.row)
    have hW_finrank : Module.finrank K W = 1 := by
      simpa [W, R.rank_eq_finrank_span_row] using hrank
    have hmatrix_ne_zero : R ≠ 0 := by
      intro hzero
      have hrank_zero : Matrix.rank (0 : Matrix m n K) = 0 := Matrix.rank_zero
      have : Matrix.rank R = 0 := by simpa [hzero] using hrank_zero
      exact zero_ne_one (this.symm.trans hrank)
    have hrow_exists : ∃ i, R.row i ≠ 0 := by
      by_contra hrows
      push_neg at hrows
      apply hmatrix_ne_zero
      ext i j
      simpa [Matrix.row] using congrArg (fun f : n → K ↦ f j) (hrows i)
    obtain ⟨i₀, hi₀⟩ := hrow_exists
    have hentry_exists : ∃ j, R i₀ j ≠ 0 := by
      by_contra hcols
      push_neg at hcols
      apply hi₀
      ext j
      exact hcols j
    obtain ⟨j₀, hj₀⟩ := hentry_exists
    have hentry₀_one : R i₀ j₀ = 1 := by
      rcases hzero_one i₀ j₀ with hzero | hone
      · exact False.elim (hj₀ hzero)
      · exact hone
    have hi₀_mem : R.row i₀ ∈ W := Submodule.subset_span ⟨i₀, rfl⟩
    let v₀ : W := ⟨R.row i₀, hi₀_mem⟩
    have hv₀_ne : v₀ ≠ 0 := by
      intro hv₀
      apply hi₀
      simpa [v₀] using congrArg Subtype.val hv₀
    have hrow_multiple : ∀ w : W, ∃ c : K, c • v₀ = w := by
      exact (finrank_eq_one_iff_of_nonzero' v₀ hv₀_ne).mp hW_finrank
    let I : Set m := {i | R.row i ≠ 0}
    let J : Set n := {j | R i₀ j = 1}
    have hI_nonempty : I.Nonempty := by
      exact ⟨i₀, by simpa [I] using hi₀⟩
    have hJ_nonempty : J.Nonempty := by
      exact ⟨j₀, by simpa [J] using hentry₀_one⟩
    refine (is_rectangle_matrix_iff).mpr ?_
    refine ⟨hzero_one, I, J, hI_nonempty, hJ_nonempty, ?_⟩
    ext p
    rcases p with ⟨i, j⟩
    constructor
    · intro hmem
      have hij_ne : R i j ≠ 0 := mem_matrix_support_iff.mp hmem
      have hrowi_mem : R.row i ∈ W := Submodule.subset_span ⟨i, rfl⟩
      obtain ⟨c, hc⟩ := hrow_multiple ⟨R.row i, hrowi_mem⟩
      have hcrow : c • R.row i₀ = R.row i := congrArg Subtype.val hc
      have hc_eq : c = R i j₀ := by
        simpa [Matrix.row, hentry₀_one] using congrArg (fun f : n → K ↦ f j₀) hcrow
      have hc_zero_or_one : c = 0 ∨ c = 1 := by
        simpa [hc_eq] using hzero_one i j₀
      have hc_ne_zero : c ≠ 0 := by
        intro hc_zero
        have hrow_zero : R.row i = 0 := by
          calc
            R.row i = c • R.row i₀ := by simpa using hcrow.symm
            _ = 0 := by simp [hc_zero]
        exact hij_ne (by simpa [Matrix.row] using congrArg (fun f : n → K ↦ f j) hrow_zero)
      have hc_one : c = 1 := by
        rcases hc_zero_or_one with hc_zero | hc_one
        · exact False.elim (hc_ne_zero hc_zero)
        · exact hc_one
      have hrow_eq : R.row i = R.row i₀ := by
        calc
          R.row i = c • R.row i₀ := by simpa using hcrow.symm
          _ = R.row i₀ := by simpa [hc_one]
      have hrowi_ne : R.row i ≠ 0 := by
        intro hrow_zero
        exact hij_ne (by simpa [Matrix.row] using congrArg (fun f : n → K ↦ f j) hrow_zero)
      have hi_mem : i ∈ I := by
        simpa [I] using hrowi_ne
      have hrow_eq_at_j : R i j = R i₀ j := by
        simpa [Matrix.row] using congrArg (fun f : n → K ↦ f j) hrow_eq
      have hi₀j_ne : R i₀ j ≠ 0 := by
        intro hi₀j_zero
        exact hij_ne (hrow_eq_at_j.trans hi₀j_zero)
      have hi₀j_one : R i₀ j = 1 := by
        rcases hzero_one i₀ j with hzero | hone
        · exact False.elim (hi₀j_ne hzero)
        · exact hone
      have hj_mem : j ∈ J := by
        simpa [J] using hi₀j_one
      exact ⟨hi_mem, hj_mem⟩
    · rintro ⟨hi_mem, hj_mem⟩
      have hrowi_ne : R.row i ≠ 0 := by
        simpa [I] using hi_mem
      have hrowi_mem : R.row i ∈ W := Submodule.subset_span ⟨i, rfl⟩
      obtain ⟨c, hc⟩ := hrow_multiple ⟨R.row i, hrowi_mem⟩
      have hcrow : c • R.row i₀ = R.row i := congrArg Subtype.val hc
      have hc_eq : c = R i j₀ := by
        simpa [Matrix.row, hentry₀_one] using congrArg (fun f : n → K ↦ f j₀) hcrow
      have hc_zero_or_one : c = 0 ∨ c = 1 := by
        simpa [hc_eq] using hzero_one i j₀
      have hc_one : c = 1 := by
        rcases hc_zero_or_one with hc_zero | hc_one
        · exfalso
          apply hrowi_ne
          calc
            R.row i = c • R.row i₀ := by simpa using hcrow.symm
            _ = 0 := by simp [hc_zero]
        · exact hc_one
      have hrow_eq : R.row i = R.row i₀ := by
        calc
          R.row i = c • R.row i₀ := by simpa using hcrow.symm
          _ = R.row i₀ := by simpa [hc_one]
      have hi₀j_one : R i₀ j = 1 := by
        simpa [J] using hj_mem
      have hij_one : R i j = 1 := by
        simpa [Matrix.row, hi₀j_one] using congrArg (fun f : n → K ↦ f j) hrow_eq
      exact mem_matrix_support_iff.mpr (by simpa [hij_one])

/-- Definition 4.10.1-extra-1 (2). A rectangle cover of `S` is a finite family of rectangle
matrices whose supports cover the support of `S`. -/
class is_rectangle_cover {m : Type u} {n : Type v} {α : Type w} [Zero α] [One α]
    (S : Matrix m n α) (R : Fin k → Matrix m n α) : Prop where
  /-- Every member of a rectangle cover is a rectangle matrix. -/
  rectangles (t : Fin k) : is_rectangle_matrix (R t)
  /-- The support of the covered matrix is the union of the rectangle supports. -/
  support_eq : matrix_support S = ⋃ t, matrix_support (R t)

/-- `is_rectangle_cover` unfolds to a family of rectangle matrices whose supports cover exactly the
support of `S`. -/
theorem is_rectangle_cover_iff
    {m : Type u} {n : Type v} {α : Type w} [Zero α] [One α]
    {S : Matrix m n α} {R : Fin k → Matrix m n α} :
    is_rectangle_cover S R ↔
      (∀ t, is_rectangle_matrix (R t)) ∧
        matrix_support S = ⋃ t, matrix_support (R t) := by
  constructor
  · intro h
    exact ⟨h.rectangles, h.support_eq⟩
  · rintro ⟨hrectangles, hsupport⟩
    exact ⟨hrectangles, hsupport⟩

@[simp] theorem matrix_support_reindex
    {m : Type u} {n : Type v} {l : Type*} {o : Type*} {α : Type w} [Zero α]
    (eₘ : m ≃ l) (eₙ : n ≃ o) (R : Matrix m n α) :
    matrix_support (Matrix.reindex eₘ eₙ R) = Prod.map eₘ eₙ '' matrix_support R := by
  ext p
  rcases p with ⟨i, j⟩
  constructor
  · intro hp
    refine ⟨(eₘ.symm i, eₙ.symm j), ?_, ?_⟩
    · simpa [Matrix.reindex_apply] using hp
    · simp
  · rintro ⟨⟨i', j'⟩, hp, hpij⟩
    have hpij' : (eₘ i', eₙ j') = (i, j) := by
      simpa using hpij
    cases hpij'
    simpa [Matrix.reindex_apply] using hp

theorem is_rectangle_matrix.reindex
    {m : Type u} {n : Type v} {l : Type*} {o : Type*} {α : Type w} [Zero α] [One α]
    {R : Matrix m n α} (hR : is_rectangle_matrix R) (eₘ : m ≃ l) (eₙ : n ≃ o) :
    is_rectangle_matrix (Matrix.reindex eₘ eₙ R) := by
  classical
  rcases hR.support_eq with ⟨I, J, hI, hJ, hsupport⟩
  refine (is_rectangle_matrix_iff).mpr ?_
  refine ⟨?_, eₘ '' I, eₙ '' J, ?_, ?_, ?_⟩
  · intro i j
    simpa [Matrix.reindex_apply] using hR.zero_one (eₘ.symm i) (eₙ.symm j)
  · rcases hI with ⟨i, hi⟩
    exact ⟨eₘ i, ⟨i, hi, rfl⟩⟩
  · rcases hJ with ⟨j, hj⟩
    exact ⟨eₙ j, ⟨j, hj, rfl⟩⟩
  · ext p
    rcases p with ⟨i, j⟩
    constructor
    · intro hp
      have hp' : (eₘ.symm i, eₙ.symm j) ∈ matrix_support R := by
        simpa [Matrix.reindex_apply] using hp
      have hmem : eₘ.symm i ∈ (I : Set m) ∧ eₙ.symm j ∈ (J : Set n) := by
        simpa [hsupport] using hp'
      exact ⟨⟨eₘ.symm i, hmem.1, by simp⟩, ⟨eₙ.symm j, hmem.2, by simp⟩⟩
    · rintro ⟨⟨i', hi', rfl⟩, ⟨j', hj', rfl⟩⟩
      have hp' : (i', j') ∈ matrix_support R := by
        simpa [hsupport] using And.intro hi' hj'
      simpa [Matrix.reindex_apply] using hp'

theorem is_rectangle_cover.reindex
    {m : Type u} {n : Type v} {l : Type*} {o : Type*} {α : Type w} [Zero α] [One α]
    {S : Matrix m n α} {R : Fin k → Matrix m n α} (hR : is_rectangle_cover S R)
    (eₘ : m ≃ l) (eₙ : n ≃ o) :
    is_rectangle_cover (Matrix.reindex eₘ eₙ S) (fun t ↦ Matrix.reindex eₘ eₙ (R t)) := by
  refine (is_rectangle_cover_iff).mpr ?_
  refine ⟨fun t ↦ (hR.rectangles t).reindex eₘ eₙ, ?_⟩
  ext p
  rcases p with ⟨i, j⟩
  constructor
  · intro hp
    have hp' : (eₘ.symm i, eₙ.symm j) ∈ matrix_support S := by
      simpa [Matrix.reindex_apply] using hp
    rw [hR.support_eq] at hp'
    rcases Set.mem_iUnion.1 hp' with ⟨t, ht⟩
    exact Set.mem_iUnion.2 ⟨t, by simpa [Matrix.reindex_apply] using ht⟩
  · intro hp
    rcases Set.mem_iUnion.1 hp with ⟨t, ht⟩
    have hp' : (eₘ.symm i, eₙ.symm j) ∈ matrix_support (R t) := by
      simpa [Matrix.reindex_apply] using ht
    have hcover : (eₘ.symm i, eₙ.symm j) ∈ matrix_support S := by
      rw [hR.support_eq]
      exact Set.mem_iUnion.2 ⟨t, hp'⟩
    simpa [Matrix.reindex_apply] using hcover

/-- Every matrix over a `0,1` type with `1 ≠ 0` admits a finite rectangle cover. -/
theorem exists_rectangle_cover
    {m : Type u} {n : Type v} {α : Type w} [Finite m] [Finite n] [Zero α] [One α]
    [NeZero (1 : α)] (S : Matrix m n α) :
    ∃ k : ℕ, ∃ R : Fin k → Matrix m n α, is_rectangle_cover S R := by
  classical
  let _ := Fintype.ofFinite m
  let _ := Fintype.ofFinite n
  let T : Type _ := {p : m × n // p ∈ matrix_support S}
  let e : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let Rsub : T → Matrix m n α := fun p ↦ rectangle_indicator ({p.1.1} : Set m) ({p.1.2} : Set n)
  let R : Fin (Fintype.card T) → Matrix m n α := fun t ↦ Rsub (e.symm t)
  refine ⟨Fintype.card T, R, ?_⟩
  refine (is_rectangle_cover_iff).mpr ?_
  refine ⟨?_, ?_⟩
  · intro t
    simpa [R, Rsub] using
      rectangle_indicator_is_rectangle_matrix (Set.singleton_nonempty (e.symm t).1.1)
        (Set.singleton_nonempty (e.symm t).1.2)
  · ext p
    rcases p with ⟨i, j⟩
    constructor
    · intro hS
      refine Set.mem_iUnion.2 ⟨e ⟨(i, j), hS⟩, ?_⟩
      have hsingleton : (i, j) ∈ ({i} : Set m).prod ({j} : Set n) := ⟨by simp, by simp⟩
      have hrectangle :
          (i, j) ∈
            matrix_support (rectangle_indicator ({i} : Set m) ({j} : Set n) : Matrix m n α) := by
        simpa using hsingleton
      simpa [R, Rsub] using hrectangle
    · intro hR
      rcases Set.mem_iUnion.1 hR with ⟨t, ht⟩
      have hsingle : i = (e.symm t).1.1 ∧ j = (e.symm t).1.2 := by
        simpa [R, Rsub] using ht
      rcases hsingle with ⟨hi, hj⟩
      simpa [hi, hj] using (e.symm t).2

/-- The admissible sizes of finite rectangle covers of `S` form a nonempty set when the row and
column index types are finite. -/
theorem rectangle_cover_sizes_nonempty
    {m : Type u} {n : Type v} {α : Type w} [Finite m] [Finite n] [Zero α] [One α]
    [NeZero (1 : α)] (S : Matrix m n α) :
    {k : ℕ | ∃ R : Fin k → Matrix m n α, is_rectangle_cover S R}.Nonempty := by
  obtain ⟨k, R, hR⟩ := exists_rectangle_cover S
  exact ⟨k, ⟨R, hR⟩⟩

/-- Definition 4.10.1-extra-1 (3). For a matrix with finite row and column index types, the
rectangle covering number of `S` is the smallest cardinality of a rectangle cover of `S`. -/
noncomputable def rectangle_covering_number
    {m : Type u} {n : Type v} {α : Type w} [Finite m] [Finite n] [Zero α] [One α]
    [NeZero (1 : α)] (S : Matrix m n α) : ℕ :=
  sInf {k : ℕ | ∃ R : Fin k → Matrix m n α, is_rectangle_cover S R}

/-- The definition of `rectangle_covering_number` is the infimum of all rectangle-cover sizes of
`S`. -/
theorem rectangle_covering_number_eq_sInf
    {m : Type u} {n : Type v} {α : Type w} [Finite m] [Finite n] [Zero α] [One α]
    [NeZero (1 : α)] {S : Matrix m n α} :
    rectangle_covering_number S =
      sInf {k : ℕ | ∃ R : Fin k → Matrix m n α, is_rectangle_cover S R} :=
  rfl

/-- The rectangle covering number is the least size of a finite rectangle cover. -/
theorem rectangle_covering_number_isLeast
    {m : Type u} {n : Type v} {α : Type w} [Finite m] [Finite n] [Zero α] [One α]
    [NeZero (1 : α)] (S : Matrix m n α) :
    IsLeast
      {k : ℕ | ∃ R : Fin k → Matrix m n α, is_rectangle_cover S R}
      (rectangle_covering_number S) := by
  refine ⟨?_, ?_⟩
  · simpa [rectangle_covering_number] using
      (Nat.sInf_mem (rectangle_cover_sizes_nonempty S) :
        sInf {k : ℕ | ∃ R : Fin k → Matrix m n α, is_rectangle_cover S R} ∈
          {k : ℕ | ∃ R : Fin k → Matrix m n α, is_rectangle_cover S R})
  · intro k hk
    simpa [rectangle_covering_number] using
      (Nat.sInf_le hk :
        sInf {u : ℕ | ∃ R : Fin u → Matrix m n α, is_rectangle_cover S R} ≤ k)

/-- There is a rectangle cover of `S` whose size is `rectangle_covering_number S`. -/
theorem rectangle_covering_number_spec
    {m : Type u} {n : Type v} {α : Type w} [Finite m] [Finite n] [Zero α] [One α]
    [NeZero (1 : α)] (S : Matrix m n α) :
    ∃ R : Fin (rectangle_covering_number S) → Matrix m n α, is_rectangle_cover S R := by
  exact (rectangle_covering_number_isLeast S).1

/-- Any rectangle cover of `S` has size at least `rectangle_covering_number S`. -/
theorem rectangle_covering_number_le
    {m : Type u} {n : Type v} {α : Type w} [Finite m] [Finite n] [Zero α] [One α]
    [NeZero (1 : α)]
    {S : Matrix m n α} {R : Fin k → Matrix m n α} (hR : is_rectangle_cover S R) :
    rectangle_covering_number S ≤ k := by
  exact (rectangle_covering_number_isLeast S).2 ⟨R, hR⟩
