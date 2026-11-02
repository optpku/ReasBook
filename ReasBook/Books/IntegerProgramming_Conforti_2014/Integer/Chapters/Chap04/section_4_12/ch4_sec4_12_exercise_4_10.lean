import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_definition_4_2_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_theorem_4_6

set_option trace.profiler true

open scoped BigOperators Matrix

-- This exercise reuses mathlib's canonical `Matrix.IsTotallyUnimodular` owner and the
-- Chapter 4.2 equitable column-bicoloring API.

-- Declarations for this item will be appended below by the statement pipeline.

section Exercise410

variable {m n k : ℕ}

/-- The sum of the entries in row `i` of `A` over the columns carrying color `c`. -/
def column_color_sum
    (A : Matrix (Fin m) (Fin n) ℤ)
    (κ : Fin n → Fin k)
    (c : Fin k)
    (i : Fin m) : ℤ :=
  (Finset.univ.filter (fun j : Fin n ↦ κ j = c)).sum (fun j ↦ A i j)

/-- The columns carrying one of the colors `c` or `d`. -/
def color_pair_columns
    (κ : Fin n → Fin k)
    (c d : Fin k) : Finset (Fin n) :=
  Finset.univ.filter (fun j ↦ κ j = c ∨ κ j = d)

/-- The canonical enumeration of the selected `(c,d)`-columns. -/
def color_pair_embedding
    (κ : Fin n → Fin k)
    (c d : Fin k) : Fin (color_pair_columns κ c d).card ↪o Fin n :=
  (color_pair_columns κ c d).orderEmbOfFin rfl

/-- Within the selected `(c,d)`-submatrix, the columns carrying color `c`. -/
def color_pair_red
    (κ : Fin n → Fin k)
    (c d : Fin k) : Finset (Fin (color_pair_columns κ c d).card) :=
  Finset.univ.filter (fun j ↦ κ (color_pair_embedding κ c d j) = c)

/-- Within the selected `(c,d)`-submatrix, the columns carrying color `d`. -/
def color_pair_blue
    (κ : Fin n → Fin k)
    (c d : Fin k) : Finset (Fin (color_pair_columns κ c d).card) :=
  Finset.univ.filter (fun j ↦ κ (color_pair_embedding κ c d j) = d)

/-- An equitable `k`-coloring is a coloring of the columns such that, in every row, the sums over
any two distinct color classes differ by at most `1`. -/
def equitable_k_coloring
    (A : Matrix (Fin m) (Fin n) ℤ)
    (κ : Fin n → Fin k) : Prop :=
  ∀ c d : Fin k, c ≠ d →
    ∀ i : Fin m,
      Int.natAbs (column_color_sum A κ c i - column_color_sum A κ d i) ≤ 1

/-- Helper for Exercise 4.10: over `ℤ`, having absolute value at most `1` is equivalent to lying
in the image of `SignType.cast`. -/
lemma natAbs_le_one_iff_mem_signType_range {z : ℤ} :
    Int.natAbs z ≤ 1 ↔ z ∈ Set.range (SignType.cast : SignType → ℤ) := by
  rw [SignType.range_eq (SignType.cast : SignType → ℤ)]
  constructor
  · intro hz
    have hz' : |z| ≤ 1 := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hz
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc, or_left_comm, or_comm] using
      (Int.abs_le_one_iff.1 hz')
  · intro hz
    have hz' : z = 0 ∨ z = 1 ∨ z = -1 := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc, or_left_comm, or_comm] using hz
    have hz'' : |z| ≤ 1 := Int.abs_le_one_iff.2 hz'
    have hz''' : (Int.natAbs z : ℤ) ≤ 1 := by
      rw [← Int.abs_eq_natAbs]
      exact hz''
    exact_mod_cast hz'''

/-- Helper for Exercise 4.10: distinct colors give disjoint red and blue classes on the selected
`(c,d)`-submatrix. -/
lemma color_pair_red_disjoint_blue
    (κ : Fin n → Fin k) {c d : Fin k} (hcd : c ≠ d) :
    Disjoint (color_pair_red κ c d) (color_pair_blue κ c d) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro j hjc hjd
  have hc : κ (color_pair_embedding κ c d j) = c := (Finset.mem_filter.1 hjc).2
  have hd : κ (color_pair_embedding κ c d j) = d := (Finset.mem_filter.1 hjd).2
  exact hcd (hc.symm.trans hd)

/-- Helper for Exercise 4.10: the canonical red and blue classes cover the selected
`(c,d)`-submatrix. -/
lemma color_pair_red_union_blue
    (κ : Fin n → Fin k) (c d : Fin k) :
    color_pair_red κ c d ∪ color_pair_blue κ c d = Finset.univ := by
  classical
  ext j
  constructor
  · intro _
    simp
  · intro _
    have hjmem : color_pair_embedding κ c d j ∈ color_pair_columns κ c d :=
      Finset.orderEmbOfFin_mem (color_pair_columns κ c d) rfl j
    have hj : κ (color_pair_embedding κ c d j) = c ∨ κ (color_pair_embedding κ c d j) = d :=
      (Finset.mem_filter.1 hjmem).2
    simpa [color_pair_red, color_pair_blue] using hj

/-- Helper for Exercise 4.10: enumerating the selected red indices and mapping them back to the
ambient columns recovers exactly the ambient columns of color `c`. -/
lemma image_color_pair_red
    (κ : Fin n → Fin k)
    (c d : Fin k) :
    (color_pair_red κ c d).image (color_pair_embedding κ c d) =
      Finset.univ.filter (fun j : Fin n ↦ κ j = c) := by
  classical
  ext j
  constructor
  · intro hj
    rcases Finset.mem_image.1 hj with ⟨j', hj', rfl⟩
    have huniv : color_pair_embedding κ c d j' ∈ Finset.univ := Finset.mem_univ _
    exact Finset.mem_filter.2 ⟨huniv, (Finset.mem_filter.1 hj').2⟩
  · intro hj
    have hjc : κ j = c := (Finset.mem_filter.1 hj).2
    have hjpair : j ∈ color_pair_columns κ c d := by
      have huniv : j ∈ Finset.univ := Finset.mem_univ _
      exact Finset.mem_filter.2 ⟨huniv, Or.inl hjc⟩
    have hjimage : j ∈ Finset.image (color_pair_embedding κ c d) Finset.univ := by
      simpa [color_pair_embedding] using hjpair
    rcases Finset.mem_image.1 hjimage with ⟨j', -, rfl⟩
    have hj'red : j' ∈ color_pair_red κ c d := by
      simp [color_pair_red, hjc]
    exact Finset.mem_image.2 ⟨j', hj'red, rfl⟩

/-- Helper for Exercise 4.10: enumerating the selected blue indices and mapping them back to the
ambient columns recovers exactly the ambient columns of color `d`. -/
lemma image_color_pair_blue
    (κ : Fin n → Fin k)
    (c d : Fin k) :
    (color_pair_blue κ c d).image (color_pair_embedding κ c d) =
      Finset.univ.filter (fun j : Fin n ↦ κ j = d) := by
  classical
  ext j
  constructor
  · intro hj
    rcases Finset.mem_image.1 hj with ⟨j', hj', rfl⟩
    have huniv : color_pair_embedding κ c d j' ∈ Finset.univ := Finset.mem_univ _
    exact Finset.mem_filter.2 ⟨huniv, (Finset.mem_filter.1 hj').2⟩
  · intro hj
    have hjd : κ j = d := (Finset.mem_filter.1 hj).2
    have hjpair : j ∈ color_pair_columns κ c d := by
      have huniv : j ∈ Finset.univ := Finset.mem_univ _
      exact Finset.mem_filter.2 ⟨huniv, Or.inr hjd⟩
    have hjimage : j ∈ Finset.image (color_pair_embedding κ c d) Finset.univ := by
      simpa [color_pair_embedding] using hjpair
    rcases Finset.mem_image.1 hjimage with ⟨j', -, rfl⟩
    have hj'blue : j' ∈ color_pair_blue κ c d := by
      simp [color_pair_blue, hjd]
    exact Finset.mem_image.2 ⟨j', hj'blue, rfl⟩

/-- Helper for Exercise 4.10: the Chapter 4.2 row-balance condition on the `(c,d)`-submatrix is
the ambient rowwise difference of the `c`- and `d`-column sums. -/
lemma color_pair_difference_apply
    (A : Matrix (Fin m) (Fin n) ℤ)
    (κ : Fin n → Fin k)
    (c d : Fin k)
    (i : Fin m) :
    column_bicoloring_difference
        (A.submatrix id (color_pair_embedding κ c d))
        (color_pair_red κ c d)
        (color_pair_blue κ c d)
        i =
      column_color_sum A κ c i - column_color_sum A κ d i := by
  -- Rewrite the selected red and blue sums back to the ambient filtered color sums.
  rw [column_bicoloring_difference_apply]
  unfold column_color_sum
  rw [← image_color_pair_red κ c d, ← image_color_pair_blue κ c d]
  congr 1
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j hj
      simp [Matrix.submatrix_apply]
    · intro a _ b _ hab
      exact (color_pair_embedding κ c d).inj' hab
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j hj
      simp [Matrix.submatrix_apply]
    · intro a _ b _ hab
      exact (color_pair_embedding κ c d).inj' hab

/-- Bridge/view companion for Exercise 4.10: the direct pairwise row-balance condition is
equivalent to requiring the Chapter 4.2 equitable bicoloring owner on every selected
`(c,d)`-submatrix. -/
theorem equitable_k_coloring_iff_pairwise_equitable_bicoloring
    (A : Matrix (Fin m) (Fin n) ℤ)
    (κ : Fin n → Fin k) :
    equitable_k_coloring A κ ↔
      ∀ c d : Fin k, c ≠ d →
        is_equitable_bicoloring
          (A.submatrix id (color_pair_embedding κ c d))
          (color_pair_red κ c d)
          (color_pair_blue κ c d) := by
  constructor
  · intro h c d hcd
    rw [is_equitable_bicoloring_iff]
    refine ⟨color_pair_red_disjoint_blue κ hcd, color_pair_red_union_blue κ c d, ?_⟩
    intro i
    have hi :
        Int.natAbs (column_color_sum A κ c i - column_color_sum A κ d i) ≤ 1 :=
      h c d hcd i
    have hi' :
        column_bicoloring_difference
            (A.submatrix id (color_pair_embedding κ c d))
            (color_pair_red κ c d)
            (color_pair_blue κ c d)
            i ∈ Set.range (SignType.cast : SignType → ℤ) := by
      rw [color_pair_difference_apply]
      exact (natAbs_le_one_iff_mem_signType_range).1 hi
    rw [SignType.range_eq (SignType.cast : SignType → ℤ)] at hi'
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc, or_left_comm, or_comm] using hi'
  · intro h c d hcd i
    have hi :
        column_bicoloring_difference
            (A.submatrix id (color_pair_embedding κ c d))
            (color_pair_red κ c d)
            (color_pair_blue κ c d)
            i ∈ Set.range (SignType.cast : SignType → ℤ) := by
      have hi' :=
        ((is_equitable_bicoloring_iff
          (A.submatrix id (color_pair_embedding κ c d))
          (color_pair_red κ c d)
          (color_pair_blue κ c d)).1 (h c d hcd)).2.2 i
      rw [SignType.range_eq (SignType.cast : SignType → ℤ)]
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc, or_left_comm, or_comm] using hi'
    rw [← color_pair_difference_apply A κ c d i]
    exact (natAbs_le_one_iff_mem_signType_range).2 hi

/-- Helper for Exercise 4.10: transport Theorem 4.6 to a chosen column set, producing the
Chapter 4.2 equitable bicoloring owner on the corresponding selected-column submatrix. -/

lemma exists_equitable_bicoloring_on_column_set
    (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : A.IsTotallyUnimodular)
    (s : Finset (Fin n)) :
    ∃ red blue : Finset (Fin s.card),
      is_equitable_bicoloring
        (A.submatrix id (s.orderEmbOfFin rfl))
        red blue := by
  classical
  let B : Matrix (Fin m) (Fin s.card) ℤ :=
    A.submatrix id (s.orderEmbOfFin rfl)
  let c : Fin m → ℤ :=
    fun i ↦ ⌊(((B *ᵥ fun _ ↦ (1 : ℤ)) i : ℝ) / 2)⌋
  let d : Fin m → ℤ :=
    fun i ↦ ⌈(((B *ᵥ fun _ ↦ (1 : ℤ)) i : ℝ) / 2)⌉
  let l : Fin s.card → ℤ := fun _ ↦ 0
  let u : Fin s.card → ℤ := fun _ ↦ 1
  let P := integer_interval_matrix_polyhedron B c d l u
  let xHalf : Fin s.card → ℝ := fun _ ↦ (1 / 2 : ℝ)
  have hB : B.IsTotallyUnimodular := by
    exact hA.submatrix id (s.orderEmbOfFin rfl)
  have hHalfMulVec :
      (B.map (Int.castRingHom ℝ)) *ᵥ xHalf =
        fun i ↦ (((B *ᵥ fun _ ↦ (1 : ℤ)) i : ℤ) : ℝ) / 2 := by
    ext i
    have hOnesRow :
        Finset.sum Finset.univ (fun j : Fin s.card ↦ (B i j : ℝ)) =
          (((B *ᵥ fun _ ↦ (1 : ℤ)) i : ℤ) : ℝ) := by
      simp [Matrix.mulVec, dotProduct]
    calc
      ((B.map (Int.castRingHom ℝ)) *ᵥ xHalf) i =
          Finset.sum Finset.univ (fun j : Fin s.card ↦ (B i j : ℝ) * (1 / 2 : ℝ)) := by
            simp [xHalf, Matrix.mulVec, dotProduct]
      _ = (Finset.sum Finset.univ (fun j : Fin s.card ↦ (B i j : ℝ))) *
          (1 / 2 : ℝ) := by
            rw [Finset.sum_mul]
      _ = (((B *ᵥ fun _ ↦ (1 : ℤ)) i : ℤ) : ℝ) / 2 := by
            rw [hOnesRow]
            ring
  have hxHalf : xHalf ∈ P := by
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
  let M := interval_reduction_matrix B
  let b := interval_reduction_rhs B c d l u
  let Q := nonnegative_matrix_polyhedron M b
  have hPQ : P = Q := by
    ext x
    simpa [P, Q, M, b, l] using
      (mem_interval_reduction_polyhedron_shift_iff B c d l u x)
  have hQclosed : IsClosed Q := by
    change IsClosed (nonnegative_matrix_polyhedron M b)
    rcases nonnegative_matrix_polyhedron_is_polyhedron M b with
      ⟨q, C, rhs, hQeq⟩
    have hPolyhedronEq :
        polyhedron_le_set C rhs =
          ⋂ i : Fin q, {x : Fin s.card → ℝ | (C *ᵥ x) i ≤ rhs i} := by
      ext x
      constructor
      · intro hx
        simpa [polyhedron_le_set] using hx
      · intro hx
        simpa [polyhedron_le_set] using hx
    rw [hQeq, hPolyhedronEq]
    refine isClosed_iInter ?_
    intro i
    have hcontinuous : Continuous (fun x : Fin s.card → ℝ ↦ (C *ᵥ x) i) :=
      (continuous_apply i).comp C.mulVecLin.continuous_of_finiteDimensional
    exact isClosed_le hcontinuous continuous_const
  have hPsubset : P ⊆ Set.Icc (0 : Fin s.card → ℝ) 1 := by
    intro x hx
    have hxBounds := (mem_integer_interval_matrix_polyhedron_iff B c d l u x).1 hx
    constructor
    · simpa [l] using hxBounds.2.2.1
    · simpa [u] using hxBounds.2.2.2
  have hQsubset : Q ⊆ Set.Icc (0 : Fin s.card → ℝ) 1 := by
    rw [← hPQ]
    exact hPsubset
  have hQcompact : IsCompact Q := by
    exact IsCompact.of_isClosed_subset isCompact_Icc hQclosed hQsubset
  have hxHalfQ : xHalf ∈ Q := by
    rw [← hPQ]
    exact hxHalf
  obtain ⟨x, hxExtreme⟩ := hQcompact.extremePoints_nonempty ⟨xHalf, hxHalfQ⟩
  have hM : M.IsTotallyUnimodular := by
    simpa [M] using (interval_reduction_matrix_isTotallyUnimodular_iff B).2 hB
  have hxInt : x ∈ integerVectors s.card :=
    extreme_point_mem_integerVectors_of_isTotallyUnimodular M b hM hxExtreme
  have hxP : x ∈ P := by
    rw [hPQ]
    exact extremePoints_subset hxExtreme
  rcases (mem_integerVectors_iff (n := s.card) (x := x)).1 hxInt with ⟨z, rfl⟩
  rcases (mem_integer_interval_matrix_polyhedron_iff B c d l u (Int.cast ∘ z)).1 hxP with
    ⟨hLowerRows, hUpperRows, hLowerBox, hUpperBox⟩
  let red : Finset (Fin s.card) := Finset.univ.filter (fun j ↦ z j = 1)
  let blue : Finset (Fin s.card) := Finset.univ.filter (fun j ↦ z j = 0)
  have hz01 : ∀ j, z j = 0 ∨ z j = 1 := by
    intro j
    have h0Real : (0 : ℝ) ≤ z j := by
      simpa [l] using hLowerBox j
    have h1Real : (z j : ℝ) ≤ 1 := by
      simpa [u] using hUpperBox j
    have h0 : 0 ≤ z j := by
      exact_mod_cast h0Real
    have h1 : z j ≤ 1 := by
      exact_mod_cast h1Real
    omega
  have hDisjoint : Disjoint red blue := by
    refine Finset.disjoint_left.2 ?_
    intro j hjRed hjBlue
    have hRed : z j = 1 := by
      simpa [red] using hjRed
    have hBlue : z j = 0 := by
      simpa [blue] using hjBlue
    omega
  have hCover : red ∪ blue = Finset.univ := by
    ext j
    constructor
    · intro _
      simp
    · intro _
      rcases hz01 j with hZero | hOne
      · simp [red, blue, hZero]
      · simp [red, blue, hOne]
  have hCastMulVec :
      (B.map (Int.castRingHom ℝ)) *ᵥ (Int.cast ∘ z) =
        fun i ↦ ((B *ᵥ z) i : ℝ) := by
    ext i
    simpa using (RingHom.map_mulVec (Int.castRingHom ℝ) B z i).symm
  have hColor : is_equitable_bicoloring B red blue := by
    rw [is_equitable_bicoloring_iff]
    refine ⟨hDisjoint, hCover, ?_⟩
    intro i
    let t : ℤ := (B *ᵥ fun _ ↦ (1 : ℤ)) i
    let y : ℤ := (B *ᵥ z) i
    have hLowerRowReal : (⌊((t : ℝ) / 2)⌋ : ℝ) ≤ (y : ℝ) := by
      have hLower := hLowerRows i
      rw [hCastMulVec] at hLower
      simpa [c, t, y] using hLower
    have hUpperRowReal : (y : ℝ) ≤ (⌈((t : ℝ) / 2)⌉ : ℝ) := by
      have hUpper := hUpperRows i
      rw [hCastMulVec] at hUpper
      simpa [d, t, y] using hUpper
    have hLowerOpen : (((t : ℤ) : ℝ) / 2) - 1 < y :=
      (Int.sub_one_lt_floor (((t : ℤ) : ℝ) / 2)).trans_le hLowerRowReal
    have hUpperOpen : (y : ℝ) < (((t : ℤ) : ℝ) / 2) + 1 :=
      hUpperRowReal.trans_lt (Int.ceil_lt_add_one (((t : ℤ) : ℝ) / 2))
    have hRedSum : red.sum (fun j ↦ B i j) = (B *ᵥ z) i := by
      calc
        red.sum (fun j ↦ B i j) =
            Finset.sum Finset.univ (fun j ↦ if z j = 1 then B i j else 0) := by
              simp [red, Finset.sum_filter]
        _ = Finset.sum Finset.univ (fun j ↦ B i j * z j) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              rcases hz01 j with hZero | hOne
              · simp [hZero]
              · simp [hOne]
        _ = (B *ᵥ z) i := by
              simp [Matrix.mulVec, dotProduct]
    have hTotalSum :
        (B *ᵥ fun _ ↦ (1 : ℤ)) i =
          red.sum (fun j ↦ B i j) + blue.sum (fun j ↦ B i j) := by
      calc
        (B *ᵥ fun _ ↦ (1 : ℤ)) i = Finset.sum Finset.univ (fun j ↦ B i j) := by
          simp [Matrix.mulVec, dotProduct]
        _ = Finset.sum (red ∪ blue) (fun j ↦ B i j) := by
          rw [hCover]
        _ = red.sum (fun j ↦ B i j) + blue.sum (fun j ↦ B i j) := by
          simpa using (Finset.sum_union hDisjoint (f := fun j : Fin s.card ↦ B i j))
    have hDifference : column_bicoloring_difference B red blue i = 2 * y - t := by
      rw [column_bicoloring_difference_apply, hRedSum]
      dsimp [t, y]
      omega
    have hLowerInteger : t - 2 < 2 * y := by
      have hLowerReal : ((t : ℤ) : ℝ) - 2 < (2 : ℝ) * y := by
        nlinarith
      exact_mod_cast hLowerReal
    have hUpperInteger : 2 * y < t + 2 := by
      have hUpperReal : (2 : ℝ) * y < ((t : ℤ) : ℝ) + 2 := by
        nlinarith
      exact_mod_cast hUpperReal
    have hBalanced : 2 * y - t = 0 ∨ 2 * y - t = 1 ∨ 2 * y - t = -1 := by
      omega
    rcases hBalanced with hZero | hOne | hNegOne
    · exact Or.inl (hDifference.trans hZero)
    · exact Or.inr (Or.inl (hDifference.trans hOne))
    · exact Or.inr (Or.inr (hDifference.trans hNegOne))
  refine ⟨red, blue, ?_⟩
  simpa [B] using hColor

/-- Helper for Exercise 4.10: the square-sum potential minimized in the bichromatic-exchange
argument. -/
def coloring_potential
    (A : Matrix (Fin m) (Fin n) ℤ)
    (κ : Fin n → Fin k) : ℤ :=
  ∑ i : Fin m, ∑ c : Fin k, (column_color_sum A κ c i) ^ 2

/-- Helper for Exercise 4.10: recolor the selected `(c,d)`-columns by sending the chosen red
indices to `c` and the remaining selected columns to `d`. -/
def recolor_two_colors
    (κ : Fin n → Fin k)
    (c d : Fin k)
    (red : Finset (Fin (color_pair_columns κ c d).card)) : Fin n → Fin k :=
  fun j ↦
    if j ∈ red.image (color_pair_embedding κ c d) then c
    else if j ∈ color_pair_columns κ c d then d
    else κ j

/-- Helper for Exercise 4.10: recoloring sends every chosen red indexed column to color `c`. -/
lemma recolor_two_colors_of_mem_red
    (κ : Fin n → Fin k) (c d : Fin k)
    {red : Finset (Fin (color_pair_columns κ c d).card)}
    {j : Fin (color_pair_columns κ c d).card}
    (hj : j ∈ red) :
    recolor_two_colors κ c d red (color_pair_embedding κ c d j) = c := by
  have himage :
      color_pair_embedding κ c d j ∈ red.image (color_pair_embedding κ c d) :=
    Finset.mem_image.2 ⟨j, hj, rfl⟩
  simp [recolor_two_colors, himage]

/-- Helper for Exercise 4.10: recoloring sends every selected column outside the chosen red image
to color `d`. -/
lemma recolor_two_colors_of_mem_pair_not_mem_red
    (κ : Fin n → Fin k) (c d : Fin k)
    {red : Finset (Fin (color_pair_columns κ c d).card)} {j : Fin n}
    (hjpair : j ∈ color_pair_columns κ c d)
    (hjred : j ∉ red.image (color_pair_embedding κ c d)) :
    recolor_two_colors κ c d red j = d := by
  simp [recolor_two_colors, hjred, hjpair]

/-- Helper for Exercise 4.10: recoloring leaves columns outside the selected `(c,d)`-set
unchanged. -/
lemma recolor_two_colors_of_not_mem_pair
    (κ : Fin n → Fin k) (c d : Fin k)
    {red : Finset (Fin (color_pair_columns κ c d).card)} {j : Fin n}
    (hj : j ∉ color_pair_columns κ c d) :
    recolor_two_colors κ c d red j = κ j := by
  have hjimage : j ∉ red.image (color_pair_embedding κ c d) := by
    intro hj'
    rcases Finset.mem_image.1 hj' with ⟨x, hx, hxj⟩
    subst hxj
    have hxpair : color_pair_embedding κ c d x ∈ color_pair_columns κ c d :=
      Finset.orderEmbOfFin_mem (color_pair_columns κ c d) rfl x
    exact hj hxpair
  simp [recolor_two_colors, hjimage, hj]

/-- Helper for Exercise 4.10: the `c`-fiber of a
two-color recoloring is exactly the image of the chosen red indices. -/
lemma recolor_two_colors_fiber_eq_red_image
    (κ : Fin n → Fin k) {c d : Fin k} (hcd : c ≠ d)
    (red : Finset (Fin (color_pair_columns κ c d).card)) :
    Finset.univ.filter (fun j : Fin n ↦ recolor_two_colors κ c d red j = c) =
      red.image (color_pair_embedding κ c d) := by
  classical
  -- A column recolored to `c` must have belonged to the chosen red image.
  ext j
  constructor
  · intro hj
    have hrecolor : recolor_two_colors κ c d red j = c := (Finset.mem_filter.1 hj).2
    by_contra hjred
    have hjpair : j ∉ color_pair_columns κ c d := by
      intro hjpair
      have hd := recolor_two_colors_of_mem_pair_not_mem_red κ c d hjpair hjred
      exact hcd (hrecolor.symm.trans hd)
    have hjc : κ j = c := by
      rw [recolor_two_colors_of_not_mem_pair κ c d hjpair] at hrecolor
      exact hrecolor
    exact hjpair (Finset.mem_filter.2 ⟨Finset.mem_univ j, Or.inl hjc⟩)
  · intro hj
    rcases Finset.mem_image.1 hj with ⟨j', hj', rfl⟩
    exact Finset.mem_filter.2
      ⟨Finset.mem_univ _, recolor_two_colors_of_mem_red κ c d hj'⟩

/-- Helper for Exercise 4.10: for a red-blue
partition, the `d`-fiber of a two-color recoloring is exactly the image of the blue indices. -/
lemma recolor_two_colors_fiber_eq_blue_image
    (κ : Fin n → Fin k) {c d : Fin k} (hcd : c ≠ d)
    (red blue : Finset (Fin (color_pair_columns κ c d).card))
    (hdisjoint : Disjoint red blue)
    (hcover : red ∪ blue = Finset.univ) :
    Finset.univ.filter (fun j : Fin n ↦ recolor_two_colors κ c d red j = d) =
      blue.image (color_pair_embedding κ c d) := by
  classical
  -- The partition property identifies precisely the selected indices not colored red.
  ext j
  constructor
  · intro hj
    have hrecolor : recolor_two_colors κ c d red j = d := (Finset.mem_filter.1 hj).2
    have hjred : j ∉ red.image (color_pair_embedding κ c d) := by
      intro hjred
      rcases Finset.mem_image.1 hjred with ⟨j', hj', rfl⟩
      have hc := recolor_two_colors_of_mem_red κ c d hj'
      exact hcd (hc.symm.trans hrecolor)
    have hjpair : j ∈ color_pair_columns κ c d := by
      by_contra hjpair
      have hjκ := recolor_two_colors_of_not_mem_pair κ c d (red := red) hjpair
      have hjd : κ j = d := hjκ.symm.trans hrecolor
      exact hjpair (Finset.mem_filter.2 ⟨Finset.mem_univ j, Or.inr hjd⟩)
    have hjimage : j ∈ Finset.image (color_pair_embedding κ c d) Finset.univ := by
      simpa [color_pair_embedding] using hjpair
    rcases Finset.mem_image.1 hjimage with ⟨j', -, rfl⟩
    have hjpartition : j' ∈ red ∨ j' ∈ blue := by
      simpa [Finset.mem_union] using
        congrArg (fun s : Finset (Fin (color_pair_columns κ c d).card) ↦ j' ∈ s) hcover
    rcases hjpartition with hj' | hj'
    · exact False.elim (hjred (Finset.mem_image.2 ⟨j', hj', rfl⟩))
    · exact Finset.mem_image.2 ⟨j', hj', rfl⟩
  · intro hj
    rcases Finset.mem_image.1 hj with ⟨j', hjblue, rfl⟩
    have hjpair : color_pair_embedding κ c d j' ∈ color_pair_columns κ c d :=
      Finset.orderEmbOfFin_mem (color_pair_columns κ c d) rfl j'
    have hjred : color_pair_embedding κ c d j' ∉
        red.image (color_pair_embedding κ c d) := by
      intro hjimage
      rcases Finset.mem_image.1 hjimage with ⟨j'', hjred, heq⟩
      have hj'eq : j'' = j' := (color_pair_embedding κ c d).inj' heq
      subst hj'eq
      exact (Finset.disjoint_left.1 hdisjoint) hjred hjblue
    exact Finset.mem_filter.2
      ⟨Finset.mem_univ _,
        recolor_two_colors_of_mem_pair_not_mem_red κ c d hjpair hjred⟩

/-- Helper for Exercise 4.10: every color other
than `c` and `d` has the same fiber before and after a two-color recoloring. -/
lemma recolor_two_colors_fiber_eq_of_ne
    (κ : Fin n → Fin k) (c d e : Fin k) (hce : e ≠ c) (hde : e ≠ d)
    (red : Finset (Fin (color_pair_columns κ c d).card)) :
    Finset.univ.filter (fun j : Fin n ↦ recolor_two_colors κ c d red j = e) =
      Finset.univ.filter (fun j : Fin n ↦ κ j = e) := by
  classical
  -- Outside the selected pair recoloring is the identity; inside it both sides exclude `e`.
  ext j
  constructor
  · intro hj
    have hrecolor : recolor_two_colors κ c d red j = e := (Finset.mem_filter.1 hj).2
    have hjpair : j ∉ color_pair_columns κ c d := by
      intro hjpair
      by_cases hjred : j ∈ red.image (color_pair_embedding κ c d)
      · have hc : recolor_two_colors κ c d red j = c := by
          simp [recolor_two_colors, hjred]
        exact hce (hrecolor.symm.trans hc)
      · have hd := recolor_two_colors_of_mem_pair_not_mem_red κ c d hjpair hjred
        exact hde (hrecolor.symm.trans hd)
    have hjκ : κ j = e := by
      rw [recolor_two_colors_of_not_mem_pair κ c d hjpair] at hrecolor
      exact hrecolor
    exact Finset.mem_filter.2 ⟨Finset.mem_univ j, hjκ⟩
  · intro hj
    have hjκ : κ j = e := (Finset.mem_filter.1 hj).2
    have hjpair : j ∉ color_pair_columns κ c d := by
      intro hjpair
      rcases (Finset.mem_filter.1 hjpair).2 with hjc | hjd
      · exact hce (hjκ.symm.trans hjc)
      · exact hde (hjκ.symm.trans hjd)
    have hrecolor := recolor_two_colors_of_not_mem_pair κ c d (red := red) hjpair
    exact Finset.mem_filter.2 ⟨Finset.mem_univ j, hrecolor.trans hjκ⟩

/-- Helper for Exercise 4.10: among two integer
bins with a fixed total, a difference in `{0, 1, -1}` minimizes the sum of squares, strictly so
against a difference of natural absolute value greater than one. -/
lemma balanced_pair_sq_comparison
    (x y x' y' : ℤ)
    (hsum : x' + y' = x + y)
    (hdiff : x' - y' = 0 ∨ x' - y' = 1 ∨ x' - y' = -1) :
    x' ^ 2 + y' ^ 2 ≤ x ^ 2 + y ^ 2 ∧
      (1 < Int.natAbs (x - y) → x' ^ 2 + y' ^ 2 < x ^ 2 + y ^ 2) := by
  -- Compare the pair energies through their equal total squares and their difference squares.
  have hsumSq : (x' + y') ^ 2 = (x + y) ^ 2 := congrArg (fun z : ℤ ↦ z ^ 2) hsum
  have hdiffSq : (x' - y') ^ 2 ≤ (x - y) ^ 2 := by
    rcases hdiff with hzero | hone | hnegone
    · rw [hzero]
      exact sq_nonneg (x - y)
    · have hne : x - y ≠ 0 := by
        intro heq
        omega
      rw [hone]
      nlinarith [sq_pos_of_ne_zero hne]
    · have hne : x - y ≠ 0 := by
        intro heq
        omega
      rw [hnegone]
      nlinarith [sq_pos_of_ne_zero hne]
  constructor
  · nlinarith
  · intro habs
    have holdDiffSq : (1 : ℤ) ^ 2 < (x - y) ^ 2 := by
      rw [← Int.natAbs_lt_iff_sq_lt]
      simpa using habs
    have hnewDiffSq : (x' - y') ^ 2 ≤ (1 : ℤ) ^ 2 := by
      rcases hdiff with hzero | hone | hnegone
      · simp [hzero]
      · simp [hone]
      · simp [hnegone]
    nlinarith

/-- Helper for Exercise 4.10: the new `c` row sum
is the red sum on the selected-column submatrix. -/
lemma recolor_two_colors_color_sum_eq_red_sum
    (A : Matrix (Fin m) (Fin n) ℤ) (κ : Fin n → Fin k)
    {c d : Fin k} (hcd : c ≠ d)
    (red : Finset (Fin (color_pair_columns κ c d).card)) (i : Fin m) :
    column_color_sum A (recolor_two_colors κ c d red) c i =
      red.sum (fun j ↦ (A.submatrix id (color_pair_embedding κ c d)) i j) := by
  -- Replace the color fiber by the red image, then sum through the injective enumeration.
  unfold column_color_sum
  rw [recolor_two_colors_fiber_eq_red_image κ hcd red]
  rw [Finset.sum_image]
  · simp [Matrix.submatrix_apply]
  · intro a _ b _ hab
    exact (color_pair_embedding κ c d).inj' hab

/-- Helper for Exercise 4.10: the new `d` row sum
is the blue sum on the selected-column submatrix. -/
lemma recolor_two_colors_color_sum_eq_blue_sum
    (A : Matrix (Fin m) (Fin n) ℤ) (κ : Fin n → Fin k)
    {c d : Fin k} (hcd : c ≠ d)
    (red blue : Finset (Fin (color_pair_columns κ c d).card))
    (hbalanced : is_equitable_bicoloring
      (A.submatrix id (color_pair_embedding κ c d)) red blue)
    (i : Fin m) :
    column_color_sum A (recolor_two_colors κ c d red) d i =
      blue.sum (fun j ↦ (A.submatrix id (color_pair_embedding κ c d)) i j) := by
  -- Replace the color fiber by the blue image, using the balanced partition to identify it.
  unfold column_color_sum
  rw [recolor_two_colors_fiber_eq_blue_image κ hcd red blue
    hbalanced.disjoint hbalanced.cover]
  rw [Finset.sum_image]
  · simp [Matrix.submatrix_apply]
  · intro a _ b _ hab
    exact (color_pair_embedding κ c d).inj' hab

/-- Helper for Exercise 4.10: row sums of colors
outside the selected pair are unchanged by the recoloring. -/
lemma recolor_two_colors_color_sum_eq_of_ne
    (A : Matrix (Fin m) (Fin n) ℤ) (κ : Fin n → Fin k)
    (c d e : Fin k) (hce : e ≠ c) (hde : e ≠ d)
    (red : Finset (Fin (color_pair_columns κ c d).card)) (i : Fin m) :
    column_color_sum A (recolor_two_colors κ c d red) e i =
      column_color_sum A κ e i := by
  -- The two sums have equal filtered fibers by the recoloring interface.
  unfold column_color_sum
  rw [recolor_two_colors_fiber_eq_of_ne κ c d e hce hde red]

/-- Helper for Exercise 4.10: recoloring preserves
the combined `c`- and `d`-row sum. -/
lemma recolor_two_colors_pair_sum_eq
    (A : Matrix (Fin m) (Fin n) ℤ) (κ : Fin n → Fin k)
    {c d : Fin k} (hcd : c ≠ d)
    (red blue : Finset (Fin (color_pair_columns κ c d).card))
    (hbalanced : is_equitable_bicoloring
      (A.submatrix id (color_pair_embedding κ c d)) red blue)
    (i : Fin m) :
    column_color_sum A (recolor_two_colors κ c d red) c i +
        column_color_sum A (recolor_two_colors κ c d red) d i =
      column_color_sum A κ c i + column_color_sum A κ d i := by
  -- Both sides are the sum of the same row over all selected `(c,d)` columns.
  have hnew :
      red.sum (fun j ↦ (A.submatrix id (color_pair_embedding κ c d)) i j) +
          blue.sum (fun j ↦ (A.submatrix id (color_pair_embedding κ c d)) i j) =
        Finset.univ.sum
          (fun j ↦ (A.submatrix id (color_pair_embedding κ c d)) i j) := by
    calc
      _ = (red ∪ blue).sum
          (fun j ↦ (A.submatrix id (color_pair_embedding κ c d)) i j) :=
        (Finset.sum_union hbalanced.disjoint).symm
      _ = _ := by rw [hbalanced.cover]
  have hfiltersDisjoint :
      Disjoint
        (Finset.univ.filter (fun j : Fin n ↦ κ j = c))
        (Finset.univ.filter (fun j : Fin n ↦ κ j = d)) := by
    refine Finset.disjoint_left.2 ?_
    intro j hjc hjd
    exact hcd ((Finset.mem_filter.1 hjc).2.symm.trans (Finset.mem_filter.1 hjd).2)
  have hfiltersUnion :
      Finset.univ.filter (fun j : Fin n ↦ κ j = c) ∪
          Finset.univ.filter (fun j : Fin n ↦ κ j = d) =
        color_pair_columns κ c d := by
    ext j
    simp [color_pair_columns]
  have hold :
      column_color_sum A κ c i + column_color_sum A κ d i =
        Finset.univ.sum
          (fun j ↦ (A.submatrix id (color_pair_embedding κ c d)) i j) := by
    have himage :
        Finset.image (color_pair_embedding κ c d) Finset.univ =
          color_pair_columns κ c d := by
      simp [color_pair_embedding]
    calc
      column_color_sum A κ c i + column_color_sum A κ d i =
          (Finset.univ.filter (fun j : Fin n ↦ κ j = c)).sum (fun j ↦ A i j) +
            (Finset.univ.filter (fun j : Fin n ↦ κ j = d)).sum (fun j ↦ A i j) := by
              rfl
      _ = (color_pair_columns κ c d).sum (fun j ↦ A i j) := by
        rw [← hfiltersUnion, Finset.sum_union hfiltersDisjoint]
      _ = (Finset.image (color_pair_embedding κ c d) Finset.univ).sum
          (fun j ↦ A i j) := by
        rw [himage]
      _ = Finset.univ.sum
          (fun j ↦ (A.submatrix id (color_pair_embedding κ c d)) i j) := by
        rw [Finset.sum_image]
        · simp [Matrix.submatrix_apply]
        · intro a _ b _ hab
          exact (color_pair_embedding κ c d).inj' hab
  rw [recolor_two_colors_color_sum_eq_red_sum A κ hcd red i,
    recolor_two_colors_color_sum_eq_blue_sum A κ hcd red blue hbalanced i,
    hnew, hold]

/-- Helper for Exercise 4.10: the new difference
of the selected two color sums is the balanced submatrix difference. -/
lemma recolor_two_colors_pair_difference_eq
    (A : Matrix (Fin m) (Fin n) ℤ) (κ : Fin n → Fin k)
    {c d : Fin k} (hcd : c ≠ d)
    (red blue : Finset (Fin (color_pair_columns κ c d).card))
    (hbalanced : is_equitable_bicoloring
      (A.submatrix id (color_pair_embedding κ c d)) red blue)
    (i : Fin m) :
    column_color_sum A (recolor_two_colors κ c d red) c i -
        column_color_sum A (recolor_two_colors κ c d red) d i =
      column_bicoloring_difference
        (A.submatrix id (color_pair_embedding κ c d)) red blue i := by
  -- Rewrite both recolored sums to the red-blue sums defining the balanced difference.
  rw [recolor_two_colors_color_sum_eq_red_sum A κ hcd red i,
    recolor_two_colors_color_sum_eq_blue_sum A κ hcd red blue hbalanced i,
    column_bicoloring_difference_apply]

/-- Helper for Exercise 4.10: a finite square sum
splits into two distinguished terms and the terms at all remaining indices. -/
lemma sum_sq_eq_pair_add_rest
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℤ) {c d : ι} (hcd : c ≠ d) :
    (∑ e : ι, f e ^ 2) =
      f c ^ 2 + f d ^ 2 +
        ∑ e ∈ (Finset.univ.erase c).erase d, f e ^ 2 := by
  -- Erase `c` and then `d`, and reassociate the resulting three summands.
  have hdmem : d ∈ (Finset.univ : Finset ι).erase c := by
    exact Finset.mem_erase.2 ⟨Ne.symm hcd, Finset.mem_univ d⟩
  calc
    (∑ e : ι, f e ^ 2) =
        (∑ e ∈ (Finset.univ : Finset ι).erase c, f e ^ 2) + f c ^ 2 :=
      (Finset.sum_erase_add (s := Finset.univ) (a := c)
        (f := fun e ↦ f e ^ 2) (Finset.mem_univ c)).symm
    _ = ((∑ e ∈ ((Finset.univ : Finset ι).erase c).erase d, f e ^ 2) +
          f d ^ 2) + f c ^ 2 := by
      rw [Finset.sum_erase_add (s := (Finset.univ : Finset ι).erase c) (a := d)
        (f := fun e ↦ f e ^ 2) hdmem]
    _ = f c ^ 2 + f d ^ 2 +
        ∑ e ∈ ((Finset.univ : Finset ι).erase c).erase d, f e ^ 2 := by
      ring

/-- Helper for Exercise 4.10: in every row the
two-color recoloring weakly decreases square energy, and decreases it strictly when the original
pair difference has natural absolute value greater than one. -/
lemma recolor_two_colors_row_energy_comparison
    (A : Matrix (Fin m) (Fin n) ℤ)
    (κ : Fin n → Fin k)
    {c d : Fin k} (hcd : c ≠ d)
    (red blue : Finset (Fin (color_pair_columns κ c d).card))
    (hbalanced : is_equitable_bicoloring
      (A.submatrix id (color_pair_embedding κ c d)) red blue)
    (i : Fin m) :
    (∑ e : Fin k, (column_color_sum A (recolor_two_colors κ c d red) e i) ^ 2) ≤
        ∑ e : Fin k, (column_color_sum A κ e i) ^ 2 ∧
      (1 < Int.natAbs (column_color_sum A κ c i - column_color_sum A κ d i) →
        (∑ e : Fin k, (column_color_sum A (recolor_two_colors κ c d red) e i) ^ 2) <
          ∑ e : Fin k, (column_color_sum A κ e i) ^ 2) := by
  classical
  let newSum : Fin k → ℤ :=
    fun e ↦ column_color_sum A (recolor_two_colors κ c d red) e i
  let oldSum : Fin k → ℤ := fun e ↦ column_color_sum A κ e i
  -- The pair-total invariant and the balanced difference feed the integer energy comparison.
  have hpairTotal : newSum c + newSum d = oldSum c + oldSum d := by
    simpa [newSum, oldSum] using
      recolor_two_colors_pair_sum_eq A κ hcd red blue hbalanced i
  have hpairDifference :
      newSum c - newSum d =
        column_bicoloring_difference
          (A.submatrix id (color_pair_embedding κ c d)) red blue i := by
    simpa [newSum] using
      recolor_two_colors_pair_difference_eq A κ hcd red blue hbalanced i
  have hbalancedDifference :
      newSum c - newSum d = 0 ∨ newSum c - newSum d = 1 ∨
        newSum c - newSum d = -1 := by
    rw [hpairDifference]
    exact hbalanced.row_balance i
  have hpairEnergy :=
    balanced_pair_sq_comparison
      (oldSum c) (oldSum d) (newSum c) (newSum d) hpairTotal hbalancedDifference
  -- All colors outside the selected pair contribute exactly the same square terms.
  have hother : ∀ e : Fin k, e ≠ c → e ≠ d → newSum e = oldSum e := by
    intro e hec hed
    simpa [newSum, oldSum] using
      recolor_two_colors_color_sum_eq_of_ne A κ c d e hec hed red i
  have hrest :
      (∑ e ∈ (Finset.univ.erase c).erase d, newSum e ^ 2) =
        ∑ e ∈ (Finset.univ.erase c).erase d, oldSum e ^ 2 := by
    apply Finset.sum_congr rfl
    intro e he
    have hed : e ≠ d := (Finset.mem_erase.1 he).1
    have hec : e ≠ c :=
      (Finset.mem_erase.1 (Finset.mem_erase.1 he).2).1
    rw [hother e hec hed]
  have hnewDecomposition := sum_sq_eq_pair_add_rest newSum hcd
  have holdDecomposition := sum_sq_eq_pair_add_rest oldSum hcd
  constructor
  · -- Add the common unaffected remainder to the weak pair-energy inequality.
    rw [hnewDecomposition, holdDecomposition, hrest]
    simpa only [add_comm] using
      add_le_add_right hpairEnergy.1
        (∑ e ∈ (Finset.univ.erase c).erase d, oldSum e ^ 2)
  · intro habs
    -- At a bad row, the strict pair-energy inequality remains strict after adding the remainder.
    rw [hnewDecomposition, holdDecomposition, hrest]
    have habs' : 1 < Int.natAbs (oldSum c - oldSum d) := by
      simpa [oldSum] using habs
    simpa only [add_comm] using
      add_lt_add_right (hpairEnergy.2 habs')
        (∑ e ∈ (Finset.univ.erase c).erase d, oldSum e ^ 2)

/-- Helper for Exercise 4.10: replacing a bad pair of colors by an equitable bicoloring on their
selected-column submatrix strictly lowers the square-sum potential. -/
lemma recolor_two_colors_decreases_potential
    (A : Matrix (Fin m) (Fin n) ℤ)
    (κ : Fin n → Fin k)
    (c d : Fin k)
    (red blue : Finset (Fin (color_pair_columns κ c d).card))
    (hbalanced : is_equitable_bicoloring
      (A.submatrix id (color_pair_embedding κ c d))
      red blue)
    (iwit : Fin m)
    (hwit : 1 < Int.natAbs (column_color_sum A κ c iwit - column_color_sum A κ d iwit)) :
    coloring_potential A (recolor_two_colors κ c d red) < coloring_potential A κ := by
  classical
  -- The witness forces the two selected colors to be distinct.
  have hcd : c ≠ d := by
    intro h
    subst d
    simp at hwit
  have hrow :=
    recolor_two_colors_row_energy_comparison A κ hcd red blue hbalanced
  -- Sum the weak row inequalities, using the witness row for strictness.
  unfold coloring_potential
  exact Finset.sum_lt_sum
    (fun i _ ↦ (hrow i).1)
    ⟨iwit, Finset.mem_univ iwit, (hrow iwit).2 hwit⟩

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_10.lean
Exercise 4.10: every totally unimodular integer matrix admits an equitable `k`-coloring for every
positive integer `k`; when `k = 1`, the pairwise condition is vacuous. -/
theorem exists_equitable_k_coloring_of_is_totally_unimodular
    (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : A.IsTotallyUnimodular)
    (hk : 0 < k) :
    ∃ κ : Fin n → Fin k, equitable_k_coloring A κ := by
  classical
  let baseColor : Fin k := ⟨0, hk⟩
  have hcolorings_nonempty : (Finset.univ : Finset (Fin n → Fin k)).Nonempty := by
    have hbase_mem : (fun _ ↦ baseColor) ∈ (Finset.univ : Finset (Fin n → Fin k)) :=
      Finset.mem_univ _
    exact ⟨fun _ ↦ baseColor, hbase_mem⟩
  obtain ⟨κmin, -, hκmin_min⟩ :=
    (Finset.univ : Finset (Fin n → Fin k)).exists_min_image
      (coloring_potential A) hcolorings_nonempty
  refine ⟨κmin, ?_⟩
  intro c d hcd i
  by_contra hbad
  have hwit :
      1 < Int.natAbs (column_color_sum A κmin c i - column_color_sum A κmin d i) := by
    omega
  obtain ⟨red, blue, hredblue⟩ :=
    exists_equitable_bicoloring_on_column_set A hA
      (color_pair_columns κmin c d)
  have hredblue' :
      is_equitable_bicoloring
        (A.submatrix id (color_pair_embedding κmin c d))
        red blue := by
    simpa [color_pair_embedding] using hredblue
  let κ' := recolor_two_colors κmin c d red
  have hlt : coloring_potential A κ' < coloring_potential A κmin := by
    -- Route correction: the main minimizer skeleton is now in place, and the only remaining
    -- substantive step is the planned bichromatic-exchange decrease lemma.
    simpa [κ'] using recolor_two_colors_decreases_potential
      A κmin c d red blue hredblue' i hwit
  have hκ'mem : κ' ∈ (Finset.univ : Finset (Fin n → Fin k)) := Finset.mem_univ _
  have hmin_le : coloring_potential A κmin ≤ coloring_potential A κ' :=
    hκmin_min κ' hκ'mem
  exact (not_lt_of_ge hmin_le) hlt

end Exercise410

#print axioms exists_equitable_k_coloring_of_is_totally_unimodular
