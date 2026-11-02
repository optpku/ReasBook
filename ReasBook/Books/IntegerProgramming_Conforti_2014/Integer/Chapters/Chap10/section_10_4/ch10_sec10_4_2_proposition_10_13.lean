import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section Proposition1013

variable {V : Type u} [DecidableEq V]

/-- The order-`t + 1` moment matrix attached to the subset-moment coordinates `y`. Its rows and
columns are indexed by finite subsets of cardinality at most `t + 1`, and its `(I,J)`-entry is
`y_{I ∪ J}`. -/
def lasserre_moment_matrix
    (t : ℕ) (y : Finset V → ℝ) :
    Matrix {I : Finset V // I.card ≤ t + 1} {J : Finset V // J.card ≤ t + 1} ℝ :=
  fun I J ↦ y (I ∪ J)

/-- `lasserre_moment_matrix t y` evaluates at `(I,J)` to the coordinate `y_{I ∪ J}`. -/
@[simp] theorem lasserre_moment_matrix_apply
    (t : ℕ) (y : Finset V → ℝ)
    (I : {I : Finset V // I.card ≤ t + 1})
    (J : {J : Finset V // J.card ≤ t + 1}) :
    lasserre_moment_matrix t y I J = y (I ∪ J) :=
  rfl

/-- The set `K_t` of normalized order-`t + 1` subset-moment vectors: the empty-set coordinate is
`1`, and the associated order-`t + 1` moment matrix is positive semidefinite. The ambient
function `y : Finset V → ℝ` supplies all subset coordinates, while `K_t` constrains only those
needed up to order `2t + 2`. -/
def K_t (t : ℕ) : Set (Finset V → ℝ) :=
  {y | y ∅ = 1 ∧ (lasserre_moment_matrix t y).PosSemidef}

/-- Membership in `K_t` means normalization at the empty set together with positive
semidefiniteness of the order-`t + 1` moment matrix. -/
@[simp] theorem mem_K_t_iff
    (t : ℕ) (y : Finset V → ℝ) :
    y ∈ K_t t ↔ y ∅ = 1 ∧ (lasserre_moment_matrix t y).PosSemidef :=
  Iff.rfl

namespace K_t

/-- A point of `K_t` is normalized at the empty set. -/
theorem empty_eq_one
    {t : ℕ} {y : Finset V → ℝ} (hy : y ∈ K_t t) :
    y ∅ = 1 :=
  (mem_K_t_iff t y).1 hy |>.1

/-- A point of `K_t` has positive semidefinite order-`t + 1` moment matrix. -/
theorem posSemidef
    {t : ℕ} {y : Finset V → ℝ} (hy : y ∈ K_t t) :
    (lasserre_moment_matrix t y).PosSemidef :=
  (mem_K_t_iff t y).1 hy |>.2

end K_t

end Proposition1013

section

variable {V : Type u}

attribute [local instance] Classical.decEq

/-- The singleton coordinates of a subset-moment vector, viewed as the point `x` with
`x_i = y_{ {i} }`. -/
def lasserre_point (y : Finset V → ℝ) : V → ℝ :=
  fun i ↦ y {i}

/-- `lasserre_point y i` is the singleton coordinate `y_{ {i} }`. -/
@[simp] theorem lasserre_point_apply
    (y : Finset V → ℝ) (i : V) :
    lasserre_point y i = y {i} :=
  rfl

end

section Proposition1013

variable {V : Type u} [DecidableEq V]

/-- Helper for Proposition 10.13: the `2 × 2` principal minor indexed by `I` and `J` has the
expected determinant. -/
lemma momentMatrixPairDet
    {t : ℕ} {y : Finset V → ℝ}
    {I J : Finset V}
    (hI : I.card ≤ t + 1)
    (hJ : J.card ≤ t + 1) :
    Matrix.det
      ((lasserre_moment_matrix t y).submatrix
        ![⟨I, hI⟩, ⟨J, hJ⟩]
        ![⟨I, hI⟩, ⟨J, hJ⟩]) =
      y I * y J - y (I ∪ J) ^ 2 := by
  -- Expand the principal minor and collapse the repeated unions.
  rw [Matrix.det_fin_two]
  simp [pow_two, Finset.union_comm]

/-- Helper for Proposition 10.13: the `3 × 3` principal minor indexed by `∅`, `I`, and `J`
reduces to the square obstruction from part (2). -/
lemma momentMatrixEmptyPairDet
    {t : ℕ} {y : Finset V → ℝ}
    {I J : Finset V}
    (hI : I.card ≤ t + 1)
    (hJ : J.card ≤ t + 1)
    (hy0 : y ∅ = 1)
    (hyI : y I = 1) :
    Matrix.det
      ((lasserre_moment_matrix t y).submatrix
        ![⟨∅, Nat.zero_le _⟩, ⟨I, hI⟩, ⟨J, hJ⟩]
        ![⟨∅, Nat.zero_le _⟩, ⟨I, hI⟩, ⟨J, hJ⟩]) =
      -((y J - y (I ∪ J)) ^ 2) := by
  -- Expand the principal minor, substitute the normalized entries, and simplify algebraically.
  rw [Matrix.det_fin_three]
  simp [hy0, hyI, pow_two, Finset.union_comm]
  ring

/-- Part (1) of Proposition 10.13. Let `y ∈ K_t`. Given finite subsets `I, J` with
`|I|, |J| ≤ t + 1`,
if `y_I = 0`, then `y_{I ∪ J} = 0`. -/
theorem k_t_union_eq_zero_of_eq_zero
    {t : ℕ} {y : Finset V → ℝ}
    (hy : y ∈ K_t t)
    {I J : Finset V}
    (hI : I.card ≤ t + 1)
    (hJ : J.card ≤ t + 1)
    (hyI : y I = 0) :
    y (I ∪ J) = 0 := by
  -- Take the `2 × 2` principal minor on `I` and `J`.
  let e : Fin 2 → {S : Finset V // S.card ≤ t + 1} := ![⟨I, hI⟩, ⟨J, hJ⟩]
  have hMinor : ((lasserre_moment_matrix t y).submatrix e e).PosSemidef :=
    (K_t.posSemidef hy).submatrix e
  have hDet :
      0 ≤ Matrix.det ((lasserre_moment_matrix t y).submatrix e e) := hMinor.det_nonneg
  have hMinorDet :
      Matrix.det ((lasserre_moment_matrix t y).submatrix e e) =
        y I * y J - y (I ∪ J) ^ 2 := by
    simpa [e] using momentMatrixPairDet (t := t) (y := y) hI hJ
  have hSq : 0 ≤ y I * y J - y (I ∪ J) ^ 2 := by
    rw [hMinorDet] at hDet
    exact hDet
  -- After substituting `y I = 0`, only the negative square remains.
  rw [hyI, zero_mul] at hSq
  nlinarith [sq_nonneg (y (I ∪ J))]

/-- Part (2) of Proposition 10.13. Let `y ∈ K_t`. Given finite subsets `I, J` with
`|I|, |J| ≤ t + 1`,
if `y_I = 1`, then `y_{I ∪ J} = y_J`. -/
theorem k_t_union_eq_right_of_eq_one
    {t : ℕ} {y : Finset V → ℝ}
    (hy : y ∈ K_t t)
    {I J : Finset V}
    (hI : I.card ≤ t + 1)
    (hJ : J.card ≤ t + 1)
    (hyI : y I = 1) :
    y (I ∪ J) = y J := by
  -- Take the `3 × 3` principal minor on `∅`, `I`, and `J`.
  let e : Fin 3 → {S : Finset V // S.card ≤ t + 1} :=
    ![⟨∅, Nat.zero_le _⟩, ⟨I, hI⟩, ⟨J, hJ⟩]
  have hMinor : ((lasserre_moment_matrix t y).submatrix e e).PosSemidef :=
    (K_t.posSemidef hy).submatrix e
  have hDet :
      0 ≤ Matrix.det ((lasserre_moment_matrix t y).submatrix e e) := hMinor.det_nonneg
  have hy0 : y ∅ = 1 := K_t.empty_eq_one hy
  have hMinorDet :
      Matrix.det ((lasserre_moment_matrix t y).submatrix e e) =
        -((y J - y (I ∪ J)) ^ 2) := by
    simpa [e] using momentMatrixEmptyPairDet (t := t) (y := y) hI hJ hy0 hyI
  have hSq : 0 ≤ -((y J - y (I ∪ J)) ^ 2) := by
    rw [hMinorDet] at hDet
    exact hDet
  -- A nonnegative negative square must vanish.
  nlinarith [sq_nonneg (y J - y (I ∪ J))]

/-- Helper for Proposition 10.13: singleton coordinates equal to `1` force every moment indexed
by a set of size at most `t + 1` to equal `1`. -/
lemma k_t_eq_one_of_singletons_eq_one_small
    {t : ℕ} {y : Finset V → ℝ}
    (hy : y ∈ K_t t) :
    ∀ {I : Finset V},
      I.card ≤ t + 1 →
      (∀ i ∈ I, lasserre_point y i = 1) →
      y I = 1 := by
  intro I
  refine Finset.induction_on I ?_ ?_
  · intro hI hx
    -- The empty set is normalized in every point of `K_t`.
    simpa using K_t.empty_eq_one hy
  · intro i I hi hInd hInsert hxInsert
    -- Restrict the singleton hypotheses to the smaller set and apply part (2) to add `i`.
    have hI : I.card ≤ t + 1 := (Finset.card_le_card (Finset.subset_insert i I)).trans hInsert
    have hyI : y I = 1 := hInd hI fun j hj ↦ hxInsert j (Finset.mem_insert_of_mem hj)
    have hySingleton : y ({i} : Finset V) = 1 := by
      simpa [lasserre_point_apply] using hxInsert i (Finset.mem_insert_self i I)
    calc
      y (insert i I) = y (({i} : Finset V) ∪ I) := by simp [Finset.singleton_union]
      _ = y I := k_t_union_eq_right_of_eq_one hy (by simp) hI hySingleton
      _ = 1 := hyI

/-- Proposition 10.13 (3). Let `y ∈ K_t`, and write `x_i := y_{ {i} }`. Given a finite subset
`I` with `|I| ≤ 2t + 2`, if `x_i = 1` for all `i ∈ I`, then `y_I = 1`. -/
theorem k_t_eq_one_of_singletons_eq_one
    {t : ℕ} {y : Finset V → ℝ}
    (hy : y ∈ K_t t)
    {I : Finset V}
    (hI : I.card ≤ 2 * t + 2)
    (hx : ∀ i ∈ I, lasserre_point y i = 1) :
    y I = 1 := by
  by_cases hSmall : I.card ≤ t + 1
  · -- Small sets are handled directly by the induction helper.
    exact k_t_eq_one_of_singletons_eq_one_small hy hSmall hx
  · -- Route correction: for larger sets, split off a subset of size `t + 1` and use part (2).
    have hLower : t + 1 ≤ I.card := Nat.le_of_lt (Nat.lt_of_not_ge hSmall)
    obtain ⟨I₁, hI₁sub, hI₁card⟩ := Finset.exists_subset_card_eq hLower
    let I₂ : Finset V := I \ I₁
    have hI₁ : I₁.card ≤ t + 1 := hI₁card.le
    have hI₂ : I₂.card ≤ t + 1 := by
      -- The complement has the remaining cardinality inside the `2 * t + 2` bound.
      have hI₂card : I₂.card = I.card - I₁.card := by
        simp [I₂, Finset.card_sdiff_of_subset hI₁sub]
      rw [hI₂card, hI₁card]
      omega
    have hx₁ : ∀ i ∈ I₁, lasserre_point y i = 1 := fun i hi ↦ hx i (hI₁sub hi)
    have hx₂ : ∀ i ∈ I₂, lasserre_point y i = 1 := fun i hi ↦ hx i (Finset.mem_sdiff.mp hi).1
    have hy₁ : y I₁ = 1 := k_t_eq_one_of_singletons_eq_one_small hy hI₁ hx₁
    have hy₂ : y I₂ = 1 := k_t_eq_one_of_singletons_eq_one_small hy hI₂ hx₂
    have hSplit : I = I₁ ∪ I₂ := by
      symm
      simpa [I₂] using Finset.union_sdiff_of_subset hI₁sub
    calc
      y I = y (I₁ ∪ I₂) := by rw [hSplit]
      _ = y I₂ := k_t_union_eq_right_of_eq_one hy hI₁ hI₂ hy₁
      _ = 1 := hy₂

end Proposition1013
