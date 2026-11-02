import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1

open scoped Matrix

-- This file is organized around the Chapter 3 owner `polyhedron_le_set`; the implicit and
-- remaining subsystems are its source-facing row-restricted views.

/-- Definition 3.7-extra-1 (1). An inequality indexed by `i` in the system `A *ᵥ x ≤ b` is an
implicit equality if every solution of the system satisfies it with equality. -/
def is_implicit_equality
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i : Fin m) : Prop :=
  ∀ ⦃x : Fin n → ℝ⦄, A *ᵥ x ≤ b → (A *ᵥ x) i = b i

/-- An inequality is an implicit equality exactly when the polyhedron is contained in the
corresponding hyperplane. -/
theorem is_implicit_equality_iff_matrix_polyhedron_subset_hyperplane
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i : Fin m) :
    is_implicit_equality A b i ↔
      polyhedron_le_set A b ⊆ {x : Fin n → ℝ | (A *ᵥ x) i = b i} := by
  constructor
  · intro hi x hx
    exact hi hx
  · intro hi x hx
    exact hi hx

/-- Definition 3.7-extra-1 (2). The indices of the implicit equalities in the system
`A *ᵥ x ≤ b`. -/
def implicit_equality_indices
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Set (Fin m) :=
  {i | is_implicit_equality A b i}

/-- Membership in `implicit_equality_indices A b` means that the indexed inequality is implicit. -/
theorem mem_implicit_equality_indices_iff
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i : Fin m) :
    i ∈ implicit_equality_indices A b ↔ is_implicit_equality A b i := by
  rfl

/-- Definition 3.7-extra-1 (3). The indices of the remaining, non-implicit inequalities in the
system `A *ᵥ x ≤ b`. -/
def remaining_inequality_indices
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Set (Fin m) :=
  (implicit_equality_indices A b)ᶜ

/-- Membership in `remaining_inequality_indices A b` means that the indexed inequality is not an
implicit equality. -/
theorem mem_remaining_inequality_indices_iff
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i : Fin m) :
    i ∈ remaining_inequality_indices A b ↔ ¬ is_implicit_equality A b i := by
  rfl

/-- The subsystem matrix obtained by restricting `A` to the rows indexed by the implicit
equalities. -/
abbrev implicit_equality_matrix
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    Matrix {i // i ∈ implicit_equality_indices A b} (Fin n) ℝ :=
  A.submatrix Subtype.val id

/-- The right-hand side obtained by restricting `b` to the implicit equalities. -/
abbrev implicit_equality_rhs
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    {i // i ∈ implicit_equality_indices A b} → ℝ :=
  b ∘ Subtype.val

/-- The subsystem matrix obtained by restricting `A` to the remaining inequalities. -/
abbrev remaining_inequality_matrix
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    Matrix {i // i ∈ remaining_inequality_indices A b} (Fin n) ℝ :=
  A.submatrix Subtype.val id

/-- The right-hand side obtained by restricting `b` to the remaining inequalities. -/
abbrev remaining_inequality_rhs
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    {i // i ∈ remaining_inequality_indices A b} → ℝ :=
  b ∘ Subtype.val

section ImplicitEqualitySurface

variable {m n : ℕ}
variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)

local notation:max A "^=" => implicit_equality_matrix A b
local notation:max "b^=" => implicit_equality_rhs A b

/-- The implicit-equality subsystem matrix has the same row entries as `A` on its
restricted index type. -/
theorem implicit_equality_matrix_apply
    (i : {i // i ∈ implicit_equality_indices A b})
    (j : Fin n) :
    A^= i j = A i.1 j := by
  rfl

/-- The implicit-equality right-hand side has the same entries as `b` on its restricted
index type. -/
theorem implicit_equality_rhs_apply
    (i : {i // i ∈ implicit_equality_indices A b}) :
    b^= i = b i.1 := by
  rfl

/-- The remaining-inequality subsystem matrix has the same row entries as `A` on its restricted
index type. -/
theorem remaining_inequality_matrix_apply
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i : {i // i ∈ remaining_inequality_indices A b})
    (j : Fin n) :
    remaining_inequality_matrix A b i j = A i.1 j := by
  rfl

/-- The remaining-inequality right-hand side has the same entries as `b` on its restricted index
type. -/
theorem remaining_inequality_rhs_apply
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i : {i // i ∈ remaining_inequality_indices A b}) :
    remaining_inequality_rhs A b i = b i.1 := by
  rfl

/-- Helper for Definition 3.7-extra-1: evaluating the implicit-equality subsystem on a
restricted row agrees with evaluating the original system on the underlying row. -/
theorem implicit_equality_mulVec_apply
    (x : Fin n → ℝ)
    (i : {i // i ∈ implicit_equality_indices A b}) :
    (A^= *ᵥ x) i = (A *ᵥ x) i.1 := by
  rfl

/-- Helper for Definition 3.7-extra-1: evaluating the remaining-inequality subsystem on a
restricted row agrees with evaluating the original system on the underlying row. -/
theorem remaining_inequality_mulVec_apply
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (x : Fin n → ℝ)
    (i : {i // i ∈ remaining_inequality_indices A b}) :
    (remaining_inequality_matrix A b *ᵥ x) i = (A *ᵥ x) i.1 := by
  rfl

/-- Definition 3.7-extra-1 (4). The polyhedron defined by `A *ᵥ x ≤ b` is exactly the set of
points satisfying the implicit-equality subsystem `A^= x ≤ b^=` and the remaining subsystem
together as inequalities. -/
theorem polyhedron_le_set_eq_implicit_and_remaining_subsystems
    :
    polyhedron_le_set A b =
      {x : Fin n → ℝ |
        A^= *ᵥ x ≤ b^= ∧
        remaining_inequality_matrix A b *ᵥ x ≤ remaining_inequality_rhs A b} := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    simp only [Set.mem_setOf_eq]
    constructor
    · intro i
      simpa [implicit_equality_mulVec_apply, implicit_equality_rhs_apply] using
        hx i.1
    · intro i
      simpa [remaining_inequality_mulVec_apply, remaining_inequality_rhs_apply] using
        hx i.1
  · intro hx
    simp only [Set.mem_setOf_eq] at hx
    change A *ᵥ x ≤ b
    intro i
    by_cases hi : i ∈ implicit_equality_indices A b
    · simpa [implicit_equality_mulVec_apply, implicit_equality_rhs_apply] using hx.1 ⟨i, hi⟩
    · have hi' : i ∈ remaining_inequality_indices A b := hi
      simpa [remaining_inequality_mulVec_apply, remaining_inequality_rhs_apply] using hx.2 ⟨i, hi'⟩

/-- Definition 3.7-extra-1 (5). The polyhedron defined by `A *ᵥ x ≤ b` is exactly the set of
points satisfying the implicit-equality subsystem as equations `A^= x = b^=` together with the
remaining subsystem as inequalities. -/
theorem polyhedron_le_set_eq_implicit_eq_and_remaining_subsystems
    :
    polyhedron_le_set A b =
      {x : Fin n → ℝ |
        A^= *ᵥ x = b^= ∧
        remaining_inequality_matrix A b *ᵥ x ≤ remaining_inequality_rhs A b} := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    simp only [Set.mem_setOf_eq]
    constructor
    · funext i
      rw [implicit_equality_mulVec_apply, implicit_equality_rhs_apply]
      exact (mem_implicit_equality_indices_iff A b i.1).1 i.2
        hx
    · intro i
      simpa [remaining_inequality_mulVec_apply, remaining_inequality_rhs_apply] using
        hx i.1
  · intro hx
    simp only [Set.mem_setOf_eq] at hx
    have hx' :
        x ∈ {x : Fin n → ℝ |
          A^= *ᵥ x ≤ b^= ∧
          remaining_inequality_matrix A b *ᵥ x ≤ remaining_inequality_rhs A b} := by
      simp only [Set.mem_setOf_eq]
      constructor
      · intro i
        exact le_of_eq <| by simpa using congrArg (fun f ↦ f i) hx.1
      · exact hx.2
    rw [polyhedron_le_set_eq_implicit_and_remaining_subsystems A b]
    exact hx'

end ImplicitEqualitySurface

/-- Definition 3.7-extra-1 (6). Every remaining inequality is strict at some point of the
polyhedron `polyhedron_le_set A b`. -/
theorem exists_mem_polyhedron_le_set_lt_of_mem_remaining_inequality_indices
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i : Fin m)
    (hi : i ∈ remaining_inequality_indices A b) :
    ∃ x : Fin n → ℝ, x ∈ polyhedron_le_set A b ∧ (A *ᵥ x) i < b i := by
  classical
  have hnot_implicit : ¬ is_implicit_equality A b i := by
    exact (mem_remaining_inequality_indices_iff A b i).1 hi
  have hwitness :
      ∃ x : Fin n → ℝ, A *ᵥ x ≤ b ∧ (A *ᵥ x) i ≠ b i := by
    by_contra hwitness
    apply hnot_implicit
    intro x hx
    by_contra hneq
    exact hwitness ⟨x, hx, hneq⟩
  rcases hwitness with ⟨x, hx, hneq⟩
  refine ⟨x, hx, ?_⟩
  exact lt_of_le_of_ne (hx i) hneq

/-- Definition 3.7-extra-1 (7). If the polyhedron `polyhedron_le_set A b` is empty,
then the set of remaining inequalities is empty. -/
theorem remaining_inequality_indices_eq_empty_of_polyhedron_le_set_eq_empty
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP : polyhedron_le_set A b = (∅ : Set (Fin n → ℝ))) :
    remaining_inequality_indices A b = (∅ : Set (Fin m)) := by
  ext i
  constructor
  · intro hi
    rw [Set.mem_empty_iff_false]
    rcases
        exists_mem_polyhedron_le_set_lt_of_mem_remaining_inequality_indices
          A b i hi with
      ⟨x, hx, _⟩
    exact by rwa [hP] at hx
  · intro hi
    simp at hi
