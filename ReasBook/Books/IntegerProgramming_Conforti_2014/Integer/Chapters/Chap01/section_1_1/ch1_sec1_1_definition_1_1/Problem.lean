import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.MixedSpace
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1.MatrixPolyhedron

open scoped IntegerVectorNotation Matrix

section Definition11

variable {m n : ℕ}

/-- Definition 1.1 (1): a pure integer linear program packages the objective vector `c`,
constraint matrix `A`, and right-hand side `b` for the source problem
`max c x` subject to `A x ≤ b` and `x ∈ ℤ_+^n`. -/
structure PureIntegerLinearProgram (m n : ℕ) where
  objective : Fin n → ℝ
  constraintMatrix : Matrix (Fin m) (Fin n) ℝ
  constraintRhs : Fin m → ℝ

namespace PureIntegerLinearProgram

/-- Construct a pure integer linear program from its coefficient data. -/
def ofCoefficients
    (objective : Fin n → ℝ)
    (constraintMatrix : Matrix (Fin m) (Fin n) ℝ)
    (constraintRhs : Fin m → ℝ) :
    PureIntegerLinearProgram m n :=
  { objective := objective
    constraintMatrix := constraintMatrix
    constraintRhs := constraintRhs }

end PureIntegerLinearProgram

/-- Definition 1.1 (2): the pure integer linear set
`{x | A *ᵥ x ≤ b ∧ 0 ≤ x ∧ x ∈ ℤ^n}`. -/
def pureIntegerLinearSet
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  polyhedron_le_set A b ∩ Set.Ici (0 : Fin n → ℝ) ∩ ℤ^n

/-- Membership in `pureIntegerLinearSet A b` means satisfying `A *ᵥ x ≤ b`, nonnegativity, and
integrality in the canonical lattice owner `ℤ^n`. -/
theorem mem_pureIntegerLinearSet_iff_mem_integerVectors
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (x : Fin n → ℝ) :
    x ∈ pureIntegerLinearSet A b ↔
      A *ᵥ x ≤ b ∧ 0 ≤ x ∧ x ∈ ℤ^n := by
  rw [pureIntegerLinearSet, Set.mem_inter_iff, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨hAx, hx_nonneg⟩, hx_int⟩
    exact ⟨hAx, hx_nonneg, hx_int⟩
  · rintro ⟨hAx, hx_nonneg, hx_int⟩
    exact ⟨⟨hAx, hx_nonneg⟩, hx_int⟩

/-- Membership in `pureIntegerLinearSet A b` is exactly the source system `A *ᵥ x ≤ b`,
`0 ≤ x`, and coordinatewise integrality. -/
theorem mem_pureIntegerLinearSet_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (x : Fin n → ℝ) :
    x ∈ pureIntegerLinearSet A b ↔
      A *ᵥ x ≤ b ∧ 0 ≤ x ∧ ∀ j : Fin n, ∃ z : ℤ, x j = (z : ℝ) := by
  rw [mem_pureIntegerLinearSet_iff_mem_integerVectors, mem_integerVectors_iff_forall]
  simp [Set.mem_range, eq_comm]

namespace PureIntegerLinearProgram

/-- The feasible set of a pure integer linear program. -/
def feasibleSet
    (P : PureIntegerLinearProgram m n) : Set (Fin n → ℝ) :=
  pureIntegerLinearSet P.constraintMatrix P.constraintRhs

/-- `P.feasibleSet` is the canonical pure integer linear set cut out by the coefficient data of
`P`. -/
theorem feasibleSet_eq_pureIntegerLinearSet
    (P : PureIntegerLinearProgram m n) :
    P.feasibleSet = pureIntegerLinearSet P.constraintMatrix P.constraintRhs :=
  rfl

/-- Membership in `P.feasibleSet` means satisfying the matrix inequalities, nonnegativity, and the
canonical integrality condition `x ∈ ℤ^n`. -/
theorem mem_feasibleSet_iff_mem_integerVectors
    (P : PureIntegerLinearProgram m n)
    (x : Fin n → ℝ) :
    x ∈ P.feasibleSet ↔
      P.constraintMatrix *ᵥ x ≤ P.constraintRhs ∧ 0 ≤ x ∧ x ∈ ℤ^n := by
  simpa [feasibleSet] using
    mem_pureIntegerLinearSet_iff_mem_integerVectors P.constraintMatrix P.constraintRhs x

/-- Membership in `P.feasibleSet` is exactly the source feasibility system attached to `P`. -/
theorem mem_feasibleSet_iff
    (P : PureIntegerLinearProgram m n)
    (x : Fin n → ℝ) :
    x ∈ P.feasibleSet ↔
      P.constraintMatrix *ᵥ x ≤ P.constraintRhs ∧
        0 ≤ x ∧ ∀ j : Fin n, ∃ z : ℤ, x j = (z : ℝ) := by
  simpa [feasibleSet] using
    mem_pureIntegerLinearSet_iff P.constraintMatrix P.constraintRhs x

end PureIntegerLinearProgram

end Definition11
