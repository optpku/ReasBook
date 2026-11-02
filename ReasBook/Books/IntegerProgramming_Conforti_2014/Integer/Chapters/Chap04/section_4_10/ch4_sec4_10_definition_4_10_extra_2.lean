import Mathlib
import Mathlib.Algebra.Order.Ring.Basic

open scoped Matrix

section LinearExtendedSystem

variable {ι κ ρ σ : Type*}
variable [Fintype ι] [Fintype κ]

/-- The lifted feasible set of a linear system with equality rows
`Aeq x + Beq z = beq` and inequality rows `Aineq x + Bineq z ≤ bineq`, indexed by arbitrary
finite types. This source-facing owner is kept in the Section 4.10 definition layer because the
later extension-complexity theorems reuse the same lifted feasible-set notion. -/
def linear_extended_system
    (Aeq : Matrix ρ ι ℝ)
    (Beq : Matrix ρ κ ℝ)
    (beq : ρ → ℝ)
    (Aineq : Matrix σ ι ℝ)
    (Bineq : Matrix σ κ ℝ)
    (bineq : σ → ℝ) : Set ((ι → ℝ) × (κ → ℝ)) :=
  {xz |
    Aeq.mulVec xz.1 + Beq.mulVec xz.2 = beq ∧
      Aineq.mulVec xz.1 + Bineq.mulVec xz.2 ≤ bineq}

/-- Membership in `linear_extended_system Aeq Beq beq Aineq Bineq bineq` unfolds to the defining
equality and inequality blocks. -/
theorem mem_linear_extended_system_iff
    {Aeq : Matrix ρ ι ℝ}
    {Beq : Matrix ρ κ ℝ}
    {beq : ρ → ℝ}
    {Aineq : Matrix σ ι ℝ}
    {Bineq : Matrix σ κ ℝ}
    {bineq : σ → ℝ}
    {xz : (ι → ℝ) × (κ → ℝ)} :
    xz ∈ linear_extended_system Aeq Beq beq Aineq Bineq bineq ↔
      Aeq.mulVec xz.1 + Beq.mulVec xz.2 = beq ∧
        Aineq.mulVec xz.1 + Bineq.mulVec xz.2 ≤ bineq :=
  Iff.rfl

end LinearExtendedSystem

section Ring

variable {R : Type*} [Ring R]

/-- Definition 4.10-extra-2. Given a system `A x ≤ b` describing a polytope whose vertices are
`vertices 0, ..., vertices (p - 1)`, the slack matrix is the matrix whose `(i, j)` entry is the
slack `b i - (A *ᵥ vertices j) i` of the `i`th inequality at the `j`th vertex. -/
def slack_matrix
    {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) R)
    (b : Fin m → R)
    (vertices : Fin p → Fin n → R) :
    Matrix (Fin m) (Fin p) R :=
  fun i j ↦ b i - (A *ᵥ vertices j) i

@[simp] theorem slack_matrix_apply
    {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) R)
    (b : Fin m → R)
    (vertices : Fin p → Fin n → R)
    (i : Fin m)
    (j : Fin p) :
    slack_matrix A b vertices i j = b i - (A *ᵥ vertices j) i :=
  rfl

end Ring

section OrderedRing

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]

/-- If every listed vertex satisfies the system `A x ≤ b`, then every entry of the slack matrix is
nonnegative. -/
theorem slack_matrix_nonneg
    {m n p : ℕ}
    {A : Matrix (Fin m) (Fin n) R}
    {b : Fin m → R}
    {vertices : Fin p → Fin n → R}
    (hvertices : ∀ j, A *ᵥ vertices j ≤ b) :
    ∀ i j, 0 ≤ slack_matrix A b vertices i j := by
  intro i j
  dsimp [slack_matrix]
  exact sub_nonneg.mpr (hvertices j i)

end OrderedRing
