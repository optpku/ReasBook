import Mathlib.Data.Matrix.Mul
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.LinearAlgebra.Matrix.DotProduct

open scoped Matrix

section Proposition81

variable {m₁ n : ℕ}

/-- The feasible set of the integer program obtained by intersecting the base set `Q` with the
complicating inequalities `A₁ x ≤ b¹`. -/
def lagrangian_integer_feasible_set
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (Q : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | x ∈ Q ∧ A₁ *ᵥ x ≤ b₁}

/-- `lagrangian_integer_feasible_set A₁ b₁ Q` means exactly that `x ∈ Q` and `A₁ x ≤ b¹`
coordinatewise. -/
theorem mem_lagrangian_integer_feasible_set_iff
    {A₁ : Matrix (Fin m₁) (Fin n) ℝ}
    {b₁ : Fin m₁ → ℝ}
    {Q : Set (Fin n → ℝ)}
    {x : Fin n → ℝ} :
    x ∈ lagrangian_integer_feasible_set A₁ b₁ Q ↔
      x ∈ Q ∧ A₁ *ᵥ x ≤ b₁ :=
  Iff.rfl

/-- The source value `z_I` of the integer program
`max { c x | x ∈ Q, A₁ x ≤ b¹ }`, represented in `EReal` so that infeasible instances have
value `⊥ = -∞` and unbounded-above instances have value `⊤ = +∞`. -/
noncomputable def integer_program_value
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ)) : EReal :=
  sSup
    ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
      lagrangian_integer_feasible_set A₁ b₁ Q)

/-- `integer_program_value A₁ b₁ c Q` is the supremum of the linear objective over the feasible
set `Q ∩ {x | A₁ x ≤ b¹}`. -/
theorem integer_program_value_eq_sSup
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ)) :
    integer_program_value A₁ b₁ c Q =
      sSup
        ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
          lagrangian_integer_feasible_set A₁ b₁ Q) :=
  rfl

/-- The source value `z_LR(λ)` of the Lagrangian relaxation
`max { c x + λ (b¹ - A₁ x) | x ∈ Q }`, represented in `EReal` so that unbounded-above
relaxations have value `⊤ = +∞`. -/
noncomputable def lagrangian_relaxation_value
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (lam : Fin m₁ → ℝ) : EReal :=
  sSup
    ((fun x : Fin n → ℝ ↦
        ((c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) : ℝ) : EReal)) '' Q)

/-- `lagrangian_relaxation_value A₁ b₁ c Q λ` unfolds to the supremum of the penalized objective
over the base set `Q`. -/
theorem lagrangian_relaxation_value_eq_sSup
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (lam : Fin m₁ → ℝ) :
    lagrangian_relaxation_value A₁ b₁ c Q lam =
      sSup
        ((fun x : Fin n → ℝ ↦
            ((c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) : ℝ) : EReal)) '' Q) :=
  rfl

/-- Every point of `Q` contributes one candidate value to `z_LR(λ)`. -/
theorem lagrangian_objective_le_lagrangian_relaxation_value
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (lam : Fin m₁ → ℝ)
    {x : Fin n → ℝ}
    (hx : x ∈ Q) :
    ((c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) : ℝ) : EReal) ≤
      lagrangian_relaxation_value A₁ b₁ c Q lam := by
  -- Unfold `z_LR(λ)` and insert `x` as one admissible point of the supremum set.
  rw [lagrangian_relaxation_value_eq_sSup]
  exact le_sSup ⟨x, hx, rfl⟩

/-- A feasible point has nonnegative Lagrangian penalty whenever the multiplier vector is
componentwise nonnegative. -/
theorem objective_le_lagrangian_objective_of_mem_feasible
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (lam : Fin m₁ → ℝ)
    (hlam : 0 ≤ lam)
    {x : Fin n → ℝ}
    (hx : x ∈ lagrangian_integer_feasible_set A₁ b₁ Q) :
    c ⬝ᵥ x ≤ c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) := by
  have hslack : 0 ≤ b₁ - A₁ *ᵥ x := fun i ↦ sub_nonneg.mpr (hx.2 i)
  exact le_add_of_nonneg_right <| dotProduct_nonneg_of_nonneg hlam hslack

/-- Every feasible point of the integer program contributes a value bounded above by `z_LR(λ)`. -/
theorem objective_le_lagrangian_relaxation_value_of_mem_feasible
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (lam : Fin m₁ → ℝ)
    (hlam : 0 ≤ lam)
    {x : Fin n → ℝ}
    (hx : x ∈ lagrangian_integer_feasible_set A₁ b₁ Q) :
    ((c ⬝ᵥ x : ℝ) : EReal) ≤ lagrangian_relaxation_value A₁ b₁ c Q lam := by
  -- First compare the plain objective to the penalized objective in `ℝ`.
  have hobjective :
      c ⬝ᵥ x ≤ c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) :=
    objective_le_lagrangian_objective_of_mem_feasible A₁ b₁ c Q lam hlam hx
  -- Cast that inequality once to `EReal`, then use the relaxation supremum bound.
  exact
    (show ((c ⬝ᵥ x : ℝ) : EReal) ≤
        ((c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) : ℝ) : EReal) by
      exact_mod_cast hobjective).trans
      (lagrangian_objective_le_lagrangian_relaxation_value A₁ b₁ c Q lam hx.1)

/-- Proposition 8.1 in callable `≤` form: a nonnegative multiplier vector yields a Lagrangian
upper bound on the integer-program value. -/
theorem integer_program_value_le_lagrangian_relaxation_value
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (lam : Fin m₁ → ℝ)
    (hlam : 0 ≤ lam) :
    integer_program_value A₁ b₁ c Q ≤ lagrangian_relaxation_value A₁ b₁ c Q lam := by
  -- Rewrite `z_I` as a supremum over feasible-point objective values.
  rw [integer_program_value_eq_sSup]
  -- Bound each witness in that image set by the pointwise weak-duality estimate.
  refine sSup_le ?_
  rintro _ ⟨x, hx, rfl⟩
  exact objective_le_lagrangian_relaxation_value_of_mem_feasible A₁ b₁ c Q lam hlam hx

/-- Proposition 8.1. For every multiplier vector `λ ∈ ℝ_+^{m₁}`, the Lagrangian relaxation value
`z_LR(λ)` is an upper bound on the integer-program value `z_I`. -/
theorem lagrangian_relaxation_value_ge_integer_program_value
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (lam : Fin m₁ → ℝ)
    (hlam : 0 ≤ lam) :
    lagrangian_relaxation_value A₁ b₁ c Q lam ≥ integer_program_value A₁ b₁ c Q :=
  integer_program_value_le_lagrangian_relaxation_value A₁ b₁ c Q lam hlam

end Proposition81
