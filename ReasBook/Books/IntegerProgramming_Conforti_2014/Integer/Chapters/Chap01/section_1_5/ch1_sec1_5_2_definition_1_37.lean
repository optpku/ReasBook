module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Matrix.Mul

public section

open scoped Matrix

namespace RationalLinearSystem

variable {m n : ℕ}

/-- The integer vectors solving the rational linear system `A *ᵥ (fun j ↦ (x j : ℚ)) = b`. -/
def integerSolutionSet
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) : Set (Fin n → ℤ) :=
  {x | A *ᵥ (fun j ↦ (x j : ℚ)) = b}

/-- Membership in `integerSolutionSet A b` is exactly the equation
`A *ᵥ (fun j ↦ (x j : ℚ)) = b`. -/
theorem mem_integerSolutionSet_iff
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (x : Fin n → ℤ) :
    x ∈ integerSolutionSet A b ↔ A *ᵥ (fun j ↦ (x j : ℚ)) = b := by
  -- Unfold the set definition so membership becomes the defining equation.
  rfl

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_definition_1_37.lean.
Definition 1.37 (Integer feasibility for a rational linear system). The system `A x = b`
has an integer solution when there exists `x : Fin n → ℤ` with
`A *ᵥ (fun j ↦ (x j : ℚ)) = b`. -/
def hasIntegerSolution
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) : Prop :=
  (integerSolutionSet A b).Nonempty

/-- Expanding `hasIntegerSolution A b` recovers the existence of an integer vector solving
`A *ᵥ (fun j ↦ (x j : ℚ)) = b`. -/
theorem hasIntegerSolution_iff
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    hasIntegerSolution A b ↔ ∃ x : Fin n → ℤ, A *ᵥ (fun j ↦ (x j : ℚ)) = b := by
  -- Expand nonemptiness of the solution set into an explicit integer witness.
  constructor
  · intro h
    rcases h with ⟨x, hx⟩
    exact ⟨x, (mem_integerSolutionSet_iff A b x).mp hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (mem_integerSolutionSet_iff A b x).mpr hx⟩

/-- Two rational systems have the same integer solution set when they satisfy the same solving
equation on every integer vector. -/
theorem integerSolutionSet_ext
    {m' : ℕ}
    {A : Matrix (Fin m) (Fin n) ℚ}
    {b : Fin m → ℚ}
    {A₁ : Matrix (Fin m') (Fin n) ℚ}
    {b₁ : Fin m' → ℚ}
    (h :
      ∀ x : Fin n → ℤ,
        A *ᵥ (fun j ↦ (x j : ℚ)) = b ↔
          A₁ *ᵥ (fun j ↦ (x j : ℚ)) = b₁) :
    integerSolutionSet A b = integerSolutionSet A₁ b₁ := by
  ext x
  simp [integerSolutionSet, h x]

/-- Equality of integer solution sets gives the corresponding equivalence of integer feasibility. -/
theorem hasIntegerSolution_congr
    {m' : ℕ}
    {A : Matrix (Fin m) (Fin n) ℚ}
    {b : Fin m → ℚ}
    {A₁ : Matrix (Fin m') (Fin n) ℚ}
    {b₁ : Fin m' → ℚ}
    (h : integerSolutionSet A b = integerSolutionSet A₁ b₁) :
    hasIntegerSolution A b ↔ hasIntegerSolution A₁ b₁ := by
  simp [hasIntegerSolution, h]

end RationalLinearSystem

end
