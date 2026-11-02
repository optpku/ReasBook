import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

open scoped Matrix

/-- The polyhedron in `ℝ^n` cut out by the linear system `A *ᵥ x ≤ b`. This source-facing owner
is kept in the Section 3.6 definition layer so later files can reuse the matrix presentation
without importing larger recession-cone developments. -/
def polyhedron_le_set {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Set (Fin n → ℝ) :=
  {x : Fin n → ℝ | A *ᵥ x ≤ b}

/-- Membership in `polyhedron_le_set A b` unfolds to the defining system of inequalities. -/
theorem mem_polyhedron_le_set_iff
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ} :
    x ∈ polyhedron_le_set A b ↔ A *ᵥ x ≤ b :=
  Iff.rfl
