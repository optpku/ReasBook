/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

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
