import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

/-
Definition 3.3-extra-1 (1) and (2). This file follows the Chapter 3 owner surface
`primal_feasible_region` and `dual_feasible_region` for the primal and dual feasible sets.
-/

/-- Definition 3.3-extra-1 (1). The feasible region of the primal linear program
`max {c ⬝ᵥ x | A *ᵥ x ≤ b}`. -/
def primal_feasible_region {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | A *ᵥ x ≤ b}

/-- Membership in the primal feasible region is the coordinatewise inequality `A *ᵥ x ≤ b`. -/
theorem mem_primal_feasible_region_iff {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    x ∈ primal_feasible_region A b ↔ A *ᵥ x ≤ b := by
  rfl

/-- Definition 3.3-extra-1 (2). The feasible region of the dual linear program
`min {u ⬝ᵥ b | u ᵥ* A = c, 0 ≤ u}`. -/
def dual_feasible_region {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) : Set (Fin m → ℝ) :=
  {u | u ᵥ* A = c ∧ 0 ≤ u}

/-- Membership in the dual feasible region means satisfying `u ᵥ* A = c` and `0 ≤ u`. -/
theorem mem_dual_feasible_region_iff {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (u : Fin m → ℝ) :
    u ∈ dual_feasible_region A c ↔ u ᵥ* A = c ∧ 0 ≤ u := by
  rfl

/-- The set of primal objective values `c ⬝ᵥ x` attained on the primal feasible region. -/
def primal_objective_values {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) : Set ℝ :=
  (fun x : Fin n → ℝ ↦ c ⬝ᵥ x) '' primal_feasible_region A b

/-- The set of dual objective values `u ⬝ᵥ b` attained on the dual feasible region. -/
def dual_objective_values {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) : Set ℝ :=
  (fun u : Fin m → ℝ ↦ u ⬝ᵥ b) '' dual_feasible_region A c

/-- Definition 3.3-extra-1 (3). Strong duality for the primal-dual pair with data `(A, b, c)`
means that whenever both feasible regions are nonempty, the primal optimal value equals the dual
optimal value. -/
def linear_programming_strong_duality {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) : Prop :=
  Set.Nonempty (primal_feasible_region A b) →
    Set.Nonempty (dual_feasible_region A c) →
      sSup (primal_objective_values A b c) = sInf (dual_objective_values A b c)

/-- Strong duality unfolds to equality of the primal and dual optimal values under feasibility. -/
theorem linear_programming_strong_duality_iff {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    linear_programming_strong_duality A b c ↔
      (Set.Nonempty (primal_feasible_region A b) →
        Set.Nonempty (dual_feasible_region A c) →
          sSup (primal_objective_values A b c) = sInf (dual_objective_values A b c)) := by
  -- Unfold the proposition; the right-hand side is exactly its defining body.
  rfl
