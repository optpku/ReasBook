/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

open scoped BigOperators

/-- The objective values in the source definition of the lifting function for an ordered flow-cover
`C`. The coordinate `a i` represents the ordered coefficient `a_{j_{i+1}}`. -/
def flow_cover_lifting_objective_values
    {t : ℕ} (b lam : ℝ) (a : Fin t → ℝ) (z : ℝ) : Set ℝ :=
  {v | ∃ x : Fin t → Bool, ∃ y : Fin t → ℝ,
      (∀ i, 0 ≤ y i) ∧
        (∑ i, y i) ≤ b - z ∧
        (∀ i, y i ≤ a i * (if x i then (1 : ℝ) else 0)) ∧
          v =
            ∑ i, (y i + max (a i - lam) 0 * (1 - if x i then (1 : ℝ) else 0))}

/-- Membership in `flow_cover_lifting_objective_values b λ a z` is the feasibility-and-objective
condition from the source maximization formula defining the lifting function. -/
@[simp] theorem mem_flow_cover_lifting_objective_values_iff
    {t : ℕ} (b lam : ℝ) (a : Fin t → ℝ) (z v : ℝ) :
    v ∈ flow_cover_lifting_objective_values b lam a z ↔
      ∃ x : Fin t → Bool, ∃ y : Fin t → ℝ,
        (∀ i, 0 ≤ y i) ∧
          (∑ i, y i) ≤ b - z ∧
          (∀ i, y i ≤ a i * (if x i then (1 : ℝ) else 0)) ∧
            v =
              ∑ i, (y i + max (a i - lam) 0 * (1 - if x i then (1 : ℝ) else 0)) := Iff.rfl

/-- The lifting function for an ordered flow-cover, defined as `b` minus the supremum of the
source optimization problem. -/
noncomputable def flow_cover_lifting_function
    {t : ℕ} (b lam : ℝ) (a : Fin t → ℝ) (z : ℝ) : ℝ :=
  b - sSup (flow_cover_lifting_objective_values b lam a z)

end
