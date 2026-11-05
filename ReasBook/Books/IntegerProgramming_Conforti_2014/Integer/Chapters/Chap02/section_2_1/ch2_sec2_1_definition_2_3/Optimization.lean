/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Data.Set.Image
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Order.Bounds.Defs
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_2.ch2_sec2_2_definition_2_4.KnapsackSet

open scoped Matrix

public section

namespace ZeroOneKnapsack

variable {n : ℕ}

/-- The linear objective value `c x` of a candidate `0`--`1` knapsack vector `x`. -/
def objectiveValue
    (c : Fin n → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  c ⬝ᵥ x

/-- Unfolding equation for `objectiveValue c x`. -/
theorem objectiveValue_def
    (c : Fin n → ℝ)
    (x : Fin n → ℝ) :
    objectiveValue c x = c ⬝ᵥ x := by
  -- Unfolding the wrapper exposes the defining dot product.
  rfl

/-- The attained objective-value set of the `0`--`1` knapsack problem with data `(a, b, c)`. -/
def objectiveValues
    (a : Fin n → ℝ)
    (b : ℝ)
    (c : Fin n → ℝ) : Set ℝ :=
  objectiveValue c '' zero_one_knapsack_set a b

/-- Membership in `objectiveValues a b c` means that some feasible binary vector attains `r`. -/
theorem mem_objectiveValues_iff
    (a : Fin n → ℝ)
    (b : ℝ)
    (c : Fin n → ℝ)
    (r : ℝ) :
    r ∈ objectiveValues a b c ↔
      ∃ x : Fin n → ℝ, x ∈ zero_one_knapsack_set a b ∧ objectiveValue c x = r := by
  -- Membership in the image is definitionally the displayed witness condition.
  rfl

/-- A vector `x` is an optimal solution when it is feasible and its objective value is greatest
in the attained-value set `objectiveValues a b c`. -/
def isOptimalSolution
    (a : Fin n → ℝ)
    (b : ℝ)
    (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Prop :=
  x ∈ zero_one_knapsack_set a b ∧
    IsGreatest (objectiveValues a b c) (objectiveValue c x)

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_1/ch2_sec2_1_definition_2_3/Optimization.lean
The optimality predicate unfolds to feasibility together with greatest attained objective value. -/
theorem isOptimalSolution_iff
    (a : Fin n → ℝ)
    (b : ℝ)
    (c : Fin n → ℝ)
    (x : Fin n → ℝ) :
    isOptimalSolution a b c x ↔
      x ∈ zero_one_knapsack_set a b ∧
        IsGreatest (objectiveValues a b c) (objectiveValue c x) := by
  -- Unfolding optimality exposes its feasibility and maximality components.
  rfl

namespace isOptimalSolution

/-- An optimal `0`--`1` knapsack solution belongs to the feasible set. -/
theorem mem_feasibleSet
    {a : Fin n → ℝ}
    {b : ℝ}
    {c : Fin n → ℝ}
    {x : Fin n → ℝ}
    (hx : isOptimalSolution a b c x) :
    x ∈ zero_one_knapsack_set a b := by
  -- Project feasibility from the public characterization of optimality.
  exact (ZeroOneKnapsack.isOptimalSolution_iff a b c x).mp hx |>.1

/-- An optimal `0`--`1` knapsack solution attains the greatest attained objective value. -/
theorem objectiveIsGreatest
    {a : Fin n → ℝ}
    {b : ℝ}
    {c : Fin n → ℝ}
    {x : Fin n → ℝ}
    (hx : isOptimalSolution a b c x) :
    IsGreatest (objectiveValues a b c) (objectiveValue c x) := by
  -- Project greatestness from the public characterization of optimality.
  exact (ZeroOneKnapsack.isOptimalSolution_iff a b c x).mp hx |>.2

end isOptimalSolution

end ZeroOneKnapsack
