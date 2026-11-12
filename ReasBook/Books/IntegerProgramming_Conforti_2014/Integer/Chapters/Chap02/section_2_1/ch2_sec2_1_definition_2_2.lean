/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_1.ch2_sec2_1_definition_2_2.Problem

/-!
Definition 2.2.

The reusable owner `KnapsackProblem` and its feasible/objective API live in the item-local
foundation module imported above. This file keeps the labeled source-facing entry.
-/

/- Definition 2.2: the knapsack problem owner and its core feasible/objective surfaces. -/
#check KnapsackProblem
#check KnapsackProblem.feasibleSet
#check KnapsackProblem.objectiveValue
#check KnapsackProblem.objectiveValues
#check KnapsackProblem.toPureIntegerLinearProgram

namespace KnapsackProblem

/-- Helper for Definition 2.2: `P.objectiveValues` is the set of real values attained by
feasible integer vectors. -/
lemma objectiveValues_eq_setOf_exists_feasible
    {n : ℕ}
    (P : KnapsackProblem n) :
    P.objectiveValues =
      {r : ℝ | ∃ x : Fin n → ℤ, x ∈ P.feasibleSet ∧ P.objectiveValue x = r} := by
  -- Extensionality reduces the set equality to the owner's membership characterization.
  ext r
  exact mem_objectiveValues_iff_exists_feasible

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_1/ch2_sec2_1_definition_2_2.lean.
Definition 2.2: A real number belongs to `P.objectiveValues` exactly when some feasible integer
vector of the knapsack problem `P` attains it. -/
theorem mem_objectiveValues_iff
    {n : ℕ}
    {P : KnapsackProblem n}
    {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ x : Fin n → ℤ, x ∈ P.feasibleSet ∧ P.objectiveValue x = r := by
  -- Rewrite the objective-value set to its extensional attained-value description.
  rw [objectiveValues_eq_setOf_exists_feasible]
  -- Membership in the resulting set-builder is definitionally its predicate.
  rfl

end KnapsackProblem
