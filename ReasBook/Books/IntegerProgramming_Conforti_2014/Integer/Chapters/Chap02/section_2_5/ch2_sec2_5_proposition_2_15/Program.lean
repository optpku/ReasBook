/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Data.Set.Image
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_5.ch2_sec2_5_definition_2_30
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_5.ch2_sec2_5_definition_2_31.ZeroOneILP

open scoped Matrix

namespace InferenceIP

/-- The binary integer program attached to the clause matrix `A`. -/
def program {m n : ℕ} (A : SAT.ClauseMatrix m n) : ZeroOneILPInstance :=
  (SAT.ClauseMatrix.toInstance A).toZeroOneILP

/-- The feasible `0/1` vectors of the inference program attached to `A`. -/
def feasibleSet {m n : ℕ} (A : SAT.ClauseMatrix m n) : Set (Fin n → ℤ) :=
  (program A).feasibleSet

/-- Membership in `feasibleSet A` is exactly binary feasibility for the translated inference
program `program A`. -/
theorem mem_feasibleSet_iff
    {m n : ℕ} {A : SAT.ClauseMatrix m n} {x : Fin n → ℤ} :
    x ∈ feasibleSet A ↔
      (∀ j, x j = 0 ∨ x j = 1) ∧ (program A).matrix *ᵥ x ≤ (program A).rhs := by
  exact ZeroOneILPInstance.mem_feasibleSet_iff (program A) x

/-- Every vector in `feasibleSet A` has binary coordinates. -/
theorem feasible_binary
    {m n : ℕ} {A : SAT.ClauseMatrix m n} {x : Fin n → ℤ}
    (hx : x ∈ feasibleSet A) (j : Fin n) :
    x j = 0 ∨ x j = 1 :=
  (mem_feasibleSet_iff.mp hx).1 j

/-- The clause-objective values attained on the feasible set of the inference program attached
to `A`. -/
def objectiveValues {m n : ℕ} (A : SAT.ClauseMatrix m n) (C : SAT.Clause n) : Set ℤ :=
  C.objective '' feasibleSet A

/-- Membership in `objectiveValues A C` means that some feasible binary vector for the inference
program attached to `A` attains the clause objective value `r`. -/
theorem mem_objectiveValues_iff
    {m n : ℕ} {A : SAT.ClauseMatrix m n} {C : SAT.Clause n} {r : ℤ} :
    r ∈ objectiveValues A C ↔
      ∃ x : Fin n → ℤ, x ∈ feasibleSet A ∧ C.objective x = r := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

end InferenceIP
