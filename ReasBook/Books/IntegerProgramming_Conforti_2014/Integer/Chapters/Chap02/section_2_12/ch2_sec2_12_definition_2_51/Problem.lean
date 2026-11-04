/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Image

public section

/-- A `0`--`1` polynomial program with objective polynomial `f` and equality-constraint
polynomials `g_i` in `n` binary variables. -/
structure ZeroOnePolynomialProgram (m n : ℕ) where
  objective : MvPolynomial (Fin n) ℝ
  constraints : Fin m → MvPolynomial (Fin n) ℝ

namespace ZeroOnePolynomialProgram

/-- Construct a `0`--`1` polynomial program from its objective polynomial and constraint
polynomials. -/
def ofPolynomials
    {m n : ℕ}
    (objective : MvPolynomial (Fin n) ℝ)
    (constraints : Fin m → MvPolynomial (Fin n) ℝ) :
    ZeroOnePolynomialProgram m n :=
  { objective := objective
    constraints := constraints }

/-- The feasible points of `P` are the real vectors that satisfy every equality constraint and
have only binary coordinates. -/
def feasibleSet
    {m n : ℕ}
    (P : ZeroOnePolynomialProgram m n) : Set (Fin n → ℝ) :=
  {x | (∀ i : Fin m, MvPolynomial.eval x (P.constraints i) = 0) ∧
      (∀ j : Fin n, x j = 0 ∨ x j = 1)}

/-- Membership in `P.feasibleSet` is exactly the conjunction of polynomial equality constraints
and binary coordinate conditions. -/
theorem mem_feasibleSet_iff
    {m n : ℕ}
    {P : ZeroOnePolynomialProgram m n}
    {x : Fin n → ℝ} :
    x ∈ P.feasibleSet ↔
      (∀ i : Fin m, MvPolynomial.eval x (P.constraints i) = 0) ∧
        (∀ j : Fin n, x j = 0 ∨ x j = 1) := by
  -- Unfold `feasibleSet`; membership in the set-builder is exactly the displayed conjunction.
  rfl

/-- The objective value of `x` for `P` is the evaluation of the objective polynomial at `x`. -/
noncomputable def objectiveValue
    {m n : ℕ}
    (P : ZeroOnePolynomialProgram m n)
    (x : Fin n → ℝ) : ℝ :=
  MvPolynomial.eval x P.objective

/-- Unfolding equation for `P.objectiveValue x`. -/
theorem objectiveValue_def
    {m n : ℕ}
    (P : ZeroOnePolynomialProgram m n)
    (x : Fin n → ℝ) :
    P.objectiveValue x = MvPolynomial.eval x P.objective := by
  -- Unfold `objectiveValue`; the theorem is its defining equation.
  rfl

/-- The set of objective values attained by feasible binary points of `P`. -/
noncomputable def objectiveValues
    {m n : ℕ}
    (P : ZeroOnePolynomialProgram m n) : Set ℝ :=
  P.objectiveValue '' P.feasibleSet

/-- Membership in `P.objectiveValues` means that some feasible binary vector attains the value
`r`. -/
theorem mem_objectiveValues_iff
    {m n : ℕ}
    {P : ZeroOnePolynomialProgram m n}
    {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ x : Fin n → ℝ, x ∈ P.feasibleSet ∧ P.objectiveValue x = r := by
  -- Rewrite membership in the image set into the existence of a feasible preimage.
  simp [objectiveValues, Set.mem_image]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_12/ch2_sec2_12_definition_2_51/Problem.lean

Membership in `P.objectiveValues` is equivalent to the existence of a feasible binary vector
attaining the value `r`. -/
theorem mem_objectiveValues_iff_exists_feasible
    {m n : ℕ}
    {P : ZeroOnePolynomialProgram m n}
    {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ x : Fin n → ℝ, x ∈ P.feasibleSet ∧ P.objectiveValue x = r := by
  -- This is exactly the witness form already proved in `mem_objectiveValues_iff`.
  exact mem_objectiveValues_iff

end ZeroOnePolynomialProgram

end
