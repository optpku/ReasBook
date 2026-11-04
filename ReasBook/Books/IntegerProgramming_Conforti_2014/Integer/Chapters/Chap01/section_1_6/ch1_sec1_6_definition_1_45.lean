/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_1.Problem
import Mathlib.LinearAlgebra.Matrix.Notation

open scoped Matrix

/- Definition 1.45 (1). A pure integer linear program is formalized by the reusable owner
`PureIntegerLinearProgram`, whose feasible-set API presents the canonical `max`/`≤` form; the
source `min`/`≥` presentation is recovered by negating objective and constraint data. -/
#check PureIntegerLinearProgram
#check PureIntegerLinearProgram.ofCoefficients
#check PureIntegerLinearProgram.feasibleSet
#check PureIntegerLinearProgram.mem_feasibleSet_iff

namespace OrderedCover

/-- Definition 1.45 (2). The displayed optimization problem in variables `(y, x1, x2, x3)` is the
closed pure integer linear program obtained by negating the source minimization objective and the
three covering inequalities into the canonical `max`/`≤` PILP format. -/
noncomputable def pilpExample : PureIntegerLinearProgram 3 4 :=
  PureIntegerLinearProgram.ofCoefficients
    ![(-8 : ℝ), -3, -4, -2]
    !![(-1 : ℝ), -1, 0, 0;
      -1, 0, -1, 0;
      -1, 0, 0, -1]
    ![-((1 : ℝ) / 5), -((4 : ℝ) / 5), -((3 : ℝ) / 2)]

/-- Package the source integer coordinates `(y, x1, x2, x3)` as a vector in `Fin 4 → ℤ`. -/
def integerPoint (y x1 x2 x3 : ℤ) : Fin 4 → ℤ :=
  ![y, x1, x2, x3]

/-- Helper for Definition 1.45: the three matrix rows of `pilpExample` are precisely the
displayed covering inequalities. -/
private lemma integerPoint_satisfies_pilpExample_constraints_iff
    (y x1 x2 x3 : ℤ) :
    pilpExample.constraintMatrix *ᵥ (fun i ↦ (integerPoint y x1 x2 x3 i : ℝ)) ≤
        pilpExample.constraintRhs ↔
      (1 / 5 : ℝ) ≤ (y : ℝ) + x1 ∧
        (4 / 5 : ℝ) ≤ (y : ℝ) + x2 ∧
        (3 / 2 : ℝ) ≤ (y : ℝ) + x3 := by
  constructor
  · intro hconstraints
    -- Normalize each of the three owner rows and reverse its negated inequality.
    refine ⟨?_, ?_, ?_⟩
    · have hrow := hconstraints 0
      simp [pilpExample, PureIntegerLinearProgram.ofCoefficients, integerPoint,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hrow
      simpa [add_comm] using hrow
    · have hrow := hconstraints 1
      simp [pilpExample, PureIntegerLinearProgram.ofCoefficients, integerPoint,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hrow
      simpa [add_comm] using hrow
    · have hrow := hconstraints 2
      simp [pilpExample, PureIntegerLinearProgram.ofCoefficients, integerPoint,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hrow
      simpa [add_comm] using hrow
  · rintro ⟨hfirst, hsecond, hthird⟩ i
    -- Enumerate the finite row index and rebuild each canonical negated constraint.
    fin_cases i
    · simpa [pilpExample, PureIntegerLinearProgram.ofCoefficients, integerPoint,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_comm] using neg_le_neg hfirst
    · simpa [pilpExample, PureIntegerLinearProgram.ofCoefficients, integerPoint,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_comm] using neg_le_neg hsecond
    · simpa [pilpExample, PureIntegerLinearProgram.ofCoefficients, integerPoint,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_comm] using neg_le_neg hthird

/-- Helper for Definition 1.45: nonnegativity of the cast tuple is equivalent to nonnegativity of
its four integer coordinates. -/
private lemma integerPoint_cast_nonnegative_iff
    (y x1 x2 x3 : ℤ) :
    (0 : Fin 4 → ℝ) ≤ (fun i ↦ (integerPoint y x1 x2 x3 i : ℝ)) ↔
      0 ≤ y ∧ 0 ≤ x1 ∧ 0 ≤ x2 ∧ 0 ≤ x3 := by
  constructor
  · intro hnonnegative
    -- Read the pointwise real inequalities at the four coordinates and remove the casts.
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hy : (0 : ℝ) ≤ (y : ℝ) := by
        simpa [integerPoint] using hnonnegative 0
      exact_mod_cast hy
    · have hx1 : (0 : ℝ) ≤ (x1 : ℝ) := by
        simpa [integerPoint] using hnonnegative 1
      exact_mod_cast hx1
    · have hx2 : (0 : ℝ) ≤ (x2 : ℝ) := by
        simpa [integerPoint] using hnonnegative 2
      exact_mod_cast hx2
    · have hx3 : (0 : ℝ) ≤ (x3 : ℝ) := by
        simpa [integerPoint] using hnonnegative 3
      exact_mod_cast hx3
  · rintro ⟨hy, hx1, hx2, hx3⟩ i
    -- Enumerate the tuple coordinate and transport each integer inequality to `ℝ`.
    fin_cases i
    · have hy' : (0 : ℝ) ≤ (y : ℝ) := by
        exact_mod_cast hy
      simpa [integerPoint] using hy'
    · have hx1' : (0 : ℝ) ≤ (x1 : ℝ) := by
        exact_mod_cast hx1
      simpa [integerPoint] using hx1'
    · have hx2' : (0 : ℝ) ≤ (x2 : ℝ) := by
        exact_mod_cast hx2
      simpa [integerPoint] using hx2'
    · have hx3' : (0 : ℝ) ≤ (x3 : ℝ) := by
        exact_mod_cast hx3
      simpa [integerPoint] using hx3'

/-- Helper for Definition 1.45: every coordinate of the cast integer tuple has an integer
witness. -/
private lemma integerPoint_cast_hasIntegralCoordinates
    (y x1 x2 x3 : ℤ) :
    ∀ j : Fin 4, ∃ z : ℤ, (integerPoint y x1 x2 x3 j : ℝ) = (z : ℝ) := by
  intro j
  -- Use the corresponding integer coordinate itself as the lattice witness.
  exact ⟨integerPoint y x1 x2 x3 j, rfl⟩

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_definition_1_45.lean.
Membership of the integer source point `(y, x1, x2, x3)` in `pilpExample.feasibleSet` is
exactly the displayed nonnegativity and covering system from Definition 1.45. -/
theorem integerPoint_mem_pilpExample_feasibleSet_iff
    (y x1 x2 x3 : ℤ) :
    (fun i ↦ (integerPoint y x1 x2 x3 i : ℝ)) ∈ pilpExample.feasibleSet ↔
      0 ≤ y ∧
        0 ≤ x1 ∧
        0 ≤ x2 ∧
        0 ≤ x3 ∧
        (1 / 5 : ℝ) ≤ (y : ℝ) + x1 ∧
        (4 / 5 : ℝ) ≤ (y : ℝ) + x2 ∧
        (3 / 2 : ℝ) ≤ (y : ℝ) + x3 := by
  constructor
  · intro hmem
    -- Unpack owner feasibility, then translate its first two components through the interfaces.
    rcases (pilpExample.mem_feasibleSet_iff _).mp hmem with
      ⟨hconstraints, hnonnegative, _⟩
    rcases (integerPoint_cast_nonnegative_iff y x1 x2 x3).mp hnonnegative with
      ⟨hy, hx1, hx2, hx3⟩
    rcases (integerPoint_satisfies_pilpExample_constraints_iff y x1 x2 x3).mp hconstraints with
      ⟨hfirst, hsecond, hthird⟩
    exact ⟨hy, hx1, hx2, hx3, hfirst, hsecond, hthird⟩
  · rintro ⟨hy, hx1, hx2, hx3, hfirst, hsecond, hthird⟩
    -- Reassemble the owner constraints, nonnegativity, and automatic integrality witnesses.
    refine (pilpExample.mem_feasibleSet_iff _).mpr ⟨?_, ?_, ?_⟩
    · exact (integerPoint_satisfies_pilpExample_constraints_iff y x1 x2 x3).mpr
        ⟨hfirst, hsecond, hthird⟩
    · exact (integerPoint_cast_nonnegative_iff y x1 x2 x3).mpr ⟨hy, hx1, hx2, hx3⟩
    · exact integerPoint_cast_hasIntegralCoordinates y x1 x2 x3

end OrderedCover
