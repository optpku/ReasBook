/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_6.ch5_sec5_6_exercise_5_18
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_3.ch8_sec8_3_theorem_8_18

open scoped Matrix

section Exercise818

variable {m p : ℕ}

/-- The source-facing feasibility-cut cone
`C = {u ∈ ℝ^m_+ | u ᵥ* G ≥ 0}`, provided as the Exercise 8.18 name for the Chapter 8 Benders
dual cone. -/
abbrev benders_feasibility_cone
    (G : Matrix (Fin m) (Fin p) ℝ) : Set (Fin m → ℝ) :=
  benders_dual_cone G

/-- Membership in `benders_feasibility_cone G` is exactly the conjunction `u ≥ 0` and
`u ᵥ* G ≥ 0`. -/
theorem mem_benders_feasibility_cone_iff
    (G : Matrix (Fin m) (Fin p) ℝ)
    (u : Fin m → ℝ) :
    u ∈ benders_feasibility_cone G ↔ 0 ≤ u ∧ 0 ≤ u ᵥ* G :=
  mem_benders_dual_cone_iff G u

end Exercise818
