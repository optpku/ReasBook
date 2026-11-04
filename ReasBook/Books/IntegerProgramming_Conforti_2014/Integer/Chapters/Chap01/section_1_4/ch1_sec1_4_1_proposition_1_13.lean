/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_4.ch1_sec1_4_1_definition_1_32
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_4.ch1_sec1_4_1_proposition_1_5

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_1_proposition_1_13.lean.
Proposition 1.13. The convex hull of `mixedIntegerStrip β` is cut out by the original
inequality, the mixed-integer cut with fractional part `Int.fract β`, and the nonnegativity
constraint on the second coordinate. -/
theorem convexHull_mixedIntegerStrip_eq
    (β : ℝ) :
    convexHull ℝ (mixedIntegerStrip β) =
      {p : ℝ × ℝ |
        p.1 - p.2 ≤ β ∧
          p.1 - p.2 / (1 - Int.fract β) ≤ (⌊β⌋ : ℝ) ∧
          0 ≤ p.2} := by
  -- Identify the named mixed-integer strip with the explicit source set of Proposition 1.5.
  have hsource :
      mixedIntegerStrip β =
        {p : ℝ × ℝ |
          p.1 ∈ Set.range (fun z : ℤ ↦ (z : ℝ)) ∧
            0 ≤ p.2 ∧
            p.1 - p.2 ≤ β} := by
    ext p
    simp only [mem_mixedIntegerStrip_iff, Set.mem_setOf_eq]
  -- Transport the established convex-hull formula across this presentation equality.
  rw [hsource]
  exact convexHull_mixed_integer_strip_eq β

#print axioms convexHull_mixedIntegerStrip_eq
