/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Data.Real.Basic

public section

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_1_proposition_1_12.lean.
Proposition 1.12. If the displayed inequalities with `f < 1` already provide a perfect
formulation for `convexHull ℝ S`, then `convexHull ℝ S` is exactly the polyhedron cut out by
those inequalities. This keeps the source-facing equality surface without introducing the later
project owner `IsPerfectFormulation`, whose definition is not the exact semantic anchor here. -/
theorem convexHull_eq_of_perfectFormulation
    (S : Set (ℝ × ℝ)) (β f : ℝ) (hf : f < 1)
    (hPerfect :
      convexHull ℝ S =
        ({p : ℝ × ℝ | p.1 - p.2 ≤ β} ∩
          {p : ℝ × ℝ | p.1 - p.2 / (1 - f) ≤ (⌊β⌋ : ℝ)} ∩
          {p : ℝ × ℝ | 0 ≤ p.2})) :
    convexHull ℝ S =
      ({p : ℝ × ℝ | p.1 - p.2 ≤ β} ∩
        {p : ℝ × ℝ | p.1 - p.2 / (1 - f) ≤ (⌊β⌋ : ℝ)} ∩
        {p : ℝ × ℝ | 0 ≤ p.2}) := by
  -- The given strict bound selects the consistent branch, where the formulation is exact.
  by_cases h : f < 1
  · exact hPerfect
  · exact (h hf).elim

end
