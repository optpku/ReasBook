/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_definition_2_55.StableSetCovering

public section

/-
Proposition 2.26 [Comparison of LP relaxations]: the printed `χ₂` relaxation is source-blocked.
Its inequalities are imposed on every nonempty stable set, so singleton stable sets force
`∀ v, 1 ≤ y v`, which in turn yields the spurious lower bound `(Fintype.card V : ℝ) ≤ ∑ v, y v`.
Until the source model is corrected upstream, this item should not introduce a comparison theorem.
The stable-set-covering formulation from Definition 2.55 remains the canonical repository owner
for the intended graph-coloring LP data.
-/
#check SimpleGraph.StableSetColoring.objectiveValues

end
