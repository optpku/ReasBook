/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Clique

public section

/-!
Clique inequalities.

The canonical owner for the clique notion in Definition 2.13 is
`SimpleGraph.IsClique`.
-/

/- Definition 2.13 [Clique inequality]: a clique of a graph `G` is canonically formalized by
`SimpleGraph.IsClique`, and `SimpleGraph.isClique_iff` states exactly that a subset `K` is a
clique when every two distinct vertices of `K` are adjacent. For a clique `K`, the displayed
inequality `∑ j ∈ K, x j ≤ 1` is called a clique inequality in the source text. -/
#check SimpleGraph.IsClique
#check SimpleGraph.isClique_iff
