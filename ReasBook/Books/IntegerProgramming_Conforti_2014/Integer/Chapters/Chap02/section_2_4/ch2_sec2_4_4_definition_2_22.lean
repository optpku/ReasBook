/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_22.ShortestPathCutLP

public section

/-!
Shortest `s,t`-path linear program via cut constraints.

The reusable owner is `SimpleGraph.ShortestPathCutLP`; the declarations below record the
canonical feasible-region and objective-value API for Definition 2.22.
-/

/- Definition 2.22 (Shortest `s,t`-path linear program via cut constraints): the cut-constraint
feasible region is formalized by `SimpleGraph.ShortestPathCutLP.feasible`, the weighted objective
is `SimpleGraph.ShortestPathCutLP.objective`, and the attained-value set is
`SimpleGraph.ShortestPathCutLP.objectiveValues`. -/
#check SimpleGraph.ShortestPathCutLP.feasible
#check SimpleGraph.ShortestPathCutLP.feasible_iff
#check SimpleGraph.ShortestPathCutLP.objective
#check SimpleGraph.ShortestPathCutLP.objectiveValues
#check SimpleGraph.ShortestPathCutLP.mem_objectiveValues_iff
