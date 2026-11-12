/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_3_definition_2_19.MinimumWeightSet

public section

/-!
Minimum-weight set problem over a family of subsets.

The canonical reusable owners for Definition 2.19 are the subset objective
`MinimumWeightSet.objective`, the attained-value set `MinimumWeightSet.objectiveValues`, and the
optimality predicate `MinimumWeightSet.IsOptimal`. The source-facing companion theorems
`MinimumWeightSet.mem_objectiveValues_iff` and `MinimumWeightSet.isOptimal_iff` expose these
owners in textbook form.
-/

/- Definition 2.19 (Minimum-weight set problem over `R`): for a ground set
`E = {1, ..., n}`, nonnegative weights `w : Fin n → NNReal`, and a family
`R : Set (Finset (Fin n))`, the problem is formalized by the objective
`MinimumWeightSet.objective w`, the attained-value set
`MinimumWeightSet.objectiveValues w R`, and the optimizer predicate
`MinimumWeightSet.IsOptimal w R`. The companion characterizations
`MinimumWeightSet.mem_objectiveValues_iff` and `MinimumWeightSet.isOptimal_iff` recover the
source-facing existential and pointwise minimum formulations. -/

#check MinimumWeightSet.objective
#check MinimumWeightSet.objectiveValues
#check MinimumWeightSet.IsOptimal
#check MinimumWeightSet.mem_objectiveValues_iff
#check MinimumWeightSet.isOptimal_iff
