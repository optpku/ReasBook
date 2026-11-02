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
