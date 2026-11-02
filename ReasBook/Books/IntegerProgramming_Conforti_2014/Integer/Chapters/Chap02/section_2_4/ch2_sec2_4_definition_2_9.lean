module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_definition_2_9.Optimization

public section

/-!
Definition 2.9 [Set packing/partitioning/covering optimization problems]. For a family
`family : Fin m → Finset (Fin n)` and a weight vector `w : Fin n → ℝ`, the source optimization
problems are formalized by the feasible-set owners
`SetFamilyOptimization.packingFeasibleSet family`,
`SetFamilyOptimization.partitioningFeasibleSet family`,
`SetFamilyOptimization.coveringFeasibleSet family`, the common linear objective
`SetFamilyOptimization.objective w`, and the attained-value sets
`SetFamilyOptimization.packingObjectiveValues family w`,
`SetFamilyOptimization.partitioningObjectiveValues family w`,
`SetFamilyOptimization.coveringObjectiveValues family w`.
-/

/- Definition 2.9 [Set packing/partitioning/covering optimization problems]: maximizing
`SetFamilyOptimization.objective w` on `SetFamilyOptimization.packingFeasibleSet family` and
minimizing it on `SetFamilyOptimization.partitioningFeasibleSet family` and
`SetFamilyOptimization.coveringFeasibleSet family` formalizes the three textbook problems. -/

#check SetFamilyOptimization.packingFeasibleSet
#check SetFamilyOptimization.partitioningFeasibleSet
#check SetFamilyOptimization.coveringFeasibleSet
#check SetFamilyOptimization.mem_packingFeasibleSet_iff
#check SetFamilyOptimization.mem_partitioningFeasibleSet_iff
#check SetFamilyOptimization.mem_coveringFeasibleSet_iff
#check SetFamilyOptimization.objective
#check SetFamilyOptimization.objective_def
#check SetFamilyOptimization.packingObjectiveValues
#check SetFamilyOptimization.partitioningObjectiveValues
#check SetFamilyOptimization.coveringObjectiveValues

/- The attained-value sets above have the expected source-facing companion characterizations:
membership means that some feasible `0,1` vector attains the displayed objective value. -/
#check SetFamilyOptimization.mem_packingObjectiveValues_iff
#check SetFamilyOptimization.mem_partitioningObjectiveValues_iff
#check SetFamilyOptimization.mem_coveringObjectiveValues_iff
