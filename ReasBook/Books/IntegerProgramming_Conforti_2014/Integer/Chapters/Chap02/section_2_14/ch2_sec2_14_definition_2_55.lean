module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_definition_2_55.NodeColoring
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_definition_2_55.StableSetCovering

public section

/-!
Integer programming formulations of graph coloring.

This item is formalized by the reusable owner namespaces
`SimpleGraph.StableSetColoring` and `SimpleGraph.NodeColoring`.
-/

/- Definition 2.55 (1) [Integer programming formulations of graph coloring]: the stable-set
set-covering formulation is formalized by the maximal-stable-set family
`SimpleGraph.StableSetColoring.maximalStableSets`, the covering subfamilies
`SimpleGraph.StableSetColoring.maximalStableSetsContaining`, the objective
`SimpleGraph.StableSetColoring.objective`, the feasibility predicate
`SimpleGraph.StableSetColoring.feasible`, and the attained-value set
`SimpleGraph.StableSetColoring.objectiveValues`. -/
#check SimpleGraph.StableSetColoring.maximalStableSets
#check SimpleGraph.StableSetColoring.mem_maximalStableSets_iff
#check SimpleGraph.StableSetColoring.maximalStableSetsContaining
#check SimpleGraph.StableSetColoring.mem_maximalStableSetsContaining_iff
#check SimpleGraph.StableSetColoring.objective
#check SimpleGraph.StableSetColoring.objective_def
#check SimpleGraph.StableSetColoring.feasible
#check SimpleGraph.StableSetColoring.feasible_iff
#check SimpleGraph.StableSetColoring.objectiveValues
#check SimpleGraph.StableSetColoring.mem_objectiveValues_iff

/- Definition 2.55 (2) [Integer programming formulations of graph coloring]: for an available
color type `C` satisfying the adequacy hypothesis
`Fintype.card C ≥ ENat.toNat G.chromaticNumber`, the source-facing node-color formulation is
recorded by
`SimpleGraph.NodeColoring.mem_objectiveValues_iff_of_card_ge_chromaticNumber`. Its reusable owner
namespace keeps the objective `SimpleGraph.NodeColoring.objective`, the feasibility predicate
`SimpleGraph.NodeColoring.feasible`, the attained-value set
`SimpleGraph.NodeColoring.objectiveValues`, and the coloring bridge declarations
`SimpleGraph.NodeColoring.vertexColorIndicator`,
`SimpleGraph.NodeColoring.usedColorIndicator`, and
`SimpleGraph.NodeColoring.feasible_ofColoring`. -/
#check SimpleGraph.NodeColoring.mem_objectiveValues_iff_of_card_ge_chromaticNumber
#check SimpleGraph.NodeColoring.objective
#check SimpleGraph.NodeColoring.objective_def
#check SimpleGraph.NodeColoring.feasible
#check SimpleGraph.NodeColoring.feasible_iff
#check SimpleGraph.NodeColoring.objectiveValues
#check SimpleGraph.NodeColoring.mem_objectiveValues_iff
#check SimpleGraph.NodeColoring.vertexColorIndicator
#check SimpleGraph.NodeColoring.usedColorIndicator
#check SimpleGraph.NodeColoring.feasible_ofColoring

end
