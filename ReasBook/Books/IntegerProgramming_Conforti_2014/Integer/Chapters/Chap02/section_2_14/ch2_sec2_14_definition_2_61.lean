import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_definition_2_61.SpanningTreeWithLeaves

/-!
Spanning-tree-with-leaves MILP formulation.

This item is formalized by the reusable owner namespace
`SimpleGraph.SpanningTreeWithLeaves`, with source-facing constraint predicate
`SimpleGraph.SpanningTreeWithLeaves.constraints`, feasibility predicate
`SimpleGraph.SpanningTreeWithLeaves.feasible`, objective
`SimpleGraph.SpanningTreeWithLeaves.objective`, and attained-value set
`SimpleGraph.SpanningTreeWithLeaves.objectiveValues`.
-/

/- Definition 2.61 (Spanning-tree-with-leaves MILP formulation): the textbook edge/leaf
constraints are formalized by `SimpleGraph.SpanningTreeWithLeaves.constraints`, feasibility by
`SimpleGraph.SpanningTreeWithLeaves.feasible`, the objective by
`SimpleGraph.SpanningTreeWithLeaves.objective`, and the attained-value set by
`SimpleGraph.SpanningTreeWithLeaves.objectiveValues`. -/
#check SimpleGraph.SpanningTreeWithLeaves.constraints
#check SimpleGraph.SpanningTreeWithLeaves.feasible
#check SimpleGraph.SpanningTreeWithLeaves.objective
#check SimpleGraph.SpanningTreeWithLeaves.objectiveValues

/- Definition 2.61 (Spanning-tree-with-leaves MILP formulation): a real number `r` belongs to
`SimpleGraph.SpanningTreeWithLeaves.objectiveValues G` exactly when some feasible edge assignment
and leaf assignment attain objective value `r`. This is the canonical companion theorem for
`SimpleGraph.SpanningTreeWithLeaves.objectiveValues`. -/
#check SimpleGraph.SpanningTreeWithLeaves.mem_objectiveValues_iff
