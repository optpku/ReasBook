module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_2_definition_2_14.CliqueMatrix

public section

/-!
Clique matrix.

The canonical owner for Definition 2.14 is `SimpleGraph.cliqueMatrix`.
-/

/- Definition 2.14 (Clique matrix): the canonical reusable definition is
`SimpleGraph.cliqueMatrix`, the `0`-`1` matrix whose rows are indexed by maximal cliques of a
finite graph `G`, whose columns are indexed by vertices, and whose `(K, v)` entry is `1` exactly
when `v ∈ K`. -/
#check SimpleGraph.cliqueMatrix
