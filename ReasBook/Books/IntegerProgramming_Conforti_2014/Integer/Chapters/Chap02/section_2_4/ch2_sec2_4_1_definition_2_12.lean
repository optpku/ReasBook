module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_1_definition_2_12.IntersectionGraph

public section

/-!
Intersection graph.

The canonical reusable owner for Definition 2.12 is `Matrix.intersectionGraph`.
-/

/- Definition 2.12 (Intersection graph): the canonical reusable definition is
`Matrix.intersectionGraph`, the simple graph on the columns of a `0`-`1` matrix `A` in which two
distinct columns are adjacent exactly when some row contains `true` in both columns. -/
#check Matrix.intersectionGraph
