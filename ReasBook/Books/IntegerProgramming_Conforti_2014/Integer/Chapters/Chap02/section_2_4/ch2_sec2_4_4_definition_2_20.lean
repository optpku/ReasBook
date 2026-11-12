/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_20.Cuts

public section

/-!
Cuts in an undirected graph.

This item uses the reusable cut-boundary API in
`SimpleGraph.cutEdgeSet`, `SimpleGraph.IsCut`, and `SimpleGraph.IsProperCut`.
-/

/- Definition 2.20 [Cuts in an undirected graph]. For a vertex set `S`, the edge boundary `δ(S)`
is formalized by `SimpleGraph.cutEdgeSet`, a cut by `SimpleGraph.IsCut`, a proper cut by
`SimpleGraph.IsProperCut`, and the singleton boundary/degree identification by the theorems below.
-/
#check SimpleGraph.cutEdgeSet
#check SimpleGraph.IsCut
#check SimpleGraph.IsProperCut
#check SimpleGraph.cutEdgeSet_singleton_eq_incidenceSet
#check SimpleGraph.card_cutEdgeSet_singleton_eq_degree
