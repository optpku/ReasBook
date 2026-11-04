/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

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
