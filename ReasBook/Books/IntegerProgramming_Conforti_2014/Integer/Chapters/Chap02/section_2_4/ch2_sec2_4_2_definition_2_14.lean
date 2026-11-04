/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

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
