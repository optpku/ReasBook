/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_1.Problem

/- Definition 1.1 (1). A pure integer linear program is formalized by the reusable owner
`PureIntegerLinearProgram`. -/
#check PureIntegerLinearProgram

/- Definition 1.1 (2). The pure integer linear set attached to `A` and `b` is formalized by
`pureIntegerLinearSet`, with the program-attached view `PureIntegerLinearProgram.feasibleSet`. -/
#check pureIntegerLinearSet
#check PureIntegerLinearProgram.feasibleSet
