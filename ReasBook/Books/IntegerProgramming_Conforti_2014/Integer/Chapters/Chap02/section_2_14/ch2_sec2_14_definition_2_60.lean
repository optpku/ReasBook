/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_6

public section

/-!
Assignment constraints for permutation matrices.

Definition 2.60 is already formalized by the reusable owner
`assignmentProblemFeasibleSet`, together with its source-form membership
criterion `mem_assignmentProblemFeasibleSet_iff`.
-/

/- Definition 2.60 (Assignment constraints for permutation matrices): for `n ∈ ℤ≥1`, the set
`𝒜 = {x ∈ {0, 1}^{n × n} : ∑ i, x i j = 1 ∀ j, ∑ j, x i j = 1 ∀ i}` is formalized by the
existing feasible-set owner `assignmentProblemFeasibleSet`. -/
#check assignmentProblemFeasibleSet

#check mem_assignmentProblemFeasibleSet_iff

#check mem_assignmentProblemFeasibleSet_iff_mem_doublyStochastic_and_zeroOne
