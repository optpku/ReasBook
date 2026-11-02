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
