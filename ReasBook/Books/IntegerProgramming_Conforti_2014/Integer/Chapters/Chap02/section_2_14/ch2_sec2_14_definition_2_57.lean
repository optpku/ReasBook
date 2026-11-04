/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_definition_2_57.SingleMachineReleaseTime

/-!
Single-machine scheduling with release times.

Definition 2.57 is formalized by the reusable owner `SingleMachineReleaseTimeProblem`, together
with the directed off-diagonal ordering-variable carrier
`SingleMachineReleaseTimeProblem.jobArc`, the source-facing feasibility/objective/objective-values
API, and the canonical bridge
`SingleMachineReleaseTimeProblem.toMixedIntegerLinearProgram` to the Chapter 1
`MixedIntegerLinearProgram`.
-/

/- Definition 2.57 [Single-machine scheduling with release times: ILP]: the textbook formulation
with release times `r`, processing times `p`, weights `w`, start times `s`, completion times `C`,
binary ordering variables `δ`, and big-M parameter `M` is formalized by the declarations below. -/
#check SingleMachineReleaseTimeProblem
#check SingleMachineReleaseTimeProblem.jobArc
#check SingleMachineReleaseTimeProblem.jobArcOfNe
#check SingleMachineReleaseTimeProblem.reverseJobArc
#check SingleMachineReleaseTimeProblem.reverseJobArc_reverseJobArc
#check SingleMachineReleaseTimeProblem.ofData
#check SingleMachineReleaseTimeProblem.feasible
#check SingleMachineReleaseTimeProblem.feasible_iff
#check SingleMachineReleaseTimeProblem.feasible_releaseTime
#check SingleMachineReleaseTimeProblem.feasible_completionTime
#check SingleMachineReleaseTimeProblem.feasible_nonoverlapForward
#check SingleMachineReleaseTimeProblem.feasible_nonoverlapBackward
#check SingleMachineReleaseTimeProblem.feasible_pairwiseChoice
#check SingleMachineReleaseTimeProblem.feasible_start_nonneg
#check SingleMachineReleaseTimeProblem.feasible_completion_nonneg
#check SingleMachineReleaseTimeProblem.feasible_binary
#check SingleMachineReleaseTimeProblem.objectiveValue
#check SingleMachineReleaseTimeProblem.objectiveValue_def
#check SingleMachineReleaseTimeProblem.objectiveValues
#check SingleMachineReleaseTimeProblem.mem_objectiveValues_iff
#check SingleMachineReleaseTimeProblem.toMixedIntegerLinearProgram
#check SingleMachineReleaseTimeProblem.toMixedIntegerLinearProgram_isMixedZeroOne
#check
  SingleMachineReleaseTimeProblem.objectiveValues_eq_toMixedIntegerLinearProgram_objectiveValues
