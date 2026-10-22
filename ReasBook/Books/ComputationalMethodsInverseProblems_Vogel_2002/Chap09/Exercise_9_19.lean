/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Algorithm_9_5_1

public section

/-
Exercise 9.19.

The source exercise is procedural: apply the MRNSD algorithm to the
two-dimensional test problem from `§9.4.2`. The current repository snapshot
already provides the generic recursive MRNSD iterate owner `Mrnsd.iterates`
together with the companion validity predicate `Mrnsd.IsIterateSequence`, but
it does not yet contain verified Lean declarations for the concrete `§9.4.2`
forward operator, datum, or initialization data. This file therefore records
only the exercise-level specialization shape through direct checks of those
canonical owners, keeping the concrete benchmark objects explicit rather than
inventing unsupported Chapter 9 infrastructure.
-/

section Exercise919

variable
  (forwardOperator942 : Matrix (Fin 2) (Fin 2) ℝ)
  (data942 initialIterate942 : EuclideanSpace ℝ (Fin 2))
  (boundarySteps942 stepSizes942 : ℕ → ℝ)

/- Exercise 9.19. Apply the MRNSD algorithm to the two-dimensional `§9.4.2`
benchmark.

The repository still lacks the concrete `§9.4.2` benchmark operator, datum,
initial iterate, and boundary-step and step-size policies. The `#check` below
therefore records the intended exercise-level specialization with those
benchmark objects kept explicit at the source-facing API surface. -/
#check Mrnsd.iterates forwardOperator942 data942 initialIterate942 stepSizes942

/- Exercise 9.19. A specialized benchmark trajectory is valid when it satisfies
the canonical MRNSD iterate-sequence predicate for the same explicit
two-dimensional `§9.4.2` data. -/
#check Mrnsd.IsIterateSequence forwardOperator942 data942 initialIterate942
  boundarySteps942 stepSizes942

end Exercise919

/- Backend anchors for the source-facing MRNSD owner layer used above. -/
#check Mrnsd.iterates
#check Mrnsd.IsIterateSequence
#check Mrnsd.IsStep
#check Mrnsd.State
