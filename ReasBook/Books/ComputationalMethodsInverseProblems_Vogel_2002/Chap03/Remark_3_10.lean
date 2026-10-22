/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Algorithm_3_2_1.Iterates
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_4.ConditionNumber

public section

/-!
Remark 3.10. Statement-stage blocker.

The source remark compares the per-iteration cost of CG and PCG and asserts a
qualitative necessity claim: using PCG is computationally worthwhile only when
the preconditioner solves `M z = g` are cheap and the PCG convergence rate is
substantially faster than the CG rate.

The current repository snapshot still does not expose a checked source-faithful
owner for the PCG recurrence from `Algorithm 3.2.2`, nor a checked quantitative
cost/comparison theorem relating PCG and CG. Replacing the remark by a local
qualitative wrapper or implication schema would therefore guess missing
mathematics and drift from the source meaning.

This file remains a labeled blocker/anchor entry instead. The `#check`
commands below record only verified backend owners that a later faithful
formalization should reuse for the CG iterate surface, Euclidean-space matrix
action, SPD invertibility needed for inverse-solve reasoning, and the
condition-number convergence proxy.
-/

/- Remark 3.10. Main labeled source-facing entry for the current blocked-item
state: the source compares actual PCG and CG cost/convergence behavior, but the
current repository does not yet provide a checked PCG iterate owner or a
checked cost/comparison statement, so this file records only verified anchors
instead of inventing a surrogate public API.
-/

#check ConjugateGradient.State
#check ConjugateGradient.step
#check ConjugateGradient.iterates
#check Matrix.toEuclideanLin
#check Matrix.PosDef
#check Matrix.PosDef.isUnit
#check Matrix.mul_nonsing_inv
#check Matrix.conditionNumber
#check Matrix.conditionNumber_eq_spectralExtrema_of_posDef
