/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Remark_9_19.InexactLineSearch

public section

/-
Remark 9.19 (1). The projected sufficient-decrease condition `(9.26)` for
`φ t = J (P (f_v + t • p_v))` is formalized by the reusable predicate
`GradientProjection.SufficientDecrease`.
-/
#check GradientProjection.SufficientDecrease

/- Remark 9.19 (2)-(3). The derivative-jump comment for the piecewise-linear
projected path and the asymptotically linear convergence comment after active-set
identification are not introduced as theorems here: the current Chapter 9 API
lacks the projection-path regularity and reduced-space convergence owners those
sentences would need. -/
