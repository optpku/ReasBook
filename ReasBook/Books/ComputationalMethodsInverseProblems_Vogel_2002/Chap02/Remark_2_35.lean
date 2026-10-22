/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Prop_2_34

public section

/- Remark 2.35. The left-hand side of (2.38) is the Gateaux, or directional,
derivative of `J` at `f` in the direction `h`, also called the first variation of
`J`; in Lean this quantity is the canonical `lineDeriv ℝ J f h`, often denoted in
the source text by `δJ(f, h)`. The Chapter 2 Hilbert-space specialization used
later in Proposition 2.34 is the repository theorem
`lineDeriv_eq_inner_gradient`. -/
#check lineDeriv
#check lineDeriv_eq_inner_gradient
