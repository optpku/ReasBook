/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_9.CriticalPoint

public section

/- Definition 9.9. A point `fStar` that satisfies the coordinatewise
feasibility, gradient nonnegativity, and complementarity conditions
`(9.17)`-`(9.19)` is formalized by `NonnegativeOrthant.IsCriticalPoint`. -/
#check NonnegativeOrthant.IsCriticalPoint
