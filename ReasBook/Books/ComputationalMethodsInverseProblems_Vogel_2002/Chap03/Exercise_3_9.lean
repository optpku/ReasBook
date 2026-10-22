/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Theorem_3_11

public section

/- Exercise 3.9. The chapter's significant-digits consequence of the quadratic
estimate `(3.19)` is supported by the canonical Newton theorem
`Newton.newtonConvergesWithQuadraticEstimate`, which packages both convergence
to `fStar` and the estimate
`‖f (v + 1) - fStar‖ ≤ cStar J fStar γ * ‖f v - fStar‖ ^ 2`. -/
#check Newton.newtonConvergesWithQuadraticEstimate
