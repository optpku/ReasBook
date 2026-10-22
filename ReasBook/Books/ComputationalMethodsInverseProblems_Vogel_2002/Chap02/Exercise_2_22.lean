/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic

public section

/- Exercise 2.22.

Equation `(2.35)` is the canonical mathlib identity
`DifferentiableAt.lineDeriv_eq_fderiv`: for a differentiable map, the line
derivative in direction `v` equals the Fréchet derivative applied to `v`.

The source-style derivative witness for the one-variable map
`τ ↦ f (x + τ • v)` is the companion bridge `HasFDerivAt.hasLineDerivAt`.
-/

#check DifferentiableAt.lineDeriv_eq_fderiv
#check HasFDerivAt.hasLineDerivAt
