/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_4.Operator

public section

namespace RealL2

variable {Ω : Type} [MeasurableSpace Ω]
variable (μ : MeasureTheory.Measure Ω) [MeasureTheory.SFinite μ]
variable (k : Ω → Ω → ℝ)

/- Example 2.13. Every Fredholm first-kind integral operator realization `(2.7)` from Example 2.4
is compact on real `L²(Ω)` whenever its kernel is square-integrable on `Ω × Ω`.

This source statement is already the canonical reusable theorem
`IsKernelOperator.isCompactOperator` from `Book.Ch2.Example_2_4.Operator`, so this example keeps
the direct owner instead of introducing a duplicate wrapper. -/
#check IsKernelOperator.isCompactOperator

end RealL2
