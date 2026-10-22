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

/-- Exercise 2.12. The Fredholm first-kind integral operator `(2.7)` from Example 2.4 is a
compact operator on real `L²(Ω)` whenever its kernel is square-integrable on `Ω × Ω`. -/
theorem kernelOperator_isCompactOperator
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    {K : MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ}
    (hK : IsKernelOperator μ k K) :
    IsCompactOperator K :=
  IsKernelOperator.isCompactOperator μ k h_kernel hK

end RealL2
