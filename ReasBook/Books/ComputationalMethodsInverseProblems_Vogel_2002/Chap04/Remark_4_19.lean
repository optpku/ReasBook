/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Exercise_4_7.Factorization

public section

noncomputable section

namespace ProbabilityTheory.JointPmf

universe u v w

variable {Ω : Type u} {α : Type v} {β : Type w}

/-- Remark 4.19. If `X` and `Y` are independent random vectors, then
`condSndGivenFst joint x hx y = sndMarginal joint y`, so the conditional PMF of `Y`
given `X = x` agrees pointwise with the marginal PMF of `Y`. -/
theorem condSndGivenFst_apply_eq_sndMarginal_of_indepFun
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → α} {Y : Ω → β}
    (joint : PMF (α × β))
    (hLaw : ProbabilityTheory.HasLaw (fun ω ↦ (X ω, Y ω)) joint.toMeasure μ)
    (hIndep : ProbabilityTheory.IndepFun X Y μ)
    (x : α) (hx : fstMarginal joint x ≠ 0) (y : β) :
    condSndGivenFst joint x hx y = sndMarginal joint y := by
  rw [condSndGivenFst_apply, apply_eq_mul_marginals_of_indepFun joint hLaw hIndep]
  have hcancel : sndMarginal joint y * fstMarginal joint x / fstMarginal joint x =
      sndMarginal joint y := by
    exact ENNReal.mul_div_cancel_right hx ((fstMarginal joint).apply_ne_top x)
  simpa [mul_comm] using hcancel

/-- Under independence, conditioning on `X = x` leaves the PMF of `Y` unchanged. -/
theorem condSndGivenFst_eq_sndMarginal_of_indepFun
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → α} {Y : Ω → β}
    (joint : PMF (α × β))
    (hLaw : ProbabilityTheory.HasLaw (fun ω ↦ (X ω, Y ω)) joint.toMeasure μ)
    (hIndep : ProbabilityTheory.IndepFun X Y μ)
    (x : α) (hx : fstMarginal joint x ≠ 0) :
    condSndGivenFst joint x hx = sndMarginal joint := by
  ext y
  exact condSndGivenFst_apply_eq_sndMarginal_of_indepFun joint hLaw hIndep x hx y

end ProbabilityTheory.JointPmf
