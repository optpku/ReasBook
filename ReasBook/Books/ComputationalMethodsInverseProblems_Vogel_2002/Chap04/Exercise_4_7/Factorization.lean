/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_18.JointPmf
public import Mathlib.Probability.Independence.Basic

public section

noncomputable section

open MeasureTheory

namespace ProbabilityTheory.JointPmf

universe u v w

variable {Ω : Type u} {α : Type v} {β : Type w}

/-- Under independence, the joint law `joint.toMeasure` factors as the product of the marginal
PMF laws of `X` and `Y`. -/
theorem toMeasure_eq_prod_marginals_of_indepFun
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → α} {Y : Ω → β}
    (joint : PMF (α × β))
    (hLaw : ProbabilityTheory.HasLaw (fun ω ↦ (X ω, Y ω)) joint.toMeasure μ)
    (hIndep : ProbabilityTheory.IndepFun X Y μ) :
    joint.toMeasure = (fstMarginal joint).toMeasure.prod (sndMarginal joint).toMeasure := by
  have hfstJoint :
      ProbabilityTheory.HasLaw Prod.fst (fstMarginal joint).toMeasure joint.toMeasure := by
    exact ⟨measurable_fst.aemeasurable, (fstMarginal_toMeasure joint).symm⟩
  have hsndJoint :
      ProbabilityTheory.HasLaw Prod.snd (sndMarginal joint).toMeasure joint.toMeasure := by
    exact ⟨measurable_snd.aemeasurable, (sndMarginal_toMeasure joint).symm⟩
  have hfst : ProbabilityTheory.HasLaw X (fstMarginal joint).toMeasure μ := by
    have hfstComp := hfstJoint.comp hLaw
    change ProbabilityTheory.HasLaw (fun ω ↦ X ω) (fstMarginal joint).toMeasure μ at hfstComp
    exact hfstComp
  have hsnd : ProbabilityTheory.HasLaw Y (sndMarginal joint).toMeasure μ := by
    have hsndComp := hsndJoint.comp hLaw
    change ProbabilityTheory.HasLaw (fun ω ↦ Y ω) (sndMarginal joint).toMeasure μ at hsndComp
    exact hsndComp
  have hProd :
      ProbabilityTheory.HasLaw (fun ω ↦ (X ω, Y ω))
        ((fstMarginal joint).toMeasure.prod (sndMarginal joint).toMeasure) μ :=
    (ProbabilityTheory.indepFun_iff_hasLaw_prodMk_prod hfst hsnd).mp hIndep
  calc
    joint.toMeasure = Measure.map (fun ω ↦ (X ω, Y ω)) μ := hLaw.map_eq.symm
    _ = (fstMarginal joint).toMeasure.prod (sndMarginal joint).toMeasure := hProd.map_eq

/-- Evaluating the product-law factorization on a singleton yields the pointwise factorization
`joint (x, y) = fstMarginal joint x * sndMarginal joint y`. -/
theorem apply_eq_mul_marginals_of_indepFun
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → α} {Y : Ω → β}
    (joint : PMF (α × β))
    (hLaw : ProbabilityTheory.HasLaw (fun ω ↦ (X ω, Y ω)) joint.toMeasure μ)
    (hIndep : ProbabilityTheory.IndepFun X Y μ)
    (x : α) (y : β) :
    joint (x, y) = fstMarginal joint x * sndMarginal joint y := by
  have h :=
    congrArg
      (fun ν : Measure (α × β) ↦ ν {(x, y)})
      (toMeasure_eq_prod_marginals_of_indepFun joint hLaw hIndep)
  rw [joint.toMeasure_apply_singleton (x, y) (measurableSet_singleton (x, y)),
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    (fstMarginal joint).toMeasure_apply_singleton x (measurableSet_singleton x),
    (sndMarginal joint).toMeasure_apply_singleton y (measurableSet_singleton y)] at h
  exact h

end ProbabilityTheory.JointPmf
