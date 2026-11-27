/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_2.DiscreteRandomVariable

public section

namespace ProbabilityTheory

universe u

/-- Helper for Definition 4.2: the point probabilities of a discrete real random variable sum to
`1`. -/
lemma hasSumDiscretePointProbabilities
    {Ω : Type u} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {X : Ω → ℝ}
    (hX : IsDiscreteRandomVariable μ X) :
    HasSum (fun x : ℝ ↦ μ {ω | X ω = x}) 1 := by
  classical
  rcases isDiscreteRandomVariable_iff.mp hX with ⟨p, hp⟩
  -- Transport the mass function law to point probabilities of `X`.
  convert p.hasSum_coe_one using 1
  ext x
  calc
    μ {ω | X ω = x} = p.toMeasure {y | y = x} :=
      hp.measure_eq (measurableSet_singleton x)
    _ = p x := by
      simpa using p.toMeasure_apply_singleton x (measurableSet_singleton x)


end ProbabilityTheory
