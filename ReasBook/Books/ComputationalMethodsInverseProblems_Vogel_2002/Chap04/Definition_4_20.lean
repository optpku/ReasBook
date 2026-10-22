/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_18.JointPmf
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

public section

noncomputable section

namespace ProbabilityTheory.JointPmf

universe u v w

open MeasureTheory

variable {α : Type u} {β : Type v} {E : Type w}

/-- Helper for Definition 4.20: the conditional expectation of `φ(Y)` given `X = x`,
computed by integrating `φ` against the conditional PMF of the second coordinate given
the first. -/
def condSndExpectationGivenFst
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (joint : PMF (α × β)) (φ : β → E) (x : α)
    (hx : fstMarginal joint x ≠ 0) : E :=
  ∫ y, φ y ∂(condSndGivenFst joint x hx).toMeasure

/-- Definition 4.20: the conditional expectation of `φ(Y)` given `X = x` is the `tsum`
of `φ y` weighted by the conditional PMF `p_{Y | X}(y | x)`. -/
theorem condSndExpectationGivenFst_eq_tsum
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (joint : PMF (α × β)) (φ : β → E) (x : α)
    (hx : fstMarginal joint x ≠ 0)
    (hφ : Integrable φ ((condSndGivenFst joint x hx).toMeasure)) :
    condSndExpectationGivenFst joint φ x hx =
      ∑' y, ((condSndGivenFst joint x hx y).toReal) • φ y := by
  -- Rewrite the conditional expectation as the integral against the conditional PMF.
  unfold condSndExpectationGivenFst
  -- Apply the standard PMF integral formula to the already-constructed conditional PMF.
  simpa using PMF.integral_eq_tsum (condSndGivenFst joint x hx) φ hφ

end ProbabilityTheory.JointPmf
