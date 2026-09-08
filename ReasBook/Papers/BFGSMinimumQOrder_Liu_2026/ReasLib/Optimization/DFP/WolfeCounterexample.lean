module

public import ReasLib.Analysis.Calculus.Gradient.Hessian
public import ReasLib.Optimization.DFP.Iteration
public import ReasLib.Optimization.LineSearch

/-!
# Nonconvergent weak-Wolfe DFP trajectories

This file packages the reusable mathematical content of a DFP counterexample.
The Hessian bounds and Wolfe constants are parameters; particular papers may
specialize them without creating a second trajectory structure.
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP

/-- An inverse-form DFP trajectory with uniform Hessian bounds and weak-Wolfe
steps whose gradient norms converge to a positive limit. -/
structure WolfeCounterexample (ι : Type u) [Fintype ι]
    (m M c₁ c₂ : ℝ) where
  iteration : InverseIteration ι
  gradientLimit : ℝ
  objectiveContDiff : ContDiff ℝ 2 iteration.objective
  stepLengthPos : ∀ k, 0 < iteration.stepLength k
  hessianBounds : HasHessianBounds m M iteration.objective
  weakWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
    (iteration.point k) (iteration.point (k + 1) - iteration.point k)
  gradientLimitPos : 0 < gradientLimit
  gradientNormTendsto : Tendsto
    (fun k ↦ ‖gradients iteration.objective iteration.point k‖) atTop
      (𝓝 gradientLimit)

namespace WolfeCounterexample

/-- Assemble a weak-Wolfe counterexample certificate from its constituent
trajectory properties. -/
def ofIteration {ι : Type u} [Fintype ι] {m M c₁ c₂ : ℝ}
    (iteration : InverseIteration ι) (gradientLimit : ℝ)
    (objectiveContDiff : ContDiff ℝ 2 iteration.objective)
    (stepLengthPos : ∀ k, 0 < iteration.stepLength k)
    (hessianBounds : HasHessianBounds m M iteration.objective)
    (weakWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    (gradientLimitPos : 0 < gradientLimit)
    (gradientNormTendsto : Tendsto
      (fun k ↦ ‖gradients iteration.objective iteration.point k‖) atTop
        (𝓝 gradientLimit)) :
    WolfeCounterexample ι m M c₁ c₂ where
  iteration := iteration
  gradientLimit := gradientLimit
  objectiveContDiff := objectiveContDiff
  stepLengthPos := stepLengthPos
  hessianBounds := hessianBounds
  weakWolfe := weakWolfe
  gradientLimitPos := gradientLimitPos
  gradientNormTendsto := gradientNormTendsto

/-- The initial inverse-Hessian approximation of a certified counterexample is
positive definite. -/
theorem initialInverseHessianPosDef {ι : Type u} [Fintype ι]
    {m M c₁ c₂ : ℝ} (c : WolfeCounterexample ι m M c₁ c₂) :
    (c.iteration.inverseHessian 0).PosDef :=
  c.iteration.inverseHessianPosDef 0

end WolfeCounterexample

end DFP
