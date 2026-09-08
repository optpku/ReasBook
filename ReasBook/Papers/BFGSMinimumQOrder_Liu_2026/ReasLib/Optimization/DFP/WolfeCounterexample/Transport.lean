module

public import ReasLib.Optimization.DFP.Operator.Matrix
public import ReasLib.Optimization.DFP.OrthogonalSum.Hessian
public import ReasLib.Optimization.DFP.WolfeCounterexample
public import ReasLib.Optimization.LineSearch.Wolfe.CoordinateChange

/-!
# Transport of weak-Wolfe DFP counterexamples

Counterexample certificates are preserved by adjoining an identity quadratic
block and by isometric linear changes of Euclidean coordinates.
-/

public section

noncomputable section

universe u v

open Filter
open scoped Topology

namespace DFP.WolfeCounterexample

/-- A weak-Wolfe DFP counterexample remains one after adjoining an identity
quadratic block on an orthogonal finite-dimensional summand, provided the
identity Hessian lies between the original bounds. -/
theorem orthogonalSum {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] {m M c₁ c₂ : ℝ}
    (c : DFP.WolfeCounterexample ι m M c₁ c₂) (hm : m ≤ 1) (hM : 1 ≤ M) :
    Nonempty (DFP.WolfeCounterexample (ι ⊕ κ) m M c₁ c₂) := by
  classical
  let iteration : DFP.InverseIteration (ι ⊕ κ) :=
    c.iteration.orthogonalSum (κ := κ) c.stepLengthPos
  have objectiveContDiff : ContDiff ℝ 2 iteration.objective := by
    have h := EuclideanSpace.OrthogonalSum.Gradient.contDiff_objective
      (kappa := κ) c.objectiveContDiff
    simpa only [iteration, DFP.InverseIteration.orthogonalSum_objective,
      DFP.OrthogonalSum.objective_eq] using h
  have stepLengthPos (k : ℕ) : 0 < iteration.stepLength k := by
    simpa only [iteration,
      DFP.InverseIteration.orthogonalSum_stepLength] using
        c.stepLengthPos k
  have hessianBounds : HasHessianBounds m M iteration.objective := by
    have h := DFP.OrthogonalSum.hasHessianBounds_objective
      (κ := κ) c.objectiveContDiff c.hessianBounds hm hM
    simpa only [iteration,
      DFP.InverseIteration.orthogonalSum_objective] using h
  have weakWolfe (k : ℕ) :
      LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
        (iteration.point k) (iteration.point (k + 1) - iteration.point k) := by
    have h := (LineSearch.IsWeakWolfe.orthogonalSum_iff
      (κ := κ)).mpr (c.weakWolfe k)
    simpa only [iteration, DFP.InverseIteration.orthogonalSum_objective,
      DFP.InverseIteration.orthogonalSum_point, map_sub] using h
  have gradientNormTendsto :
      Tendsto
        (fun k ↦ ‖DFP.gradients iteration.objective iteration.point k‖)
        atTop (𝓝 c.gradientLimit) := by
    dsimp only [iteration]
    rw [DFP.InverseIteration.orthogonalSum_gradients]
    simpa only [DFP.OrthogonalSum.norm_embed] using
      c.gradientNormTendsto
  let result : DFP.WolfeCounterexample (ι ⊕ κ) m M c₁ c₂ :=
    DFP.WolfeCounterexample.ofIteration iteration c.gradientLimit
      objectiveContDiff stepLengthPos hessianBounds weakWolfe
      c.gradientLimitPos gradientNormTendsto
  exact ⟨result⟩

/-- Pulling a weak-Wolfe DFP counterexample back through a linear isometry
equivalence preserves its Hessian bounds, Wolfe conditions, and positive
limiting gradient norm. -/
theorem pullback_linearIsometryEquiv {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] {m M c₁ c₂ : ℝ}
    (c : DFP.WolfeCounterexample ι m M c₁ c₂)
    (Q : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hm : 0 ≤ m) (hM : 0 ≤ M) :
    Nonempty (DFP.WolfeCounterexample κ m M c₁ c₂) := by
  classical
  let iteration : DFP.InverseIteration κ :=
    c.iteration.pullback_linearIsometryEquiv c.stepLengthPos Q
  have objectiveContDiff : ContDiff ℝ 2 iteration.objective := by
    have h := c.objectiveContDiff.comp Q.contDiff
    simpa only [iteration,
      DFP.InverseIteration.pullback_linearIsometryEquiv_objective] using h
  have stepLengthPos (k : ℕ) : 0 < iteration.stepLength k := by
    simpa only [iteration,
      DFP.InverseIteration.pullback_linearIsometryEquiv_stepLength] using
        c.stepLengthPos k
  have gradientDifferentiable :
      Differentiable ℝ (gradient c.iteration.objective) := by
    exact (c.objectiveContDiff.gradient_succ
      (n := 1)).differentiable_one
  have hessianBounds : HasHessianBounds m M iteration.objective := by
    have h := c.hessianBounds.comp_linearIsometryEquiv Q
      gradientDifferentiable hm hM
    simpa only [iteration,
      DFP.InverseIteration.pullback_linearIsometryEquiv_objective] using h
  have weakWolfe (k : ℕ) :
      LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
        (iteration.point k) (iteration.point (k + 1) - iteration.point k) := by
    have h := LineSearch.IsWeakWolfe.comp_linearIsometryEquiv
      (c.weakWolfe k) Q
    simpa only [iteration,
      DFP.InverseIteration.pullback_linearIsometryEquiv_objective,
      DFP.InverseIteration.pullback_linearIsometryEquiv_point, map_sub] using h
  have gradientNormTendsto :
      Tendsto
        (fun k ↦ ‖DFP.gradients iteration.objective iteration.point k‖)
        atTop (𝓝 c.gradientLimit) := by
    dsimp only [iteration]
    rw [DFP.InverseIteration.pullback_linearIsometryEquiv_gradients]
    simpa only [Q.symm.norm_map] using c.gradientNormTendsto
  let result : DFP.WolfeCounterexample κ m M c₁ c₂ :=
    DFP.WolfeCounterexample.ofIteration iteration c.gradientLimit
      objectiveContDiff stepLengthPos hessianBounds weakWolfe
      c.gradientLimitPos gradientNormTendsto
  exact ⟨result⟩

end DFP.WolfeCounterexample
