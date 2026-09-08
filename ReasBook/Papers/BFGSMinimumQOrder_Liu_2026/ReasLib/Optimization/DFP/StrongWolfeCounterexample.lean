module

public import ReasLib.Optimization.DFP.WolfeCounterexample.Transport
public import ReasLib.Optimization.DFP.AbstractSecantStep.Wolfe.DiscreteRatio
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.Wolfe
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.RealizedObjective.Interpolation
public import ReasLib.Optimization.DFP.OrthogonalSum
import ReasLib.LinearAlgebra.Matrix.OrthogonalTransport

/-!
# Strong-Wolfe counterexample certificates

This module keeps the established weak-Wolfe certificate unchanged and adds a
strong-Wolfe field in a wrapper.  The strong predicate below deliberately uses
the same gradient-based endpoint interface as `LineSearch.IsWeakWolfe`; its
curvature field is the absolute (strong-Wolfe) inequality.
-/

public section

noncomputable section

universe u v

open Filter
open scoped Matrix Topology

namespace LineSearch

/-! `IsStrongWolfe` is the canonical gradient-facing strong predicate in this module. -/

/-- TASK-03: A gradient-based step satisfies strong Wolfe when it has endpoint
differentiability, Armijo decrease, and absolute curvature control. -/
structure IsStrongWolfe {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (c₁ c₂ : ℝ) (f : E → ℝ) (x s : E) : Prop where
  c₁_pos : 0 < c₁
  c₁_lt_c₂ : c₁ < c₂
  c₂_lt_one : c₂ < 1
  differentiableAt : DifferentiableAt ℝ f x
  differentiableAtNext : DifferentiableAt ℝ f (x + s)
  armijo : f (x + s) ≤ f x + c₁ * inner ℝ (gradient f x) s
  strongCurvature :
    |inner ℝ (gradient f (x + s)) s| ≤ c₂ * |inner ℝ (gradient f x) s|

/-- Helper for TASK-03: certified endpoint gradients normalize the canonical
gradient pairings in the strong-Wolfe inequalities. -/
private lemma canonicalStrongWolfeInequalities_of_hasGradientAt
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {c₁ c₂ : ℝ} {f : E → ℝ} {x s g gNext : E}
    (gradientAt : HasGradientAt f g x)
    (gradientAtNext : HasGradientAt f gNext (x + s))
    (armijo : f (x + s) ≤ f x + c₁ * inner ℝ g s)
    (strongCurvature : |inner ℝ gNext s| ≤ c₂ * |inner ℝ g s|) :
    f (x + s) ≤ f x + c₁ * inner ℝ (gradient f x) s ∧
      |inner ℝ (gradient f (x + s)) s| ≤
        c₂ * |inner ℝ (gradient f x) s| := by
  constructor
  · simpa only [gradientAt.gradient] using armijo
  · simpa only [gradientAt.gradient, gradientAtNext.gradient] using strongCurvature

/-- TASK-03: Certified endpoint gradients and strong curvature construct the
gradient-based strong-Wolfe predicate. -/
theorem IsStrongWolfe.ofHasGradientAt {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {c₁ c₂ : ℝ} {f : E → ℝ}
    {x s g gNext : E} (c₁_pos : 0 < c₁) (c₁_lt_c₂ : c₁ < c₂) (c₂_lt_one : c₂ < 1)
    (gradientAt : HasGradientAt f g x) (gradientAtNext : HasGradientAt f gNext (x + s))
    (armijo : f (x + s) ≤ f x + c₁ * inner ℝ g s)
    (strongCurvature : |inner ℝ gNext s| ≤ c₂ * |inner ℝ g s|) :
    IsStrongWolfe c₁ c₂ f x s := by
  obtain ⟨canonicalArmijo, canonicalStrongCurvature⟩ :=
    canonicalStrongWolfeInequalities_of_hasGradientAt gradientAt gradientAtNext armijo
      strongCurvature
  exact {
    c₁_pos := c₁_pos
    c₁_lt_c₂ := c₁_lt_c₂
    c₂_lt_one := c₂_lt_one
    differentiableAt := gradientAt.differentiableAt
    differentiableAtNext := gradientAtNext.differentiableAt
    armijo := canonicalArmijo
    strongCurvature := canonicalStrongCurvature
  }

/-- TASK-03: Strong curvature gives weak curvature when the initial directional
derivative is nonpositive. -/
theorem IsStrongWolfe.toWeakWolfe {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {c₁ c₂ : ℝ} {f : E → ℝ}
    {x s : E} (h : IsStrongWolfe c₁ c₂ f x s)
    (descent : inner ℝ (gradient f x) s ≤ 0) :
    IsWeakWolfe c₁ c₂ f x s := by
  have hstrong : LineSearch.Wolfe.IsStrongCurvature c₂
      (inner ℝ (gradient f x) s)
      (inner ℝ (gradient f (x + s)) s) :=
    LineSearch.Wolfe.isStrongCurvature_iff.mpr h.strongCurvature
  have hweak' := LineSearch.Wolfe.IsStrongCurvature.weak hstrong descent
  have hweak : LineSearch.Wolfe.IsWeakCurvature c₂
      (inner ℝ (gradient f x) s)
      (inner ℝ (gradient f (x + s)) s) := hweak'
  exact {
    c₁_pos := h.c₁_pos
    c₁_lt_c₂ := h.c₁_lt_c₂
    c₂_lt_one := h.c₂_lt_one
    differentiableAt := h.differentiableAt
    differentiableAtNext := h.differentiableAtNext
    armijo := h.armijo
    weakCurvature := LineSearch.Wolfe.isWeakCurvature_iff.mp hweak
  }

end LineSearch

namespace DFP

/-! A wrapper preserves all projections of the existing weak certificate. -/

/-- TASK-03: A strong-Wolfe certificate extends a weak DFP certificate with
absolute-curvature certificates for every iteration step. -/
structure StrongWolfeCounterexample (ι : Type u) [Fintype ι]
    (m M c₁ c₂ : ℝ) extends WolfeCounterexample ι m M c₁ c₂ where
  strongWolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ iteration.objective
    (iteration.point k) (iteration.point (k + 1) - iteration.point k)

namespace StrongWolfeCounterexample

/-- TASK-03: Attach strong-Wolfe endpoint certificates to an existing weak
certificate without changing its trajectory or analytic bounds. -/
def ofWeak {ι : Type u} [Fintype ι] {m M c₁ c₂ : ℝ}
    (weak : WolfeCounterexample ι m M c₁ c₂)
    (strongWolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ weak.iteration.objective
      (weak.iteration.point k)
      (weak.iteration.point (k + 1) - weak.iteration.point k)) :
    StrongWolfeCounterexample ι m M c₁ c₂ := {
  toWolfeCounterexample := weak
  strongWolfe := strongWolfe
}

/-- TASK-03: The initial inverse-Hessian positivity projection is inherited
from the weak certificate wrapper. -/
theorem initialInverseHessianPosDef {ι : Type u} [Fintype ι]
    {m M c₁ c₂ : ℝ} (c : StrongWolfeCounterexample ι m M c₁ c₂) :
    (c.iteration.inverseHessian 0).PosDef :=
  c.toWolfeCounterexample.initialInverseHessianPosDef

end StrongWolfeCounterexample

end DFP

namespace DFP.TwoPhaseOrbit

/-- Helper for TASK-03: a special-orthogonal phase frame preserves the Euclidean
inner product of the transported abstract vectors. -/
private theorem inner_toLp_mulVec_eq_of_mem_specialOrthogonalGroup
    (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (u v : Fin 2 → ℝ) :
    inner ℝ (WithLp.toLp 2 (R *ᵥ u)) (WithLp.toLp 2 (R *ᵥ v)) = u ⬝ᵥ v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simpa [dotProduct_comm] using
    Matrix.dotProduct_mulVec_eq_of_mem_specialOrthogonalGroup R hR v u

/-- Helper for TASK-03: the strong scalar-curvature certificate of one exact
phase transports to its flattened physical endpoint step. -/
private theorem endpointPhaseStrongCurvature
    (orbit : DFP.TwoPhaseOrbit) (j : ℕ) (i : Fin 2)
    (h : State.ExactCycle (orbit.state j)) {c₂ : ℝ}
    (hc₂ : (2 / 3 : ℝ) ≤ c₂) :
    let k := 2 * j + i.val
    let d := orbit.endpoint (k + 1) - orbit.endpoint k
    LineSearch.Wolfe.IsStrongCurvature c₂
      (inner ℝ (orbit.endpointGradient k) d)
      (inner ℝ (orbit.endpointGradient (k + 1)) d) := by
  dsimp only
  have hstart :
      inner ℝ (orbit.endpointGradient (2 * j + i.val))
          (orbit.endpoint (2 * j + i.val + 1) -
            orbit.endpoint (2 * j + i.val)) =
        (h.step i).slope := by
    rw [endpointGradient_eq_exactStepTransport orbit j i h,
      endpointStep_eq_exactStepTransport orbit j i h]
    rw [DFP.AbstractSecantStep.slope_def]
    exact inner_toLp_mulVec_eq_of_mem_specialOrthogonalGroup
      ((orbit.state j).phaseFrame i) (h.valid.phaseFrame_mem_specialOrthogonal i)
      (h.step i).gradient (h.step i).displacement
  have hnext :
      inner ℝ (orbit.endpointGradient (2 * j + i.val + 1))
          (orbit.endpoint (2 * j + i.val + 1) -
            orbit.endpoint (2 * j + i.val)) =
        (h.step i).nextSlope := by
    rw [endpointGradient_succ_eq_exactStepTransport orbit j i h,
      endpointStep_eq_exactStepTransport orbit j i h]
    rw [DFP.AbstractSecantStep.nextSlope_def]
    exact inner_toLp_mulVec_eq_of_mem_specialOrthogonalGroup
      ((orbit.state j).phaseFrame i) (h.valid.phaseFrame_mem_specialOrthogonal i)
      (h.step i).nextGradient (h.step i).displacement
  rw [hstart, hnext]
  exact DFP.AbstractSecantStep.strongCurvature_of_tau_values
    (h.step i) (h.step_tau_mem i) hc₂

/-- TASK-03: Every flattened endpoint step of an exact two-phase orbit has
strong curvature for any `c₂ ≥ 2 / 3`. -/
theorem endpointStrongCurvature (orbit : DFP.TwoPhaseOrbit)
    (h_exact : ∀ j, State.ExactCycle (orbit.state j)) {c₂ : ℝ}
    (hc₂ : (2 / 3 : ℝ) ≤ c₂) (k : ℕ) :
    let d := orbit.endpoint (k + 1) - orbit.endpoint k
    LineSearch.Wolfe.IsStrongCurvature c₂
      (inner ℝ (orbit.endpointGradient k) d)
      (inner ℝ (orbit.endpointGradient (k + 1)) d) := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · simpa only [Fin.val_zero, add_zero] using
      endpointPhaseStrongCurvature orbit j (0 : Fin 2) (h_exact j) hc₂
  · simpa only [Fin.val_one] using
      endpointPhaseStrongCurvature orbit j (1 : Fin 2) (h_exact j) hc₂

/-- TASK-03: Endpoint gradient data and the exact two-phase ratio certificate
construct the strong-Wolfe predicate for every flattened endpoint step. -/
theorem endpointStrongWolfe_of_endpointData
    (orbit : DFP.TwoPhaseOrbit)
    (h_exact : ∀ j, State.ExactCycle (orbit.state j))
    {c₁ c₂ : ℝ} {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hc₁_pos : 0 < c₁) (hc₁_lt_c₂ : c₁ < c₂) (hc₂_lt_one : c₂ < 1)
    (hgradient : ∀ k, HasGradientAt f (orbit.endpointGradient k)
      (orbit.endpoint k))
    (hArmijo : ∀ k, f (orbit.endpoint (k + 1)) ≤ f (orbit.endpoint k) +
      c₁ * inner ℝ (orbit.endpointGradient k)
        (orbit.endpoint (k + 1) - orbit.endpoint k))
    (hc₂ : (2 / 3 : ℝ) ≤ c₂) (k : ℕ) :
    LineSearch.IsStrongWolfe c₁ c₂ f (orbit.endpoint k)
      (orbit.endpoint (k + 1) - orbit.endpoint k) := by
  have hsum : orbit.endpoint k +
      (orbit.endpoint (k + 1) - orbit.endpoint k) = orbit.endpoint (k + 1) := by
    abel
  have hgradientNext : HasGradientAt f (orbit.endpointGradient (k + 1))
      (orbit.endpoint k + (orbit.endpoint (k + 1) - orbit.endpoint k)) := by
    rw [hsum]
    exact hgradient (k + 1)
  apply LineSearch.IsStrongWolfe.ofHasGradientAt hc₁_pos hc₁_lt_c₂ hc₂_lt_one
    (hgradient k) hgradientNext
  · simpa only [hsum] using hArmijo k
  · exact LineSearch.Wolfe.isStrongCurvature_iff.mp
      (endpointStrongCurvature orbit h_exact hc₂ k)

end DFP.TwoPhaseOrbit

namespace LineSearch.IsStrongWolfe

/-- TASK-03: The gradient-based strong-Wolfe predicate is invariant under an
orthogonal-sum quadratic extension. -/
theorem orthogonalSum_iff {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] {c₁ c₂ : ℝ}
    {f : EuclideanSpace ℝ ι → ℝ} {x s : EuclideanSpace ℝ ι} :
    IsStrongWolfe c₁ c₂
        (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f)
        (EuclideanSpace.OrthogonalSum.inl (κ := κ) x)
        (EuclideanSpace.OrthogonalSum.inl (κ := κ) s) ↔
      IsStrongWolfe c₁ c₂ f x s := by
  have hsum :
      EuclideanSpace.OrthogonalSum.inl (κ := κ) x +
          EuclideanSpace.OrthogonalSum.inl (κ := κ) s =
        EuclideanSpace.OrthogonalSum.inl (κ := κ) (x + s) :=
    ((EuclideanSpace.OrthogonalSum.inl (ι := ι) (κ := κ)).map_add x s).symm
  constructor
  · intro h
    have hxDiff : DifferentiableAt ℝ f x :=
      EuclideanSpace.OrthogonalSum.Gradient.differentiableAt_objective_inl_iff.mp
        h.differentiableAt
    have hnextObjective :
        DifferentiableAt ℝ
          (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f)
          (EuclideanSpace.OrthogonalSum.inl (κ := κ) (x + s)) := by
      rw [← hsum]
      exact h.differentiableAtNext
    have hnextDiff : DifferentiableAt ℝ f (x + s) :=
      EuclideanSpace.OrthogonalSum.Gradient.differentiableAt_objective_inl_iff.mp
        hnextObjective
    refine {
      c₁_pos := h.c₁_pos
      c₁_lt_c₂ := h.c₁_lt_c₂
      c₂_lt_one := h.c₂_lt_one
      differentiableAt := hxDiff
      differentiableAtNext := hnextDiff
      armijo := ?_
      strongCurvature := ?_
    }
    · simpa only [hsum,
        EuclideanSpace.OrthogonalSum.Gradient.objective_inl,
        EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl hxDiff,
        EuclideanSpace.OrthogonalSum.inner_inl] using h.armijo
    · simpa only [hsum,
        EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl hxDiff,
        EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl hnextDiff,
        EuclideanSpace.OrthogonalSum.inner_inl] using h.strongCurvature
  · intro h
    have hxObjective :
        DifferentiableAt ℝ
          (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f)
          (EuclideanSpace.OrthogonalSum.inl (κ := κ) x) :=
      EuclideanSpace.OrthogonalSum.Gradient.differentiableAt_objective_inl_iff.mpr
        h.differentiableAt
    have hnextObjectiveInl :
        DifferentiableAt ℝ
          (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f)
          (EuclideanSpace.OrthogonalSum.inl (κ := κ) (x + s)) :=
      EuclideanSpace.OrthogonalSum.Gradient.differentiableAt_objective_inl_iff.mpr
        h.differentiableAtNext
    have hnextObjective :
        DifferentiableAt ℝ
          (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f)
          (EuclideanSpace.OrthogonalSum.inl (κ := κ) x +
            EuclideanSpace.OrthogonalSum.inl (κ := κ) s) := by
      rw [hsum]
      exact hnextObjectiveInl
    refine {
      c₁_pos := h.c₁_pos
      c₁_lt_c₂ := h.c₁_lt_c₂
      c₂_lt_one := h.c₂_lt_one
      differentiableAt := hxObjective
      differentiableAtNext := hnextObjective
      armijo := ?_
      strongCurvature := ?_
    }
    · simpa only [hsum,
        EuclideanSpace.OrthogonalSum.Gradient.objective_inl,
        EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl h.differentiableAt,
        EuclideanSpace.OrthogonalSum.inner_inl] using h.armijo
    · simpa only [hsum,
        EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl h.differentiableAt,
        EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl h.differentiableAtNext,
        EuclideanSpace.OrthogonalSum.inner_inl] using h.strongCurvature

/-- TASK-03: Pulling back a strong-Wolfe step through a linear isometry
equivalence preserves endpoint gradients and absolute curvature. -/
theorem comp_linearIsometryEquiv
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {c₁ c₂ : ℝ} {f : F → ℝ} {x s : F}
    (h : IsStrongWolfe c₁ c₂ f x s) (Q : E ≃ₗᵢ[ℝ] F) :
    IsStrongWolfe c₁ c₂ (f ∘ Q) (Q.symm x) (Q.symm s) := by
  have hstart : Q (Q.symm x) = x := Q.apply_symm_apply x
  have hnext : Q (Q.symm x + Q.symm s) = x + s := by
    rw [map_add, Q.apply_symm_apply, Q.apply_symm_apply]
  have hgradientStart : gradient (f ∘ Q) (Q.symm x) = Q.symm (gradient f x) := by
    have hgradient := Q.toContinuousLinearEquiv.comp_right_gradient f (Q.symm x)
    simpa [Function.comp_def, hstart, Q.adjoint_eq_symm] using hgradient
  have hgradientNext : gradient (f ∘ Q) (Q.symm x + Q.symm s) =
      Q.symm (gradient f (x + s)) := by
    have hgradient :=
      Q.toContinuousLinearEquiv.comp_right_gradient f (Q.symm x + Q.symm s)
    simpa [Function.comp_def, hnext, Q.adjoint_eq_symm] using hgradient
  refine {
    c₁_pos := h.c₁_pos
    c₁_lt_c₂ := h.c₁_lt_c₂
    c₂_lt_one := h.c₂_lt_one
    differentiableAt := ?_
    differentiableAtNext := ?_
    armijo := ?_
    strongCurvature := ?_
  }
  · have hf : DifferentiableAt ℝ f (Q (Q.symm x)) := by
      simpa only [hstart] using h.differentiableAt
    exact hf.comp (Q.symm x) Q.differentiableAt
  · have hf : DifferentiableAt ℝ f (Q (Q.symm x + Q.symm s)) := by
      simpa only [hnext] using h.differentiableAtNext
    exact hf.comp (Q.symm x + Q.symm s) Q.differentiableAt
  · rw [Function.comp_apply, Function.comp_apply, hnext, hstart, hgradientStart]
    simpa only [Q.symm.inner_map_map] using h.armijo
  · rw [hgradientStart, hgradientNext]
    simpa only [Q.symm.inner_map_map] using h.strongCurvature

end LineSearch.IsStrongWolfe

namespace DFP.StrongWolfeCounterexample

/-- TASK-03: Adjoining an identity quadratic block transports a strong-Wolfe
counterexample while preserving all inherited weak-certificate fields. -/
theorem orthogonalSum {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] {m M c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample ι m M c₁ c₂)
    (hm : m ≤ 1) (hM : 1 ≤ M) :
    Nonempty (DFP.StrongWolfeCounterexample (ι ⊕ κ) m M c₁ c₂) := by
  classical
  let iteration : DFP.InverseIteration (ι ⊕ κ) :=
    c.iteration.orthogonalSum (κ := κ) c.stepLengthPos
  have hembed (z : EuclideanSpace ℝ ι) :
      (DFP.OrthogonalSum.embed z : EuclideanSpace ℝ (ι ⊕ κ)) =
        EuclideanSpace.OrthogonalSum.inl (κ := κ) z := by
    ext i
    cases i with
    | inl i =>
        have h := DFP.OrthogonalSum.embed_apply_inl (κ := κ) z i
        simpa only [EuclideanSpace.OrthogonalSum.inl_apply_inl] using h
    | inr j =>
        have h := DFP.OrthogonalSum.embed_apply_inr (κ := κ) z j
        simpa only [EuclideanSpace.OrthogonalSum.inl_apply_inr] using h
  have objectiveContDiff : ContDiff ℝ 2 iteration.objective := by
    have h := EuclideanSpace.OrthogonalSum.Gradient.contDiff_objective
      (kappa := κ) c.objectiveContDiff
    simpa only [iteration, DFP.InverseIteration.orthogonalSum_objective,
      DFP.OrthogonalSum.objective_eq] using h
  have stepLengthPos (k : ℕ) : 0 < iteration.stepLength k := by
    simpa only [iteration, DFP.InverseIteration.orthogonalSum_stepLength] using
      c.stepLengthPos k
  have hessianBounds : HasHessianBounds m M iteration.objective := by
    have h := DFP.OrthogonalSum.hasHessianBounds_objective
      (κ := κ) c.objectiveContDiff c.hessianBounds hm hM
    simpa only [iteration, DFP.InverseIteration.orthogonalSum_objective] using h
  have weakWolfe (k : ℕ) :
      LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
        (iteration.point k) (iteration.point (k + 1) - iteration.point k) := by
    have h := (LineSearch.IsWeakWolfe.orthogonalSum_iff
      (κ := κ)).mpr (c.weakWolfe k)
    simpa only [iteration, DFP.InverseIteration.orthogonalSum_objective,
      DFP.InverseIteration.orthogonalSum_point, map_sub] using h
  have strongWolfe (k : ℕ) :
      LineSearch.IsStrongWolfe c₁ c₂ iteration.objective
        (iteration.point k) (iteration.point (k + 1) - iteration.point k) := by
    have h := (LineSearch.IsStrongWolfe.orthogonalSum_iff
      (κ := κ)).mpr (c.strongWolfe k)
    simpa only [iteration, DFP.InverseIteration.orthogonalSum_objective,
      DFP.InverseIteration.orthogonalSum_point, DFP.OrthogonalSum.objective_eq,
      hembed, map_sub] using h
  have gradientNormTendsto :
      Tendsto
        (fun k ↦ ‖DFP.gradients iteration.objective iteration.point k‖)
        atTop (𝓝 c.gradientLimit) := by
    dsimp only [iteration]
    rw [DFP.InverseIteration.orthogonalSum_gradients]
    simpa only [DFP.OrthogonalSum.norm_embed] using c.gradientNormTendsto
  let result : DFP.StrongWolfeCounterexample (ι ⊕ κ) m M c₁ c₂ := {
    toWolfeCounterexample := {
      iteration := iteration
      gradientLimit := c.gradientLimit
      objectiveContDiff := objectiveContDiff
      stepLengthPos := stepLengthPos
      hessianBounds := hessianBounds
      weakWolfe := weakWolfe
      gradientLimitPos := c.gradientLimitPos
      gradientNormTendsto := gradientNormTendsto
    }
    strongWolfe := strongWolfe
  }
  exact ⟨result⟩

/-- TASK-03: Pulling a strong-Wolfe counterexample back through a linear
isometry equivalence preserves its trajectory, bounds, and strong field. -/
theorem pullback_linearIsometryEquiv {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] {m M c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample ι m M c₁ c₂)
    (Q : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hm : 0 ≤ m) (hM : 0 ≤ M) :
    Nonempty (DFP.StrongWolfeCounterexample κ m M c₁ c₂) := by
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
  have strongWolfe (k : ℕ) :
      LineSearch.IsStrongWolfe c₁ c₂ iteration.objective
        (iteration.point k) (iteration.point (k + 1) - iteration.point k) := by
    have h := LineSearch.IsStrongWolfe.comp_linearIsometryEquiv
      (c.strongWolfe k) Q
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
  let result : DFP.StrongWolfeCounterexample κ m M c₁ c₂ := {
    toWolfeCounterexample := {
      iteration := iteration
      gradientLimit := c.gradientLimit
      objectiveContDiff := objectiveContDiff
      stepLengthPos := stepLengthPos
      hessianBounds := hessianBounds
      weakWolfe := weakWolfe
      gradientLimitPos := c.gradientLimitPos
      gradientNormTendsto := gradientNormTendsto
    }
    strongWolfe := strongWolfe
  }
  exact ⟨result⟩

end DFP.StrongWolfeCounterexample
