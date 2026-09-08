module

public import ReasLib.Analysis.Calculus.Gradient.OrthogonalSum
public import ReasLib.Optimization.DFP.OrthogonalSum.Transport
public import ReasLib.Optimization.DFP.Orbit
public import ReasLib.Optimization.LineSearch

public section

/-!
# Orthogonal-sum transport for DFP orbits and weak Wolfe conditions

This file packages the final transport layer needed by the finite-dimensional
orthogonal-sum construction.  The results are stated against the public APIs in
the generic Euclidean, gradient, DFP, and line-search modules, so downstream
proofs do not have to unfold the corresponding definitions.
-/

noncomputable section

universe u v

open scoped Matrix

namespace EuclideanSpace.OrthogonalSum.Gradient

/-- Differentiability of the lifted objective at an embedded point is equivalent
to differentiability of the original objective. -/
theorem differentiableAt_objective_inl_iff {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] {f : EuclideanSpace ℝ ι → ℝ}
    {z : EuclideanSpace ℝ ι} :
    DifferentiableAt ℝ (objective (κ := κ) f)
        (EuclideanSpace.OrthogonalSum.inl (κ := κ) z) ↔
      DifferentiableAt ℝ f z := by
  constructor
  · intro h
    have hcomp := h.comp z
      (EuclideanSpace.OrthogonalSum.inl (ι := ι) (κ := κ)).differentiableAt
    have heq :
        objective (κ := κ) f ∘ EuclideanSpace.OrthogonalSum.inl (ι := ι) (κ := κ) = f := by
      funext w
      exact objective_inl f w
    rw [heq] at hcomp
    exact hcomp
  · intro h
    exact (hasGradientAt_objective_inl (κ := κ) h.hasGradientAt).differentiableAt

end EuclideanSpace.OrthogonalSum.Gradient

namespace DFP.OrthogonalSum.Lift

/-- A DFP orbit lifts through the orthogonal-sum embedding. -/
theorem isOrbit {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    {f : EuclideanSpace ℝ ι → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ ι} {H : ℕ → Matrix ι ι ℝ}
    (h : DFP.IsOrbit f α x g H) :
    DFP.IsOrbit (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f) α
      (fun k ↦ EuclideanSpace.OrthogonalSum.inl (κ := κ) (x k))
      (fun k ↦ EuclideanSpace.OrthogonalSum.inl (κ := κ) (g k))
      (fun k ↦ EuclideanSpace.OrthogonalSum.extendMatrix (κ := κ) (H k)) := by
  refine {
    stepLengthPos := h.stepLengthPos
    gradientAt := fun k =>
      EuclideanSpace.OrthogonalSum.Gradient.hasGradientAt_objective_inl (h.gradientAt k)
    pointSucc := ?_
    inverseHessianSucc := ?_
  }
  · intro k
    rw [DFP.steps_apply,
      DFP.OrthogonalSum.Transport.directions_inl (κ := κ) H g k]
    rw [← (EuclideanSpace.OrthogonalSum.inl (ι := ι) (κ := κ)).map_smul,
      ← (EuclideanSpace.OrthogonalSum.inl (ι := ι) (κ := κ)).map_add]
    have hp := congrArg (EuclideanSpace.OrthogonalSum.inl (ι := ι) (κ := κ))
      (h.pointSucc k)
    rw [DFP.steps_apply] at hp
    exact hp
  · intro k
    rw [DFP.steps_apply,
      DFP.OrthogonalSum.Transport.directions_inl (κ := κ) H g k,
      ← (EuclideanSpace.OrthogonalSum.inl (ι := ι) (κ := κ)).map_smul,
      ← DFP.steps_apply α (DFP.directions H g) k,
      DFP.gradientChanges_apply,
      ← (EuclideanSpace.OrthogonalSum.inl (ι := ι) (κ := κ)).map_sub,
      ← DFP.gradientChanges_apply g k,
      DFP.OrthogonalSum.Transport.inverseDFPUpdate_extendMatrix_inl]
    exact congrArg (EuclideanSpace.OrthogonalSum.extendMatrix (κ := κ))
      (h.inverseHessianSucc k)

/-- The weak Wolfe conditions are invariant under the orthogonal-sum embedding. -/
theorem weakWolfe_iff {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] {c₁ c₂ : ℝ}
    {f : EuclideanSpace ℝ ι → ℝ} {x s : EuclideanSpace ℝ ι} :
    LineSearch.IsWeakWolfe c₁ c₂
        (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f)
        (EuclideanSpace.OrthogonalSum.inl (κ := κ) x)
        (EuclideanSpace.OrthogonalSum.inl (κ := κ) s) ↔
      LineSearch.IsWeakWolfe c₁ c₂ f x s := by
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
      weakCurvature := ?_
    }
    · simpa only [hsum,
        EuclideanSpace.OrthogonalSum.Gradient.objective_inl,
        EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl hxDiff,
        EuclideanSpace.OrthogonalSum.inner_inl] using h.armijo
    · simpa only [hsum,
        EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl hxDiff,
        EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl hnextDiff,
        EuclideanSpace.OrthogonalSum.inner_inl] using h.weakCurvature
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
      weakCurvature := ?_
    }
    · simpa only [hsum,
        EuclideanSpace.OrthogonalSum.Gradient.objective_inl,
        EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl h.differentiableAt,
        EuclideanSpace.OrthogonalSum.inner_inl] using h.armijo
    · simpa only [hsum,
        EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl h.differentiableAt,
        EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl h.differentiableAtNext,
        EuclideanSpace.OrthogonalSum.inner_inl] using h.weakCurvature

end DFP.OrthogonalSum.Lift
