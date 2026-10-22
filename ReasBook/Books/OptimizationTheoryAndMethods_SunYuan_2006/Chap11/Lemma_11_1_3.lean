/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Lemma_11_1_1

noncomputable section

section Chapter11Lemma113

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Semantic recall: `lean_leansearch` surfaced the generic extremum/minimizer APIs and
-- `DifferentiableAt.hasGradientAt`, so the Hessian-max owner below records the along-ray
-- differentiability needed for `gradient f` and `fderiv ℝ (gradient f)` to denote the source
-- `∇ f` and `∇² f` data rather than their totalized Lean terms. The chapter already owns the
-- source feasible-direction predicate in `Chapter08.Definition_8_2_1` and the Chapter 11
-- use of the canonical distance owner `Metric.infDist x Xᶜ`, so this file keeps only the exact
-- line-search step domain and the Hessian-ray bound that are specific to Lemma 11.1.3.

/-- The source exact line-search step domain along `d` from `x`, truncated by the radius bound
`Metric.infDist x Xᶜ / ‖d‖` and including the endpoint `0`. -/
def feasibleDirectionStepSet
    (X : Set Point) (x d : Point) : Set ℝ :=
  Set.Icc (0 : ℝ) (Metric.infDist x Xᶜ / ‖d‖)

/-- Membership in `feasibleDirectionStepSet X x d` means exactly that `α` lies in the source
truncated interval `Set.Icc 0 (Metric.infDist x Xᶜ / ‖d‖)`. -/
theorem mem_feasibleDirectionStepSet_iff
    (X : Set Point) (x d : Point) (α : ℝ) :
    α ∈ feasibleDirectionStepSet X x d ↔
      α ∈ Set.Icc (0 : ℝ) (Metric.infDist x Xᶜ / ‖d‖) :=
  Iff.rfl

/-- `IsFeasibleDirectionHessianRayMaximum f x d M` says that `M` is the source quantity
`max_(t ≥ 0) ‖∇² f (x + t • d)‖₂`, with the needed along-ray differentiability hypotheses bundled
so that `gradient f` and `fderiv ℝ (gradient f)` denote the actual gradient and Hessian data
along the nonnegative ray `x + t • d`. -/
class IsFeasibleDirectionHessianRayMaximum
    (f : Point → ℝ) (x d : Point) (M : ℝ) : Prop where
  differentiableAlongRay :
    ∀ t ∈ Set.Ici (0 : ℝ), DifferentiableAt ℝ f (x + t • d)
  gradientDifferentiableAlongRay :
    ∀ t ∈ Set.Ici (0 : ℝ), DifferentiableAt ℝ (gradient f) (x + t • d)
  isGreatest :
    IsGreatest ((fun t : ℝ ↦ ‖fderiv ℝ (gradient f) (x + t • d)‖) '' Set.Ici (0 : ℝ)) M

/-- `IsFeasibleDirectionHessianRayMaximum f x d M` is proposition-valued. -/
instance isFeasibleDirectionHessianRayMaximumSubsingleton
    (f : Point → ℝ) (x d : Point) (M : ℝ) :
    Subsingleton (IsFeasibleDirectionHessianRayMaximum f x d M) := inferInstance

/-- Unfolding formula for `IsFeasibleDirectionHessianRayMaximum f x d M`. -/
theorem isFeasibleDirectionHessianRayMaximum_iff
    (f : Point → ℝ) (x d : Point) (M : ℝ) :
    IsFeasibleDirectionHessianRayMaximum f x d M ↔
      (∀ t ∈ Set.Ici (0 : ℝ), DifferentiableAt ℝ f (x + t • d)) ∧
        (∀ t ∈ Set.Ici (0 : ℝ), DifferentiableAt ℝ (gradient f) (x + t • d)) ∧
          IsGreatest ((fun t : ℝ ↦ ‖fderiv ℝ (gradient f) (x + t • d)‖) '' Set.Ici (0 : ℝ))
            M := by
  constructor
  · intro h
    exact ⟨h.differentiableAlongRay, h.gradientDifferentiableAlongRay, h.isGreatest⟩
  · rintro ⟨hdiff, hgrad, hGreatest⟩
    exact
      { differentiableAlongRay := hdiff
        gradientDifferentiableAlongRay := hgrad
        isGreatest := hGreatest }

/-- Chapter11 Lemma 11.1.3. Assume `d ∈ FD(x, X)` and `αStar` satisfies the source exact
line-search condition `(11.1.11)` on the truncated step domain
`feasibleDirectionStepSet X x d = Set.Icc 0 (Metric.infDist x Xᶜ / ‖d‖)`, encoded as both
`αStar ∈ feasibleDirectionStepSet X x d` and minimization of `α ↦ f (x + α • d)` on that set
because `IsMinOn` itself does not enforce set membership. If `M` is the source maximum
`max_(t ≥ 0) ‖∇² f (x + t • d)‖₂` along the ray, with the needed along-ray differentiability
bundled into `IsFeasibleDirectionHessianRayMaximum`, and `0 < M` so the coefficient
`1 / (2 * M)` matches the source formula, then either the source quadratic-model decrease
estimate `(11.1.12)` or the boundary-limited decrease estimate `(11.1.13)` holds. -/
theorem exactLineSearch_decrease_or_boundaryDecrease_of_feasibleDirection
    (f : Point → ℝ) (X : Set Point) (x d : Point) (M αStar : ℝ)
    (hd : d ∈ feasibleDirections x X)
    (hM : IsFeasibleDirectionHessianRayMaximum f x d M)
    (hM_pos : 0 < M)
    (hαStar_mem : αStar ∈ feasibleDirectionStepSet X x d)
    (hαStar :
      IsMinOn (fun α : ℝ ↦ f (x + α • d))
        (feasibleDirectionStepSet X x d) αStar) :
    f x - f (x + αStar • d) ≥
        (1 / (2 * M)) * (inner ℝ d (gradient f x) / ‖d‖) ^ (2 : ℕ) ∨
      f x - f (x + αStar • d) ≥
        -((Metric.infDist x Xᶜ) / (2 * ‖d‖)) * inner ℝ d (gradient f x) := sorry

#print axioms IsFeasibleDirectionHessianRayMaximum
#print axioms feasibleDirectionStepSet

end Chapter11Lemma113
