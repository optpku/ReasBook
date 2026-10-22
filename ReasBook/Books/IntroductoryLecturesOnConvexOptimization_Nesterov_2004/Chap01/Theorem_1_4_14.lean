/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped Gradient

noncomputable section

/-
Theorem 1.4.14 lives in smooth equality-constrained optimization.

Relevant owner declarations sampled before refinement:
* `IsLocalMinOn.hasFDerivWithinAt_eq_zero`
* `mem_posTangentConeAt_of_segment_subset`
* `LinearMap.orthogonal_ker`
* `DifferentiableAt.hasGradientAt`
* `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`

Best owner abstraction:
* the linear constraint map `L : E →ₗ[ℝ] F`

Primitive data:
* `f`, `L`, `b`, `xStar`
* pointwise differentiability of `f` at `xStar`
* feasibility `L xStar = b`
* local minimality of `f` on the affine level set

Derived API:
* the canonical range statement `∇ f xStar ∈ L.adjoint.range`
* the matrix-source bridge witness `λStar` with `∇ f xStar = Aᵀ.toEuclideanLin λStar`

Source/core/bridge triage:
* source-facing: existence of a Lagrange multiplier for the linear equality constraint in the
  textbook transpose form
* core/canonical: a real finite-dimensional inner-product-space map `L` together with
  `LinearMap.orthogonal_ker`
* bridge/view: `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`

The proof only uses differentiability at the minimizing point, so the refined API exposes
`DifferentiableAt ℝ f xStar` instead of a stronger global differentiability assumption. In
finite-dimensional real inner-product spaces the adjoint-range identity
`L.kerᗮ = L.adjoint.range` makes the usual surjectivity hypothesis for the constraint map
redundant, so the refined theorem omits that binder.
-/

section

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- If `xStar` is a local minimizer of a function on the linear level set `{x | L x = b}` and `f`
is differentiable at `xStar`, then the gradient at `xStar` belongs to the adjoint range of the
constraint map. -/
-- Proof sketch: every vector `h ∈ ker L` and its negative remain feasible along a
-- whole segment through `xStar`, so local minimality forces `Df(xStar) h = 0`. Hence
-- `∇ f xStar` is orthogonal to `ker L`, and `LinearMap.orthogonal_ker` rewrites
-- this orthogonality condition as membership in the adjoint range.
theorem gradient_mem_adjoint_range_of_isLocalMinOn_linearLevelSet
    (f : E → ℝ) (L : E →ₗ[ℝ] F) (b : F)
    {xStar : E} (hf : DifferentiableAt ℝ f xStar) (hxStar : L xStar = b)
    (hmin : IsLocalMinOn f {x | L x = b} xStar) :
    ∇ f xStar ∈ L.adjoint.range := by
  let constraintSet : Set E := {x | L x = b}
  have hxConstraint : xStar ∈ constraintSet := by
    simpa [constraintSet] using hxStar
  have hminConstraint : IsLocalMinOn f constraintSet xStar := by
    simpa [constraintSet] using hmin
  have hconstraint_convex : Convex ℝ constraintSet :=
    (convex_singleton b).linear_preimage L
  have hgrad_orthogonal : ∇ f xStar ∈ L.kerᗮ := by
    rw [Submodule.mem_orthogonal']
    intro h hh
    have hxPlus : xStar + h ∈ constraintSet := by
      simpa [constraintSet, hh, hxStar]
    have hxMinus : xStar + -h ∈ constraintSet := by
      simpa [constraintSet, hh, hxStar]
    have hpos : h ∈ posTangentConeAt constraintSet xStar := by
      exact mem_posTangentConeAt_of_segment_subset
        (hconstraint_convex.segment_subset hxConstraint hxPlus)
    have hneg : -h ∈ posTangentConeAt constraintSet xStar := by
      exact mem_posTangentConeAt_of_segment_subset
        (hconstraint_convex.segment_subset hxConstraint hxMinus)
    have hderiv : fderiv ℝ f xStar h = 0 :=
      hminConstraint.hasFDerivWithinAt_eq_zero hf.hasFDerivAt.hasFDerivWithinAt hpos hneg
    simpa [hf.hasGradientAt.fderiv_apply] using hderiv
  rwa [LinearMap.orthogonal_ker] at hgrad_orthogonal

end

section

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Λ" => EuclideanSpace ℝ (Fin m)

/-- Theorem 1.4.14: if `xStar` is a local minimizer of a function `f : ℝⁿ → ℝ`
on the linear level set `{x | A.toEuclideanLin x = b}` and `f` is differentiable at `xStar`,
then there is a multiplier `λStar ∈ ℝᵐ` such that
`∇ f xStar = Aᵀ.toEuclideanLin λStar`. -/
theorem exists_lagrangeMultiplier_of_isLocalMinOn_linearLevelSet
    (f : E → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Λ)
    {xStar : E} (hf : DifferentiableAt ℝ f xStar)
    (hxStar : A.toEuclideanLin xStar = b)
    (hmin : IsLocalMinOn f {x | A.toEuclideanLin x = b} xStar) :
    ∃ lamStar : Λ, ∇ f xStar = Aᵀ.toEuclideanLin lamStar := by
  rcases
      gradient_mem_adjoint_range_of_isLocalMinOn_linearLevelSet
        f A.toEuclideanLin b hf hxStar hmin with
    ⟨lamStar, hlamStar⟩
  have hAdj : A.toEuclideanLin.adjoint = Aᵀ.toEuclideanLin := by
    simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm
  refine ⟨lamStar, ?_⟩
  simpa [hAdj] using hlamStar.symm

end
