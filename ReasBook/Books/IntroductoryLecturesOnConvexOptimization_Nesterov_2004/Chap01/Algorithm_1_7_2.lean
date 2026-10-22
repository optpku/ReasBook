/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_7_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open NewtonSystem (AdmissiblePoint)

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace DampedNewton

/- Layer targeted by this refinement:
* source-facing: `DampedNewton.Method`
* core/canonical: the admissible domain `AdmissiblePoint (∇ f)` from Algorithm 1.7.1 together
  with the one-step damped update `step`
* bridge/view: the stronger closure-based recursive orbit `orbitPoint`, its underlying trajectory
  `orbit`, and the induced method `orbitMethod`

Primary domain:
* finite-dimensional damped Newton iterations for unconstrained minimization

Sampled owner-style declarations:
* `NewtonSystem.AdmissiblePoint`
* `NewtonSystem.Method`
* `NewtonSystem.orbitPoint`
* `Function.iterate`

Owner abstraction:
* `NewtonSystem.AdmissiblePoint (∇ f)` is the ambient owner of Hessian nondegeneracy; a damped
  Newton method is a trajectory in this admissible domain together with positive damping factors
  and the damped recursion

Primitive data:
* for the one-step update: `f`, an admissible point `x : AdmissiblePoint (∇ f)`, and a scalar
  step size `h`
* for a source-facing damped Newton method: an admissible-point trajectory, its initial value
  `x₀`, a positive step-size schedule `hₖ`, and the one-step recursion

Derived API:
* the underlying `E`-valued trajectory, iterate-wise Hessian nondegeneracy, and the textbook
  coordinate formula for the damped step
* under the stronger bridge hypothesis `StepPreservesAdmissibility`, the recursive orbit in the
  admissible Newton domain and the induced source-facing method `orbitMethod`

The closure-based recursive orbit is auxiliary: it constructs a damped Newton method under a
global admissibility-preservation hypothesis, but it is not the main source-facing owner.

Later chapter-specific damped-Newton notions are specializations or refinements of this owner
layer; they do not replace the chapter-1 source-facing method with arbitrary positive damping
factors.
-/

/-- The damped Newton update with step size `h` at an admissible point `x`. It is the affine
interpolation between the current point and the full Newton step. -/
def step (f : E → ℝ) (x : AdmissiblePoint (∇ f)) (h : ℝ) : E :=
  AffineMap.lineMap (x : E) (NewtonSystem.step (∇ f) x) h

/-- Expanding `step f x h` gives the textbook formula
`x₊ = x - h [∇² f(x)]⁻¹ ∇ f(x)`. -/
theorem step_def (f : E → ℝ) (x : AdmissiblePoint (∇ f)) (h : ℝ) :
    step f x h =
      x - h • (((fderiv ℝ (∇ f) x).toContinuousLinearEquivOfDetNeZero x.property).symm
        (∇ f x)) := by
  rw [step, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, NewtonSystem.step_def,
    sub_eq_add_neg]
  abel_nf
  simp

section EuclideanSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- In Euclidean coordinates, the owner damped Newton update is the textbook line-search
formula `x - h [∇² f(x)]⁻¹ ∇ f(x)`. -/
theorem step_eq_hessianMatrixFormula
    (f : E → ℝ) (x : AdmissiblePoint (∇ f)) (h : ℝ) :
    step f x h = x - h • ((∇² f x)⁻¹).toEuclideanLin (∇ f x) := by
  rw [step_def]
  suffices
      (((fderiv ℝ (∇ f) (x : E)).toContinuousLinearEquivOfDetNeZero x.property).symm (∇ f x)) =
        ((∇² f x)⁻¹).toEuclideanLin (∇ f x) by
    rw [this]
  let A := ∇² f x
  have hA_det : A.det ≠ 0 := by
    have hx : (fderiv ℝ (∇ f) (x : E)).det ≠ 0 := x.property
    change LinearMap.det (fderiv ℝ (∇ f) (x : E)).toLinearMap ≠ 0 at hx
    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (fderiv ℝ (∇ f) (x : E)).toLinearMap] at hx
    simpa [A, hessianMatrix] using hx
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let eM : E ≃ₗ[ℝ] E := Matrix.toLinearEquiv b A (isUnit_iff_ne_zero.mpr hA_det)
  let eF : E ≃ₗ[ℝ] E :=
    ((fderiv ℝ (∇ f) (x : E)).toContinuousLinearEquivOfDetNeZero x.property).toLinearEquiv
  have heq : eM = eF := by
    apply LinearEquiv.toLinearMap_injective
    change ((∇² f x).toEuclideanLin : E →ₗ[ℝ] E) =
      (fderiv ℝ (∇ f) (x : E)).toLinearMap
    simpa using hessianMatrix_toEuclideanLin f (x : E)
  have hsymm := congrArg (fun e' : E ≃ₗ[ℝ] E ↦ e'.symm (∇ f x)) heq
  have hmatrix :
      eM.symm (∇ f x) = (A⁻¹).toEuclideanLin (∇ f x) := by
    change (Matrix.toLinearEquiv b A (isUnit_iff_ne_zero.mpr hA_det)).symm (∇ f x) =
      (Matrix.toLin b b A⁻¹) (∇ f x)
    rfl
  exact hsymm.symm.trans hmatrix

end EuclideanSpace

/-- Algorithm 1.7.2: a damped Newton method for `f` started at `x₀` is an iterate sequence
`x₀, x₁, x₂, ...` through Hessian-nondegenerate points, together with positive damping factors
`hₖ`, and the damped Newton recursion
`xₖ₊₁ = xₖ - hₖ [∇² f(xₖ)]⁻¹ ∇ f(xₖ)` at every step. -/
structure Method (f : E → ℝ) (x0 : E) where
  /-- The iterate sequence `x₀, x₁, x₂, ...`, valued in the natural admissible domain. -/
  x : ℕ → AdmissiblePoint (∇ f)
  /-- The zeroth iterate is the prescribed initial point `x₀`. -/
  x_zero : x 0 = x0
  /-- The positive damping factors `hₖ`. -/
  stepSize : ℕ → ℝ
  /-- Every damping factor is strictly positive. -/
  stepSize_pos : ∀ k : ℕ, 0 < stepSize k
  /-- Each iterate is obtained from the previous one by the damped Newton update. -/
  step_eq : ∀ k : ℕ, x (k + 1) = step f (x k) (stepSize k)

namespace Method

variable {f : E → ℝ} {x0 : E}

/-- A damped Newton method can be used as its underlying trajectory of iterates. -/
instance : CoeFun (Method f x0) (fun _ ↦ ℕ → E) where
  coe method := fun k ↦ method.x k

/-- The Hessian of `f` is nondegenerate at every iterate of a damped Newton method. -/
theorem hessian_nondegenerate
    (method : Method f x0) (k : ℕ) :
    (fderiv ℝ (∇ f) (method k)).det ≠ 0 :=
  (method.x k).property

/-- Every damped Newton method starts from its prescribed initial point. -/
@[simp] theorem zero_eq (method : Method f x0) :
    method 0 = x0 :=
  method.x_zero

/-- Each iterate of a damped Newton method is the damped Newton update of the previous iterate. -/
theorem succ_eq
    (method : Method f x0) (k : ℕ) :
    method (k + 1) = step f (method.x k) (method.stepSize k) :=
  method.step_eq k

end Method

/-- Auxiliary bridge hypothesis: a damped Newton step of size `h` carries every Hessian-
nondegenerate point to another Hessian-nondegenerate point. This stronger global condition is
used only to build the canonical recursive orbit in the admissible Newton domain. -/
def StepPreservesAdmissibility (f : E → ℝ) (h : ℝ) : Prop :=
  ∀ x : AdmissiblePoint (∇ f), (fderiv ℝ (∇ f) (step f x h)).det ≠ 0

private def stepMap
    (f : E → ℝ)
    (h : ℝ)
    (hstep : StepPreservesAdmissibility f h) :
    AdmissiblePoint (∇ f) → AdmissiblePoint (∇ f) :=
  fun x ↦ ⟨step f x h, hstep x⟩

section Orbit

variable (f : E → ℝ) (x0 : AdmissiblePoint (∇ f))
variable (stepSize : ℕ → ℝ)
variable (hstep : ∀ k : ℕ, StepPreservesAdmissibility f (stepSize k))

/-- The canonical recursive orbit in the admissible Newton domain, defined when admissibility is
preserved by one damped Newton step at each prescribed step size. -/
def orbitPoint : ℕ → AdmissiblePoint (∇ f)
  | 0 => x0
  | k + 1 => stepMap f (stepSize k) (hstep k) (orbitPoint k)

/-- The damped Newton orbit generated from the initial point `x₀` and the step-size schedule
`hₖ`, assuming `x₀` lies in the admissible Newton domain and admissibility remains true after
every damped Newton step. -/
abbrev orbit : ℕ → E :=
  fun k ↦ orbitPoint f x0 stepSize hstep k

@[simp] theorem orbit_zero :
    orbit f x0 stepSize hstep 0 = x0 :=
  rfl

/-- The Hessian of `f` is nondegenerate at every iterate of the canonical damped Newton orbit. -/
theorem orbit_hessian_nondegenerate
    (k : ℕ) :
    (fderiv ℝ (∇ f) (orbit f x0 stepSize hstep k)).det ≠ 0 :=
  (orbitPoint f x0 stepSize hstep k).property

/-- The canonical damped Newton orbit satisfies the recursive damped update rule. -/
theorem orbit_succ
    (k : ℕ) :
    orbit f x0 stepSize hstep (k + 1) =
      step f (orbitPoint f x0 stepSize hstep k) (stepSize k) := by
  simp [orbit, orbitPoint, stepMap]

/-- Under the stronger global admissibility-preservation hypothesis, the canonical recursive orbit
produces a source-facing damped Newton method. -/
def orbitMethod
    (stepSize_pos : ∀ k : ℕ, 0 < stepSize k) :
    Method f x0 where
  x := orbitPoint f x0 stepSize hstep
  x_zero := rfl
  stepSize := stepSize
  stepSize_pos := stepSize_pos
  step_eq := fun k ↦ by simp [orbitPoint, stepMap]

end Orbit

end DampedNewton

end
