/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.FDeriv.WithLp
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin Gradient ModifiedGaussNewtonLocalModelNotation
open ContinuousLinearMap PiLp

universe u v

/- Definition 4.4.2 lies in the constrained Gauss--Newton local-model domain.

Primary domain:
* feasible-step minimization for the affine Gauss--Newton residual model

Sampled owner-style declarations:
* `modifiedGaussNewtonLocalModel` with notation `ψ[F; φ; J]` in `Definition_4_4_11`, the chapter
  owner for affine residual/Jacobian local models
* `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project
  owner for minimizers on a feasible set
* `LagrangianProblem.constraintVector` in `Chap01/Definition_1_10_2`, the upstream owner for
  packaging a finite scalar family into an `ℝ^m`-valued residual map
* `fderiv` / `HasGradientAt.fderiv_apply`, the canonical Jacobian and scalar-gradient bridge in
  mathlib

Best owner abstraction:
* source-facing: feasible step directions `h` with `x + h ∈ D x`
* core/canonical: the affine residual local model `ψ[F; φ; J]` together with `argmin[Q]`
* bridge/view: the step-space specialization `h ↦ ψ[F; φ; J](x; x + h)` and, under
  differentiability hypotheses on coordinate functions, the textbook formula
  `f_i(x) + ⟪∇ f_i(x), h⟫`

Primitive data:
* a residual map `F : E₁ → E₂`
* a Jacobian family `J : E₁ → E₁ →L[ℝ] E₂`
* a merit function `φ : E₂ → ℝ`
* a neighborhood map `D : E₁ → Set E₁`
* a base point `x : E₁`

Derived API:
* the feasible-direction set `{h | x + h ∈ D x}`
* the source-facing search-direction predicate as constrained minimization of the step-space view
  of `ψ[F; φ; J]`
* the coordinate-gradient bridge when `F = (LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector`
  and `J` is its Jacobian

Source/core/bridge triage:
* source-facing: `IsGaussNewtonSearchDirectionAt`
* core/canonical: `modifiedGaussNewtonLocalModel` and `argmin[Q]`
* bridge/view: step-space evaluation at `x + h`, and the coordinate-gradient specialization

This refinement keeps the source-facing feasible-step predicate, but moves its objective to the
chapter's explicit residual/Jacobian owner layer. The coordinate formula with totalized gradients
survives only as a bridge theorem.
-/

section FeasibleDirections

variable {E : Type u} [Add E]

/-- The feasible directions for the local Gauss--Newton subproblem are the steps `h` such that
the trial point `x + h` stays inside the chosen neighborhood `D x`. -/
def gaussNewtonFeasibleDirections
    (D : E → Set E) (x : E) : Set E :=
  {h | x + h ∈ D x}

/-- Membership in the feasible-direction set is exactly the condition `x + h ∈ D x`. -/
@[simp]
theorem mem_gaussNewtonFeasibleDirections_iff
    {D : E → Set E} {x h : E} :
    h ∈ gaussNewtonFeasibleDirections D x ↔ x + h ∈ D x :=
  Iff.rfl

end FeasibleDirections

section StepModelBridge

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- Evaluating the chapter Gauss--Newton local model at the trial point `x + h` gives the
step-space affine residual formula `φ (F x + J x h)`. -/
@[simp] theorem modifiedGaussNewtonLocalModel_step_apply
    (F : E₁ → E₂)
    (φ : E₂ → ℝ)
    (J : E₁ → E₁ →L[ℝ] E₂) (x h : E₁) :
    ψ[F; φ; J](x; (x + h)) = φ (F x + J x h) := by
  simp [modifiedGaussNewtonLocalModel]

end StepModelBridge

section CoordinateGradientBridge

variable {m : ℕ}
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "ResidualSpace" => EuclideanSpace ℝ (Fin m)

/-- If each coordinate residual `f_i` has gradient `∇ f_i(x)` at `x`, then the Jacobian of the
packaged residual map `(LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector` has the expected
coordinate formula. -/
theorem fderiv_constraintVector_apply
    (fs : Fin m → E → ℝ) (x h : E)
    (hfs_grad : ∀ i, HasGradientAt (fs i) (∇ (fs i) x) x) (i : Fin m) :
    fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h i =
      inner ℝ (∇ (fs i) x) h := by
  have hdiff :
      DifferentiableAt ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x := by
    rw [differentiableAt_piLp]
    intro j
    simpa [LagrangianProblem.constraintVector_apply] using (hfs_grad j).differentiableAt
  have hproj :
      HasFDerivAt
        (fun y ↦ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector y).ofLp i)
        ((PiLp.proj 2 (fun _ : Fin m ↦ ℝ) i).comp
          (fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x)) x := by
    exact
      (PiLp.hasFDerivAt_apply
        2
        ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x)
        i).comp x hdiff.hasFDerivAt
  have hcoord :
      fderiv ℝ (fun y ↦ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector y).ofLp i) x h =
        inner ℝ (∇ (fs i) x) h := by
    change fderiv ℝ (fs i) x h = inner ℝ (∇ (fs i) x) h
    exact (hfs_grad i).fderiv_apply
  have hproj_apply := congrArg (fun L : E →L[ℝ] ℝ ↦ L h) hproj.fderiv
  simpa [PiLp.proj_apply] using hproj_apply.symm.trans hcoord

/-- Under the coordinate gradient hypotheses, the affine residual attached to
`(LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector` is exactly the packaged textbook
linearization `(f_i(x) + ⟪∇ f_i(x), h⟫)_i`. -/
@[simp] theorem constraintVector_add_fderiv_eq_linearizedResidual
    (fs : Fin m → E → ℝ) (x h : E)
    (hfs_grad : ∀ i, HasGradientAt (fs i) (∇ (fs i) x) x) :
    (LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x +
        fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h =
      (LagrangianProblem.mk
        (fun _ ↦ 0)
        (fun i h' ↦ fs i x + inner ℝ (∇ (fs i) x) h')).constraintVector h := by
  ext i
  simp [fderiv_constraintVector_apply, hfs_grad, LagrangianProblem.constraintVector_apply]

/-- For the packaged residual map `(LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector`, the
step-space local model attached to its canonical Jacobian recovers the textbook
coordinate-gradient formula under the corresponding gradient hypotheses. -/
@[simp] theorem modifiedGaussNewtonLocalModel_step_constraintVector_fderiv_apply
    (φ : ResidualSpace → ℝ)
    (fs : Fin m → E → ℝ) (x h : E)
    (hfs_grad : ∀ i, HasGradientAt (fs i) (∇ (fs i) x) x) :
    modifiedGaussNewtonLocalModel
        ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector)
        φ
        (fun y ↦ fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) y)
        x
        (x + h) =
      φ
        ((LagrangianProblem.mk
          (fun _ ↦ 0)
          (fun i h' ↦ fs i x + inner ℝ (∇ (fs i) x) h')).constraintVector h) := by
  rw [modifiedGaussNewtonLocalModel_step_apply]
  simp [constraintVector_add_fderiv_eq_linearizedResidual, hfs_grad]

end CoordinateGradientBridge

section Definition_4_4_2

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- Definition 4.4.2: a Gauss--Newton search direction at `x` is a feasible step `h` with
`x + h ∈ D x` whose step-space local-model value `ψ[F; φ; J](x; x + h)` is minimal among all
feasible steps for the auxiliary Gauss--Newton subproblem. -/
def IsGaussNewtonSearchDirectionAt
    (φ : E₂ → ℝ)
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (D : E₁ → Set E₁) (x h : E₁) : Prop :=
  h ∈ argmin[gaussNewtonFeasibleDirections D x] (fun h' ↦ ψ[F; φ; J](x; (x + h')))

namespace IsGaussNewtonSearchDirectionAt

/-- Expanding `IsGaussNewtonSearchDirectionAt φ F J D x h` gives feasibility of `h` together with
minimality of the step-space Gauss--Newton local model among all feasible steps. -/
@[simp] theorem iff
    (φ : E₂ → ℝ)
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (D : E₁ → Set E₁) (x h : E₁) :
    IsGaussNewtonSearchDirectionAt φ F J D x h ↔
      x + h ∈ D x ∧
        ∀ h', x + h' ∈ D x →
          ψ[F; φ; J](x; (x + h)) ≤ ψ[F; φ; J](x; (x + h')) := by
  simp [IsGaussNewtonSearchDirectionAt, isMinOn_iff, gaussNewtonFeasibleDirections]

/-- A Gauss--Newton search direction is feasible for the local model constraint set. -/
theorem feasible
    {φ : E₂ → ℝ}
    {F : E₁ → E₂}
    {J : E₁ → E₁ →L[ℝ] E₂}
    {D : E₁ → Set E₁} {x h : E₁}
    (hh : IsGaussNewtonSearchDirectionAt φ F J D x h) :
    x + h ∈ D x :=
  (iff φ F J D x h).1 hh |>.1

/-- A Gauss--Newton search direction minimizes the step-space Gauss--Newton local model over all
feasible directions. -/
theorem isMinOn
    {φ : E₂ → ℝ}
    {F : E₁ → E₂}
    {J : E₁ → E₁ →L[ℝ] E₂}
    {D : E₁ → Set E₁} {x h : E₁}
    (hh : IsGaussNewtonSearchDirectionAt φ F J D x h) :
    IsMinOn
      (fun h' ↦ ψ[F; φ; J](x; (x + h')))
      (gaussNewtonFeasibleDirections D x) h := by
  exact (mem_constrainedArgmin_iff.mp (by simpa [IsGaussNewtonSearchDirectionAt] using hh)).2

end IsGaussNewtonSearchDirectionAt

end Definition_4_4_2

section CoordinateGradientView

variable {m : ℕ}
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "ResidualSpace" => EuclideanSpace ℝ (Fin m)

namespace IsGaussNewtonSearchDirectionAt

/-- When `F = (LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector` and `J` is its Jacobian,
Definition 4.4.2 reduces to the textbook coordinate-gradient formula. This is a bridge theorem,
not the owner declaration. -/
@[simp] theorem iff_constraintVector_fderiv
    (φ : ResidualSpace → ℝ)
    (fs : Fin m → E → ℝ)
    (D : E → Set E) (x h : E)
    (hfs_grad : ∀ i, HasGradientAt (fs i) (∇ (fs i) x) x) :
    IsGaussNewtonSearchDirectionAt
        φ
        ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector)
        (fun y ↦ fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) y)
        D
        x
        h ↔
      x + h ∈ D x ∧
        ∀ h', x + h' ∈ D x →
          φ
              ((LagrangianProblem.mk
                (fun _ ↦ 0)
                (fun i h'' ↦ fs i x + inner ℝ (∇ (fs i) x) h'')).constraintVector h) ≤
            φ
              ((LagrangianProblem.mk
                (fun _ ↦ 0)
                (fun i h'' ↦ fs i x + inner ℝ (∇ (fs i) x) h'')).constraintVector h') := by
  constructor
  · intro hh
    rcases
        (iff
          φ
          ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector)
          (fun y ↦ fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) y)
          D
          x
          h).1 hh with
      ⟨hx, hmin⟩
    refine ⟨hx, ?_⟩
    intro h' hh'
    have hAffine :
        φ
            ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x +
              fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h) ≤
          φ
            ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x +
              fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h') := by
      simpa [modifiedGaussNewtonLocalModel_step_apply] using hmin h' hh'
    calc
      φ
          ((LagrangianProblem.mk
            (fun _ ↦ 0)
            (fun i h'' ↦ fs i x + inner ℝ (∇ (fs i) x) h'')).constraintVector h) =
        φ
          ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x +
            fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h) := by
          symm
          exact congrArg φ (constraintVector_add_fderiv_eq_linearizedResidual fs x h hfs_grad)
      _ ≤ φ
          ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x +
            fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h') :=
          hAffine
      _ = φ
          ((LagrangianProblem.mk
            (fun _ ↦ 0)
            (fun i h'' ↦ fs i x + inner ℝ (∇ (fs i) x) h'')).constraintVector h') := by
          exact congrArg φ (constraintVector_add_fderiv_eq_linearizedResidual fs x h' hfs_grad)
  · rintro ⟨hx, hmin⟩
    refine
      (iff
        φ
        ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector)
        (fun y ↦ fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) y)
        D
        x
        h).2 ?_
    refine ⟨hx, ?_⟩
    intro h' hh'
    have hAffine :
        φ
            ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x +
              fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h) ≤
          φ
            ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x +
              fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h') := by
      calc
        φ
            ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x +
              fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h) =
          φ
            ((LagrangianProblem.mk
              (fun _ ↦ 0)
              (fun i h'' ↦ fs i x + inner ℝ (∇ (fs i) x) h'')).constraintVector h) := by
            exact congrArg φ (constraintVector_add_fderiv_eq_linearizedResidual fs x h hfs_grad)
        _ ≤ φ
            ((LagrangianProblem.mk
              (fun _ ↦ 0)
              (fun i h'' ↦ fs i x + inner ℝ (∇ (fs i) x) h'')).constraintVector h') :=
            hmin h' hh'
        _ = φ
            ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x +
              fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h') := by
            symm
            exact congrArg φ
              (constraintVector_add_fderiv_eq_linearizedResidual fs x h' hfs_grad)
    simpa [modifiedGaussNewtonLocalModel_step_apply] using hAffine

end IsGaussNewtonSearchDirectionAt

end CoordinateGradientView

end
