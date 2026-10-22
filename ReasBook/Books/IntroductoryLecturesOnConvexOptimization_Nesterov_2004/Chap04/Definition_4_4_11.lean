/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin

noncomputable section

universe u v

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {E₂ : Type v} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Definition 4.4.11 lies in the Gauss--Newton local-model / unconstrained minimization domain.

Sampled owner-style declarations:
* `meritFunctionReformulation` in `Definition_4_4_10`, the chapter owner for scalarizing a
  residual map by composing with a merit function;
* `ContinuousLinearMap.toAffineMap` in mathlib, the canonical owner for turning a Jacobian slice
  into the affine map `y ↦ F x + J x (y - x)`;
* `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project
  owner for minimizer sets, specialized here to `Set.univ`;
* `ConvexOn.comp_affineMap` in mathlib, the canonical convexity owner for precomposing `φ` with
  that affine residual model.

Source/core/bridge triage:
* source-facing: the modified Gauss--Newton local model `ψ(x; y)`;
* core/canonical: composition of `φ` with the affine residual linearization determined by a
  Jacobian family `J x : E₁ →L[ℝ] E₂`;
* bridge/view: the pointwise evaluation formula for `ψ(x; y)`.

Primitive data:
* a residual map `F : E₁ → E₂`;
* a Jacobian family `J : E₁ → E₁ →L[ℝ] E₂`;
* a merit function `φ : E₂ → ℝ`.

Derived API:
* pointwise evaluation of the local model;
* convexity in the trial-point variable when `φ` is convex;
* the candidate next-iterate set as the canonical owner `argmin[Set.univ]`.

The public owner therefore takes the Jacobian family as primitive data instead of presenting the
totalized operator `fderiv` as the textbook Jacobian for an arbitrary residual map.
-/

/-- Definition 4.4.11: given a residual map `F`, a Jacobian family `J`, and a merit function
`φ`, the modified Gauss--Newton local model is the two-variable function
`ψ(x; y) = φ (F(x) + J(x)(y - x))`. When `J x = F'(x)`, this is the textbook affine
first-order residual model at the base point `x`. -/
def modifiedGaussNewtonLocalModel
    (F : E₁ → E₂)
    (φ : E₂ → ℝ)
    (J : E₁ → E₁ →L[ℝ] E₂) : E₁ → E₁ → ℝ :=
  fun x ↦ meritFunctionReformulation (fun y ↦ F x + J x (y - x)) φ

/-
Source-facing Lean notation for the textbook local model `ψ(x; y)`, with the ambient residual
map, merit function, and Jacobian family recorded in bracket arguments.
-/
namespace ModifiedGaussNewtonLocalModelNotation

scoped notation:max "ψ[" F:arg "; " φ:arg "; " J:arg "]" =>
  modifiedGaussNewtonLocalModel F φ J

scoped notation:max "ψ[" F:arg "; " φ:arg "; " J:arg "](" x:arg "; " y:arg ")" =>
  modifiedGaussNewtonLocalModel F φ J x y

end ModifiedGaussNewtonLocalModelNotation

open scoped ModifiedGaussNewtonLocalModelNotation

/-- Evaluating the modified Gauss--Newton local model gives the textbook formula
`ψ[F; φ; J](x; y) = φ (F(x) + J(x)(y - x))`. -/
@[simp] theorem modifiedGaussNewtonLocalModel_apply
    (F : E₁ → E₂)
    (φ : E₂ → ℝ)
    (J : E₁ → E₁ →L[ℝ] E₂) (x y : E₁) :
    ψ[F; φ; J](x; y) = φ (F x + J x (y - x)) :=
  rfl

/-- If `φ` is convex, then the modified Gauss--Newton local model is convex in the second
argument `y` for each fixed base point `x`. -/
-- Proof sketch: for fixed `x`, the map `y ↦ F x + J x (y - x)` is affine. The
-- composition of a convex `φ` with this affine map is therefore convex on all of `E₁`.
theorem modifiedGaussNewtonLocalModel_convex
    (F : E₁ → E₂)
    (φ : E₂ → ℝ)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (hφ : ConvexOn ℝ Set.univ φ)
    (x : E₁) :
    ConvexOn ℝ Set.univ (ψ[F; φ; J] x) := by
  let g : E₁ →ᵃ[ℝ] E₂ :=
    (J x).toAffineMap.comp (AffineMap.id ℝ E₁ - AffineMap.const ℝ E₁ x) +
      AffineMap.const ℝ E₁ (F x)
  simpa [g, modifiedGaussNewtonLocalModel, meritFunctionReformulation, Function.comp,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    hφ.comp_affineMap g

section ArgminRecall

variable (F : E₁ → E₂) (φ : E₂ → ℝ) (J : E₁ → E₁ →L[ℝ] E₂) (x y : E₁)

/- The candidate next-iterate set for the local model is the canonical minimizer owner
`argmin[Set.univ] (ψ[F; φ; J] x)`. -/
set_option linter.hashCommand false in
#check (argmin[Set.univ] (ψ[F; φ; J] x) : Set E₁)

set_option linter.hashCommand false in
#check
  (show y ∈ argmin[Set.univ] (ψ[F; φ; J] x) ↔
      IsMinOn (ψ[F; φ; J] x) Set.univ y from by
    simp)

end ArgminRecall

end
