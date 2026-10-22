/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}

/- Definition 5.4.6.7 lies in the Fréchet-derivative/product-map domain.

Sampled owner-style declarations:
* `fderiv`
* `HasFDerivAt.prodMk`
* `DifferentiableAt.fderiv_prodMk`
* `fderiv_const_apply`

Best owner abstraction:
* source-facing: the directional derivative of the lifted map `y ↦ (ξ' y, v)` at `x` applied to
  `d`;
* core/canonical: `fderiv 𝕜 (fun y ↦ (ξ' y, v)) x d`;
* bridge/view: the component formula identifying this derivative with `(fderiv 𝕜 ξ' x d, 0)`.

Primitive data:
* `ξ'`, `v`, `x`, `d`;
* for the subsection-specialized bridge, the map `ξ` together with the repeated direction `d`.

Derived API:
* the componentwise derivative formula below;
* the subsection-specialized bridge `compositionSecondLiftedDirectionDerivative 𝕜 ξ x d =
  (D²ξ(x)[d, d], 0)`. -/

section

variable [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
variable [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
variable [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]

variable (ξ' : E₁ → E₂) (v : E₃) (x d : E₁)

/- Definition 5.4.6.7: for the lifted map `l(y) = (ξ' y, v)`, the textbook directional
derivative `Dl(x)[d]` is the canonical Fréchet derivative application below. -/
#check fderiv 𝕜 (fun y : E₁ ↦ (ξ' y, v)) x d

end

section LiftedSecondDerivative

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
variable [Zero E₃]

/-- The lifted derivative direction `l' = (D²ξ(x)[d, d], 0)` used in the subsection's
composition formulas. -/
abbrev compositionSecondLiftedDirectionDerivative
    (ξ : E₁ → E₂) (x d : E₁) : E₂ × E₃ :=
  (iteratedFDeriv ℝ 2 ξ x (fun _ ↦ d), 0)

end LiftedSecondDerivative

section LiftedSecondDerivativeEq

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
variable [Zero E₃]

/- If `ξ` is `C²` at `x`, then the product-space lift of `D²ξ(x)[d, d]` is the canonical pair
whose first component is the nested Fréchet derivative `D(Dξ(·)[d])(x)[d]`. -/
theorem compositionSecondLiftedDirectionDerivative_eq
    {ξ : E₁ → E₂} {x d : E₁}
    (hξ : ContDiffAt ℝ 2 ξ x) :
    compositionSecondLiftedDirectionDerivative ξ x d =
      (fderiv ℝ (fun y ↦ fderiv ℝ ξ y d) x d, (0 : E₃)) := by
  rw [compositionSecondLiftedDirectionDerivative]
  have hξ' : ContDiffAt ℝ 1 (fderiv ℝ ξ) x := by
    simpa using (show ContDiffAt ℝ (1 + 1) ξ x from hξ).fderiv_right_succ
  have hξfderiv :
      HasFDerivAt (fderiv ℝ ξ) (fderiv ℝ (fderiv ℝ ξ) x) x :=
    hξ'.differentiableAt_one.hasFDerivAt
  have hfd :
      HasFDerivAt (fun y ↦ fderiv ℝ ξ y d) ((fderiv ℝ (fderiv ℝ ξ) x).flip d) x := by
    simpa using hξfderiv.clm_apply (hasFDerivAt_const d x)
  rw [show fderiv ℝ (fun y ↦ fderiv ℝ ξ y d) x = (fderiv ℝ (fderiv ℝ ξ) x).flip d from
    hfd.fderiv]
  ext
  · simpa using iteratedFDeriv_two_apply ξ x (fun _ ↦ d)
  · rfl

end LiftedSecondDerivativeEq
