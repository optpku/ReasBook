/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped LevelSetNotation

/-
Definition 4.1.10 lies in the nonlinear change-of-variables domain for convex minimization.

Sampled owner-style declarations:
* project `𝓛[f](a)` / `mem_levelSet_iff` in `Chap01/Definition_1_4_8`, the chapter owner for
  sublevel sets;
* project `norm_sub_le_sigma_mul_norm_image_sub` in `Chap04/Lemma_4_1_9`, which uses the same
  controlling level set and the derivative bound needed downstream;
* project `modifiedGaussNewtonLocalModel` in `Chap04/Definition_4_4_11`, which treats a
  pointwise Jacobian family as primitive data via the canonical owner `HasFDerivAt`;
* mathlib `IsMinOn f Set.univ xStar`, the canonical owner of the chosen minimizer relation.

Best owner abstraction:
* source-facing: the nonlinear convex transformation together with the chosen minimizer `uStar`
  and the textbook constants `σ` and `D`;
* core/canonical: the equivalence `u : E ≃ E`, the potential `φ`, the chapter level-set owner
  `𝓛[φ](φ (u x0))`, and pointwise differentiability of `u.symm` together with its canonical
  derivative `fderiv ℝ u.symm` on that level set;
* bridge/view: the transformed objective `φ ∘ u`, the transported minimizer `xStar`, and the
  derived within-set differentiability used by later mean-value estimates.

Primitive data:
* the equivalence `u`, the convex potential `φ`, the base point `x0`;
* pointwise differentiability of `u.symm` on the controlling level set;
* the chosen minimizer `uStar` of `φ`;
* the constants `σ` and `D` recorded by their attained-maximum properties on the controlling
  level set.

Derived API:
* the transformed objective `objective`;
* the transported minimizer `xStar = u.symm uStar`;
* the within-set differentiability and derivative-norm bounds needed by the distortion lemma.

This file therefore keeps the source-facing owner `NonlinearConvexTransformation`, but reuses the
chapter sublevel-set owner directly and records `σ` using the ordinary derivative data of
`u.symm`, not the proof-oriented within derivative. -/

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Definition 4.1.10: a nonlinear transformation of a convex objective consists of an
invertible map `u : E → E`, a convex function `φ`, a starting point `x₀`, differentiability of
`u⁻¹` on the controlling level set `𝓛[φ]((φ (u x₀)))`, a chosen minimizer `u*` of `φ`, and the
corresponding constants `σ` and `D`. The transformed objective is `f = φ ∘ u`, the transported
minimizer is `x* = u⁻¹(u*)`, and the constants `σ` and `D` are the maxima of
`‖(u⁻¹)'(z)‖` and `‖z - u*‖` on `𝓛[φ]((φ (u x₀)))`. -/
structure NonlinearConvexTransformation where
  /-- The nonlinear change of variables `u`. -/
  u : E ≃ E
  /-- The convex potential `φ`. -/
  φ : E → ℝ
  /-- The starting point `x₀`. -/
  x0 : E
  /-- The potential `φ` is convex on the whole space. -/
  φ_convex : ConvexOn ℝ Set.univ φ
  /-- The inverse map `u⁻¹` is differentiable at every point of the controlling level set
  `𝓛[φ]((φ (u x₀)))`. -/
  u_symm_differentiableAt_controllingLevelSet
    {z : E} (hz : z ∈ (𝓛[φ]((φ (u x0))) : Set E)) : DifferentiableAt ℝ u.symm z
  /-- The chosen global minimizer `u*` of `φ`. -/
  uStar : E
  /-- The chosen point `u*` minimizes `φ` globally. -/
  isMinOn_uStar : IsMinOn φ Set.univ uStar
  /-- The constant `σ`, defined as the maximum of `‖fderiv ℝ u.symm z‖` on the controlling
  level set. -/
  sigma : ℝ
  /-- The displayed value `σ` is the maximum of `‖fderiv ℝ u.symm z‖` on the controlling level
  set. -/
  sigma_isGreatest :
    IsGreatest
      ((fun z : E ↦ ‖fderiv ℝ u.symm z‖) '' (𝓛[φ]((φ (u x0))) : Set E))
      sigma
  /-- The constant `D`, defined as the maximum distance from `u*` on the controlling level set. -/
  D : ℝ
  /-- The displayed value `D` is the maximum of `‖z - u*‖` on the controlling level set. -/
  D_isGreatest :
    IsGreatest
      ((fun z : E ↦ ‖z - uStar‖) '' (𝓛[φ]((φ (u x0))) : Set E))
      D

namespace NonlinearConvexTransformation

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The transformed objective `f(x) = φ(u(x))`. -/
def objective (problem : NonlinearConvexTransformation E) : E → ℝ :=
  problem.φ ∘ problem.u

/-- A nonlinear convex transformation can be used as its transformed objective `f = φ ∘ u`. -/
instance : CoeFun (NonlinearConvexTransformation E) (fun _ ↦ E → ℝ) where
  coe problem := problem.objective

/-- Evaluating the transformed objective recovers `φ (u x)`. -/
@[simp] theorem objective_apply (problem : NonlinearConvexTransformation E) (x : E) :
    problem.objective x = problem.φ (problem.u x) :=
  rfl

/-- A nonlinear convex transformation evaluates as its transformed objective. -/
@[simp] theorem coe_apply (problem : NonlinearConvexTransformation E) (x : E) :
    problem x = problem.objective x :=
  rfl

/-- The inverse map `u⁻¹` is differentiable on the controlling level set
`𝓛[φ]((φ (u x₀)))`. -/
theorem u_symm_differentiableOn_controllingLevelSet
    (problem : NonlinearConvexTransformation E) :
    DifferentiableOn ℝ problem.u.symm
      (𝓛[problem.φ]((problem.φ (problem.u problem.x0))) : Set E) := by
  intro z hz
  exact (problem.u_symm_differentiableAt_controllingLevelSet hz).differentiableWithinAt

/-- On the controlling level set, the ordinary derivative norm of `u⁻¹` is bounded by `σ`. -/
theorem norm_fderiv_u_symm_le_sigma
    (problem : NonlinearConvexTransformation E)
    {z : E}
    (hz : z ∈ (𝓛[problem.φ]((problem.φ (problem.u problem.x0))) : Set E)) :
    ‖fderiv ℝ problem.u.symm z‖ ≤ problem.sigma := by
  exact
    problem.sigma_isGreatest.2
      (Set.mem_image_of_mem (fun z : E ↦ ‖fderiv ℝ problem.u.symm z‖) hz)

/-- Every point of the controlling level set lies at distance at most `D` from `u*`. -/
theorem norm_sub_uStar_le_D
    (problem : NonlinearConvexTransformation E)
    {z : E}
    (hz : z ∈ (𝓛[problem.φ]((problem.φ (problem.u problem.x0))) : Set E)) :
    ‖z - problem.uStar‖ ≤ problem.D := by
  exact problem.D_isGreatest.2 (Set.mem_image_of_mem (fun z : E ↦ ‖z - problem.uStar‖) hz)

/-- The point `x* = u⁻¹(u*)` corresponding to the chosen minimizer `u*` of `φ`. -/
def xStar (problem : NonlinearConvexTransformation E) : E :=
  problem.u.symm problem.uStar

/-- The point `x* = u⁻¹(u*)` is a global minimizer of the transformed objective `f = φ ∘ u`. -/
theorem isMinOn_xStar (problem : NonlinearConvexTransformation E) :
    IsMinOn problem Set.univ problem.xStar := by
  have hphi : IsMinOn problem.φ Set.univ (problem.u problem.xStar) := by
    simpa [xStar] using problem.isMinOn_uStar
  simpa [objective] using hphi.on_preimage problem.u

end NonlinearConvexTransformation
