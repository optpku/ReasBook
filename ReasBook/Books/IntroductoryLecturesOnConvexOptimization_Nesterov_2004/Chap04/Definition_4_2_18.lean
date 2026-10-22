/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

open scoped DegreeConditioning

/- Definition 4.2.18 lies in Chapter 4's higher-order conditioning-class domain.

Sampled owner-style declarations:
* `HasIteratedFDerivLipschitzConstantOfDegree p f` in `Definition_4_2_11`
* `σ[p](f)` in `Definition_4_2_11`
* the sibling source-facing class `IsInFunctionClassF23 f` in `Definition_4_2_17`

Best owner abstraction:
* `source-facing`: `IsInFunctionClassF2Lip f`
* `core/canonical`: the inherited finiteness owners
  `HasUniformConvexityParameterOfDegree 2 f`,
  `HasIteratedFDerivLipschitzConstantOfDegree 2 f` and
  `HasIteratedFDerivLipschitzConstantOfDegree 3 f`
* `bridge/view`: the Lean surface notation `f ∈ 𝓕₂Lip`

Primitive data:
* a finite degree-`2` uniform-convexity parameter, carried by the parent owner
  `HasUniformConvexityParameterOfDegree 2 f`
* finiteness of `L[2](f)` and `L[3](f)`, carried by the parent owners

Derived API:
* the inherited instance for `HasIteratedFDerivLipschitzConstantOfDegree 3 f`
* the derived instance for `HasIteratedFDerivLipschitzConstantOfDegree 2 f`
* the positivity theorem `IsInFunctionClassF2Lip.sigma_pos`, now derived from the parent sigma
  owner
* the source-facing notation `f ∈ 𝓕₂Lip`

This file therefore keeps `𝓕₂^{Lip}` as the public source-facing owner, but it reuses the
canonical degree-two and degree-three Lipschitz-finiteness owners directly. It also reuses the
canonical finite-parameter owner for `σ[2](f)` instead of storing sigma-positivity as primitive
data, and it exposes positivity by theorem rather than a global `Fact` instance. -/

/-- Definition 4.2.18: a function belongs to the class `𝓕₂^{Lip}` when its degree-two
uniform-convexity parameter is positive and the degree-two and degree-three derivative Lipschitz
constants are finite. The finiteness clauses are carried by the canonical owner classes
`HasUniformConvexityParameterOfDegree 2 f`,
`HasIteratedFDerivLipschitzConstantOfDegree 2 f` and
`HasIteratedFDerivLipschitzConstantOfDegree 3 f`. -/
class IsInFunctionClassF2Lip (f : E → ℝ) : Prop where
  /-- The degree-two uniform-convexity parameter of `f` is a genuine finite real parameter. -/
  degreeTwo_uniform : HasUniformConvexityParameterOfDegree 2 f
  /-- The gradient of `f` admits a global Lipschitz constant. -/
  degreeTwo_lipschitz : HasIteratedFDerivLipschitzConstantOfDegree 2 f
  /-- The Hessian of `f` admits a global Lipschitz constant. -/
  degreeThree_lipschitz : HasIteratedFDerivLipschitzConstantOfDegree 3 f

attribute [instance] IsInFunctionClassF2Lip.degreeTwo_uniform
attribute [instance] IsInFunctionClassF2Lip.degreeTwo_lipschitz
attribute [instance] IsInFunctionClassF2Lip.degreeThree_lipschitz

scoped[FunctionClasses] notation:50 f:50 " ∈ " "𝓕₂Lip" => IsInFunctionClassF2Lip f

open scoped FunctionClasses

namespace IsInFunctionClassF2Lip

/-- Membership in `𝓕₂Lip` records positivity of the source-facing conditioning parameter
`σ[2](f)`. -/
theorem sigma_pos {f : E → ℝ} (hf : f ∈ 𝓕₂Lip) :
    0 < σ[2](f) := by
  letI : f ∈ 𝓕₂Lip := hf
  exact HasUniformConvexityParameterOfDegree.uniformConvexityParameterOfDegree_pos

end IsInFunctionClassF2Lip
