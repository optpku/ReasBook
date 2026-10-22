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

/- Primary domain: higher-order conditioning classes for real-valued objectives on real normed
spaces.

Sampled owner-style declarations:
* `σ[p](f)` and `L[p](f)` from `Definition_4_2_11`
* `HasIteratedFDerivLipschitzConstantOfDegree p f` from `Definition_4_2_11`
* the sibling source-facing class `IsInFunctionClassF2Lip` in `Definition_4_2_18`
* mathlib's `Fact`, whose library note warns against adding global proof-search instances

Best owner abstraction:
* `source-facing`: `IsInFunctionClassF23 f`
* `core/canonical`: the inherited finiteness owner
  `HasIteratedFDerivLipschitzConstantOfDegree 3 f` together with the inherited finite
  uniform-convexity owners `HasUniformConvexityParameterOfDegree 2 f` and
  `HasUniformConvexityParameterOfDegree 3 f`
* `bridge/view`: the textbook surface notation `f ∈ 𝓕₂₃`

Primitive data:
* finite degree-`2` and degree-`3` uniform-convexity parameters, carried by the parent owners
  `HasUniformConvexityParameterOfDegree 2 f` and `HasUniformConvexityParameterOfDegree 3 f`
* finiteness of `L[3](f)`, carried by the parent owner

Derived API:
* the inherited instance `HasIteratedFDerivLipschitzConstantOfDegree 3 f`
* the paired positivity theorem `IsInFunctionClassF23.sigma_pos`, now derived from the parent
  sigma owners
* the source-facing notation `f ∈ 𝓕₂₃`

This file therefore keeps the source-facing class `𝓕_{2,3}` but stores the degree-three
Lipschitz finiteness hypothesis through its canonical upstream owner, and it also stores the
well-definedness of `σ[2](f)` and `σ[3](f)` through their canonical finite-parameter owners
instead of duplicating sigma-positivity as primitive fields. Positivity is then exposed by theorem
rather than a global `Fact` instance. -/

/-- Definition 4.2.17: a function belongs to the class `𝓕_{2,3}` when `σ[2](f)` and `σ[3](f)`
are positive and `L[3](f)` is finite. The finiteness clause is carried by the canonical owner
`HasIteratedFDerivLipschitzConstantOfDegree 3 f`, while the well-definedness of `σ[2](f)` and
`σ[3](f)` is carried by the canonical finite-parameter owners
`HasUniformConvexityParameterOfDegree 2 f` and `HasUniformConvexityParameterOfDegree 3 f`. -/
class IsInFunctionClassF23 (f : E → ℝ) : Prop where
  /-- The degree-two uniform-convexity parameter of `f` is a genuine finite real parameter. -/
  degreeTwo_uniform : HasUniformConvexityParameterOfDegree 2 f
  /-- The degree-three uniform-convexity parameter of `f` is a genuine finite real parameter. -/
  degreeThree_uniform : HasUniformConvexityParameterOfDegree 3 f
  /-- The degree-three Lipschitz constant of `f` is finite. -/
  degreeThree_lipschitz : HasIteratedFDerivLipschitzConstantOfDegree 3 f

attribute [instance] IsInFunctionClassF23.degreeTwo_uniform
attribute [instance] IsInFunctionClassF23.degreeThree_uniform
attribute [instance] IsInFunctionClassF23.degreeThree_lipschitz

scoped[FunctionClasses] notation:50 f:50 " ∈ " "𝓕₂₃" => IsInFunctionClassF23 f

open scoped FunctionClasses

namespace IsInFunctionClassF23

/-- Membership in `𝓕₂₃` records positivity of both source-facing conditioning parameters. -/
theorem sigma_pos {f : E → ℝ} (hf : f ∈ 𝓕₂₃) :
    0 < σ[2](f) ∧ 0 < σ[3](f) := by
  letI : f ∈ 𝓕₂₃ := hf
  exact ⟨HasUniformConvexityParameterOfDegree.uniformConvexityParameterOfDegree_pos,
    HasUniformConvexityParameterOfDegree.uniformConvexityParameterOfDegree_pos⟩

end IsInFunctionClassF23
