/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {U : Type v} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/- Definition 7.14 lies in the chapter's slice-infimum / constrained-minimization domain.

Sampled owner-style declarations:
- `boundedFeasibleSet` in `Chap07/Definition_7_13`, the chapter owner of the localized set
  `Q₁(ρ)`
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`
- `SetConstrainedMinimizationProblem.optimalValue` and `optimalValue_eq_sInf_image` in
  `Chap01/Definition_1_3_7`
- `supportFunction_toReal_comp_linearMap_dualNorm_bounds` in `Chap07/Lemma_7_2`, the nearby
  intrinsic linear-map formulation of the same `⟪A x, u⟫` pairing pattern

Best owner abstraction:
- source-facing: the relative-scale lower-value function `u ↦ inf_{x ∈ Q₁(\hatρ)} ⟪A x, u⟫`
- core/canonical: for fixed `u`, the constrained minimization owner
  `SetConstrainedMinimizationProblem X`
- bridge/view: the explicit `sInf` image formula for that owner's `optimalValue`

Primitive data:
- the feasible set `Q₁ : Set X`
- the linear map `A : X →ₗ[ℝ] U`
- the objective `f : X → ℝ`
- the base point `x₀ : X`
- the radius parameter `γ₀(F)`

Derived API:
- the localized feasible slice `Q₁(\hatρ)` as `boundedFeasibleSet Q₁ x₀ \hatρ`
- the fixed-`u` constrained linear minimization problem on that slice
- the lower-value function as the owner's canonical `optimalValue : EReal`

Source/core/bridge triage:
- source-facing: the lower-value function from Definition 7.14
- core/canonical: the Chapter 1 constrained minimization owner
- bridge/view: the fixed-`u` problem and its `sInf` presentation

This refinement removes two non-canonical choices from the public core:
- the ad hoc radius-indexed feasible-set family is replaced by the chapter owner
  `boundedFeasibleSet`
- the raw real-valued `sInf` is replaced by the faithful owner value `optimalValue : EReal`

The public surface is also lifted from the coordinate model `Matrix (Fin m) (Fin n) ℝ` on
`EuclideanSpace ℝ (Fin _)` to the intrinsic linear-map formulation `A : X →ₗ[ℝ] U`.
-/

/-- For fixed `u`, the lower-value slice of Definition 7.14 is the constrained linear
minimization problem on the localized feasible set
`Q₁(\hatρ) = boundedFeasibleSet Q₁ x₀ \hatρ`, where `\hatρ = (1 / γ₀(F)) f(x₀)`. -/
def relativeScaleLowerValueProblem
    (gamma0F : ℝ) (Q1 : Set X) (A : X →ₗ[ℝ] U)
    (f : X → ℝ) (x0 : X) (u : U) : SetConstrainedMinimizationProblem X where
  feasibleSet := boundedFeasibleSet Q1 x0 (aPrioriRadiusEstimate f gamma0F x0)
  objective := fun x ↦ inner ℝ (A x) u

@[simp] theorem relativeScaleLowerValueProblem_feasibleSet
    (gamma0F : ℝ) (Q1 : Set X) (A : X →ₗ[ℝ] U)
    (f : X → ℝ) (x0 : X) (u : U) :
    (relativeScaleLowerValueProblem gamma0F Q1 A f x0 u).feasibleSet =
      boundedFeasibleSet Q1 x0 (aPrioriRadiusEstimate f gamma0F x0) :=
  rfl

@[simp] theorem relativeScaleLowerValueProblem_apply
    (gamma0F : ℝ) (Q1 : Set X) (A : X →ₗ[ℝ] U)
    (f : X → ℝ) (x0 : X) (u : U) (x : X) :
    relativeScaleLowerValueProblem gamma0F Q1 A f x0 u x =
      inner ℝ (A x) u :=
  rfl

/-- The owner optimal value of the fixed-`u` constrained problem is the extended-real infimum of
the feasible linear values `⟪A x, u⟫` over `Q₁(\hatρ)`. -/
theorem relativeScaleLowerValueProblem_optimalValue_eq_sInf_image
    (gamma0F : ℝ) (Q1 : Set X) (A : X →ₗ[ℝ] U)
    (f : X → ℝ) (x0 : X) (u : U) :
    (relativeScaleLowerValueProblem gamma0F Q1 A f x0 u).optimalValue =
      sInf ((fun x : X ↦ (inner ℝ (A x) u : EReal)) ''
        boundedFeasibleSet Q1 x0 (aPrioriRadiusEstimate f gamma0F x0)) := by
  simpa [relativeScaleLowerValueProblem] using
    (relativeScaleLowerValueProblem gamma0F Q1 A f x0 u).optimalValue_eq_sInf_image

/-- Definition 7.14: for `\hatρ = (1 / γ₀(F)) f(x₀)`, the lower-value function sends `u` to the
canonical constrained optimal value of `x ↦ ⟪A x, u⟫` on `Q₁(\hatρ)`. Using `optimalValue :
EReal` keeps the source minimum faithful even when the feasible slice is empty or the linear
objective is unbounded below. -/
def relativeScaleLowerValueFunction
    (gamma0F : ℝ) (Q1 : Set X) (A : X →ₗ[ℝ] U)
    (f : X → ℝ) (x0 : X) : U → EReal :=
  fun u ↦ (relativeScaleLowerValueProblem gamma0F Q1 A f x0 u).optimalValue

/-- Evaluating `relativeScaleLowerValueFunction` at `u` gives the defining owner optimal value of
the linear minimization problem on `Q₁(\hatρ)`. -/
@[simp] theorem relativeScaleLowerValueFunction_apply
    (gamma0F : ℝ) (Q1 : Set X) (A : X →ₗ[ℝ] U)
    (f : X → ℝ) (x0 : X) (u : U) :
    relativeScaleLowerValueFunction gamma0F Q1 A f x0 u =
      (relativeScaleLowerValueProblem gamma0F Q1 A f x0 u).optimalValue :=
  rfl

/-- Expanding `relativeScaleLowerValueFunction` recovers the extended-real infimum of the feasible
linear values over `Q₁(\hatρ)`. -/
theorem relativeScaleLowerValueFunction_eq_sInf_image
    (gamma0F : ℝ) (Q1 : Set X) (A : X →ₗ[ℝ] U)
    (f : X → ℝ) (x0 : X) (u : U) :
    relativeScaleLowerValueFunction gamma0F Q1 A f x0 u =
      sInf ((fun x : X ↦ (inner ℝ (A x) u : EReal)) ''
        boundedFeasibleSet Q1 x0 (aPrioriRadiusEstimate f gamma0F x0)) := by
  simpa [relativeScaleLowerValueFunction] using
    relativeScaleLowerValueProblem_optimalValue_eq_sInf_image gamma0F Q1 A f x0 u

/-- If the linear objective attains its minimum on the localized feasible slice `Q₁(\hatρ)` at
`xStar`, then the lower-value function equals that attained value. This is the justified
real-minimum reading of Definition 7.14 under an attainment hypothesis. -/
theorem relativeScaleLowerValueFunction_eq_of_isMinOn
    (gamma0F : ℝ) (Q1 : Set X) (A : X →ₗ[ℝ] U)
    (f : X → ℝ) (x0 : X) (u : U) {xStar : X}
    (hxStar :
      xStar ∈ boundedFeasibleSet Q1 x0 (aPrioriRadiusEstimate f gamma0F x0))
    (hmin :
      IsMinOn (fun x : X ↦ inner ℝ (A x) u)
        (boundedFeasibleSet Q1 x0 (aPrioriRadiusEstimate f gamma0F x0)) xStar) :
    relativeScaleLowerValueFunction gamma0F Q1 A f x0 u =
      (inner ℝ (A xStar) u : EReal) := by
  simpa [relativeScaleLowerValueFunction, relativeScaleLowerValueProblem] using
    (relativeScaleLowerValueProblem gamma0F Q1 A f x0 u).optimalValue_eq_of_isMinOn
      hxStar hmin

end

end
