/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 1.6.5 lies in the Chapter 1 black-box domain of lower-bounded unconstrained
`C^{1,1}_L` objectives.

Sampled owner-style declarations:
* `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)` in `Chap01/Definition_1_5_2`, the canonical
  objective-side owners of the `C^{1,1}_L` condition;
* `gradientMethod` in `Chap01/Algorithm_1_6_1`, whose owner abstraction already lives on a real
  complete inner-product space rather than on coordinates;
* `SatisfiesExactLineSearch` in `Chap01/Definition_1_6_3`, which keeps differentiability data on
  the owner layer instead of treating the totalized gradient as intrinsic;
* `DifferentiableAt.hasGradientAt` and
  `gradient_eq_zero_of_not_differentiableAt` in mathlib's gradient API, which show why the
  displayed `∇ f x` is source-faithful only under differentiability data;
* `BlackBoxOptimizationProblemClass` in `Chap01/Definition_1_2_4`, the owner of the model/oracle/
  stopping-criterion package.

Best owner abstraction:
* source-facing/core: an objective `f : E → ℝ` on a real complete inner-product space, together
  with
  `ContDiff ℝ 1 f`, `LipschitzWith L (∇ f)`, and `BddBelow (Set.range f)`;
* bridge/view: the finite-dimensional black-box class `gStarProblemClass n L ε`, whose stopping
  criterion evaluates the source-facing stopping predicate on the underlying objective of a model
  point `f : {g : E → ℝ // g ∈ 𝒢⋆[L]}`.

Primitive data:
* the objective `f`
* the Lipschitz constant `L`

Derived API:
* the source-facing membership predicate `f ∈ 𝒢⋆[L]` for the textbook class `𝒢_*`
* `IsEpsilonSolution f x₀ ε x̄` for a plain objective `f : E → ℝ`
* `gStarProblemClass n L ε`

Source/core/bridge triage:
* source-facing: `f ∈ 𝒢⋆[L]` and `IsEpsilonSolution f x₀ ε x̄` for `f : E → ℝ`
* core/canonical: `ContDiff ℝ 1 f`, `LipschitzWith L (∇ f)`, and `BddBelow (Set.range f)`
* bridge/view: `gStarProblemClass`. -/

variable {L : NNReal}

/-- Definition 1.6.5 (1): an objective `f : E → ℝ` belongs to the textbook class `𝒢_*` when
`f ∈ C^{1,1}_L` and `f` is bounded below. Specializing `E` to `ℝⁿ` recovers the textbook
formulation. -/
def IsGStar (f : E → ℝ) (L : NNReal) : Prop :=
  ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f) ∧ BddBelow (Set.range f)

namespace GStarNotation

scoped notation:max "𝒢⋆[" L:arg "]" => setOf (fun f ↦ IsGStar f L)

end GStarNotation

open scoped GStarNotation

/-- Unfolding `f ∈ 𝒢⋆[L]` gives the canonical conjunction of `C^{1,1}_L` regularity and
lower boundedness. -/
@[simp] theorem isGStar_iff
    (f : E → ℝ) (L : NNReal) :
    f ∈ 𝒢⋆[L] ↔ ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f) ∧ BddBelow (Set.range f) :=
  Iff.rfl

namespace IsGStar

variable {f : E → ℝ} {L : NNReal}

/-- Membership in `𝒢_*` supplies the `C¹` regularity component of the objective. -/
theorem contDiff (h : f ∈ 𝒢⋆[L]) :
    ContDiff ℝ 1 f :=
  h.1

/-- Membership in `𝒢_*` supplies the global `L`-Lipschitz bound on the gradient. -/
theorem gradient_lipschitz (h : f ∈ 𝒢⋆[L]) :
    LipschitzWith L (∇ f) :=
  h.2.1

/-- Membership in `𝒢_*` supplies lower boundedness of the objective values. -/
theorem bddBelow (h : f ∈ 𝒢⋆[L]) :
    BddBelow (Set.range f) :=
  h.2.2

/-- Membership in `𝒢_*` supplies ordinary differentiability at every point. -/
theorem differentiableAt (h : f ∈ 𝒢⋆[L]) (x : E) :
    DifferentiableAt ℝ f x :=
  (contDiff h).differentiable_one x

/-- Membership in `𝒢_*` makes the displayed totalized gradient the genuine gradient. -/
theorem hasGradientAt (h : f ∈ 𝒢⋆[L]) (x : E) :
    HasGradientAt f (∇ f x) x :=
  (differentiableAt h x).hasGradientAt

end IsGStar

/-- A point `x̄` is an `ε`-solution for an objective `f` relative to the starting point `x₀`
when `f(x̄) ≤ f(x₀)` and `‖∇ f(x̄)‖ ≤ ε`. This source-facing stopping predicate lives on the
plain objective `f : E → ℝ`; when `f ∈ 𝒢⋆[L]`, the displayed gradient is source-faithful by
`IsGStar.hasGradientAt`. Specializing `E` to `ℝⁿ` recovers the textbook formulation. -/
def IsEpsilonSolution
    (f : E → ℝ) (x0 : E) (ε : ℝ) (xBar : E) : Prop :=
  f xBar ≤ f x0 ∧ ‖∇ f xBar‖ ≤ ε

/-- Unfolding `IsEpsilonSolution f x₀ ε x̄` gives the textbook conditions
`f(x̄) ≤ f(x₀)` and `‖∇ f(x̄)‖ ≤ ε`. -/
@[simp] theorem isEpsilonSolution_iff
    (f : E → ℝ) (x0 xBar : E) (ε : ℝ) :
    IsEpsilonSolution f x0 ε xBar ↔
      f xBar ≤ f x0 ∧ ‖∇ f xBar‖ ≤ ε :=
  Iff.rfl

section EuclideanBridge

variable {n : ℕ}

/-- Definition 1.6.5 (2): the textbook class `𝒢_*` at accuracy threshold `ε`, viewed as a
Chapter 1 black-box optimization problem class.
Its model is the subtype of lower-bounded unconstrained
`C^{1,1}_L(ℝⁿ)` objectives, its oracle is the canonical first-order answer map
`x ↦ (f x, ∇ f x)`, and its stopping criterion accepts exactly the triples `(f, x₀, x̄)` for
which `x̄` is an `ε`-solution for the model objective `f` relative to `x₀`. -/
def gStarProblemClass (n : ℕ) (L : NNReal) (ε : ℝ) :
    BlackBoxOptimizationProblemClass
      (EuclideanSpace ℝ (Fin n))
      (ℝ × EuclideanSpace ℝ (Fin n))
      ({ f : EuclideanSpace ℝ (Fin n) → ℝ // f ∈ 𝒢⋆[L] } ×
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) where
  model := { f : EuclideanSpace ℝ (Fin n) → ℝ // f ∈ 𝒢⋆[L] }
  oracle := fun f x ↦ (f.1 x, ∇ f.1 x)
  stoppingCriterion := {state | let ⟨f, x0, xBar⟩ := state
    IsEpsilonSolution f.1 x0 ε xBar}

local notation "En" => EuclideanSpace ℝ (Fin n)

/-- A state is accepted by `gStarProblemClass n L ε` exactly when its endpoint is an
`ε`-solution for the model objective relative to its starting point. -/
@[simp] theorem gStarProblemClass_stops_iff
    (f : { f : En → ℝ // f ∈ 𝒢⋆[L] }) (x0 xBar : En) :
    (f, x0, xBar) ∈ (gStarProblemClass n L ε).stoppingCriterion ↔
      IsEpsilonSolution f.1 x0 ε xBar := by
  rfl

variable {ε : ℝ}

/-- The oracle of `gStarProblemClass n L ε` is the canonical first-order answer map
`(f, x) ↦ (f x, ∇ f x)`. -/
@[simp] theorem gStarProblemClass_oracle_apply
    (f : { f : En → ℝ // f ∈ 𝒢⋆[L] }) (x : En) :
    (gStarProblemClass n L ε).oracle f x =
      (f.1 x, ∇ f.1 x) :=
  rfl

end EuclideanBridge

end
