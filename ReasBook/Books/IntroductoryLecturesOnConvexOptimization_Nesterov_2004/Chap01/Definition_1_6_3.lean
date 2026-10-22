/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Gradient

noncomputable section

/-
Definition 1.6.3 lies in the exact line-search domain for first-order trajectories on real vector
spaces.

Relevant owner-style declarations sampled before refining:
* `gradientMethod` in `Algorithm_1_6_1.lean`, the chapter owner of the gradient trajectory;
* `IsMinOn`, the mathlib owner predicate for constrained minimizers on a feasible set;
* `HasGradientAt`, the chapter/mathlib owner predicate for a genuine gradient witness at a point;
* the later reuse of the same trajectory-level owner shape in
  `NonlinearConjugateGradientMethod.lineSearch` from `Algorithm_1_9_9.lean`.

Source/core/bridge triage:
* source-facing: `SatisfiesExactLineSearch`, the textbook exact line-search rule for a gradient
  trajectory, including genuine gradient existence at each iterate;
* core/canonical: the pair of owner predicates `DifferentiableAt` and
  `SatisfiesExactLineSearchAlong`;
* bridge/view: the owner-derived accessors `differentiableAt`, `hasGradientAt`, `nonneg`, and
  `isMinOn`.

Primitive data:
* the objective `f`,
* a trajectory `xₖ`,
* a search-direction field `pₖ`,
* a step-size schedule `hₖ`.

Derived API:
* gradient existence and line-search accessors in the gradient specialization,
* nonnegativity of each `hₖ`,
* the minimizing property of `hₖ` for the one-variable line-search objective.

The generic owner `SatisfiesExactLineSearchAlong` intentionally does not mention gradients; it
records only a minimizing property along a prescribed direction field. The source-facing
gradient-method specialization must additionally assert differentiability at each iterate, because
mathlib's totalized `∇ f` alone would otherwise admit nondifferentiable objectives. The genuine
gradient statement for the displayed `∇ f (xₖ)` is then a derived owner theorem via
`DifferentiableAt.hasGradientAt`. -/

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-
The owner abstraction for exact line search in this chapter is the generic predicate on a real
vector space saying that a scalar schedule `hₖ` minimizes `f (xₖ - h pₖ)` over `h ≥ 0` along a
prescribed trajectory `xₖ` and direction field `pₖ`.

Definition 1.6.3 is the gradient-method specialization of this owner, with
`xₖ = gradientMethod stepSize f x0 k` and `pₖ = ∇ f (xₖ)`.

Algorithm 1.9.9 later reuses the same owner shape with the nonlinear conjugate-gradient search
directions.
-/

/-- A step-size schedule satisfies the exact line-search rule along the trajectory `xₖ` and search
directions `pₖ` when every `hₖ` is a nonnegative minimizer of `h ↦ f (xₖ - h • pₖ)` on
`[0, ∞)`. -/
def SatisfiesExactLineSearchAlong (f : X → ℝ) (x p : ℕ → X) (stepSize : ℕ → ℝ) : Prop :=
  ∀ k : ℕ,
    stepSize k ∈ Set.Ici (0 : ℝ) ∧
      IsMinOn (fun h : ℝ ↦ f (x k - h • p k)) (Set.Ici (0 : ℝ)) (stepSize k)

namespace SatisfiesExactLineSearchAlong

/-- Every exact line-search step size is nonnegative. -/
theorem nonneg
    {f : X → ℝ} {x p : ℕ → X} {stepSize : ℕ → ℝ}
    (hexact : SatisfiesExactLineSearchAlong f x p stepSize) (k : ℕ) :
    stepSize k ∈ Set.Ici (0 : ℝ) :=
  (hexact k).1

/-- Every exact line-search step size minimizes the one-variable search objective over
`[0, ∞)`. -/
theorem isMinOn
    {f : X → ℝ} {x p : ℕ → X} {stepSize : ℕ → ℝ}
    (hexact : SatisfiesExactLineSearchAlong f x p stepSize) (k : ℕ) :
    IsMinOn (fun h : ℝ ↦ f (x k - h • p k)) (Set.Ici (0 : ℝ)) (stepSize k) :=
  (hexact k).2

end SatisfiesExactLineSearchAlong

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Definition 1.6.3 is represented by the pair of canonical owner predicates

`∀ k : ℕ,
    DifferentiableAt ℝ f (x k)`

and

`∀ k : ℕ,
    stepSize k ∈ Set.Ici (0 : ℝ) ∧
      IsMinOn (fun h : ℝ ↦ f (x k - h • ∇ f (x k))) (Set.Ici (0 : ℝ)) (stepSize k)`.

The owner abstraction is the project's usual constrained-minimizer pattern: feasible-set
membership together with mathlib's `IsMinOn`, paired with iterate-wise differentiability so that
the displayed totalized gradient is genuine. The one-variable objective obtained by restricting
`f` to the antigradient ray is derived syntax, not separate primitive data. This is also the
chapter's generic exact line-search shape, specialized in later files by
`NonlinearConjugateGradientMethod.lineSearch`, where differentiability data is likewise carried
separately from the pure line-search minimization condition.
-/

/-- Definition 1 6 3: a step-size schedule `hₖ` satisfies the exact line-search rule for the
gradient-method trajectory started at `x₀` when the objective is differentiable at every iterate,
so the displayed antigradient direction is genuine, and every `hₖ` is a nonnegative minimizer of
the one-variable objective `h ↦ f (xₖ - h ∇ f(xₖ))` over `h ≥ 0`. -/
def SatisfiesExactLineSearch (f : E → ℝ) (stepSize : ℕ → ℝ) (x0 : E) : Prop :=
  let x := gradientMethod stepSize f x0
  (∀ k : ℕ, DifferentiableAt ℝ f (x k)) ∧
    SatisfiesExactLineSearchAlong f x (fun k ↦ ∇ f (x k)) stepSize

namespace SatisfiesExactLineSearch

variable {f : E → ℝ} {stepSize : ℕ → ℝ} {x0 : E}

local notation "traj" => gradientMethod stepSize f x0

/-- Along an exact-line-search gradient trajectory, the objective is differentiable at every
iterate. -/
theorem differentiableAt
    (hexact : SatisfiesExactLineSearch f stepSize x0) (k : ℕ) :
    DifferentiableAt ℝ f (traj k) := by
  simpa [SatisfiesExactLineSearch] using hexact.1 k

/-- Along an exact-line-search gradient trajectory, the displayed antigradient is the genuine
gradient at every iterate. -/
theorem hasGradientAt
    (hexact : SatisfiesExactLineSearch f stepSize x0) (k : ℕ) :
    HasGradientAt f (∇ f (traj k)) (traj k) :=
  (hexact.differentiableAt k).hasGradientAt

/-- `SatisfiesExactLineSearch` packages the generic line-search minimization condition along the
gradient-method trajectory. -/
theorem along
    (hexact : SatisfiesExactLineSearch f stepSize x0) :
    SatisfiesExactLineSearchAlong
      f
      traj
      (fun k ↦ ∇ f (traj k))
      stepSize := by
  simpa [SatisfiesExactLineSearch] using hexact.2

/-- Every exact line-search step size is nonnegative. -/
theorem nonneg
    (hexact : SatisfiesExactLineSearch f stepSize x0) (k : ℕ) :
    stepSize k ∈ Set.Ici (0 : ℝ) := by
  exact hexact.along.nonneg k

/-- Every exact line-search step size minimizes the antigradient line-search objective over
`h ≥ 0`. -/
theorem isMinOn
    (hexact : SatisfiesExactLineSearch f stepSize x0) (k : ℕ) :
    IsMinOn
      (fun h : ℝ ↦ f (traj k - h • ∇ f (traj k)))
      (Set.Ici (0 : ℝ))
      (stepSize k) := by
  exact hexact.along.isMinOn k

end SatisfiesExactLineSearch

end
