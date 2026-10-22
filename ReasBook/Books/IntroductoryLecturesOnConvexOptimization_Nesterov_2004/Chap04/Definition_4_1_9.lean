/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 4.1.9 lies in the gradient-domination / global-minimization domain on a real
inner-product space. The textbook `ℝⁿ` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)`.

Sampled owner-style declarations:
* `IsMinOn` in mathlib, the canonical fixed-point minimizer predicate on a feasible set;
* `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project owner
  for minimizer sets on a feasible set;
* `gradientWithin`, `HasGradientWithinAt`, and `UniqueDiffOn` in mathlib / Chapter 2, the
  canonical constrained first-order owner layer when within derivatives are required to be
  intrinsic on a feasible set;
* `StarConvexFunction` in `Chap04/Definition_4_1_7`, which keeps a source-facing optimization
  property while exposing the minimizer layer through the canonical owner data;
* `HasGloballyNondegenerateOptimalSet` in `Chap04/Definition_4_1_8`, which likewise treats the
  optimal set as derived canonical API rather than duplicating a local wrapper.

Best owner abstraction:
* source-facing: `GradientDominatedOn p 𝓕 f`;
* core/canonical: `DifferentiableOn ℝ f 𝓕`, `UniqueDiffOn ℝ 𝓕`, `gradientWithin f 𝓕`,
  `argmin[𝓕] f`, and `IsMinOn f 𝓕 xStar`;
* bridge/view: `GradientDominatedOn.UsesConstant` and
  `GradientDominatedOn.exists_usesConstant_of_mem_argmin`.

Primitive data:
* a feasible set `𝓕 : Set E`;
* a differentiable objective `f : E → ℝ` on `𝓕`;
* a unique-differentiability hypothesis on `𝓕`, making `gradientWithin f 𝓕` intrinsic;
* a degree `p ∈ [1, 2]`;
* existence of a feasible global minimizer and a positive domination constant.

Derived API:
* nonemptiness of the canonical optimal set `argmin[𝓕] f`;
* the constrained gradient map `gradientWithin f 𝓕`, now used only on the intrinsic
  `UniqueDiffOn ℝ 𝓕` layer;
* the bridge predicate `GradientDominatedOn.UsesConstant p 𝓕 f xStar τf`;
* transport of one domination constant to any canonical minimizer in `argmin[𝓕] f`.

This refinement keeps the source-facing owner `GradientDominatedOn`, upgrades the minimizer field
to the canonical owner `argmin[𝓕] f`, and records the minimal `UniqueDiffOn ℝ 𝓕` hypothesis
needed for `gradientWithin f 𝓕` to be a canonical first-order datum rather than an arbitrary
chosen `fderivWithin` witness. On open feasible sets, and in particular for `𝓕 = Set.univ`, the
resulting bound reduces to the textbook ambient-gradient form.
-/

namespace GradientDominatedOn

/-- `UsesConstant p 𝓕 f xStar τf` packages the unique differentiability of the feasible set, the
canonical `argmin` membership of `xStar`, and the positive domination constant `τf` used in the
source-facing gradient-domination bound. -/
def UsesConstant (p : ℝ) (𝓕 : Set E) (f : E → ℝ) (xStar : E) (τf : ℝ) : Prop :=
  UniqueDiffOn ℝ 𝓕 ∧ xStar ∈ argmin[𝓕] f ∧ 0 < τf ∧
    ∀ ⦃x : E⦄, x ∈ 𝓕 → f x - f xStar ≤ τf * Real.rpow ‖gradientWithin f 𝓕 x‖ p

end GradientDominatedOn

/-- Definition 4.1.9: a differentiable function `f` on a uniquely differentiable feasible set
`𝓕 ⊆ ℝⁿ` is gradient dominated of degree `p ∈ [1, 2]` when it has a global minimizer `xStar` on
`𝓕` and a positive constant `τf` such that
`f x - f xStar ≤ τf * ‖gradientWithin f 𝓕 x‖^p` for every `x ∈ 𝓕`. On open feasible sets, and in
particular for `𝓕 = Set.univ`, this agrees with the textbook ambient-gradient form. -/
class GradientDominatedOn (p : ℝ) (𝓕 : Set E) (f : E → ℝ) : Prop where
  /-- The function is differentiable on the feasible set. -/
  differentiableOn : DifferentiableOn ℝ f 𝓕
  /-- The degree of domination lies in the interval `[1, 2]`. -/
  degree_mem_Icc : p ∈ Set.Icc (1 : ℝ) 2
  /-- The canonical minimizer set `argmin[𝓕] f` is nonempty, and one minimizer carries the
  unique-differentiability and positive-constant data needed for the source-facing
  gradient-domination inequality. -/
  exists_usesConstant :
    ∃ xStar τf, GradientDominatedOn.UsesConstant p 𝓕 f xStar τf

namespace GradientDominatedOn

variable {p : ℝ} {𝓕 : Set E} {f : E → ℝ}

theorem uniqueDiffOn (hf : GradientDominatedOn p 𝓕 f) :
    UniqueDiffOn ℝ 𝓕 := by
  rcases hf.exists_usesConstant with ⟨xStar, τf, hτf⟩
  exact hτf.1

/-- A `GradientDominatedOn p 𝓕 f` hypothesis canonically supplies the differentiability of `f` on
`𝓕`, the intrinsic within-gradient layer on `𝓕`, and the admissible degree range
`p ∈ [1, 2]`. -/
instance {p : ℝ} {𝓕 : Set E} {f : E → ℝ} [hf : GradientDominatedOn p 𝓕 f] :
    Fact (DifferentiableOn ℝ f 𝓕 ∧ UniqueDiffOn ℝ 𝓕 ∧ p ∈ Set.Icc (1 : ℝ) 2) where
  out := ⟨hf.differentiableOn, hf.uniqueDiffOn, hf.degree_mem_Icc⟩

theorem UsesConstant.uniqueDiffOn
    {xStar : E} {τf : ℝ}
    (hτf : UsesConstant p 𝓕 f xStar τf) :
    UniqueDiffOn ℝ 𝓕 :=
  hτf.1

theorem UsesConstant.mem_argmin
    {xStar : E} {τf : ℝ}
    (hτf : UsesConstant p 𝓕 f xStar τf) :
    xStar ∈ argmin[𝓕] f :=
  hτf.2.1

theorem UsesConstant.pos
    {xStar : E} {τf : ℝ}
    (hτf : UsesConstant p 𝓕 f xStar τf) :
    0 < τf :=
  hτf.2.2.1

theorem UsesConstant.bound
    {xStar : E} {τf : ℝ}
    (hτf : UsesConstant p 𝓕 f xStar τf) {x : E} (hx : x ∈ 𝓕) :
    f x - f xStar ≤ τf * Real.rpow ‖gradientWithin f 𝓕 x‖ p :=
  hτf.2.2.2 hx

/-- On an open feasible set, the within-gradient bound from `UsesConstant` is exactly the
textbook ambient-gradient bound. -/
theorem UsesConstant.bound_eq_gradient_of_isOpen
    {xStar x : E} {τf : ℝ}
    (hτf : UsesConstant p 𝓕 f xStar τf)
    (hf : DifferentiableOn ℝ f 𝓕) (h𝓕_open : IsOpen 𝓕) (hx : x ∈ 𝓕) :
    f x - f xStar ≤ τf * Real.rpow ‖∇ f x‖ p := by
  have hgrad : gradientWithin f 𝓕 x = ∇ f x := by
    rw [gradientWithin, gradient]
    congr
    exact fderivWithin_eq_fderiv (h𝓕_open.uniqueDiffWithinAt hx)
      ((hf x hx).differentiableAt (h𝓕_open.mem_nhds hx))
  simpa [hgrad] using hτf.bound hx

/-- Any point of the canonical minimizer set can be paired with some positive domination
constant. -/
theorem exists_usesConstant_of_mem_argmin
    (hf : GradientDominatedOn p 𝓕 f) {xStar : E} (hxStar : xStar ∈ argmin[𝓕] f) :
    ∃ τf, UsesConstant p 𝓕 f xStar τf := by
  rcases hf.exists_usesConstant with ⟨yStar, τf, hyStar⟩
  have hxStar_mem : xStar ∈ argmin[𝓕] f := hxStar
  have hyStar_mem : yStar ∈ argmin[𝓕] f := hyStar.mem_argmin
  rw [mem_constrainedArgmin_iff] at hxStar hyStar_mem
  have hfxStar : f xStar = f yStar := by
    exact le_antisymm (hxStar.2 hyStar_mem.1) (hyStar_mem.2 hxStar.1)
  refine ⟨τf, ⟨hyStar.uniqueDiffOn, hxStar_mem, hyStar.pos, ?_⟩⟩
  intro x hx
  simpa [hfxStar] using hyStar.bound hx

end GradientDominatedOn

/-- A gradient-dominated function has a nonempty canonical minimizer set on its feasible set. -/
theorem GradientDominatedOn.argmin_nonempty
    {p : ℝ} {𝓕 : Set E} {f : E → ℝ} (hf : GradientDominatedOn p 𝓕 f) :
    (argmin[𝓕] f).Nonempty := by
  rcases hf.exists_usesConstant with ⟨xStar, τf, hτf⟩
  exact ⟨xStar, hτf.mem_argmin⟩
