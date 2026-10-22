/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open scoped ConstrainedArgmin

noncomputable section

universe u

/- Definition 5.2.3 lies in the chapter's constrained-minimization / auxiliary-central-path
domain.

Sampled owner declarations:
* `IsMinOn` in mathlib, the canonical minimizer predicate on a feasible set;
* `constrainedArgmin` and the scoped notation `argmin[Q]` in `Chap01/Definition_1_3_3`, the
  project owner for minimizer sets on a fixed feasible set;
* `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the bridge decomposing canonical
  argmin membership into feasibility and minimality;
* the later Chapter 5 owner `IsCentralPath` in `Definition_5_3_6_1`, whose pointwise minimizer
  interface confirms that central-path data should be expressed through minimizers rather than a
  separate chosen-witness wrapper.

Best owner abstraction:
* source-facing: the auxiliary tilted objective and the corresponding path of its minimizers on
  `t ∈ [0, 1]`;
* core/canonical: the dependent family `∀ t, {y : E // y ∈ argmin[dom] ...}`;
* bridge/view: `mem_constrainedArgmin_iff`, which yields the textbook facts that each path point
  lies in `dom` and minimizes the tilted objective there.

Primitive data:
* the domain `dom : Set E`;
* the objective `f : E → ℝ`;
* the base point `y0 : dom`.

Derived API:
* the tilted objective `auxiliaryCentralPathObjective f y0 t`;
* the canonical argmin subtype at each parameter `t`;
* the feasibility and `IsMinOn` facts for any auxiliary central path.

Source/core/bridge triage:
* source-facing: the auxiliary central path from Definition 5.2.3;
* core/canonical: `argmin[dom] (auxiliaryCentralPathObjective f y0 t)`;
* bridge/view: coercion from the argmin subtype to `E` together with
  `mem_constrainedArgmin_iff`.

This refinement removes the public `Classical.choose` trajectory. The source-facing path is kept
as a function into the canonical argmin subtype, so the pointwise minimizer and domain facts are
derived rather than stored as primitive chosen-witness data. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The tilted objective `ψ(t; y) = f(y) - t ⟪∇ f(y₀), y⟫` whose minimizers define the
auxiliary central path. -/
def auxiliaryCentralPathObjective
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ) : E → ℝ :=
  fun y ↦ f y - (t : ℝ) * inner ℝ (∇ f (y0 : E)) y

/-- Evaluating `auxiliaryCentralPathObjective f y₀ t` recovers the textbook formula
`f(y) - t ⟪∇ f(y₀), y⟫`. -/
@[simp] theorem auxiliaryCentralPathObjective_apply
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ) (y : E) :
    auxiliaryCentralPathObjective f y0 t y =
      f y - (t : ℝ) * inner ℝ (∇ f (y0 : E)) y :=
  rfl

section

variable {dom : Set E} (f : E → ℝ) (y0 : dom)

/- Definition 5.2.3: the auxiliary central path of `f` based at `y₀ ∈ dom` is a trajectory on
`t ∈ [0, 1]` whose value at each parameter is a point of the canonical minimizer set of the
tilted objective `y ↦ f(y) - t ⟪∇ f(y₀), y⟫` on `dom`. -/
set_option linter.hashCommand false in
#check
  (∀ t : Set.Icc (0 : ℝ) 1,
    {y : E // y ∈ argmin[dom] (auxiliaryCentralPathObjective f y0 t)})

end

section

variable {dom : Set E} {f : E → ℝ} {y0 : dom}
variable
  (yStar :
    ∀ t : Set.Icc (0 : ℝ) 1,
      {y : E // y ∈ argmin[dom] (auxiliaryCentralPathObjective f y0 t)})

/-- Evaluating an auxiliary central path at time `t` yields a point of `dom` that minimizes the
tilted objective over `dom`. -/
theorem auxiliaryCentralPath_spec (t : Set.Icc (0 : ℝ) 1) :
    (yStar t : E) ∈ dom ∧
      IsMinOn (auxiliaryCentralPathObjective f y0 t) dom (yStar t : E) :=
  mem_constrainedArgmin_iff.mp (yStar t).2

/-- The value of an auxiliary central path at time `t` minimizes the tilted objective over
`dom`. -/
theorem auxiliaryCentralPath_isMinOn (t : Set.Icc (0 : ℝ) 1) :
    IsMinOn (auxiliaryCentralPathObjective f y0 t) dom (yStar t : E) :=
  (auxiliaryCentralPath_spec yStar t).2

/-- Every point on an auxiliary central path belongs to the domain on which the tilted problem is
posed. -/
theorem auxiliaryCentralPath_mem_domain (t : Set.Icc (0 : ℝ) 1) :
    (yStar t : E) ∈ dom :=
  (auxiliaryCentralPath_spec yStar t).1

end
