/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin WithTopConvexAnalysis

universe u

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/- Theorem 3.1.20 lies in the chapter's minimizer/common-subdifferential domain.

Relevant owner-style declarations sampled before refinement:
- `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project
  owner API for minimizers on a set;
- `withTopEffectiveDomain` and the notation `dom f` in `Definition_3_3`, the chapter owner for
  the effective domain of an `ℝ ∪ {+∞}`-valued function;
- `subdifferential` and `mem_subdifferential_iff` in `Definition_3_1_5`, the chapter owner API
  for extended-valued subgradients;
- `commonRegularSubdifferential` and `mem_commonRegularSubdifferential_iff` in
  `Definition_3_1_5_4`, the owner API for common subdifferentials.

Best owner abstraction:
- `argmin[dom f] f` together with `commonRegularSubdifferential`.

Primitive data:
- an extended-valued function `f`;
- a set `XStar`.

Derived API:
- membership in `argmin[dom f] f`, via `mem_constrainedArgmin_iff`;
- membership in `∂̂ f(XStar)`, via `mem_commonRegularSubdifferential_iff`.

Source/core/bridge triage:
- source-facing: the textbook criterion identifying sets of global minimizers by the common
  regular subdifferential;
- core/canonical: `argmin[dom f] f` and `commonRegularSubdifferential`;
- bridge/view: the theorem below relating these two owner objects.

The previous version introduced a second owner `globalMinimizers` for the exact Chapter 1 object
`argmin[dom f] f`. This file now deletes that duplicate wheel and states the theorem
directly with the canonical minimizer-set owner. -/

/-- Theorem 3.1.20: a set `X_*` is contained in
`arg min_{x ∈ dom f} f(x)` if and only if the zero vector lies in the common
subdifferential `∂̂ f(X_*)`. -/
-- Proof sketch: if `X_* ⊆ argmin[dom f] f`, then for each `x ∈ X_*` the minimizer
-- property on `dom f` is exactly the subgradient inequality with slope `0`, so `0 ∈ ∂f(x)` and
-- hence `0 ∈ ∂̂ f(X_*)`. Conversely, if `0 ∈ ∂̂ f(X_*)`, then at each `x ∈ X_*` the defining
-- inequality for `0 ∈ ∂f(x)` says `f x ≤ f y` for every `y ∈ dom f`, so
-- `x ∈ argmin[dom f] f`.
theorem subset_constrainedArgmin_effectiveDomain_iff_zero_mem_commonRegularSubdifferential
    {f : V → WithTop ℝ} {XStar : Set V} :
    XStar ⊆ argmin[dom f] f ↔ (0 : V) ∈ ∂̂ f(XStar) := by
  rw [mem_commonRegularSubdifferential_iff]
  constructor
  · intro h x hx
    rw [mem_subdifferential_iff]
    rcases mem_constrainedArgmin_iff.mp (h hx) with ⟨hx_dom, hx_min⟩
    exact ⟨hx_dom, fun y hy ↦ by simpa using (isMinOn_iff.mp hx_min y hy)⟩
  · intro h x hx
    rw [mem_constrainedArgmin_iff]
    have hx_zero : (0 : V) ∈ ∂ f(x) := h x hx
    rw [mem_subdifferential_iff] at hx_zero
    rcases hx_zero with ⟨hx_dom, hx_subgrad⟩
    refine ⟨hx_dom, isMinOn_iff.mpr ?_⟩
    intro y hy
    simpa using hx_subgrad hy
