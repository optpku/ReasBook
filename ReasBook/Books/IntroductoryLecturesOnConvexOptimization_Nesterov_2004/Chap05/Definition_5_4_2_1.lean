/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped PolarSet

/- Definition 5.4.2.1 lies in the chapter's based-polar-set domain.

Sampled declarations before refinement:
- project `polarSet`
- project `mem_polarSet_iff`
- mathlib `StrongDual.polar`
- mathlib `StrongDual.mem_polar_iff`

Best owner abstraction:
- the chapter owner `polarSet`

Primitive data:
- a set `Q`
- a base point `xBar`

Derived API:
- the textbook based polar as the polar of the displacement set `Q -ᵥ {xBar}`

Source/core/bridge triage:
- source-facing: the textbook based polar `P(xBar)`
- core/canonical: `polarSet`
- bridge/view: `polarSetAt`

The strong-dual mathlib polar is not the exact owner here because it uses the absolute-value bound
on continuous linear functionals rather than the one-sided real inner-product inequality from the
chapter. The correct refinement is therefore to keep the chapter owner `polarSet` and express the
based variant as its displacement-set bridge. No extra notation is introduced here: the recurring
owner notation already lives on `Qᵒ`, while the based object is a view depending on `xBar`.
-/

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Definition 5.4.2.1, generalized from the textbook Euclidean setting: the polar set of `Q`
with respect to the base point `xBar` is the chapter polar of the displacement set
`Q -ᵥ ({xBar} : Set E)`. Specializing to `E = EuclideanSpace ℝ (Fin n)` recovers the textbook
definition. -/
abbrev polarSetAt (Q : Set E) (xBar : E) : Set E :=
  (Q -ᵥ ({xBar} : Set E))ᵒ

/-- Membership in `polarSetAt Q xBar` is exactly the defining uniform inner-product inequality over
the displacement vectors from `xBar` to points of `Q`. -/
theorem mem_polarSetAt_iff {Q : Set E} {xBar s : E} :
    s ∈ polarSetAt Q xBar ↔ ∀ x ∈ Q, inner ℝ s (x - xBar) ≤ 1 := by
  rw [polarSetAt, mem_polarSet_iff]
  simp
