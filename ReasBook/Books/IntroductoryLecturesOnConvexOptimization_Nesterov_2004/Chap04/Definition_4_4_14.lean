/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped LevelSetNotation

/-
Definition 4.4.14 lies in the order/set-theoretic sublevel-set domain.

Sampled owner-style declarations:
- project `Definition_1_4_8`, which already owns `𝓛[f](τ)`, `mem_levelSet_iff`, and
  `levelSet_eq_setOf`
- project `Definition_4_1_1`, the chapter recall of that same owner surface
- mathlib `Set.Iic`
- mathlib `Set.preimage`

Best owner abstraction:
- source-facing: the recalled level-set notation `𝓛[f](τ)` for a function `f`
- core/canonical: `(f ⁻¹' Set.Iic τ : Set E)`
- bridge/view: `levelSet_eq_setOf`

Primitive data:
- a function `f : E → ℝ`
- a threshold `τ : ℝ`

Derived API:
- `mem_levelSet_iff`
- `levelSet_eq_setOf`

Source/core/bridge triage:
- source-facing: Definition 4.4.14's recalled level-set notation `𝓛[f](τ)`
- core/canonical: the Chapter 1 owner surface imported through `Definition_4_1_1`
- bridge/view: the imported atomic pointwise and set-builder lemmas

This numbered item adds no new owner-layer mathematics. It is a pure recall/use surface for the
existing chapter sublevel-set API, so it reuses the imported notation and companion lemmas
directly instead of defining them again.
-/

section

variable {E : Type u} {α : Type v} [Preorder α]
variable (f : E → α) (τ : α)

/- Definition 4.4.14: the level set `𝓛[f](τ)` is the recalled owner surface for the canonical
sublevel set of `f` at level `τ`. -/
#check (𝓛[f](τ) : Set E)

recall mem_levelSet_iff {f : E → α} {τ : α} {x : E} :
    x ∈ 𝓛[f](τ) ↔ f x ≤ τ

recall levelSet_eq_setOf (f : E → α) (τ : α) :
    (𝓛[f](τ) : Set E) = {x | f x ≤ τ}

end
