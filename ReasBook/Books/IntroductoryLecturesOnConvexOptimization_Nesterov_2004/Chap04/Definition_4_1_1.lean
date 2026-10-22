/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped LevelSetNotation

/-
Definition 4.1.1 lies in the order/set-theoretic sublevel-set domain.

Sampled owner-style declarations:
- project `Definition_1_4_8`, which already owns the level-set notation `𝓛[f](α)` and its
  atomic companion lemmas
- mathlib `Set.Iic`
- mathlib `Set.preimage`
- mathlib `Set.mem_Iic`

Best owner abstraction:
- source-facing: the lower level set `𝓛[f](α)` of `f`
- core/canonical: `(f ⁻¹' Set.Iic α : Set E)`
- bridge/view: `levelSet_eq_setOf`

Source/core/bridge triage:
- source-facing: Definition 4.1.1's lower level set `𝓛[f](α)`
- core/canonical: the Chapter 1 owner `(f ⁻¹' Set.Iic α : Set E)`
- bridge/view: `mem_levelSet_iff` and `levelSet_eq_setOf`

Primitive data:
- a function `f : E → ℝ`
- a level `α : ℝ`

Derived API:
- `mem_levelSet_iff`
- `levelSet_eq_setOf`

This numbered item is therefore recall-only. The chapter already has the canonical owner shape for
sublevel sets, so this file reuses the owner notation and companion lemmas directly instead of
maintaining a parallel local definition such as `lowerLevelSet`.
-/

/- Definition 4.1.1 reuses the imported pointwise and set-builder companion facts directly. -/
recall mem_levelSet_iff {E : Type u} {α : Type v} [Preorder α] {f : E → α} {a : α} {x : E} :
    x ∈ f ⁻¹' Set.Iic a ↔ f x ≤ a

recall levelSet_eq_setOf {E : Type u} {α : Type v} [Preorder α] (f : E → α) (a : α) :
    f ⁻¹' Set.Iic a = {x | f x ≤ a}

section

variable {E : Type u}
variable (f : E → ℝ) (α : ℝ) (x₀ : E)
variable {x : E}

/- Definition 4.1.1: the lower level set of `f` at level `α` is the recalled owner `𝓛[f](α)`,
equivalently `{x | f x ≤ α}`. -/
#check (𝓛[f](α) : Set E)

#check (show x ∈ 𝓛[f](α) ↔ f x ≤ α from mem_levelSet_iff)

#check (show (𝓛[f](α) : Set E) = {x : E | f x ≤ α} from levelSet_eq_setOf f α)

#check (show (𝓛[f]((f x₀)) : Set E) = {x : E | f x ≤ f x₀} from levelSet_eq_setOf f (f x₀))

end
