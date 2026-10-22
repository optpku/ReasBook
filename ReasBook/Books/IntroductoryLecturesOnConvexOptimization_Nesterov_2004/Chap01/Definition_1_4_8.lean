/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Definition 1.4.8 is the source-facing owner file in the order/set-theoretic domain of sublevel
sets.

Relevant owner-style declarations sampled before refinement:
- mathlib `Set.Iic`
- mathlib `Set.preimage`
- mathlib `Set.mem_Iic`
- mathlib `Set.mem_preimage`

Best owner abstraction:
- source-facing: the textbook level-set notation `𝓛[f](a)`
- core/canonical: `(f ⁻¹' Set.Iic a : Set E)`
- bridge/view: the textbook set-builder equality
  `(𝓛[f](a) : Set E) = {x : E | f x ≤ a}`

Primitive data:
- a function `f : E → α`
- a level `a : α`

Derived API:
- pointwise membership via `mem_levelSet_iff`
- the set-builder bridge `levelSet_eq_setOf`

The source notion is exactly the canonical lower-interval preimage `f ⁻¹' Set.Iic a`. This file
therefore places the textbook level-set notation on that owner expression here, together with the
atomic pointwise and set-builder companion lemmas used downstream.
-/

namespace LevelSetNotation

scoped notation:max "𝓛[" f:arg "](" a:arg ")" => f ⁻¹' Set.Iic a

end LevelSetNotation

open scoped LevelSetNotation

section

variable {E : Type u} {α : Type v} [Preorder α]
variable (f : E → α) (a : α)
variable {x : E}

/-
Definition 1.4.8: the level set `𝓛[f](a)` is the canonical lower-interval preimage
`f ⁻¹' Set.Iic a`.
-/
#check (𝓛[f](a) : Set E)

@[simp] theorem mem_levelSet_iff {f : E → α} {a : α} {x : E} :
    x ∈ 𝓛[f](a) ↔ f x ≤ a :=
  Iff.rfl

theorem levelSet_eq_setOf (f : E → α) (a : α) :
    (𝓛[f](a) : Set E) = {x : E | f x ≤ a} :=
  rfl

#check (show x ∈ 𝓛[f](a) ↔ f x ≤ a from mem_levelSet_iff)

#check (show (𝓛[f](a) : Set E) = {x : E | f x ≤ a} from levelSet_eq_setOf f a)

end
