/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set
open scoped LevelSetNotation

/-
Assumption 4.4.2 lies in the order/topological sublevel-set domain.

Sampled owner-style declarations:
* `Definition_1_4_8`, which already owns the level-set notation `𝓛[f](τ)` together with the
  atomic companions `mem_levelSet_iff` and `levelSet_eq_setOf`
* `Definition_4_1_1`, the Chapter 4 recall of that same owner surface
* mathlib `Set.Iic`, the canonical lower interval whose preimage defines `𝓛[f](τ)`
* `HasUniformDualNondegeneracyOnInitialSublevelSet` in `Assumption_4_4_3`, the nearby Chapter 4
  source-facing owner that specializes the same sublevel-set surface to the modified
  Gauss--Newton merit function

Best owner abstraction:
* source-facing: `IsSufficientlyLargeFeasibleSetAt f 𝓕 x₀`
* core/canonical: `x₀ ∈ interior 𝓕 ∧ 𝓛[f]((f x₀)) ⊆ 𝓕`
* bridge/view: `levelSet_eq_setOf f (f x₀)`

Primitive data:
* the feasible set `𝓕`
* the base point `x₀`
* the preorder-valued objective `f : E → α`
* the interior condition `x₀ ∈ interior 𝓕`
* containment of the canonical initial sublevel set `𝓛[f]((f x₀))` in `𝓕`

Derived API:
* the interior-membership projection
* the owner-level sublevel-set inclusion
* the whole-space specialization, where the assumption is automatic

There is no upstream owner for the full conjunction in this assumption, so the source-facing
predicate stays. The duplicate wheel was the raw set-builder encoding of the sublevel set, which
is refined here to the existing chapter owner notation.
-/

/-- Assumption 4.4.2: a feasible set `𝓕` is sufficiently large with respect to `x₀` for the
objective `f` when `x₀ ∈ interior 𝓕` and the canonical sublevel set `𝓛[f]((f x₀))` is contained
in `𝓕`. -/
def IsSufficientlyLargeFeasibleSetAt
    {E : Type u} [TopologicalSpace E] {α : Type v} [Preorder α]
    (f : E → α) (𝓕 : Set E) (x0 : E) : Prop :=
  x0 ∈ interior 𝓕 ∧ 𝓛[f]((f x0)) ⊆ 𝓕

namespace IsSufficientlyLargeFeasibleSetAt

variable {E : Type u} [TopologicalSpace E] {α : Type v} [Preorder α]
variable {f : E → α} {𝓕 : Set E} {x0 : E}

/-- In the whole-space case `𝓕 = Set.univ`, Assumption 4.4.2 is automatic. -/
@[simp] theorem univ (f : E → α) (x0 : E) :
    IsSufficientlyLargeFeasibleSetAt f Set.univ x0 := by
  simp [IsSufficientlyLargeFeasibleSetAt]

/-- A sufficiently large feasible set contains the base point `x₀` in its interior. -/
theorem mem_interior
    (hlarge : IsSufficientlyLargeFeasibleSetAt f 𝓕 x0) :
    x0 ∈ interior 𝓕 :=
  hlarge.1

/-- A sufficiently large feasible set contains the whole sublevel set `𝓛(f(x₀))`. -/
theorem levelSet_subset
    (hlarge : IsSufficientlyLargeFeasibleSetAt f 𝓕 x0) :
    𝓛[f]((f x0)) ⊆ 𝓕 :=
  hlarge.2

/-- A sufficiently large feasible set contains the base point `x₀`. -/
@[simp] theorem mem
    (hlarge : IsSufficientlyLargeFeasibleSetAt f 𝓕 x0) :
    x0 ∈ 𝓕 :=
  hlarge.levelSet_subset (by simp)

end IsSufficientlyLargeFeasibleSetAt
