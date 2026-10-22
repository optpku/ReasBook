/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

universe u v

open Set

section

variable {α : Type u} {β : Type v}
variable (𝒮 : α → Set β) (X : Set α) (y : β)

/-- Definition 3.17 (Intersection of images of a set-valued mapping): the common-value set of
all images `𝒮 x` with `x ∈ X`. -/
def intersectionOfImages : Set β :=
  ⋂ x ∈ X, 𝒮 x

/-- Helper for Definition 3.17: membership in the intersection of images means belonging to every
image indexed by `X`. -/
theorem mem_intersectionOfImages_iff :
    y ∈ intersectionOfImages 𝒮 X ↔ ∀ x ∈ X, y ∈ 𝒮 x := by
  -- Unfold the source-facing definition to reach the canonical bounded intersection.
  unfold intersectionOfImages
  -- The generic membership rule for bounded intersections is exactly the desired expansion.
  exact
    (Set.mem_iInter₂ : y ∈ (⋂ x ∈ X, 𝒮 x : Set β) ↔ ∀ x ∈ X, y ∈ 𝒮 x)

end
