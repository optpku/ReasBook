/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Convex.Cone.Dual

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Pointwise

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Definition 2.12: the polar cone of a set `K ⊆ E` is the pointed cone of dual vectors `y`
whose pairing with every `x ∈ K` is nonpositive. -/
def polar_cone (K : Set E) : PointedCone ℝ (Module.Dual ℝ E) :=
  -PointedCone.dual (Module.Dual.eval ℝ E) K

/-- Membership in the polar cone means being nonpositive on every point of `K`. -/
@[simp] lemma mem_polar_cone (K : Set E) (y : Module.Dual ℝ E) :
    y ∈ polar_cone K ↔ ∀ x ∈ K, y x ≤ 0 := by
  simp [polar_cone, PointedCone.mem_dual]

/-- The polar cone is the negative of the dual cone for the evaluation pairing. -/
lemma polar_cone_eq_neg_dual (K : Set E) :
    polar_cone K = -PointedCone.dual (Module.Dual.eval ℝ E) K := rfl

end
