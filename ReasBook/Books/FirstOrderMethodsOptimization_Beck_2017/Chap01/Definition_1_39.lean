/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} {V : Type v}
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]
variable (f : E → V)

/- Definition 1.39: a linear transformation between real vector spaces is represented in mathlib
by the canonical type of real linear maps `E →ₗ[ℝ] V`. -/
#check (E →ₗ[ℝ] V)

/- The source-facing predicate `IsLinearMap ℝ f` converts to the owner object `E →ₗ[ℝ] V` via
`IsLinearMap.mk'`, and every real linear map induces that predicate via `LinearMap.isLinear`. -/
recall IsLinearMap.mk'
recall LinearMap.isLinear

-- Proof sketch: for the forward direction, expand preservation of a binary linear combination
-- using `IsLinearMap.map_add` together with `IsLinearMap.map_smul`. For the reverse direction,
-- recover additivity from the case `α = β = 1` and recover homogeneity from the case `β = 0`
-- and `y = 0`.
/-- A function between real vector spaces is linear exactly when it preserves every binary real
linear combination. -/
theorem isLinearMap_iff_map_linear_combination :
    IsLinearMap ℝ f ↔
      ∀ (x y : E) (α β : ℝ),
        f (α • x + β • y) = α • f x + β • f y := by
  constructor
  · intro hf x y α β
    rw [hf.map_add, hf.map_smul, hf.map_smul]
  · intro hf
    refine IsLinearMap.mk ?_ ?_
    · intro x y
      simpa using hf x y (1 : ℝ) (1 : ℝ)
    · intro α x
      simpa using hf x (0 : E) α (0 : ℝ)

end
