/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part12

section Chap05
section Section26

attribute [local instance] Classical.propDecidable

/-- Helper for Example 26.2.1: extend the real core
`ξ₂^2 / (2 ξ₁) - 2 √ξ₂` by `+∞` outside the open positive quadrant. -/
noncomputable def helperForExample_26_2_1_openQuadrantExtension : (Fin 2 → ℝ) → EReal :=
  fun x =>
    (((x 1 ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1) : ℝ)) : EReal) +
      indicatorFunction openPositiveQuadrantR2 x

/-- Helper for Example 26.2.1: the open positive quadrant is an open subset of `ℝ²`. -/
lemma helperForExample_26_2_1_openQuadrant_isOpen :
    IsOpen openPositiveQuadrantR2 := by
  -- Each strict coordinate inequality defines an open half-space, and the quadrant is their
  -- intersection.
  simpa [openPositiveQuadrantR2, Set.setOf_and] using
    (isOpen_lt continuous_const (continuous_apply 0)).inter
      (isOpen_lt continuous_const (continuous_apply 1))

/-- Helper for Example 26.2.1: the open positive quadrant is convex. -/
lemma helperForExample_26_2_1_openQuadrant_isConvex :
    Convex ℝ openPositiveQuadrantR2 := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  constructor
  · -- Nonnegative convex weights with sum `1` preserve positivity in the first coordinate.
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha0, hb1] using hy0
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hx_term : 0 < a * x 0 := mul_pos ha_pos hx0
      have hy_term : 0 ≤ b * y 0 := mul_nonneg hb hy0.le
      have : 0 < a * x 0 + b * y 0 := add_pos_of_pos_of_nonneg hx_term hy_term
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  · -- The same coordinatewise argument gives positivity in the second coordinate.
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha0, hb1] using hy1
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hx_term : 0 < a * x 1 := mul_pos ha_pos hx1
      have hy_term : 0 ≤ b * y 1 := mul_nonneg hb hy1.le
      have : 0 < a * x 1 + b * y 1 := add_pos_of_pos_of_nonneg hx_term hy_term
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this

end Section26
end Chap05
