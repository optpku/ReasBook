/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_42
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Metric

/- Proposition 3.3 is a `bridge/view` specialization in the chapter convex-analysis API. The
owner declarations are `normal_cone`, Proposition 3.2's
`subdifferential_extended_indicator_eq_normal_cone`, and Chapter 1's canonical `dualNorm`
interface together with `exists_dualNorm_eq_apply`. The only primitive data here are the closed
unit ball and the point `x`; the dual-norm inequality description is derived API. -/

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: this is the closed-unit-ball specialization of the owner theorem
-- `subdifferential_extended_indicator_eq_normal_cone`.
/-- Proposition 3.3: the subdifferential of the indicator of the closed unit ball is its normal
cone. -/
theorem subdifferential_extended_indicator_closed_unit_ball_eq_normal_cone (x : E) :
    subdifferential (extendedIndicator (closedBall (0 : E) 1)) x =
      normal_cone (closedBall (0 : E) 1) x := by
  simpa using
    subdifferential_extended_indicator_eq_normal_cone (closedBall (0 : E) 1) x

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: if `‖x‖ ≤ 1`, rewrite membership in `normal_cone (closedBall (0 : E) 1) x`
-- as `∀ z, ‖z‖ ≤ 1 → y z ≤ y x`, then use `exists_dualNorm_eq_apply` to realize the chapter owner
-- dual norm on the closed unit ball and `abs_apply_le_dual_norm_mul_norm` for the converse
-- bound. If `‖x‖ > 1`, then `x ∉ closedBall (0 : E) 1`, so the normal cone is empty by
-- definition.
/-- The normal cone of the closed unit ball is described by the chapter dual-norm inequality
`dualNorm y ≤ y x` on the ball and is empty outside the ball. -/
theorem normal_cone_closed_unit_ball_eq_if_dualNorm_le_apply (x : E) :
    normal_cone (closedBall (0 : E) 1) x =
      if ‖x‖ ≤ 1 then { y : Module.Dual ℝ E | dualNorm y ≤ y x } else ∅ := by
  let B : Set E := closedBall (0 : E) 1
  by_cases hx : ‖x‖ ≤ 1
  · have hxB : x ∈ B := by
      simpa [B] using hx
    rw [if_pos hx]
    ext y
    constructor
    · intro hy
      have hy' := (mem_normal_cone B hxB y).1 (by simpa [B] using hy)
      obtain ⟨z, hz, hdual⟩ := exists_dualNorm_eq_apply y
      calc
        dualNorm y = y z := hdual
        _ ≤ y x := by
          have hz' : y (z - x) ≤ 0 := hy' z (by simpa [B] using hz)
          exact sub_nonpos.mp (by simpa using hz')
    · intro hy
      refine (mem_normal_cone B hxB y).2 ?_
      intro z hz
      have hznorm : ‖z‖ ≤ 1 := by
        simpa [B] using hz
      have hdual_nonneg : 0 ≤ dualNorm y := by
        change 0 ≤ ‖y.toContinuousLinearMap‖
        exact norm_nonneg _
      have hyz_le_dual : y z ≤ dualNorm y := by
        calc
          y z ≤ |y z| := le_abs_self _
          _ ≤ dualNorm y * ‖z‖ := abs_apply_le_dual_norm_mul_norm y z
          _ ≤ dualNorm y * 1 := by
            exact mul_le_mul_of_nonneg_left hznorm hdual_nonneg
          _ = dualNorm y := by simp
      have hyz_le_x : y z ≤ y x := hyz_le_dual.trans hy
      have : y z - y x ≤ 0 := sub_nonpos.mpr hyz_le_x
      simpa using this
  · have hxball : x ∉ closedBall (0 : E) 1 := by
      simpa using hx
    rw [normal_cone_eq_empty_of_not_mem (closedBall (0 : E) 1) hxball, if_neg hx]

end
