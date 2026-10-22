/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap09.Text_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

/- Text 9.2 is a `bridge/view` item. The chapter's Bregman-distance owner already lives in
`Definition_9_2`, and `Text_9_1` already provides the real-valued gradient specialization.
This file only adds the one-dimensional `deriv` bridge and the asymmetry example. -/

-- Proof sketch: rewrite the real-valued bridge theorem from `Text_9_1` and use the canonical
-- `gradient_eq_deriv'` bridge on `ℝ`, together with the standard formula for the real inner
-- product.
/-- For a real-valued potential on `ℝ`, the Chapter 9 Bregman distance specializes to the
one-variable derivative formula `ω(x) - ω(y) - ω'(y) (x - y)`. -/
@[simp] theorem bregmanDistance_apply_real_deriv (ω : ℝ → ℝ) (x y : ℝ) :
    B[ω] x y = ω x - ω y - deriv ω y * (x - y) := by
  rw [bregmanDistance_apply_real]
  rw [gradient_eq_deriv']
  rw [show inner ℝ (deriv ω y) (x - y) = deriv ω y * (x - y) by
    simpa using (RCLike.inner_apply' (deriv ω y) (x - y) :
      inner ℝ (deriv ω y) (x - y) = (starRingEnd ℝ) (deriv ω y) * (x - y))]

-- Proof sketch: take `ω = exp`, `x = 0`, and `y = 1`. The function `exp` is strictly convex on
-- `Set.univ`, and the two Bregman values reduce to unequal real numbers.
/-- Text 9.2: there exists a strictly convex function and two points for which the Bregman
distance is asymmetric. -/
theorem exists_strictly_convex_bregman_asymmetric_pair :
    ∃ (ω : ℝ → ℝ) (x y : ℝ),
      StrictConvexOn ℝ Set.univ ω ∧
        B[ω] x y ≠ B[ω] y x := by
  refine ⟨Real.exp, 0, 2, ?_, ?_⟩
  · simpa using strictConvexOn_exp
  · have h02 : B[Real.exp] 0 2 = 1 + Real.exp 2 := by
      rw [bregmanDistance_apply_real_deriv]
      rw [Real.deriv_exp]
      ring_nf
      norm_num [Real.exp_zero]
    have h20 : B[Real.exp] 2 0 = Real.exp 2 - 3 := by
      rw [bregmanDistance_apply_real_deriv]
      rw [Real.deriv_exp]
      ring_nf
      norm_num [Real.exp_zero]
      ring
    intro hEq
    rw [h02, h20] at hEq
    linarith
