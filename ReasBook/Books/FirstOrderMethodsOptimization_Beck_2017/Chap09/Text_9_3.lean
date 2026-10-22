/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Tactic.NormNum
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Text_9_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

/- Text 9.3 is `source-facing`: it asserts the existence of a strictly convex real-valued
generator together with positive points witnessing triangle-inequality failure. The chapter's
canonical Bregman owner is already `B[ω]`, and the one-dimensional `deriv` bridge is reused from
`Text_9_2` to evaluate the cubic witness. -/

/-- The cubic generator `x ↦ x³` is strictly convex on the positive real line. -/
theorem strictConvexOn_cube_Ioi :
    StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ x ^ (3 : ℕ)) := by
  have hIci : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x ^ (3 : ℕ)) := by
    simpa using (strictConvexOn_pow (by decide : 2 ≤ (3 : ℕ)))
  simpa using
    hIci.subset
      (show Set.Ioi (0 : ℝ) ⊆ Set.Ici 0 by
        intro x hx
        exact le_of_lt (show 0 < x from hx))
      (convex_Ioi (0 : ℝ))

private theorem bregmanDistance_cube_3_1 :
    B[Function.toEReal (fun x : ℝ ↦ x ^ (3 : ℕ))] 3 1 = 20 := by
  have h := bregmanDistance_apply_real_deriv (fun x : ℝ ↦ x ^ (3 : ℕ)) 3 1
  norm_num [deriv_pow_field] at h ⊢
  simpa using h

private theorem bregmanDistance_cube_3_2 :
    B[Function.toEReal (fun x : ℝ ↦ x ^ (3 : ℕ))] 3 2 = 7 := by
  have h := bregmanDistance_apply_real_deriv (fun x : ℝ ↦ x ^ (3 : ℕ)) 3 2
  norm_num [deriv_pow_field] at h ⊢
  simpa using h

private theorem bregmanDistance_cube_2_1 :
    B[Function.toEReal (fun x : ℝ ↦ x ^ (3 : ℕ))] 2 1 = 4 := by
  have h := bregmanDistance_apply_real_deriv (fun x : ℝ ↦ x ^ (3 : ℕ)) 2 1
  norm_num [deriv_pow_field] at h ⊢
  simpa using h

/-- For the cubic generator `ω(x) = x³`, the Bregman distance fails the triangle inequality at
`x = 3`, `y = 2`, and `z = 1`. -/
theorem cube_bregman_triangle_counterexample :
    B[Function.toEReal (fun x : ℝ ↦ x ^ (3 : ℕ))] 3 1 >
      B[Function.toEReal (fun x : ℝ ↦ x ^ (3 : ℕ))] 3 2 +
        B[Function.toEReal (fun x : ℝ ↦ x ^ (3 : ℕ))] 2 1 := by
  rw [bregmanDistance_cube_3_1, bregmanDistance_cube_3_2, bregmanDistance_cube_2_1]
  norm_num

-- Proof sketch: witness the existential statement with `ω(x) = x^3` on `(0, ∞)` and the points
-- `x = 3`, `y = 2`, `z = 1`, combining strict convexity with the explicit counterexample above.
/-- Text 9.3: the Bregman distance need not satisfy the triangle inequality; a strictly convex
generator on the positive reals already gives a counterexample. -/
theorem exists_strictly_convex_bregman_triangle_counterexample :
    ∃ ω : ℝ → ℝ,
      StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) ω ∧
        ∃ x y z : ℝ,
          0 < x ∧
            0 < y ∧
              0 < z ∧
                B[ω] x z > B[ω] x y + B[ω] y z := by
  refine ⟨(fun x : ℝ ↦ x ^ (3 : ℕ)), strictConvexOn_cube_Ioi, 3, 2, 1, by norm_num, by norm_num,
    by norm_num, ?_⟩
  simpa using cube_bregman_triangle_counterexample
