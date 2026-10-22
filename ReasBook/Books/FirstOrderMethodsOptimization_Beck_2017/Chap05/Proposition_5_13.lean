/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Example_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_17

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 5.13 is `source-facing`: the textbook function is
`x ↦ ((‖x‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) + (δ_ C) x`. The chapter already owns this layer through
`is_strongly_convex_function`, while the real-valued statement
`StrongConvexOn C 1 (fun x ↦ ‖x‖ ^ (2 : ℕ) / 2)` is the canonical `bridge/view` companion used
downstream. -/

/-- Proposition 5.13: on a convex set `C` in a real inner product space, the extended-real-valued
function `x ↦ ((‖x‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) + (δ_ C) x` is `1`-strongly convex. -/
theorem half_squared_norm_add_indicator_is_one_strongly_convex_function
    (C : Set E) (hC : Convex ℝ C) :
    is_strongly_convex_function
      (fun x : E ↦ ((‖x‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) + (δ_ C) x)
      1 := by
  refine
    (is_strongly_convex_function_iff_sub_half_sigma_norm_sq_is_convex
      (fun x : E ↦ ((‖x‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) + (δ_ C) x)
      1
      (by norm_num)
      ?_).2 ?_
  · intro x
    change (((‖x‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) + (δ_ C) x) ≠ ⊥
    by_cases hx : x ∈ C
    · rw [extendedIndicator_of_mem hx]
      simp
    · rw [extendedIndicator_of_not_mem hx]
      rw [EReal.coe_add_top]
      simp
  · have hsub :
        (fun x : E ↦
          (((‖x‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) + (δ_ C) x) -
            ((((1 : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) : ℝ) : EReal)) = δ_ C := by
      funext x
      change
        (((‖x‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) + (δ_ C) x) -
            ((((1 : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) : ℝ) : EReal) =
          (δ_ C) x
      by_cases hx : x ∈ C
      · rw [extendedIndicator_of_mem hx]
        rw [add_zero]
        have hhalf : ‖x‖ ^ (2 : ℕ) / 2 = (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) := by
          ring
        rw [hhalf, ← EReal.coe_sub]
        simp
      · rw [extendedIndicator_of_not_mem hx]
        rw [EReal.coe_add_top]
        simpa using EReal.top_sub_coe ((1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ))
    rw [hsub]
    exact extendedIndicator_isConvexFunction_of_convex C hC

/-- Bridge/view companion to Proposition 5.13: on `C`, the real-valued half squared norm is
`1`-strongly convex in mathlib's canonical `StrongConvexOn` form. -/
theorem half_squared_norm_is_one_strongly_convex_on
    (C : Set E) (hC : Convex ℝ C) :
    StrongConvexOn C 1 (fun x : E ↦ ‖x‖ ^ (2 : ℕ) / 2) := by
  rw [strongConvexOn_iff_convex]
  have hconst : ConvexOn ℝ C (fun _ : E ↦ (0 : ℝ)) := convexOn_const (0 : ℝ) hC
  convert hconst using 1
  funext x
  ring

end
