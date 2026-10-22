/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Example_8_5

public section

noncomputable section

namespace VariationalRegularization

/-- Exercise 8.7. For `0 < β`, the whole-space conjugate functional of
`smoothNormPenalty β` is equation `(8.39)` from Example 8.5. -/
theorem smoothNormPenalty_conjugateFunctional_eq {d : ℕ}
    (β : ℝ) (hβ : 0 < β) (y : EuclideanSpace ℝ (Fin d)) :
    conjugateFunctional Set.univ (smoothNormPenalty β) y =
      if ‖y‖ ≤ 1 then (((-β) * Real.sqrt (1 - ‖y‖ ^ 2) : ℝ) : EReal) else ⊤ := by
  by_cases hy : ‖y‖ ≤ 1
  · rw [if_pos hy]
    exact smoothNormPenalty_conjugateFunctional_eq_of_norm_le_one β hβ y hy
  · rw [if_neg hy]
    exact smoothNormPenalty_conjugateFunctional_eq_top_of_one_lt_norm β hβ y (lt_of_not_ge hy)

end VariationalRegularization
