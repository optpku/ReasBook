/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_36

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: the owner recurrence on `switching_parameters α` scales both coordinates at once.
-- Then inspect the appropriate coordinate according to the parity of `k`, using the owner
-- theorems from `Definition_6_36` to read off `α_{k+1}` and `α_{k-1}`.
/-- Lemma 6.2.4: if the switching-parameter sequence attached to `α_k` satisfies the contraction
rule `parameters_{k+1} = (1 - τ_k) parameters_k`, then for every `k ≥ 0`,
`α_{k+1} = (1 - τ_k) α_{k-1}`. -/
theorem alpha_succ_eq_one_sub_tau_mul_pred_of_alternating_scalar_updates
    (α : Set.Ici (-1 : ℤ) → ℝ) (τ : ℕ → ℝ)
    (hparameters :
      ∀ k : ℕ, switching_parameters α (k + 1) = (1 - τ k) • switching_parameters α k)
    (k : ℕ) :
    α (switching_parameters_succ_index k) =
      (1 - τ k) * α (switching_parameters_pred_index k) := by
  -- Split on the parity of `k`, since parity determines which coordinate stores `α_{k-1}`.
  rcases Nat.even_or_odd k with hk | hk
  · -- For even `k`, the first coordinate of the pair carries `α_{k-1}` at step `k`
    -- and `α_{k+1}` at step `k + 1`.
    have hfst := congrArg Prod.fst (hparameters k)
    rw [switching_parameters_of_odd α (Even.add_one hk), switching_parameters_of_even α hk] at hfst
    simpa [switching_parameters_curr_index, switching_parameters_succ_index] using hfst
  · -- For odd `k`, the second coordinate carries `α_{k-1}` at step `k`
    -- and `α_{k+1}` at step `k + 1`.
    have hsnd := congrArg Prod.snd (hparameters k)
    rw [switching_parameters_of_even α (Odd.add_one hk), switching_parameters_of_odd α hk] at hsnd
    simpa [switching_parameters_curr_index, switching_parameters_succ_index] using hsnd
