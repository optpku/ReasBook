/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Theorem_8_28

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

open scoped ProjectedSubgradientErgodicNotation

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → EReal} {C XStar : Set E} {fOpt : ℝ}
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)

local notation "x̄" =>
  projected_subgradient_method_iterate C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0
local notation "x̄[" k "]" => x̄ k
local notation "T_" k => T[t](k)
local notation "x^(" k ")" => x^[h_problem, g, t, x0](k)

/- Remark 8.29 is `source-facing`: it records the one-step recursion for the weighted averages
already owned by `projected_subgradient_stepsize_average_iterate`. The canonical ambient iterate
owner is `projected_subgradient_method_iterate`, and the algebra only needs the prefix sums
`T[t](k)` and `T[t](k + 1)` to be nonzero; in the dynamic-stepsize setting of Theorem 8.28 these
nonvanishing hypotheses are provided by positivity. -/

/-- Remark 8.29: if the prefix sums `T_k = ∑_{n=0}^k t_n` and `T_{k+1}` are nonzero, then the
weighted averages from Theorem 8.28 satisfy the recursion
`x^(k+1) = (T_k / T_{k+1}) x^(k) + (t_{k+1} / T_{k+1}) x̄[k+1]`, where `x̄[k+1]` is the canonical
ambient projected iterate. In the dynamic-stepsize regime of Theorem 8.28, these nonvanishing
prefix-sum hypotheses hold automatically. -/
-- Proof sketch: unfold
-- `projected_subgradient_stepsize_average_iterate` at `k` and `k + 1`, split the sum defining
-- `x^(k+1)` into the prefix through `k` and the last term, and rewrite the prefix using
-- `projected_subgradient_stepsize_prefix_sum` and
-- `projected_subgradient_stepsize_average_iterate`; the hypotheses `hTk` and `hTsucc` justify
-- the scalar cancellations by `T_k` and `T_{k+1}`.
theorem projected_subgradient_stepsize_average_iterate_succ
    (k : ℕ) (hTk : (T_ k) ≠ 0) (hTsucc : (T_(k + 1)) ≠ 0) :
    x^(k + 1) = ((T_ k) / T_(k + 1)) • x^(k) +
      (t (k + 1) / T_(k + 1)) • x̄[k + 1] := by
  -- Rewrite both averages as center masses so the recursion becomes a one-point insertion.
  rw [projected_subgradient_stepsize_average_iterate_eq_centerMass
    (h_problem := h_problem) (g := g) (t := t) (x0 := x0) (k := k + 1)]
  rw [projected_subgradient_stepsize_average_iterate_eq_centerMass
    (h_problem := h_problem) (g := g) (t := t) (x0 := x0) (k := k)]
  -- Split `range (k + 2)` into the old prefix and the new index `k + 1`.
  simpa [projected_subgradient_stepsize_prefix_sum, Finset.sum_range_succ,
    Finset.range_add_one, add_comm, add_left_comm, add_assoc] using
    (Finset.centerMass_insert (i := k + 1) (t := Finset.range (k + 1))
      (w := fun n ↦ t n) (z := fun n ↦ x̄[n]) (by simp)
      (by simpa [projected_subgradient_stepsize_prefix_sum] using hTk))

end
