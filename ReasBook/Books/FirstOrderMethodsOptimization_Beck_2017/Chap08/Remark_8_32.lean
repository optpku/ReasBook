/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Theorem_8_31

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
local notation "x^(" k ")" =>
  projected_subgradient_strongly_convex_average_iterate h_problem g t x0 k

/- Remark 8.32 is `source-facing`: it records the one-step recursion for the strongly convex
weighted averages already owned by `projected_subgradient_strongly_convex_average_iterate`. The
canonical ambient iterate owner is `projected_subgradient_method_iterate`, so the recursive
formula should expose `x̄[k + 1]` directly rather than a coerced subtype-valued iterate. -/

/-- Helper for Remark 8.32: the first strongly convex weighted average is exactly the first
projected iterate. -/
lemma stronglyConvexAverageIterateOne :
    x^(1) = x̄[1] := by
  -- Rewrite the first average as the explicit two-term weighted sum.
  rw [projected_subgradient_strongly_convex_average_iterate_eq_sum
    (h_problem := h_problem) (g := g) (t := t) (x0 := x0) (k := 1)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  -- The weight at `0` vanishes and the weight at `1` is exactly `1`.
  simp [projected_subgradient_strongly_convex_average_weight_eq_of_pos
    (k := 1) (Nat.succ_pos 0)]
  norm_num

/-- Helper for Remark 8.32: on the old prefix `0, …, k`, the next-step weights are a common
scalar multiple of the previous weights. -/
lemma stronglyConvexAverageWeightSuccPrefix {k n : ℕ} (hk : 0 < k)
    (_hn : n ∈ Finset.range (k + 1)) :
    α[k + 1](n) = ((k : ℝ) / (k + 2 : ℝ)) * α[k](n) := by
  have hkR : (k : ℝ) ≠ 0 := by
    exact_mod_cast hk.ne'
  have hk1R : (k + 1 : ℝ) ≠ 0 := by
    positivity
  have hk2R : (k + 2 : ℝ) ≠ 0 := by
    positivity
  -- Expand both weights into their explicit rational forms for positive indices.
  rw [projected_subgradient_strongly_convex_average_weight_eq_of_pos
    (k := k + 1) (n := n) (Nat.succ_pos k)]
  rw [projected_subgradient_strongly_convex_average_weight_eq_of_pos
    (k := k) (n := n) hk]
  -- Clear the denominators and normalize the resulting polynomial identity.
  field_simp [hkR, hk1R, hk2R]
  norm_num [Nat.cast_add]
  ring_nf

/-- Helper for Remark 8.32: the new terminal weight in the `(k + 1)`-average is `2 / (k + 2)`. -/
lemma stronglyConvexAverageWeightSuccLast (k : ℕ) :
    α[k + 1](k + 1) = ((2 : ℝ) / (k + 2 : ℝ)) := by
  have hk1R : (k + 1 : ℝ) ≠ 0 := by
    positivity
  have hk2R : (k + 2 : ℝ) ≠ 0 := by
    positivity
  -- Expand the terminal weight and cancel the common factor `k + 1`.
  rw [projected_subgradient_strongly_convex_average_weight_eq_of_pos
    (k := k + 1) (n := k + 1) (Nat.succ_pos k)]
  field_simp [hk1R, hk2R]
  norm_num [Nat.cast_add]
  ring_nf

-- Proof sketch: unfold `projected_subgradient_strongly_convex_average_iterate` at `k + 1`, split
-- the weighted sum into the prefix through `k` and the last term `n = k + 1`, then rewrite the
-- prefix coefficients using the identity `α_n^(k+1) = (k / (k + 2)) α_n^k` and the last
-- coefficient as `α_(k+1)^(k+1) = 2 / (k + 2)`.
/-- Remark 8.32: the weighted average iterates `x^(k)` from Theorem 8.31 satisfy the recursion
`x^(k + 1) = (k / (k + 2)) x^(k) + (2 / (k + 2)) x̄[k + 1]`, where `x̄[k + 1]` is the canonical
ambient projected iterate. -/
theorem projected_subgradient_strongly_convex_average_iterate_succ (k : ℕ) :
    x^(k + 1) = ((k : ℝ) / (k + 2 : ℝ)) • x^(k) +
      ((2 : ℝ) / (k + 2 : ℝ)) • x̄[k + 1] := by
  by_cases hk0 : k = 0
  · subst hk0
    -- The degenerate average `x^(0)` is `x̄[0]`, and the first weighted average is `x̄[1]`.
    rw [projected_subgradient_strongly_convex_average_iterate_zero
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0)]
    rw [stronglyConvexAverageIterateOne
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0)]
    simp
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    -- Rewrite both averages as the canonical weighted finite sums from Theorem 8.31.
    rw [projected_subgradient_strongly_convex_average_iterate_eq_sum
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0) (k := k + 1)]
    rw [projected_subgradient_strongly_convex_average_iterate_eq_sum
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0) (k := k)]
    -- Split off the new terminal iterate and rewrite the old prefix by the previous weights.
    rw [Finset.sum_range_succ]
    calc
      Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k + 1](n) • x̄[n]) +
          α[k + 1](k + 1) • x̄[k + 1]
          =
            Finset.sum (Finset.range (k + 1))
              (fun n ↦ (((k : ℝ) / (k + 2 : ℝ)) * α[k](n)) • x̄[n]) +
              α[k + 1](k + 1) • x̄[k + 1] := by
                congr 1
                refine Finset.sum_congr rfl ?_
                intro n hn
                rw [stronglyConvexAverageWeightSuccPrefix
                  (k := k) (n := n) hk_pos hn]
      _ =
          Finset.sum (Finset.range (k + 1))
            (fun n ↦ ((k : ℝ) / (k + 2 : ℝ)) • (α[k](n) • x̄[n])) +
            α[k + 1](k + 1) • x̄[k + 1] := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro n hn
              simp [smul_smul]
      _ =
          ((k : ℝ) / (k + 2 : ℝ)) •
            Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n) • x̄[n]) +
            α[k + 1](k + 1) • x̄[k + 1] := by
              rw [← Finset.smul_sum]
      _ =
          ((k : ℝ) / (k + 2 : ℝ)) •
            Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n) • x̄[n]) +
            ((2 : ℝ) / (k + 2 : ℝ)) • x̄[k + 1] := by
              rw [stronglyConvexAverageWeightSuccLast (k := k)]

end
