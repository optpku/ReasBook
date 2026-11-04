/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_5.ch9_sec9_5_zero_one

open scoped BigOperators

section Proposition_2_18

variable {m : ℕ}

/-- Helper for Proposition 2.18: the aggregate knapsack forbids simultaneously having
`z = 1` and `y i = 1`. -/
private lemma notBothOneOfBinaryColumnKnapsack
    {z : ℝ}
    {y : Fin m → ℝ}
    (hy_binary : is_zero_one_vector y)
    (hknapsack : (m : ℝ) * z + ∑ k : Fin m, y k ≤ m)
    (i : Fin m)
    (hz1 : z = 1)
    (hyi1 : y i = 1) :
    False := by
  -- The selected `1`-coordinate forces the full sum to be at least `1`.
  have hsum_lb : 1 ≤ ∑ k : Fin m, y k := by
    simpa [hyi1] using is_zero_one_vector.le_sum_univ hy_binary i
  have hcontr : (m : ℝ) + 1 ≤ m := by
    -- Rewriting the aggregate inequality in this branch yields the contradiction.
    rw [hz1] at hknapsack
    linarith [hknapsack, hsum_lb]
  linarith

/-- Proposition 2.18 (1) [Cover inequality yielding disaggregation]. If binary variables
`z : ℝ` and `y : Fin m → ℝ` satisfy the aggregate constraint
`(m : ℝ) * z + ∑ k, y k ≤ m`, then each disaggregated inequality `z + y i ≤ 1` is valid. -/
theorem coverDisaggregationOfBinaryColumnKnapsack
    {z : ℝ}
    {y : Fin m → ℝ}
    (hz_binary : z = 0 ∨ z = 1)
    (hy_binary : is_zero_one_vector y)
    (hknapsack : (m : ℝ) * z + ∑ k : Fin m, y k ≤ m)
    (i : Fin m) :
    z + y i ≤ 1 := by
  -- Split on the binary value of `z`, then on the binary value of the selected coordinate.
  rcases hz_binary with hz0 | hz1
  · rw [hz0]
    rcases is_zero_one_vector.apply hy_binary i with hyi0 | hyi1
    · rw [hyi0]
      norm_num
    · rw [hyi1]
      norm_num
  · rcases is_zero_one_vector.apply hy_binary i with hyi0 | hyi1
    · rw [hz1, hyi0]
      norm_num
    · -- This is the only nontrivial branch: the aggregate cover inequality rules it out.
      exact False.elim (notBothOneOfBinaryColumnKnapsack hy_binary hknapsack i hz1 hyi1)

/-- Proposition 2.18 (1) in universal form: all disaggregated inequalities `z + y i ≤ 1` hold
simultaneously. -/
theorem coverDisaggregationOfBinaryColumnKnapsack_all
    {z : ℝ}
    {y : Fin m → ℝ}
    (hz_binary : z = 0 ∨ z = 1)
    (hy_binary : is_zero_one_vector y)
    (hknapsack : (m : ℝ) * z + ∑ k : Fin m, y k ≤ m) :
    ∀ i, z + y i ≤ 1 := by
  intro i
  exact coverDisaggregationOfBinaryColumnKnapsack hz_binary hy_binary hknapsack i

/-- Proposition 2.18 (2) [Cover inequality yielding disaggregation]. If additionally
`x : ℝ` is binary and `z = 1 - x`, then the disaggregated inequality from
`coverDisaggregationOfBinaryColumnKnapsack` rewrites to `y i ≤ x`. -/
theorem assignmentLeOfBinaryColumnKnapsack
    {x z : ℝ}
    {y : Fin m → ℝ}
    (hx_binary : x = 0 ∨ x = 1)
    (hy_binary : is_zero_one_vector y)
    (hz_eq : z = 1 - x)
    (hknapsack : (m : ℝ) * z + ∑ k : Fin m, y k ≤ m)
    (i : Fin m) :
    y i ≤ x := by
  have hz_binary : z = 0 ∨ z = 1 := by
    -- Translate the binary alternatives for `x` through `z = 1 - x`.
    rcases hx_binary with hx0 | hx1
    · right
      rw [hz_eq, hx0]
      norm_num
    · left
      rw [hz_eq, hx1]
      norm_num
  have hdisagg : z + y i ≤ 1 :=
    coverDisaggregationOfBinaryColumnKnapsack hz_binary hy_binary hknapsack i
  -- Substitute `z = 1 - x` into the disaggregated cover inequality and rearrange.
  rw [hz_eq] at hdisagg
  linarith

/-- Proposition 2.18 (2) in universal form: after substituting `z = 1 - x`, every disaggregated
inequality becomes `y i ≤ x`. -/
theorem assignmentLeOfBinaryColumnKnapsack_all
    {x z : ℝ}
    {y : Fin m → ℝ}
    (hx_binary : x = 0 ∨ x = 1)
    (hy_binary : is_zero_one_vector y)
    (hz_eq : z = 1 - x)
    (hknapsack : (m : ℝ) * z + ∑ k : Fin m, y k ≤ m) :
    ∀ i, y i ≤ x := by
  intro i
  exact assignmentLeOfBinaryColumnKnapsack hx_binary hy_binary hz_eq hknapsack i

end Proposition_2_18
