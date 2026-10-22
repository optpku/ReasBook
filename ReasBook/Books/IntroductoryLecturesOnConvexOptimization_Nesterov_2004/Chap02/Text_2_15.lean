/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Text_2_13

-- Declarations for this item will be appended below by the statement pipeline.

open Finset

noncomputable section

variable {n : ℕ}

/- Text 2.15 lies in the finite-dimensional Euclidean hard-instance domain for the chapter's
quadratic lower-bound family.

Source/core/bridge triage:
* source-facing: the norm estimate for the textbook stationary point `\bar x_k`
* core/canonical: the owner point `quadraticHardInstanceStationaryPoint k` from `Text_2_13`
* bridge/view: the coordinate formula `quadraticHardInstanceStationaryPoint_apply`, the Euclidean
  squared-norm owner theorem `EuclideanSpace.real_norm_sq_eq`, and the arithmetic estimate
  `sum_Icc_sq_le_cubic_third` from `Text_2_16`

Sampled owner-style declarations in this domain:
* `quadraticHardInstanceStationaryPoint` in `Text_2_13`
* `quadraticHardInstanceStationaryPoint_apply` in `Text_2_13`
* `EuclideanSpace.real_norm_sq_eq` in mathlib
* `sum_Icc_sq_le_cubic_third` in `Text_2_16`

Best owner abstraction:
* the canonical stationary point `quadraticHardInstanceStationaryPoint k`

Primitive data:
* the canonical stationary point `quadraticHardInstanceStationaryPoint k`

Derived API:
* its exact squared norm, obtained by coordinate expansion through the owner Euclidean norm
* the cubic upper bound from `Text_2_16`

This file keeps the source-facing norm estimate, but derives it directly from the chapter owner
stationary point and the existing Euclidean/arithmetic owner declarations rather than maintaining
any parallel local coordinate wrapper or finite-sum API.
-/

/-- The squared Euclidean norm of the canonical hard-instance stationary point is the normalized
sum of the first `k.1 + 1` squares. -/
theorem quadraticHardInstanceStationaryPoint_sqNorm_eq (k : Fin n) :
    ‖quadraticHardInstanceStationaryPoint k‖ ^ 2 =
      (∑ i ∈ Icc 1 (k.1 + 1), (i : ℝ) ^ 2) / (((k.1 + 2 : ℕ) : ℝ) ^ 2) := by
  let f : ℕ → ℝ := fun i ↦
    if hi : i < n then (quadraticHardInstanceStationaryPoint k) ⟨i, hi⟩ ^ 2 else 0
  have hnorm : ‖quadraticHardInstanceStationaryPoint k‖ ^ 2 = ∑ i ∈ range n, f i := by
    calc
      ‖quadraticHardInstanceStationaryPoint k‖ ^ 2
          = ∑ i : Fin n, (quadraticHardInstanceStationaryPoint k) i ^ 2 := by
              simpa using (EuclideanSpace.real_norm_sq_eq (quadraticHardInstanceStationaryPoint k))
      _ = ∑ i : Fin n, f i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [f]
      _ = ∑ i ∈ range n, f i := Fin.sum_univ_eq_sum_range f n
  rw [hnorm]
  have hk1 : k.1 + 1 ≤ n := Nat.succ_le_of_lt k.2
  rw [← Finset.sum_range_add_sum_Ico f hk1]
  have htail : (∑ i ∈ Ico (k.1 + 1) n, f i) = 0 := by
    refine sum_eq_zero ?_
    intro i hi
    have hk_le_i : k.1 + 1 ≤ i := (mem_Ico.mp hi).1
    have hi_lt_n : i < n := (mem_Ico.mp hi).2
    have hk_lt_i : k.1 < i := lt_of_lt_of_le (Nat.lt_succ_self _) hk_le_i
    have hnot : ¬ (⟨i, hi_lt_n⟩ : Fin n) ≤ k := by
      exact fun h ↦ not_le_of_gt hk_lt_i (Fin.le_iff_val_le_val.mp h)
    simp [f, hi_lt_n, quadraticHardInstanceStationaryPoint_apply, hnot]
  rw [htail, add_zero]
  calc
    ∑ i ∈ range (k.1 + 1), f i
        = ∑ i ∈ range (k.1 + 1),
            ((((k.1 + 1 - i : ℕ) : ℝ) / ((k.1 + 2 : ℕ) : ℝ)) ^ 2) := by
          refine sum_congr rfl ?_
          intro i hi
          have hi_lt_n : i < n := lt_of_lt_of_le (mem_range.mp hi) hk1
          have hi_le_k : i ≤ k.1 := Nat.lt_succ_iff.mp (mem_range.mp hi)
          have hik : (⟨i, hi_lt_n⟩ : Fin n) ≤ k :=
            Fin.le_iff_val_le_val.mpr hi_le_k
          simp [f, hi_lt_n, quadraticHardInstanceStationaryPoint_apply, hik]
          field_simp
          have hreal :
              (((k.1 : ℕ) : ℝ) + 2 - ((i : ℝ) + 1)) = (((k.1 + 1 - i : ℕ) : ℝ)) := by
            have hi2 : i + 1 ≤ k.1 + 2 := by omega
            have hcast : (((k.1 + 2 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ)) =
                (((k.1 + 1 - i : ℕ) : ℝ)) := by
              rw [← Nat.cast_sub hi2]
              norm_num
              omega
            simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hcast
          rw [hreal]
    _ = ∑ i ∈ range (k.1 + 1),
          ((((i + 1 : ℕ) : ℝ) / ((k.1 + 2 : ℕ) : ℝ)) ^ 2) := by
          have hrewrite :
              ∑ i ∈ range (k.1 + 1), ((((k.1 + 1 - i : ℕ) : ℝ) / ((k.1 + 2 : ℕ) : ℝ)) ^ 2) =
                ∑ i ∈ range (k.1 + 1), ((((k.1 - i + 1 : ℕ) : ℝ) / ((k.1 + 2 : ℕ) : ℝ)) ^ 2) := by
                  refine sum_congr rfl ?_
                  intro i hi
                  have hi_le_k : i ≤ k.1 := Nat.lt_succ_iff.mp (mem_range.mp hi)
                  have hnat : k.1 + 1 - i = k.1 - i + 1 := by omega
                  simp [hnat]
          have hreflect :
              ∑ i ∈ range (k.1 + 1), ((((k.1 - i + 1 : ℕ) : ℝ) / ((k.1 + 2 : ℕ) : ℝ)) ^ 2) =
                ∑ i ∈ range (k.1 + 1), ((((i + 1 : ℕ) : ℝ) / ((k.1 + 2 : ℕ) : ℝ)) ^ 2) := by
                  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                    (Finset.sum_range_reflect
                      (fun i ↦ ((((i + 1 : ℕ) : ℝ) / ((k.1 + 2 : ℕ) : ℝ)) ^ 2))
                      (k.1 + 1))
          exact hrewrite.trans hreflect
    _ = ∑ i ∈ range (k.1 + 1), (((i + 1 : ℕ) : ℝ) ^ 2) / (((k.1 + 2 : ℕ) : ℝ) ^ 2) := by
          refine sum_congr rfl ?_
          intro i hi
          rw [div_pow]
    _ = (∑ i ∈ range (k.1 + 1), (((i + 1 : ℕ) : ℝ) ^ 2)) / (((k.1 + 2 : ℕ) : ℝ) ^ 2) := by
          rw [Finset.sum_div]
    _ = (∑ i ∈ Icc 1 (k.1 + 1), (i : ℝ) ^ 2) / (((k.1 + 2 : ℕ) : ℝ) ^ 2) := by
          congr 1
          rw [show Icc 1 (k.1 + 1) = Ico 1 (k.1 + 2) by
            simpa using (Finset.Ico_succ_right_eq_Icc 1 (k.1 + 1))]
          rw [Finset.sum_Ico_eq_sum_range]
          refine sum_congr rfl ?_
          intro i hi
          ring_nf

/-- Helper for Text 2.15: the textbook square-sum bound follows from the degree-two Faulhaber
formula over `ℚ`. -/
private lemma sum_Icc_sq_le_cubic_third_rat_local (m : ℕ) :
    (∑ i ∈ Icc 1 m, (i : ℚ) ^ 2) ≤ ((m + 1 : ℚ) ^ 3) / 3 := by
  -- Route correction: prove the arithmetic estimate locally from `sum_Ico_pow` so this file no
  -- longer depends on the later statement file `Text_2_16`.
  rw [← Ico_add_one_right_eq_Icc 1 m]
  -- Expand the degree-two Faulhaber identity on the canonical half-open interval.
  rw [sum_Ico_pow]
  rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero]
  norm_num [bernoulli'_zero, bernoulli'_one, bernoulli'_two]
  have hm : (0 : ℚ) ≤ m := by
    positivity
  nlinarith

/-- Helper for Text 2.15: cast the local rational square-sum bound into `ℝ` for the norm
estimate. -/
private lemma sum_Icc_sq_le_cubic_third_real_local (m : ℕ) :
    (∑ i ∈ Icc 1 m, (i : ℝ) ^ 2) ≤ ((m + 1 : ℝ) ^ 3) / 3 := by
  -- Move the rational Faulhaber estimate into `ℝ`, keeping exactly the same interval sum.
  have hq := sum_Icc_sq_le_cubic_third_rat_local m
  have hq' :
      ((∑ i ∈ Icc 1 m, (i : ℚ) ^ 2 : ℚ) : ℝ) ≤
        ((((m + 1 : ℚ) ^ 3) / 3 : ℚ) : ℝ) := by
    exact_mod_cast hq
  simpa using hq'

/-- Text 2.15: the hard-instance stationary point `\bar x_k`, encoded by
`quadraticHardInstanceStationaryPoint k`, satisfies `‖\bar x_k‖^2 ≤ (1 / 3) * (k + 1)`. In the
file's zero-based `Fin` indexing, `k : Fin n` encodes the textbook index `k + 1`, so the right
side becomes `(1 / 3) * (k.1 + 2)`. -/
-- Proof sketch: apply the exact squared-norm identity
-- `quadraticHardInstanceStationaryPoint_sqNorm_eq`, then use the owner arithmetic estimate
-- `sum_Icc_sq_le_cubic_third` with `k + 1`, and simplify the resulting cubic-over-quadratic
-- expression.
theorem quadraticHardInstanceStationaryPoint_sqNorm_le (k : Fin n) :
    ‖quadraticHardInstanceStationaryPoint k‖ ^ 2 ≤ (1 / 3 : ℝ) * (k.1 + 2) := by
  -- Rewrite the geometric norm exactly as the arithmetic sum from the source proof.
  rw [quadraticHardInstanceStationaryPoint_sqNorm_eq]
  have hsq :
      (∑ i ∈ Icc 1 (k.1 + 1), (i : ℝ) ^ 2) ≤ (((k.1 + 2 : ℕ) : ℝ) ^ 3) / 3 := by
    -- Apply the local cubic upper bound at `m = k.1 + 1`.
    convert sum_Icc_sq_le_cubic_third_real_local (k.1 + 1) using 1
    norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
  have hdiv :
      (∑ i ∈ Icc 1 (k.1 + 1), (i : ℝ) ^ 2) / (((k.1 + 2 : ℕ) : ℝ) ^ 2) ≤
        ((((k.1 + 2 : ℕ) : ℝ) ^ 3) / 3) / (((k.1 + 2 : ℕ) : ℝ) ^ 2) := by
    -- Divide by the positive denominator to match the normalized norm identity.
    exact div_le_div_of_nonneg_right hsq (by positivity)
  -- Simplify the resulting cubic-over-quadratic expression to the claimed linear bound.
  refine hdiv.trans_eq ?_
  have hk2 : (((k.1 + 2 : ℕ) : ℝ) ^ 2) ≠ 0 := by positivity
  field_simp [hk2]
  norm_num
