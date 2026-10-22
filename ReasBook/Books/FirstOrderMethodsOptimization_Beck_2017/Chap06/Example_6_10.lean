/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Example_2_4
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_4

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain sampling for Example 6.10:
- `source-facing`: the shifted scalar penalty `hardThresholdPenalty` and its proximal
  hard-thresholding formula.
- `core/canonical`: Chapter 2's `l0Indicator`, Chapter 6's `prox[...]`, and the hard-thresholding
  owner `𝓗[...]`.
- `bridge/view`: the identity relating `hardThresholdPenalty` to the weighted scalar `l0Indicator`.

The Chapter 2 summation theorem `hammingNorm_eq_sum_l0Indicator` already owns the finite
coordinatewise `ℓ₀` decomposition, so this file should not keep a second weighted wrapper around
that same owner statement. -/

/-- The shifted scalar penalty `J`, written directly in the `EReal` codomain used by `prox`,
as the weighted nonzero indicator shifted by the constant `λ`. -/
noncomputable def hardThresholdPenalty (lam : ℝ) : ℝ → EReal :=
  fun t ↦ -lam + lam * l0Indicator t

-- Proof sketch: evaluating `hardThresholdPenalty` at `t` is exactly its defining shifted
-- weighted-indicator formula.
/-- Evaluating `hardThresholdPenalty` expands to the shifted weighted scalar `ℓ₀` penalty. -/
@[simp] theorem hardThresholdPenalty_apply (lam t : ℝ) :
    hardThresholdPenalty lam t = (lam * l0Indicator t - lam : EReal) := by
  simp [hardThresholdPenalty, sub_eq_add_neg, add_comm]

-- Proof sketch: at `t = 0`, the scalar owner `l0Indicator` vanishes, so the shifted penalty is
-- exactly the constant term `-λ`.
/-- At the origin, `hardThresholdPenalty` equals the negative shift `-λ`. -/
@[simp] theorem hardThresholdPenalty_zero (lam : ℝ) :
    hardThresholdPenalty lam 0 = (-lam : EReal) := by
  simp [hardThresholdPenalty]

-- Proof sketch: away from the origin, the scalar owner `l0Indicator` is `1`, so the weighted
-- indicator and the shift cancel.
/-- Away from the origin, `hardThresholdPenalty` vanishes. -/
@[simp] theorem hardThresholdPenalty_of_ne_zero (lam : ℝ) {t : ℝ} (ht : t ≠ 0) :
    hardThresholdPenalty lam t = 0 := by
  rw [hardThresholdPenalty_apply]
  simp [ht]

-- Proof sketch: rewrite `λ l₀` pointwise as `hardThresholdPenalty λ + λ`, then apply the
-- owner-level constant-shift invariance theorem `prox_add_const`.
/-- The weighted scalar `ℓ₀` penalty `t ↦ λ l₀(t)` and the shifted penalty `J` from Example 6.10
have the same proximal mapping, because they differ only by the additive constant `λ`. -/
theorem prox_mul_l0Indicator_eq_hardThresholdPenalty (lam : ℝ) :
    prox[fun t : ℝ ↦ (lam * l0Indicator t : EReal)] =
      prox[hardThresholdPenalty lam] := by
  simpa [hardThresholdPenalty, add_comm, add_left_comm, add_assoc] using
    (prox_add_const (fun t : ℝ ↦ (lam * l0Indicator t : EReal)) (-lam)).symm

/-- Helper for Example 6.10: at the exceptional candidate `t = 0`, the proximal objective of the
shifted `ℓ₀` penalty is the scalar value `s² / 2 - λ`. -/
private theorem proximal_objective_hardThresholdPenalty_at_zero (lam s : ℝ) :
    proximal_objective (hardThresholdPenalty lam) s 0 =
      (((1 / 2 : ℝ) * s ^ (2 : ℕ) - lam : ℝ) : EReal) := by
  -- At `t = 0`, only the constant shift from `hardThresholdPenalty` remains.
  rw [proximal_objective, hardThresholdPenalty_zero]
  simp [pow_two, sub_eq_add_neg, add_comm]

/-- Helper for Example 6.10: at the nonzero candidate `t = s`, the quadratic remainder vanishes,
so the proximal objective is `0`. -/
private theorem proximal_objective_hardThresholdPenalty_at_self_of_ne_zero
    (lam s : ℝ) (hs : s ≠ 0) :
    proximal_objective (hardThresholdPenalty lam) s s = 0 := by
  -- On the nonzero branch, the penalty vanishes and `‖s - s‖ = 0`.
  rw [proximal_objective, hardThresholdPenalty_of_ne_zero lam hs]
  simp

/-- Helper for Example 6.10: every nonzero candidate lies on the purely quadratic branch of the
proximal objective for the shifted `ℓ₀` penalty. -/
private theorem proximal_objective_hardThresholdPenalty_of_ne_zero
    (lam s t : ℝ) (ht : t ≠ 0) :
    proximal_objective (hardThresholdPenalty lam) s t =
      ((((1 / 2 : ℝ) * ‖t - s‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  -- Away from the origin, `hardThresholdPenalty` contributes no extra term.
  rw [proximal_objective, hardThresholdPenalty_of_ne_zero lam ht]
  simp

/-- Helper for Example 6.10: below the threshold `√(2 λ)`, the exceptional value
`s² / 2 - λ` is strictly negative. -/
private theorem zero_candidate_objective_neg
    (lam s : ℝ) (hlam : 0 ≤ lam) (hs : |s| < Real.sqrt (2 * lam)) :
    (1 / 2 : ℝ) * s ^ (2 : ℕ) - lam < 0 := by
  -- Square the threshold inequality to compare `s²` directly with `2 λ`.
  have harg_nonneg : 0 ≤ 2 * lam := by
    nlinarith
  have hs_sq' : |s| ^ (2 : ℕ) < (Real.sqrt (2 * lam)) ^ (2 : ℕ) := by
    exact (sq_lt_sq₀ (abs_nonneg s) (Real.sqrt_nonneg (2 * lam))).2 hs
  have hs_sq'' : |s| ^ (2 : ℕ) < 2 * lam := by
    rw [← Real.sq_sqrt harg_nonneg]
    exact hs_sq'
  have hs_sq : s ^ (2 : ℕ) < 2 * lam := by
    simpa [sq_abs] using hs_sq''
  nlinarith

/-- Helper for Example 6.10: above the threshold `√(2 λ)`, the exceptional value
`s² / 2 - λ` is strictly positive. -/
private theorem zero_candidate_objective_pos
    (lam s : ℝ) (hlam : 0 ≤ lam) (hs : Real.sqrt (2 * lam) < |s|) :
    0 < (1 / 2 : ℝ) * s ^ (2 : ℕ) - lam := by
  -- The strict threshold inequality again becomes a comparison between squares.
  have harg_nonneg : 0 ≤ 2 * lam := by
    nlinarith
  have hs_sq' : (Real.sqrt (2 * lam)) ^ (2 : ℕ) < |s| ^ (2 : ℕ) := by
    exact (sq_lt_sq₀ (Real.sqrt_nonneg (2 * lam)) (abs_nonneg s)).2 hs
  have hs_sq'' : 2 * lam < |s| ^ (2 : ℕ) := by
    rw [← Real.sq_sqrt harg_nonneg]
    exact hs_sq'
  have hs_sq : 2 * lam < s ^ (2 : ℕ) := by
    simpa [sq_abs] using hs_sq''
  nlinarith

/-- Helper for Example 6.10: exactly on the threshold `√(2 λ)`, the exceptional value
`s² / 2 - λ` vanishes. -/
private theorem zero_candidate_objective_eq_zero
    (lam s : ℝ) (hlam : 0 ≤ lam) (hs : |s| = Real.sqrt (2 * lam)) :
    (1 / 2 : ℝ) * s ^ (2 : ℕ) - lam = 0 := by
  -- Equality of absolute values at the threshold turns into equality of squares.
  have harg_nonneg : 0 ≤ 2 * lam := by
    nlinarith
  have hs_sq : s ^ (2 : ℕ) = 2 * lam := by
    calc
      s ^ (2 : ℕ) = |s| ^ (2 : ℕ) := by rw [sq_abs]
      _ = (Real.sqrt (2 * lam)) ^ (2 : ℕ) := by rw [hs]
      _ = 2 * lam := by rw [Real.sq_sqrt harg_nonneg]
  nlinarith

-- Proof sketch: under `0 ≤ λ`, compare the objective values of
-- `t ↦ hardThresholdPenalty λ t + (t - s)^2 / 2` at `t = 0` and `t = s`. The first gives
-- `s^2 / 2 - λ`, the second gives `0`, so the minimizers are exactly `{0}`, `{s}`, or `{0, s}`
-- according as `|s|` is below, above, or equal to `Real.sqrt (2 * λ)`. At `λ = 0`, both sides
-- reduce to `{s}`.
/-- Example 6.10: if `0 ≤ λ`, then the proximal mapping of the shifted scalar `ℓ₀` penalty `J`
is exactly the hard-thresholding operator `𝓗[√(2 λ)]`. -/
theorem prox_hardThresholdPenalty_eq_hardThresholding (lam : ℝ) (hlam : 0 ≤ lam) (s : ℝ) :
    prox[hardThresholdPenalty lam] s = 𝓗[Real.sqrt (2 * lam)] s := by
  by_cases hs_lt : |s| < Real.sqrt (2 * lam)
  · -- Below threshold, `t = 0` beats every nonzero candidate strictly.
    rw [hard_thresholding_of_abs_lt hs_lt, Set.eq_singleton_iff_unique_mem]
    constructor
    · rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
      intro u
      by_cases hu0 : u = 0
      · subst u
        exact le_rfl
      · have hobj0_lt_zero : proximal_objective (hardThresholdPenalty lam) s 0 < 0 := by
          rw [proximal_objective_hardThresholdPenalty_at_zero]
          exact_mod_cast zero_candidate_objective_neg lam s hlam hs_lt
        have hu_nonneg : 0 ≤ proximal_objective (hardThresholdPenalty lam) s u := by
          rw [proximal_objective_hardThresholdPenalty_of_ne_zero lam s u hu0]
          have hu_nonneg' : 0 ≤ (1 / 2 : ℝ) * ‖u - s‖ ^ (2 : ℕ) := by
            positivity
          exact_mod_cast hu_nonneg'
        exact le_trans hobj0_lt_zero.le hu_nonneg
    · intro u hu
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
      by_cases hu0 : u = 0
      · exact hu0
      · have hobj0_lt_zero : proximal_objective (hardThresholdPenalty lam) s 0 < 0 := by
          rw [proximal_objective_hardThresholdPenalty_at_zero]
          exact_mod_cast zero_candidate_objective_neg lam s hlam hs_lt
        have hu_nonneg : 0 ≤ proximal_objective (hardThresholdPenalty lam) s u := by
          rw [proximal_objective_hardThresholdPenalty_of_ne_zero lam s u hu0]
          have hu_nonneg' : 0 ≤ (1 / 2 : ℝ) * ‖u - s‖ ^ (2 : ℕ) := by
            positivity
          exact_mod_cast hu_nonneg'
        have hobj0_lt_u : proximal_objective (hardThresholdPenalty lam) s 0 <
            proximal_objective (hardThresholdPenalty lam) s u := by
          exact lt_of_lt_of_le hobj0_lt_zero hu_nonneg
        exact False.elim ((not_le_of_gt hobj0_lt_u) (hu 0))
  · by_cases hs_gt : Real.sqrt (2 * lam) < |s|
    · -- Above threshold, the nonzero candidate `t = s` has value `0`, while `t = 0` is worse.
      have hs_ne : s ≠ 0 := by
        intro hs0
        subst hs0
        exact (not_lt_of_ge (Real.sqrt_nonneg (2 * lam))) (by simpa using hs_gt)
      rw [hard_thresholding_of_lt_abs hs_gt, Set.eq_singleton_iff_unique_mem]
      constructor
      · rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
        intro u
        by_cases hu0 : u = 0
        · subst u
          rw [proximal_objective_hardThresholdPenalty_at_self_of_ne_zero lam s hs_ne,
            proximal_objective_hardThresholdPenalty_at_zero]
          exact_mod_cast (zero_candidate_objective_pos lam s hlam hs_gt).le
        · rw [proximal_objective_hardThresholdPenalty_at_self_of_ne_zero lam s hs_ne,
            proximal_objective_hardThresholdPenalty_of_ne_zero lam s u hu0]
          have hu_nonneg' : 0 ≤ (1 / 2 : ℝ) * ‖u - s‖ ^ (2 : ℕ) := by
            positivity
          exact_mod_cast hu_nonneg'
      · intro u hu
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
        have hus : proximal_objective (hardThresholdPenalty lam) s u ≤
            proximal_objective (hardThresholdPenalty lam) s s := hu s
        rw [proximal_objective_hardThresholdPenalty_at_self_of_ne_zero lam s hs_ne] at hus
        by_cases hu0 : u = 0
        · subst u
          rw [proximal_objective_hardThresholdPenalty_at_zero] at hus
          have hobj0_pos :
              (0 : EReal) <
                (((1 / 2 : ℝ) * s ^ (2 : ℕ) - lam : ℝ) : EReal) := by
            exact_mod_cast zero_candidate_objective_pos lam s hlam hs_gt
          exact False.elim ((not_le_of_gt hobj0_pos) hus)
        · have hu_nonneg : 0 ≤ proximal_objective (hardThresholdPenalty lam) s u := by
            rw [proximal_objective_hardThresholdPenalty_of_ne_zero lam s u hu0]
            have hu_nonneg' : 0 ≤ (1 / 2 : ℝ) * ‖u - s‖ ^ (2 : ℕ) := by
              positivity
            exact_mod_cast hu_nonneg'
          have huzero : proximal_objective (hardThresholdPenalty lam) s u = 0 :=
            le_antisymm hus hu_nonneg
          rw [proximal_objective_hardThresholdPenalty_of_ne_zero lam s u hu0] at huzero
          have hu_eq_zero : (1 / 2 : ℝ) * ‖u - s‖ ^ (2 : ℕ) = 0 := by
            exact_mod_cast huzero
          have hnorm_sq : ‖u - s‖ ^ (2 : ℕ) = 0 := by
            nlinarith
          exact sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_of_pow_eq_zero hnorm_sq))
    · -- The remaining branch is the threshold equality `|s| = √(2 λ)`.
      have hs_eq : |s| = Real.sqrt (2 * lam) := by
        exact le_antisymm (le_of_not_gt hs_gt) (le_of_not_gt hs_lt)
      have hobj0_zero :
          proximal_objective (hardThresholdPenalty lam) s 0 = 0 := by
        rw [proximal_objective_hardThresholdPenalty_at_zero]
        exact_mod_cast zero_candidate_objective_eq_zero lam s hlam hs_eq
      have hzero_mem : 0 ∈ prox[hardThresholdPenalty lam] s := by
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
        intro u
        by_cases hu0 : u = 0
        · subst u
          exact le_rfl
        · rw [hobj0_zero, proximal_objective_hardThresholdPenalty_of_ne_zero lam s u hu0]
          have hu_nonneg' : 0 ≤ (1 / 2 : ℝ) * ‖u - s‖ ^ (2 : ℕ) := by
            positivity
          exact_mod_cast hu_nonneg'
      have hs_mem : s ∈ prox[hardThresholdPenalty lam] s := by
        by_cases hs0 : s = 0
        · simpa [hs0] using hzero_mem
        · rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
          intro v
          by_cases hv0 : v = 0
          · subst v
            rw [proximal_objective_hardThresholdPenalty_at_self_of_ne_zero lam s hs0, hobj0_zero]
          · rw [proximal_objective_hardThresholdPenalty_at_self_of_ne_zero lam s hs0,
              proximal_objective_hardThresholdPenalty_of_ne_zero lam s v hv0]
            have hv_nonneg' : 0 ≤ (1 / 2 : ℝ) * ‖v - s‖ ^ (2 : ℕ) := by
              positivity
            exact_mod_cast hv_nonneg'
      rw [hard_thresholding_of_abs_eq hs_eq]
      ext u
      constructor
      · intro hu
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
        by_cases hu0 : u = 0
        · simp [hu0]
        · have hu_le_zero : proximal_objective (hardThresholdPenalty lam) s u ≤
              proximal_objective (hardThresholdPenalty lam) s 0 := hu 0
          rw [hobj0_zero] at hu_le_zero
          have hu_nonneg : 0 ≤ proximal_objective (hardThresholdPenalty lam) s u := by
            rw [proximal_objective_hardThresholdPenalty_of_ne_zero lam s u hu0]
            have hu_nonneg' : 0 ≤ (1 / 2 : ℝ) * ‖u - s‖ ^ (2 : ℕ) := by
              positivity
            exact_mod_cast hu_nonneg'
          have huzero : proximal_objective (hardThresholdPenalty lam) s u = 0 :=
            le_antisymm hu_le_zero hu_nonneg
          rw [proximal_objective_hardThresholdPenalty_of_ne_zero lam s u hu0] at huzero
          have hu_eq_zero : (1 / 2 : ℝ) * ‖u - s‖ ^ (2 : ℕ) = 0 := by
            exact_mod_cast huzero
          have hnorm_sq : ‖u - s‖ ^ (2 : ℕ) = 0 := by
            nlinarith
          simp [sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_of_pow_eq_zero hnorm_sq))]
      · intro hu
        have hu' : u = 0 ∨ u = s := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hu
        rcases hu' with hu0 | hus
        · simpa [hu0] using hzero_mem
        · simpa [hus] using hs_mem
