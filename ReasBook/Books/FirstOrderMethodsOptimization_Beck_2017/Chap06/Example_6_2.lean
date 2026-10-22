/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_10
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Proposition_6_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Example 6.2 is `source-facing` in the scalar proximal-operator API. The owner abstraction is
`prox[...]` from Definition 6.1. Its nontrivial scalar penalties are already owned upstream by the
Chapter 6 declaration `hardThresholdPenalty` together with the Chapter 2 owner `l0Indicator`; this
file now uses that `EReal`-valued owner directly rather than keeping parallel lifted copies. -/

/- Example 6.2 (1): the zero penalty is the specialization `c = 0` of Proposition 6.2.1. -/
recall prox_const_eq_singleton

-- Proof sketch: this is exactly the owner-level hard-thresholding computation from Example 6.10.
/- Example 6.2 (2): if `0 ≤ λ`, then the proximal mapping of the negative origin spike returns
`{0}` below the threshold `√(2 λ)`, `{x}` above the threshold, and both points at the tie case.
This exact source-facing proximal formula is already owned by Example 6.10's canonical theorem
`prox_hardThresholdPenalty_eq_hardThresholding`, so this file reuses that theorem directly rather
than keeping a duplicate renamed wrapper. -/
recall prox_hardThresholdPenalty_eq_hardThresholding

private theorem proximal_objective_positive_origin_spike_at_origin (lam : ℝ) :
    proximal_objective (hardThresholdPenalty (-lam)) 0 0 = (lam : EReal) := by
  rw [proximal_objective, hardThresholdPenalty_zero (-lam)]
  simp

private theorem proximal_objective_positive_origin_spike_at_zero_of_ne_zero
    (lam : ℝ) {u : ℝ} (hu : u ≠ 0) :
    proximal_objective (hardThresholdPenalty (-lam)) 0 u =
      ((((1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  rw [proximal_objective, hardThresholdPenalty_of_ne_zero (-lam) hu]
  simp

private theorem proximal_objective_positive_origin_spike_self
    (lam x : ℝ) (hx : x ≠ 0) :
    proximal_objective (hardThresholdPenalty (-lam)) x x = 0 := by
  rw [proximal_objective, hardThresholdPenalty_of_ne_zero (-lam) hx]
  simp

private theorem proximal_objective_positive_origin_spike_at_zero
    (lam x : ℝ) :
    proximal_objective (hardThresholdPenalty (-lam)) x 0 =
      (((lam + (1 / 2 : ℝ) * x ^ (2 : ℕ)) : ℝ) : EReal) := by
  rw [proximal_objective, hardThresholdPenalty_zero (-lam)]
  simp [pow_two]

private theorem proximal_objective_positive_origin_spike_of_ne_zero
    (lam x y : ℝ) (hy : y ≠ 0) :
    proximal_objective (hardThresholdPenalty (-lam)) x y =
      ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  rw [proximal_objective, hardThresholdPenalty_of_ne_zero (-lam) hy]
  simp

-- Proof sketch: unfold `prox` and compare the proximal objective at `u = x` and `u = 0`.
-- If `x ≠ 0`, the point `u = x` has value `0`, while `u = 0` has the larger value
-- `λ + x^2 / 2`, so `{x}` is the minimizer set. If `x = 0`, the infimum value `0` is approached
-- along nonzero `u → 0` but is not attained, because the value at `u = 0` is `λ > 0`.
/-- Example 6.2 (3): for `λ > 0`, the proximal mapping of the positive origin spike, written
canonically as `hardThresholdPenalty (-λ)`, returns `{x}` away from the origin and is empty at the
origin. -/
theorem prox_positive_origin_spike_eq_piecewise (lam : ℝ) (hlam : 0 < lam) (x : ℝ) :
    prox[hardThresholdPenalty (-lam)] x = if x = 0 then ∅ else {x} := by
  by_cases hx : x = 0
  · subst x
    ext u
    simpa using
      (show u ∈ prox[hardThresholdPenalty (-lam)] 0 ↔ False from by
        constructor
        · intro hu
          rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
          by_cases hu0 : u = 0
          · subst u
            let v : ℝ := min 1 lam
            have hvpos : 0 < v := by
              dsimp [v]
              exact lt_min zero_lt_one hlam
            have hvne : v ≠ 0 := hvpos.ne'
            have hvsq_lt : (1 / 2 : ℝ) * v ^ (2 : ℕ) < lam := by
              dsimp [v]
              by_cases hlam_le_one : lam ≤ 1
              · rw [min_eq_right hlam_le_one]
                nlinarith
              · rw [min_eq_left (le_of_lt (lt_of_not_ge hlam_le_one))]
                nlinarith
            have hvlt : proximal_objective (hardThresholdPenalty (-lam)) 0 v <
                proximal_objective (hardThresholdPenalty (-lam)) 0 0 := by
              have hvnorm : ‖v‖ = v := by
                exact abs_of_pos hvpos
              have hvlt' :
                  (((1 / 2 : ℝ) * ‖v‖ ^ (2 : ℕ) : ℝ) : EReal) < (lam : EReal) := by
                rw [hvnorm]
                exact_mod_cast hvsq_lt
              rw [proximal_objective_positive_origin_spike_at_zero_of_ne_zero lam hvne,
                proximal_objective_positive_origin_spike_at_origin]
              exact hvlt'
            exact (not_le_of_gt hvlt) (hu v)
          · have hhalf_ne : u / 2 ≠ 0 := by
              intro hhalf
              apply hu0
              linarith
            have hhalf_lt :
                proximal_objective (hardThresholdPenalty (-lam)) 0 (u / 2) <
                  proximal_objective (hardThresholdPenalty (-lam)) 0 u := by
              have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
              have hhalf_lt' :
                  ((1 / 2 : ℝ) * ‖u / 2‖ ^ (2 : ℕ) : ℝ) < (1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) := by
                have hnorm_two : ‖(2 : ℝ)‖ = 2 := by norm_num
                rw [norm_div, hnorm_two, pow_two, pow_two]
                have hu_sq_pos : 0 < ‖u‖ * ‖u‖ := by positivity
                nlinarith
              have hhalf_lt'' :
                  ((((1 / 2 : ℝ) * ‖u / 2‖ ^ (2 : ℕ)) : ℝ) : EReal) <
                    ((((1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
                exact_mod_cast hhalf_lt'
              rw [proximal_objective_positive_origin_spike_at_zero_of_ne_zero lam hhalf_ne,
                proximal_objective_positive_origin_spike_at_zero_of_ne_zero lam hu0]
              exact hhalf_lt''
            exact (not_le_of_gt hhalf_lt) (hu (u / 2))
        · intro hu
          exact False.elim hu)
  · ext u
    simpa [hx] using
      (show u ∈ prox[hardThresholdPenalty (-lam)] x ↔ u = x from by
        constructor
        · intro hu
          rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
          have hux :
              proximal_objective (hardThresholdPenalty (-lam)) x u ≤
                proximal_objective (hardThresholdPenalty (-lam)) x x := hu x
          have hxx : proximal_objective (hardThresholdPenalty (-lam)) x x = 0 :=
            proximal_objective_positive_origin_spike_self lam x hx
          rw [hxx] at hux
          by_cases hu0 : u = 0
          · subst u
            have hpos' : 0 < lam + (1 / 2 : ℝ) * x ^ (2 : ℕ) := by
              have hx_sq_pos : 0 < x ^ (2 : ℕ) := sq_pos_of_ne_zero hx
              nlinarith
            have hpos : 0 < proximal_objective (hardThresholdPenalty (-lam)) x 0 := by
              have hposE : (0 : EReal) < (((lam + (1 / 2 : ℝ) * x ^ (2 : ℕ)) : ℝ) : EReal) := by
                exact_mod_cast hpos'
              rw [proximal_objective_positive_origin_spike_at_zero]
              exact hposE
            exact False.elim ((not_le_of_gt hpos) hux)
          · have hu_obj :
                proximal_objective (hardThresholdPenalty (-lam)) x u =
                  ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
              rw [proximal_objective_positive_origin_spike_of_ne_zero lam x u hu0]
            have hu_nonneg : 0 ≤ proximal_objective (hardThresholdPenalty (-lam)) x u := by
              rw [hu_obj]
              have hu_nonneg' : 0 ≤ (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) := by
                positivity
              exact_mod_cast hu_nonneg'
            have huzero :
                proximal_objective (hardThresholdPenalty (-lam)) x u = 0 :=
              le_antisymm hux hu_nonneg
            rw [hu_obj] at huzero
            have hu_eq_zero : (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) = 0 := by
              exact_mod_cast huzero
            have hnorm_sq : ‖u - x‖ ^ (2 : ℕ) = 0 := by
              nlinarith
            exact sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_of_pow_eq_zero hnorm_sq))
        · intro hu
          subst u
          rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
          have hxx : proximal_objective (hardThresholdPenalty (-lam)) x x = 0 :=
            proximal_objective_positive_origin_spike_self lam x hx
          intro y
          by_cases hy : y = 0
          · rw [hxx,
              show proximal_objective (hardThresholdPenalty (-lam)) x y =
                  (((lam + (1 / 2 : ℝ) * x ^ (2 : ℕ)) : ℝ) : EReal) by
                    subst y
                    rw [proximal_objective_positive_origin_spike_at_zero]]
            have hy_nonneg' : 0 ≤ lam + (1 / 2 : ℝ) * x ^ (2 : ℕ) := by
              positivity
            exact_mod_cast hy_nonneg'
          · rw [hxx,
              show proximal_objective (hardThresholdPenalty (-lam)) x y =
                  ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) : ℝ) : EReal) by
                    rw [proximal_objective_positive_origin_spike_of_ne_zero lam x y hy]]
            have hy_nonneg' : 0 ≤ (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
              positivity
            exact_mod_cast hy_nonneg')

end
