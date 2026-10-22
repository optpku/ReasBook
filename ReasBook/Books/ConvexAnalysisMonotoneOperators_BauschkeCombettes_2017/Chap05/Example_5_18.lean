/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.FirmlyNonexpansiveOn
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Theorem_5_5

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Function
open scoped Topology

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Example 5.18: firmly nonexpansive self-maps are `1`-Lipschitz. -/
lemma lipschitzWith_one_of_firmlyNonexpansive {T : H → H} (hT : FirmlyNonexpansive T) :
    LipschitzWith 1 T := by
  -- Use the firm inequality and Cauchy--Schwarz, then cancel the common norm factor.
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  by_cases hxy : T x = T y
  · simp [hxy]
  · have hfirm :
        ‖T x - T y‖ ^ 2 ≤ inner ℝ (T x - T y) (x - y) := by
        simpa using (firmlyNonexpansive_iff_norm_sq_le_inner.mp hT) x y
    have hmul :
        ‖T x - T y‖ * ‖T x - T y‖ ≤ ‖T x - T y‖ * ‖x - y‖ := by
      simpa [pow_two] using le_trans hfirm (real_inner_le_norm (T x - T y) (x - y))
    have hnorm_pos : 0 < ‖T x - T y‖ := by
      refine norm_pos_iff.mpr ?_
      exact sub_ne_zero.mpr hxy
    simpa using (le_of_mul_le_mul_left hmul hnorm_pos)

/-- Helper for Example 5.18: firm nonexpansiveness yields the one-step squared-distance decrease
against every fixed point. -/
lemma sq_dist_image_fixedPoint_add_sq_residual_le_of_firmlyNonexpansive
    {T : H → H} (hT : FirmlyNonexpansive T) {x z : H} (hz : T z = z) :
    ‖T x - z‖ ^ 2 + ‖T x - x‖ ^ 2 ≤ ‖x - z‖ ^ 2 := by
  -- Rewrite the firm inequality against the fixed point `z` into a nonnegative cross term.
  have hfirm : ‖T x - z‖ ^ 2 ≤ inner ℝ (T x - z) (x - z) := by
    simpa [hz] using (firmlyNonexpansive_iff_norm_sq_le_inner.mp hT) x z
  have hcross_nonneg : 0 ≤ inner ℝ (T x - z) (x - T x) := by
    have hsplit :
        inner ℝ (T x - z) (x - z) =
          ‖T x - z‖ ^ 2 + inner ℝ (T x - z) (x - T x) := by
      calc
        inner ℝ (T x - z) (x - z) =
            inner ℝ (T x - z) ((T x - z) + (x - T x)) := by
              congr 2
              abel_nf
        _ = inner ℝ (T x - z) (T x - z) + inner ℝ (T x - z) (x - T x) := by
              rw [inner_add_right]
        _ = ‖T x - z‖ ^ 2 + inner ℝ (T x - z) (x - T x) := by
              rw [real_inner_self_eq_norm_sq]
    nlinarith [hfirm, hsplit]
  -- Expanding `x - z = (x - T x) + (T x - z)` turns the cross-term sign into the distance drop.
  have hexpand :
      ‖x - z‖ ^ 2 =
        ‖x - T x‖ ^ 2 + 2 * inner ℝ (x - T x) (T x - z) + ‖T x - z‖ ^ 2 := by
    calc
      ‖x - z‖ ^ 2 = ‖(x - T x) + (T x - z)‖ ^ 2 := by
        congr 1
        abel_nf
      _ = ‖x - T x‖ ^ 2 + 2 * inner ℝ (x - T x) (T x - z) + ‖T x - z‖ ^ 2 := by
        simpa using norm_add_sq_real (x - T x) (T x - z)
  have hres : ‖x - T x‖ ^ 2 = ‖T x - x‖ ^ 2 := by
    rw [norm_sub_rev]
  have hcross_nonneg' : 0 ≤ inner ℝ (x - T x) (T x - z) := by
    simpa [real_inner_comm] using hcross_nonneg
  nlinarith [hcross_nonneg', hexpand, hres]

variable [CompleteSpace H]

-- Proof sketch: this is Corollary 5.17(3) specialized to the constant relaxation sequence
-- `λₙ = 1`, for which the relaxed iteration is exactly the Picard orbit.
/-- Example 5.18: if `T : H → H` is firmly nonexpansive on a real Hilbert space and `Fix T` is
nonempty, then the Picard iterates `n ↦ (T^[n]) x₀` converge weakly to a fixed point of `T`. -/
theorem tendsto_weakly_iterates_to_fixedPoint_of_firmlyNonexpansive
    {T : H → H} (hT : FirmlyNonexpansive T) (hFix : (fixedPoints T).Nonempty) (x₀ : H) :
    ∃ z ∈ fixedPoints T,
      Tendsto (fun n ↦ toWeakSpace ℝ H ((T^[n]) x₀)) atTop
        (𝓝 (toWeakSpace ℝ H z)) := by
  let x : ℕ → H := fun n ↦ (T^[n]) x₀
  have hLip : LipschitzWith 1 T := lipschitzWith_one_of_firmlyNonexpansive hT
  have hfejer : FejerMonotone (fixedPoints T) x := by
    intro z hz n
    have hzfix : T z = z := Function.mem_fixedPoints_iff.mp hz
    -- Nonexpansiveness against a fixed point gives the Fejér inequality for one Picard step.
    simpa [x, dist_eq_norm, Function.iterate_succ_apply', hzfix] using hLip.dist_le_mul (x n) z
  rcases hFix with ⟨y, hy⟩
  have hres_sq_le :
      ∀ n, ‖x n - T (x n)‖ ^ 2 ≤ ‖x n - y‖ ^ 2 - ‖x (n + 1) - y‖ ^ 2 := by
    intro n
    have hstep :
        ‖x (n + 1) - y‖ ^ 2 + ‖x n - T (x n)‖ ^ 2 ≤ ‖x n - y‖ ^ 2 := by
      simpa [x, Function.iterate_succ_apply', dist_eq_norm, norm_sub_rev] using
        sq_dist_image_fixedPoint_add_sq_residual_le_of_firmlyNonexpansive hT (x := x n) hy
    nlinarith
  have hdist_tendsto : ∃ l : ℝ, Tendsto (fun n ↦ dist (x n) y) atTop (𝓝 l) := by
    -- Fejér monotonicity makes the distance to the chosen fixed point converge.
    simpa [x] using FejerMonotone.dist_tendsto hfejer hy
  rcases hdist_tendsto with ⟨l, hl⟩
  have hdist_sq_tendsto :
      Tendsto (fun n ↦ dist (x n) y ^ 2) atTop (𝓝 (l ^ 2)) := by
    exact hl.pow 2
  have hdist_sq_tendsto_succ :
      Tendsto (fun n ↦ dist (x (n + 1)) y ^ 2) atTop (𝓝 (l ^ 2)) := by
    simpa [Nat.succ_eq_add_one] using hdist_sq_tendsto.comp (tendsto_add_atTop_nat 1)
  have hdist_sq_diff_tendsto :
      Tendsto (fun n ↦ dist (x n) y ^ 2 - dist (x (n + 1)) y ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa [sub_eq_add_neg, Nat.succ_eq_add_one] using hdist_sq_tendsto.sub hdist_sq_tendsto_succ
  have hnorm_sq_diff_tendsto :
      Tendsto (fun n ↦ ‖x n - y‖ ^ 2 - ‖x (n + 1) - y‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa [dist_eq_norm] using hdist_sq_diff_tendsto
  have hres_sq_tendsto :
      Tendsto (fun n ↦ ‖x n - T (x n)‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    -- The squared residuals are trapped between `0` and successive drops of the distance squares.
    refine squeeze_zero (fun n ↦ sq_nonneg ‖x n - T (x n)‖) hres_sq_le hnorm_sq_diff_tendsto
  have hres_norm_tendsto :
      Tendsto (fun n ↦ ‖x n - T (x n)‖) atTop (𝓝 (0 : ℝ)) := by
    -- Taking square roots converts convergence of the squared norms back to convergence of norms.
    have hsqrt_tendsto :
        Tendsto (fun n ↦ Real.sqrt (‖x n - T (x n)‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) := by
      exact Real.continuous_sqrt.continuousAt.tendsto.comp hres_sq_tendsto
    simpa [Real.sqrt_zero, Real.sqrt_sq_eq_abs] using hsqrt_tendsto
  have hres :
      Tendsto (fun n ↦ x n - T (x n)) atTop (𝓝 (0 : H)) := by
    -- Norm convergence to `0` is equivalent to strong convergence to `0`.
    exact (tendsto_zero_iff_norm_tendsto_zero).mpr hres_norm_tendsto
  have hcluster :
      ∀ z : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H z) →
          z ∈ fixedPoints T := by
    intro z hz
    rcases hz.exists_subseq_tendsto with ⟨φ, hφmono, hφtendsto⟩
    let xSub : ℕ → H := fun n ↦ x (φ n)
    let r : ℕ → H := fun n ↦ xSub n - T (xSub n)
    let d : H := T z - z
    have hsub_res : Tendsto r atTop (𝓝 (0 : H)) := by
      -- Strong residual convergence passes to subsequences.
      simpa [xSub, r] using hres.comp hφmono.tendsto_atTop
    have hC :
        ∀ n, ‖xSub n - z‖ ≤ dist (x 0) y + ‖y - z‖ := by
      intro n
      calc
        ‖xSub n - z‖ = ‖(xSub n - y) + (y - z)‖ := by
          congr 1
          abel_nf
        _ ≤ ‖xSub n - y‖ + ‖y - z‖ := norm_add_le _ _
        _ = dist (xSub n) y + ‖y - z‖ := by
          rw [dist_eq_norm]
        _ ≤ dist (x 0) y + ‖y - z‖ := by
          exact add_le_add (hfejer.dist_antitone_of_mem hy (Nat.zero_le (φ n))) le_rfl
    have hinner_d :
        Tendsto (fun n ↦ inner ℝ (xSub n - z) d) atTop (𝓝 0) := by
      have hEval :=
        ((WeakBilin.eval_continuous ((topDualPairing ℝ H).flip)
          (InnerProductSpace.toDual ℝ H d)).tendsto (toWeakSpace ℝ H z)).comp hφtendsto
      have hEval' :
          Tendsto (fun n ↦ inner ℝ d (xSub n)) atTop (𝓝 (inner ℝ d z)) := by
        simpa only [xSub, toWeakSpace, LinearEquiv.refl_apply, LinearMap.flip_apply,
          topDualPairing_apply, InnerProductSpace.toDual_apply_apply] using hEval
      have hsub :
          Tendsto (fun n ↦ inner ℝ d (xSub n) - inner ℝ d z) atTop
            (𝓝 (inner ℝ d z - inner ℝ d z)) := by
        exact hEval'.sub
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ inner ℝ d z) atTop (𝓝 (inner ℝ d z)))
      simpa [xSub, inner_sub_right, real_inner_comm] using hsub
    have hres_norm :
        Tendsto (fun n ↦ ‖r n‖) atTop (𝓝 (0 : ℝ)) := by
      simpa [r] using hsub_res.norm
    have hinner_res :
        Tendsto (fun n ↦ inner ℝ (xSub n - z) (r n)) atTop (𝓝 0) := by
      have hmul :
          Tendsto (fun n ↦ (dist (x 0) y + ‖y - z‖) * ‖r n‖) atTop (𝓝 (0 : ℝ)) := by
        simpa using hres_norm.const_mul (dist (x 0) y + ‖y - z‖)
      have habs :
          Tendsto (fun n ↦ |inner ℝ (xSub n - z) (r n)|) atTop (𝓝 (0 : ℝ)) := by
        refine squeeze_zero'
          (f := fun n ↦ |inner ℝ (xSub n - z) (r n)|)
          (g := fun n ↦ (dist (x 0) y + ‖y - z‖) * ‖r n‖)
          (Eventually.of_forall fun n ↦ abs_nonneg _) ?_ ?_
        · filter_upwards with n
          exact le_trans (abs_real_inner_le_norm _ _)
            (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
        · simpa using hmul
      rw [tendsto_zero_iff_abs_tendsto_zero]
      simpa [Function.comp] using habs
    have hsq_le :
        ∀ n, ‖r n + d‖ ^ 2 ≤ inner ℝ (xSub n - z) (r n + d) := by
      intro n
      have hfirm :
          ‖T (xSub n) - T z‖ ^ 2 ≤ inner ℝ (T (xSub n) - T z) (xSub n - z) := by
        simpa [xSub] using (firmlyNonexpansive_iff_norm_sq_le_inner.mp hT) (xSub n) z
      have hrewrite : T (xSub n) - T z = (xSub n - z) - (r n + d) := by
        simp [xSub, r, d]
        abel
      have hfirm' :
          ‖(xSub n - z) - (r n + d)‖ ^ 2 ≤
            inner ℝ ((xSub n - z) - (r n + d)) (xSub n - z) := by
        simpa [hrewrite] using hfirm
      have hnorm :=
        norm_sub_sq_real (xSub n - z) (r n + d)
      have hinner :
          inner ℝ ((xSub n - z) - (r n + d)) (xSub n - z) =
            ‖xSub n - z‖ ^ 2 - inner ℝ (xSub n - z) (r n + d) := by
        calc
          inner ℝ ((xSub n - z) - (r n + d)) (xSub n - z) =
              inner ℝ (xSub n - z) (xSub n - z) -
                inner ℝ (r n + d) (xSub n - z) := by
                  rw [sub_eq_add_neg, inner_add_left, inner_neg_left, sub_eq_add_neg]
                  ring
          _ = ‖xSub n - z‖ ^ 2 - inner ℝ (xSub n - z) (r n + d) := by
              rw [real_inner_self_eq_norm_sq, real_inner_comm]
      nlinarith [hfirm', hnorm, hinner]
    have hinner_sum :
        Tendsto (fun n ↦ inner ℝ (xSub n - z) (r n + d)) atTop (𝓝 (0 : ℝ)) := by
      simpa [r, d, inner_add_right] using hinner_res.add hinner_d
    have hsq_tendsto_zero :
        Tendsto (fun n ↦ ‖r n + d‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
      refine squeeze_zero (fun n ↦ sq_nonneg ‖r n + d‖) hsq_le hinner_sum
    have hrd_tendsto : Tendsto (fun n ↦ r n + d) atTop (𝓝 d) := by
      simpa using hsub_res.add (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ d) atTop (𝓝 d))
    have hsq_tendsto_d :
        Tendsto (fun n ↦ ‖r n + d‖ ^ 2) atTop (𝓝 (‖d‖ ^ 2)) := by
      simpa using hrd_tendsto.norm.pow 2
    have hd_sq_zero : ‖d‖ ^ 2 = (0 : ℝ) :=
      tendsto_nhds_unique hsq_tendsto_d hsq_tendsto_zero
    have hd_zero : d = 0 := by
      exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero hd_sq_zero)
    exact Function.mem_fixedPoints_iff.mpr (sub_eq_zero.mp hd_zero)
  -- The Opial/Fejér convergence theorem closes the Picard-orbit argument once cluster points are fixed.
  simpa [x] using
    tendsto_weakly_of_fejerMonotone_of_weakSequentialClusterPts_mem ⟨y, hy⟩ x hfejer hcluster

end
