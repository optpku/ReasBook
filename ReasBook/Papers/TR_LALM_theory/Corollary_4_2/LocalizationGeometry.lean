/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.StochasticMoments

public section

open MeasureTheory
open scoped InnerProductSpace NNReal

namespace LALM.Correction.StochasticRun.Localization

universe u

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}

/-- Helper for Corollary 4.2: a base segment in the regularity region gives
the quadratic constraint-linearization residual bound. -/
private lemma normResidual_le_of_baseSegment
    (h : EqualityConstrained.Regularity f c)
    (x p : EuclideanSpace ℝ (Fin n))
    (hbase : segment ℝ x (trialPoint x p) ⊆ h.region) :
    ‖residual c x p‖ ≤ LALM.linearizationConstant h * ‖p‖ ^ 2 := by
  -- Apply the segmentwise Taylor remainder estimate to the constraint map.
  have hremainder := LALM.norm_sub_sub_fderiv_le c
    h.constraintGradientLipschitz h.region x (trialPoint x p)
    (fun _ hz ↦ h.differentiableAt_constraint hz)
    h.lipschitzOn_constraintFDeriv hbase
  simpa only [residual_def, trialPoint_def, add_sub_cancel_left,
    LALM.linearizationConstant_def, NNReal.coe_div, NNReal.coe_ofNat] using hremainder

/-- Helper for Corollary 4.2: a base segment in the regularity region already
controls the nonlinear correction, without assuming the correction segment. -/
private lemma normCorrection_le_of_baseSegment
    (h : EqualityConstrained.Regularity f c)
    (x p : EuclideanSpace ℝ (Fin n))
    (hbase : segment ℝ x (trialPoint x p) ⊆ h.region) :
    ‖step c x p‖ ≤ stepConstant h * ‖p‖ ^ 2 := by
  -- Use trial-point LICQ to convert the residual bound into a correction bound.
  let v := gramInverse c (trialPoint x p) (residual c x p)
  have hz : trialPoint x p ∈ h.region :=
    hbase (right_mem_segment ℝ x (trialPoint x p))
  have hvLower :
      (h.licqModulus : ℝ) * ‖v‖ ≤
        ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ :=
    h.licqLowerBound (trialPoint x p) hz v
  have hgram := comp_gramInverse h (trialPoint x p) hz (residual c x p)
  have hnormSq :
      ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ^ 2 =
        ⟪v, residual c x p⟫_ℝ := by
    calc
      ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ^ 2 =
          ⟪ContinuousLinearMap.adjoint
              (EqualityConstrained.constraintGradient c (trialPoint x p))
                (EqualityConstrained.constraintGradient c (trialPoint x p) v), v⟫_ℝ := by
        simpa only [ContinuousLinearMap.comp_apply, RCLike.re_to_real] using
          ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left
            (EqualityConstrained.constraintGradient c (trialPoint x p)) v
      _ = ⟪gram c (trialPoint x p) v, v⟫_ℝ := by
        rw [gram_def]
        rfl
      _ = ⟪residual c x p, v⟫_ℝ := by rw [hgram]
      _ = ⟪v, residual c x p⟫_ℝ := real_inner_comm _ _
  have hscaledInner :
      (h.licqModulus : ℝ) *
          ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ^ 2 ≤
        ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ *
          ‖residual c x p‖ := by
    calc
      (h.licqModulus : ℝ) *
          ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ^ 2 =
          (h.licqModulus : ℝ) * ⟪v, residual c x p⟫_ℝ := by rw [hnormSq]
      _ ≤ (h.licqModulus : ℝ) * (‖v‖ * ‖residual c x p‖) := by
        gcongr
        exact real_inner_le_norm v (residual c x p)
      _ = ((h.licqModulus : ℝ) * ‖v‖) * ‖residual c x p‖ := by ring
      _ ≤ ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ *
          ‖residual c x p‖ :=
        mul_le_mul_of_nonneg_right hvLower (norm_nonneg _)
  have hgradientBound :
      ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ≤
        ‖residual c x p‖ / (h.licqModulus : ℝ) := by
    by_cases hzero :
        ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ = 0
    · rw [hzero]
      positivity
    · have hpositive :
          0 < ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      apply (le_div_iff₀ (NNReal.coe_pos.2 h.licqModulus_pos)).mpr
      nlinarith
  have hresidual := normResidual_le_of_baseSegment h x p hbase
  rw [step_def]
  simp only [norm_neg]
  calc
    ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ≤
        ‖residual c x p‖ / (h.licqModulus : ℝ) := hgradientBound
    _ ≤ (LALM.linearizationConstant h * ‖p‖ ^ 2) /
        (h.licqModulus : ℝ) := by
      gcongr
    _ = stepConstant h * ‖p‖ ^ 2 := by
      rw [stepConstant_def, LALM.linearizationConstant_def]
      norm_num [NNReal.coe_div]
      ring

/-- Helper for Corollary 4.2: localization membership and a bounded base step
place both corrected transition segments in the regularity region. -/
lemma RegionCondition.isAdmissible_of_mem_of_norm_le
    {confidence : ℝ} {X : Set (EuclideanSpace ℝ (Fin n))}
    (h_region : RegionCondition h oracle params confidence X)
    (x p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X)
    (hp : ‖p‖ ≤ params.delta) :
    IsAdmissible h x p := by
  have hstepConstantNonneg : 0 ≤ stepConstant h := by
    rw [stepConstant_def]
    positivity
  have hdeltaNonneg : (0 : ℝ) ≤ params.delta := NNReal.coe_nonneg _
  have hbaseDistance :
      dist x (trialPoint x p) ≤ localizationRadius h params := by
    calc
      dist x (trialPoint x p) = dist (trialPoint x p) x := dist_comm _ _
      _ = ‖p‖ := by
        rw [dist_eq_norm, trialPoint_def, add_sub_cancel_left]
      _ ≤ params.delta := hp
      _ ≤ localizationRadius h params := by
        rw [localizationRadius_def, displacementFactor_def]
        nlinarith [mul_nonneg hstepConstantNonneg (sq_nonneg (params.delta : ℝ))]
  -- The base segment remains in the corrected thickening of its left endpoint.
  have hbaseSegment : segment ℝ x (trialPoint x p) ⊆ h.region := by
    intro y hy
    apply h_region.thickening_subset
    apply Metric.mem_cthickening_of_dist_le y x (localizationRadius h params) X hx
    exact (Metric.mem_closedBall.mp
      (segment_subset_closedBall_left x (trialPoint x p) hy)).trans hbaseDistance
  have hcorrection := normCorrection_le_of_baseSegment h x p hbaseSegment
  have hpSq : ‖p‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hdeltaNonneg).2 hp
  have htotalDistance :
      dist (trialPoint x p) (nextPoint c x p) + dist (trialPoint x p) x ≤
        localizationRadius h params := by
    calc
      dist (trialPoint x p) (nextPoint c x p) + dist (trialPoint x p) x =
          ‖step c x p‖ + ‖p‖ := by
        rw [dist_comm (trialPoint x p) (nextPoint c x p), dist_eq_norm,
          nextPoint_def, add_sub_cancel_left, dist_eq_norm, trialPoint_def,
          add_sub_cancel_left]
      _ ≤ stepConstant h * ‖p‖ ^ 2 + ‖p‖ :=
        add_le_add hcorrection (le_refl _)
      _ ≤ stepConstant h * params.delta ^ 2 + params.delta := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hpSq hstepConstantNonneg) hp
      _ = localizationRadius h params := by
        rw [localizationRadius_def, displacementFactor_def]
        ring
  -- Transfer the correction segment back to the same thickening center.
  have hcorrectionSegment :
      segment ℝ (trialPoint x p) (nextPoint c x p) ⊆ h.region := by
    intro y hy
    apply h_region.thickening_subset
    apply Metric.mem_cthickening_of_dist_le y x (localizationRadius h params) X hx
    have hyTrial :
        dist y (trialPoint x p) ≤ dist (trialPoint x p) (nextPoint c x p) :=
      Metric.mem_closedBall.mp
        (segment_subset_closedBall_left (trialPoint x p) (nextPoint c x p) hy)
    calc
      dist y x ≤ dist y (trialPoint x p) + dist (trialPoint x p) x :=
        dist_triangle _ _ _
      _ ≤ dist (trialPoint x p) (nextPoint c x p) +
          dist (trialPoint x p) x := add_le_add hyTrial (le_refl _)
      _ ≤ localizationRadius h params := htotalDistance
  exact ⟨hbaseSegment, hcorrectionSegment⟩

end LALM.Correction.StochasticRun.Localization

end
