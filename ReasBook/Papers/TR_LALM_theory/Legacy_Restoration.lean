/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TR_LALM_theory.Algorithm_2_1.Iteration
public import TR_LALM_theory.Legacy_Restoration.Iteration

public section

open scoped NNReal

namespace LALM.Restoration

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- Helper for legacy restoration result: the gradient of `energy c` is the constraint gradient applied to
the residual. -/
private lemma hasGradientAt_energy (x : EuclideanSpace ℝ (Fin n))
    (hc : DifferentiableAt ℝ c x) :
    HasGradientAt (energy c) (EqualityConstrained.constraintGradient c x (c x)) x := by
  -- Differentiate the squared norm, then identify its adjoint-normalized derivative.
  have hquadratic : HasFDerivAt (energy c)
      ((1 / 2 : ℝ) • 2 • innerSL ℝ
        (EqualityConstrained.constraintGradient c x (c x))) x := by
    rw [funext (energy_def c)]
    simpa only [EqualityConstrained.constraintGradient_def,
      ContinuousLinearMap.innerSL_apply_comp] using
      hc.hasFDerivAt.norm_sq.const_mul (1 / 2)
  have hderivative :
      (1 / 2 : ℝ) • 2 • innerSL ℝ
          (EqualityConstrained.constraintGradient c x (c x)) =
        innerSL ℝ (EqualityConstrained.constraintGradient c x (c x)) := by
    module
  rw [hasGradientAt_iff_hasFDerivAt]
  exact hquadratic.congr_fderiv hderivative

/-- Helper for legacy restoration result: a restoration step from the initial energy sublevel has its
whole segment in the regularity region. -/
private lemma segment_next_subset_region (hreg : EqualityConstrained.Regularity f c)
    (z₀ x : EuclideanSpace ℝ (Fin n)) (barL : ℝ)
    (h_barL : StepSizeCondition hreg z₀ barL)
    (h_region : RegionCondition hreg z₀ barL)
    (hx : x ∈ sublevel c z₀) :
    segment ℝ x (next c barL x) ⊆ hreg.region := by
  -- The step-size lower bound first makes division by `barL` order preserving.
  have hmodulusLt : (hreg.licqModulus : ℝ) ^ 2 < barL :=
    (le_max_left _ _).trans_lt h_barL
  have hbarLPos : 0 < barL :=
    (sq_pos_of_pos (NNReal.coe_pos.2 hreg.licqModulus_pos)).trans hmodulusLt
  have hradiusNonneg : 0 ≤ radius hreg z₀ barL := by
    rw [radius_def, div_nonneg_iff]
    exact Or.inl ⟨mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _), hbarLPos.le⟩
  have hdistSelf : dist x x ≤ radius hreg z₀ barL := by
    simpa only [dist_self] using hradiusNonneg
  have hxRegion : x ∈ hreg.region := by
    apply h_region
    exact Metric.mem_cthickening_of_dist_le x x (radius hreg z₀ barL)
      (sublevel c z₀) hx hdistSelf
  -- Sublevel membership bounds the current residual by the initial residual.
  have hresidual : ‖c x‖ ≤ ‖c z₀‖ := by
    rw [mem_sublevel, energy_def, energy_def] at hx
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith
  have hgradient :
      gradient (energy c) x = EqualityConstrained.constraintGradient c x (c x) :=
    (hasGradientAt_energy x (hreg.differentiableAt_constraint hxRegion)).gradient
  have hgradientNorm :
      ‖gradient (energy c) x‖ ≤ hreg.constraintGradientBound * ‖c z₀‖ := by
    rw [hgradient]
    calc
      ‖EqualityConstrained.constraintGradient c x (c x)‖ ≤
          ‖EqualityConstrained.constraintGradient c x‖ * ‖c x‖ :=
        (EqualityConstrained.constraintGradient c x).le_opNorm (c x)
      _ ≤ hreg.constraintGradientBound * ‖c x‖ :=
        mul_le_mul_of_nonneg_right (hreg.norm_constraintGradient_le x hxRegion)
          (norm_nonneg _)
      _ ≤ hreg.constraintGradientBound * ‖c z₀‖ :=
        mul_le_mul_of_nonneg_left hresidual (NNReal.coe_nonneg _)
  have hstepDistance : dist x (next c barL x) ≤ radius hreg z₀ barL := by
    rw [dist_comm, next_apply, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_pos hbarLPos, radius_def, div_eq_mul_inv]
    calc
      barL⁻¹ * ‖gradient (energy c) x‖ ≤
          barL⁻¹ * (hreg.constraintGradientBound * ‖c z₀‖) :=
        mul_le_mul_of_nonneg_left hgradientNorm (inv_nonneg.mpr hbarLPos.le)
      _ = hreg.constraintGradientBound * ‖c z₀‖ * barL⁻¹ := by ring
  -- Every segment point stays within that radius of the sublevel witness `x`.
  intro y hy
  apply h_region
  apply Metric.mem_cthickening_of_dist_le y x (radius hreg z₀ barL) (sublevel c z₀) hx
  exact (Metric.mem_closedBall.mp
    (segment_subset_closedBall_left x (next c barL x) hy)).trans
    hstepDistance

/-- Helper for legacy restoration result: residuals on a restoration segment satisfy the uniform bound used
in the energy-derivative estimate. -/
private lemma residualNorm_le_on_nextSegment
    (hreg : EqualityConstrained.Regularity f c)
    (z₀ x y : EuclideanSpace ℝ (Fin n)) (barL : ℝ)
    (h_barL : StepSizeCondition hreg z₀ barL)
    (h_region : RegionCondition hreg z₀ barL)
    (hx : x ∈ sublevel c z₀) (hy : y ∈ segment ℝ x (next c barL x)) :
    ‖c y‖ ≤ ‖c z₀‖ *
      (1 + hreg.constraintGradientBound ^ 2 / hreg.licqModulus ^ 2) := by
  -- The segment is regular, so the derivative bound makes `c` Lipschitz along it.
  have hmodulusLt : (hreg.licqModulus : ℝ) ^ 2 < barL :=
    (le_max_left _ _).trans_lt h_barL
  have hmodulusSqPos : 0 < (hreg.licqModulus : ℝ) ^ 2 :=
    sq_pos_of_pos hreg.licqModulus_pos
  have hbarLPos : 0 < barL := hmodulusSqPos.trans hmodulusLt
  have hsegment := segment_next_subset_region hreg z₀ x barL h_barL h_region hx
  have hxRegion : x ∈ hreg.region := hsegment (left_mem_segment ℝ x _)
  have hresidual : ‖c x‖ ≤ ‖c z₀‖ := by
    rw [mem_sublevel, energy_def, energy_def] at hx
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith
  have hgradient :
      gradient (energy c) x = EqualityConstrained.constraintGradient c x (c x) :=
    (hasGradientAt_energy x (hreg.differentiableAt_constraint hxRegion)).gradient
  have hgradientNorm :
      ‖gradient (energy c) x‖ ≤ hreg.constraintGradientBound * ‖c z₀‖ := by
    rw [hgradient]
    calc
      ‖EqualityConstrained.constraintGradient c x (c x)‖ ≤
          ‖EqualityConstrained.constraintGradient c x‖ * ‖c x‖ :=
        (EqualityConstrained.constraintGradient c x).le_opNorm (c x)
      _ ≤ hreg.constraintGradientBound * ‖c x‖ :=
        mul_le_mul_of_nonneg_right
          (hreg.norm_constraintGradient_le x (hsegment (left_mem_segment ℝ x _)))
          (norm_nonneg _)
      _ ≤ hreg.constraintGradientBound * ‖c z₀‖ :=
        mul_le_mul_of_nonneg_left hresidual (NNReal.coe_nonneg _)
  have hstepDistance : dist x (next c barL x) ≤ radius hreg z₀ barL := by
    rw [dist_comm, next_apply, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_pos hbarLPos, radius_def, div_eq_mul_inv]
    calc
      barL⁻¹ * ‖gradient (energy c) x‖ ≤
          barL⁻¹ * (hreg.constraintGradientBound * ‖c z₀‖) :=
        mul_le_mul_of_nonneg_left hgradientNorm (inv_nonneg.mpr hbarLPos.le)
      _ = hreg.constraintGradientBound * ‖c z₀‖ * barL⁻¹ := by ring
  have hyDistance : dist y x ≤ radius hreg z₀ barL :=
    (Metric.mem_closedBall.mp (segment_subset_closedBall_left x (next c barL x) hy)).trans
      hstepDistance
  have hcIncrement :
      ‖c y - c x‖ ≤ hreg.constraintGradientBound * ‖y - x‖ := by
    apply (convex_segment x (next c barL x)).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ)
    · intro u hu
      exact hreg.differentiableAt_constraint (hsegment hu)
    · intro u hu
      simpa only [EqualityConstrained.constraintGradient_def,
        LinearIsometryEquiv.norm_map] using
        hreg.norm_constraintGradient_le u (hsegment hu)
    · exact left_mem_segment ℝ x (next c barL x)
    · exact hy
  have hinv : 1 / barL ≤ 1 / (hreg.licqModulus : ℝ) ^ 2 :=
    one_div_le_one_div_of_le hmodulusSqPos hmodulusLt.le
  have hscaledInv := mul_le_mul_of_nonneg_left hinv
    (mul_nonneg
      (mul_nonneg (NNReal.coe_nonneg hreg.constraintGradientBound)
        (NNReal.coe_nonneg hreg.constraintGradientBound))
      (norm_nonneg (c z₀)))
  have hradiusContribution :
      hreg.constraintGradientBound * radius hreg z₀ barL ≤
        ‖c z₀‖ *
          (hreg.constraintGradientBound ^ 2 / hreg.licqModulus ^ 2) := by
    rw [radius_def]
    calc
      (hreg.constraintGradientBound : ℝ) *
          ((hreg.constraintGradientBound : ℝ) * ‖c z₀‖ / barL) =
          ((hreg.constraintGradientBound : ℝ) *
            hreg.constraintGradientBound * ‖c z₀‖) * (1 / barL) := by ring
      _ ≤ ((hreg.constraintGradientBound : ℝ) *
            hreg.constraintGradientBound * ‖c z₀‖) *
            (1 / (hreg.licqModulus : ℝ) ^ 2) := hscaledInv
      _ = ‖c z₀‖ *
          (hreg.constraintGradientBound ^ 2 / hreg.licqModulus ^ 2) := by ring
  -- Triangle inequality and the radius estimate now give the advertised residual bound.
  calc
    ‖c y‖ = ‖(c y - c x) + c x‖ := by rw [sub_add_cancel]
    _ ≤ ‖c y - c x‖ + ‖c x‖ := norm_add_le _ _
    _ ≤ hreg.constraintGradientBound * ‖y - x‖ + ‖c z₀‖ :=
      add_le_add hcIncrement hresidual
    _ = hreg.constraintGradientBound * dist y x + ‖c z₀‖ := by
      rw [dist_eq_norm]
    _ ≤ hreg.constraintGradientBound * radius hreg z₀ barL + ‖c z₀‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_left hyDistance (NNReal.coe_nonneg _)) le_rfl
    _ ≤ ‖c z₀‖ *
          (hreg.constraintGradientBound ^ 2 / hreg.licqModulus ^ 2) + ‖c z₀‖ :=
      add_le_add hradiusContribution le_rfl
    _ = ‖c z₀‖ *
        (1 + hreg.constraintGradientBound ^ 2 / hreg.licqModulus ^ 2) := by ring

/-- Helper for legacy restoration result: the derivative of `energy c` is `barL`-Lipschitz on one
restoration segment. -/
private lemma lipschitzOnWith_fderiv_energy_segment
    (hreg : EqualityConstrained.Regularity f c)
    (z₀ x : EuclideanSpace ℝ (Fin n)) (barL : ℝ)
    (h_barL : StepSizeCondition hreg z₀ barL)
    (h_region : RegionCondition hreg z₀ barL)
    (hx : x ∈ sublevel c z₀) :
    LipschitzOnWith (Real.toNNReal barL) (fderiv ℝ (energy c))
      (segment ℝ x (next c barL x)) := by
  -- Expand the energy derivative as the product of the constraint gradient and residual.
  have hmodulusLt : (hreg.licqModulus : ℝ) ^ 2 < barL :=
    (le_max_left _ _).trans_lt h_barL
  have hbarLPos : 0 < barL :=
    (sq_pos_of_pos (NNReal.coe_pos.2 hreg.licqModulus_pos)).trans hmodulusLt
  have hconstantLt :
      (hreg.constraintGradientBound : ℝ) ^ 2 +
          hreg.constraintGradientLipschitz * ‖c z₀‖ *
            (1 + hreg.constraintGradientBound ^ 2 / hreg.licqModulus ^ 2) < barL :=
    (le_max_right _ _).trans_lt h_barL
  have hsegment := segment_next_subset_region hreg z₀ x barL h_barL h_region hx
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  have hfy : fderiv ℝ (energy c) y = innerSL ℝ
      (EqualityConstrained.constraintGradient c y (c y)) :=
    (hasGradientAt_energy y
      (hreg.differentiableAt_constraint (hsegment hy))).hasFDerivAt.fderiv
  have hfz : fderiv ℝ (energy c) z = innerSL ℝ
      (EqualityConstrained.constraintGradient c z (c z)) :=
    (hasGradientAt_energy z
      (hreg.differentiableAt_constraint (hsegment hz))).hasFDerivAt.fderiv
  have hcDifference :
      ‖c y - c z‖ ≤ hreg.constraintGradientBound * ‖y - z‖ := by
    apply (convex_segment x (next c barL x)).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ)
    · intro u hu
      exact hreg.differentiableAt_constraint (hsegment hu)
    · intro u hu
      simpa only [EqualityConstrained.constraintGradient_def,
        LinearIsometryEquiv.norm_map] using
        hreg.norm_constraintGradient_le u (hsegment hu)
    · exact hz
    · exact hy
  have hoperatorDifference :
      ‖EqualityConstrained.constraintGradient c y -
          EqualityConstrained.constraintGradient c z‖ ≤
        hreg.constraintGradientLipschitz * dist y z := by
    simpa only [dist_eq_norm] using
      hreg.lipschitzOn_constraintGradient.dist_le_mul y (hsegment hy) z (hsegment hz)
  have hoperatorY : ‖EqualityConstrained.constraintGradient c y‖ ≤
      hreg.constraintGradientBound :=
    hreg.norm_constraintGradient_le y (hsegment hy)
  have hresidualZ :=
    residualNorm_le_on_nextSegment hreg z₀ x z barL h_barL h_region hx hz
  have hdecompose :
      EqualityConstrained.constraintGradient c y (c y) -
          EqualityConstrained.constraintGradient c z (c z) =
        EqualityConstrained.constraintGradient c y (c y - c z) +
          (EqualityConstrained.constraintGradient c y -
            EqualityConstrained.constraintGradient c z) (c z) := by
    rw [map_sub, sub_apply]
    module
  have hderivativeDifference :
      dist (fderiv ℝ (energy c) y) (fderiv ℝ (energy c) z) ≤
        ((hreg.constraintGradientBound : ℝ) ^ 2 +
          hreg.constraintGradientLipschitz * ‖c z₀‖ *
            (1 + hreg.constraintGradientBound ^ 2 / hreg.licqModulus ^ 2)) *
          dist y z := by
    rw [dist_eq_norm, hfy, hfz, ← map_sub, innerSL_apply_norm, hdecompose]
    calc
      ‖EqualityConstrained.constraintGradient c y (c y - c z) +
          (EqualityConstrained.constraintGradient c y -
            EqualityConstrained.constraintGradient c z) (c z)‖ ≤
          ‖EqualityConstrained.constraintGradient c y (c y - c z)‖ +
            ‖(EqualityConstrained.constraintGradient c y -
              EqualityConstrained.constraintGradient c z) (c z)‖ := norm_add_le _ _
      _ ≤ ‖EqualityConstrained.constraintGradient c y‖ * ‖c y - c z‖ +
          ‖EqualityConstrained.constraintGradient c y -
            EqualityConstrained.constraintGradient c z‖ * ‖c z‖ :=
        add_le_add
          ((EqualityConstrained.constraintGradient c y).le_opNorm (c y - c z))
          ((EqualityConstrained.constraintGradient c y -
            EqualityConstrained.constraintGradient c z).le_opNorm (c z))
      _ ≤ (hreg.constraintGradientBound : ℝ) *
            (hreg.constraintGradientBound * ‖y - z‖) +
          (hreg.constraintGradientLipschitz * dist y z) *
            (‖c z₀‖ *
              (1 + hreg.constraintGradientBound ^ 2 / hreg.licqModulus ^ 2)) := by
        apply add_le_add
        · exact mul_le_mul hoperatorY hcDifference (norm_nonneg _) (NNReal.coe_nonneg _)
        · exact mul_le_mul hoperatorDifference hresidualZ (norm_nonneg _)
            (mul_nonneg (NNReal.coe_nonneg _) (dist_nonneg))
      _ = ((hreg.constraintGradientBound : ℝ) ^ 2 +
          hreg.constraintGradientLipschitz * ‖c z₀‖ *
            (1 + hreg.constraintGradientBound ^ 2 / hreg.licqModulus ^ 2)) *
          dist y z := by
        rw [dist_eq_norm]
        ring
  simpa only [Real.coe_toNNReal barL hbarLPos.le] using
    hderivativeDifference.trans
      (mul_le_mul_of_nonneg_right hconstantLt.le (dist_nonneg))

/-- Helper for legacy restoration result: one restoration step contracts the residual energy. -/
private lemma energy_next_le (hreg : EqualityConstrained.Regularity f c)
    (z₀ x : EuclideanSpace ℝ (Fin n)) (barL : ℝ)
    (h_barL : StepSizeCondition hreg z₀ barL)
    (h_region : RegionCondition hreg z₀ barL)
    (hx : x ∈ sublevel c z₀) :
    energy c (next c barL x) ≤ contractionFactor hreg barL * energy c x := by
  -- Taylor's estimate supplies descent by one half of the squared gradient step.
  have hmodulusLt : (hreg.licqModulus : ℝ) ^ 2 < barL :=
    (le_max_left _ _).trans_lt h_barL
  have hbarLPos : 0 < barL :=
    (sq_pos_of_pos (NNReal.coe_pos.2 hreg.licqModulus_pos)).trans hmodulusLt
  have hsegment := segment_next_subset_region hreg z₀ x barL h_barL h_region hx
  have henergyDifferentiable :
      ∀ u ∈ segment ℝ x (next c barL x), DifferentiableAt ℝ (energy c) u := by
    intro u hu
    exact (hasGradientAt_energy u
      (hreg.differentiableAt_constraint (hsegment hu))).differentiableAt
  have hlipschitz :=
    lipschitzOnWith_fderiv_energy_segment hreg z₀ x barL h_barL h_region hx
  have hremainder := LALM.norm_sub_sub_fderiv_le (energy c) (Real.toNNReal barL)
    (segment ℝ x (next c barL x)) x (next c barL x) henergyDifferentiable
    hlipschitz Set.Subset.rfl
  have hgradient :
      gradient (energy c) x = EqualityConstrained.constraintGradient c x (c x) :=
    (hasGradientAt_energy x
      (hreg.differentiableAt_constraint (hsegment (left_mem_segment ℝ x _)))).gradient
  have hfderiv : fderiv ℝ (energy c) x =
      innerSL ℝ (gradient (energy c) x) := by
    rw [hgradient]
    exact (hasGradientAt_energy x
      (hreg.differentiableAt_constraint
        (hsegment (left_mem_segment ℝ x _)))).hasFDerivAt.fderiv
  have hdisplacement : next c barL x - x =
      (-barL⁻¹) • gradient (energy c) x := by
    rw [next_apply]
    module
  have hlinear : fderiv ℝ (energy c) x (next c barL x - x) =
      -barL⁻¹ * ‖gradient (energy c) x‖ ^ 2 := by
    rw [hfderiv, hdisplacement, map_smul, innerSL_apply_apply,
      real_inner_self_eq_norm_sq, smul_eq_mul]
  have hstepNorm : ‖next c barL x - x‖ =
      barL⁻¹ * ‖gradient (energy c) x‖ := by
    rw [hdisplacement, norm_smul, Real.norm_eq_abs, abs_neg, abs_inv,
      abs_of_pos hbarLPos]
  have hremainderReal :
      |energy c (next c barL x) - energy c x -
          fderiv ℝ (energy c) x (next c barL x - x)| ≤
        barL / 2 * ‖next c barL x - x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, Real.coe_toNNReal barL hbarLPos.le] using hremainder
  have hquadratic : barL / 2 *
      (barL⁻¹ * ‖gradient (energy c) x‖) ^ 2 =
        barL⁻¹ / 2 * ‖gradient (energy c) x‖ ^ 2 := by
    field_simp [hbarLPos.ne']
  have hdescent : energy c (next c barL x) ≤
      energy c x - barL⁻¹ / 2 * ‖gradient (energy c) x‖ ^ 2 := by
    have hupper := (le_abs_self
      (energy c (next c barL x) - energy c x -
        fderiv ℝ (energy c) x (next c barL x - x))).trans hremainderReal
    rw [hlinear, hstepNorm, hquadratic] at hupper
    linarith
  -- LICQ converts gradient descent into contraction of the residual energy itself.
  have hxRegion : x ∈ hreg.region := hsegment (left_mem_segment ℝ x _)
  have hlicq := hreg.licqLowerBound x hxRegion (c x)
  rw [← hgradient] at hlicq
  have hlicqSq : (hreg.licqModulus : ℝ) ^ 2 * ‖c x‖ ^ 2 ≤
      ‖gradient (energy c) x‖ ^ 2 := by
    have hsquare := (sq_le_sq₀
      (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))
      (norm_nonneg _)).mpr hlicq
    nlinarith
  have hfactorNonneg : 0 ≤ barL⁻¹ / 2 := by positivity
  calc
    energy c (next c barL x) ≤
        energy c x - barL⁻¹ / 2 * ‖gradient (energy c) x‖ ^ 2 := hdescent
    _ ≤ energy c x - barL⁻¹ / 2 *
        ((hreg.licqModulus : ℝ) ^ 2 * ‖c x‖ ^ 2) :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left hlicqSq hfactorNonneg) _
    _ = contractionFactor hreg barL * energy c x := by
      rw [contractionFactor_def, energy_def]
      field_simp [hbarLPos.ne']

/-- Part (1) of legacy restoration result: every restoration iterate remains in the initial energy sublevel. -/
theorem iterate_mem (hreg : EqualityConstrained.Regularity f c)
    (z₀ : EuclideanSpace ℝ (Fin n)) (barL : ℝ)
    (h_barL : StepSizeCondition hreg z₀ barL)
    (h_region : RegionCondition hreg z₀ barL) (t : ℕ) :
    iterate c barL z₀ t ∈ sublevel c z₀ := by
  -- The step-size hypothesis makes the contraction factor lie in `[0, 1]`.
  have hmodulusLt : (hreg.licqModulus : ℝ) ^ 2 < barL :=
    (le_max_left _ _).trans_lt h_barL
  have hmodulusSqNonneg : 0 ≤ (hreg.licqModulus : ℝ) ^ 2 := sq_nonneg _
  have hbarLPos : 0 < barL :=
    (sq_pos_of_pos (NNReal.coe_pos.2 hreg.licqModulus_pos)).trans hmodulusLt
  have hfactorLeOne : contractionFactor hreg barL ≤ 1 := by
    rw [contractionFactor_def]
    exact sub_le_self _ (div_nonneg hmodulusSqNonneg hbarLPos.le)
  have henergyNonneg (u : EuclideanSpace ℝ (Fin n)) : 0 ≤ energy c u := by
    rw [energy_def]
    positivity
  -- Induction propagates the initial sublevel through the one-step estimate.
  induction t with
  | zero =>
      exact (mem_sublevel c z₀ z₀).mpr le_rfl
  | succ t iht =>
      rw [iterate_succ, mem_sublevel]
      calc
        energy c (next c barL (iterate c barL z₀ t)) ≤
            contractionFactor hreg barL * energy c (iterate c barL z₀ t) :=
          energy_next_le hreg z₀ (iterate c barL z₀ t) barL h_barL h_region iht
        _ ≤ energy c (iterate c barL z₀ t) :=
          mul_le_of_le_one_left (henergyNonneg _) hfactorLeOne
        _ ≤ energy c z₀ := iht

/-- Part (2) of legacy restoration result: every restoration step segment lies in the regularity region. -/
theorem segment_subset (hreg : EqualityConstrained.Regularity f c)
    (z₀ : EuclideanSpace ℝ (Fin n)) (barL : ℝ)
    (h_barL : StepSizeCondition hreg z₀ barL)
    (h_region : RegionCondition hreg z₀ barL) (t : ℕ) :
    segment ℝ (iterate c barL z₀ t) (iterate c barL z₀ (t + 1)) ⊆ hreg.region := by
  -- Rewrite the next iterate and apply the arbitrary-sublevel segment bridge.
  rw [iterate_succ]
  exact segment_next_subset_region hreg z₀ (iterate c barL z₀ t) barL h_barL h_region
    (iterate_mem hreg z₀ barL h_barL h_region t)

/-- Part (3) of legacy restoration result: restoration contracts the constraint-residual energy geometrically. -/
theorem contract (hreg : EqualityConstrained.Regularity f c)
    (z₀ : EuclideanSpace ℝ (Fin n)) (barL : ℝ)
    (h_barL : StepSizeCondition hreg z₀ barL)
    (h_region : RegionCondition hreg z₀ barL) (t : ℕ) :
    energy c (iterate c barL z₀ (t + 1)) ≤
      contractionFactor hreg barL * energy c (iterate c barL z₀ t) := by
  -- The public contraction is the one-step estimate at the current iterate.
  rw [iterate_succ]
  exact energy_next_le hreg z₀ (iterate c barL z₀ t) barL h_barL h_region
    (iterate_mem hreg z₀ barL h_barL h_region t)

/-- Helper for legacy restoration result: restoration energy is bounded by the corresponding power of the
contraction factor. -/
private lemma energy_iterate_le_pow (hreg : EqualityConstrained.Regularity f c)
    (z₀ : EuclideanSpace ℝ (Fin n)) (barL : ℝ)
    (h_barL : StepSizeCondition hreg z₀ barL)
    (h_region : RegionCondition hreg z₀ barL) (t : ℕ) :
    energy c (iterate c barL z₀ t) ≤
      contractionFactor hreg barL ^ t * energy c z₀ := by
  -- Nonnegativity of the contraction factor permits multiplication of the inductive bound.
  have hmodulusLt : (hreg.licqModulus : ℝ) ^ 2 < barL :=
    (le_max_left _ _).trans_lt h_barL
  have hmodulusSqPos : 0 < (hreg.licqModulus : ℝ) ^ 2 :=
    sq_pos_of_pos (NNReal.coe_pos.2 hreg.licqModulus_pos)
  have hbarLPos : 0 < barL := hmodulusSqPos.trans hmodulusLt
  have hfactorNonneg : 0 ≤ contractionFactor hreg barL := by
    rw [contractionFactor_def]
    exact sub_nonneg.mpr ((div_le_one hbarLPos).mpr hmodulusLt.le)
  -- Induction composes the public one-step contraction inequalities.
  induction t with
  | zero =>
      rw [iterate_zero, pow_zero, one_mul]
  | succ t iht =>
      calc
        energy c (iterate c barL z₀ (t + 1)) ≤
            contractionFactor hreg barL * energy c (iterate c barL z₀ t) :=
          contract hreg z₀ barL h_barL h_region t
        _ ≤ contractionFactor hreg barL *
            (contractionFactor hreg barL ^ t * energy c z₀) :=
          mul_le_mul_of_nonneg_left iht hfactorNonneg
        _ = contractionFactor hreg barL ^ (t + 1) * energy c z₀ := by
          rw [pow_succ]
          ring

/-- Helper for legacy restoration result: the power at the ceiling of a logarithmic stopping time is at
most the reciprocal target level. -/
private lemma pow_ceil_logDiv_negLog_le_inv {q A : ℝ}
    (hqPos : 0 < q) (hqLtOne : q < 1) (hA : 1 ≤ A) :
    q ^ Nat.ceil (Real.log A / (-Real.log q)) ≤ A⁻¹ := by
  -- Multiplication by the negative logarithm reverses the ceiling comparison.
  have hlogQNeg : Real.log q < 0 := Real.log_neg hqPos hqLtOne
  have hnegativeLogPos : 0 < -Real.log q := neg_pos.mpr hlogQNeg
  have hceil : Real.log A / (-Real.log q) ≤
      (Nat.ceil (Real.log A / (-Real.log q)) : ℝ) :=
    Nat.le_ceil _
  have hlogComparison :
      (Nat.ceil (Real.log A / (-Real.log q)) : ℝ) * Real.log q ≤
        (Real.log A / (-Real.log q)) * Real.log q :=
    mul_le_mul_of_nonpos_right hceil hlogQNeg.le
  have hnormalize :
      (Real.log A / (-Real.log q)) * Real.log q = -Real.log A := by
    field_simp [hlogQNeg.ne]
  -- The logarithmic characterization of powers converts this comparison back to a power.
  apply (Real.pow_le_iff_le_log hqPos (inv_pos.mpr (zero_lt_one.trans_le hA))).mpr
  rw [Real.log_inv]
  exact hlogComparison.trans_eq hnormalize

/-- Part (4) of legacy restoration result: the explicit restoration count is below its logarithmic bound
plus one. -/
theorem stepCount_lt (hreg : EqualityConstrained.Regularity f c)
    (z₀ : EuclideanSpace ℝ (Fin n)) (barL : ℝ)
    (rho multiplierBound : NNRealˣ) (h_barL : StepSizeCondition hreg z₀ barL) :
    (stepCount hreg z₀ barL rho multiplierBound : ℝ) <
      Real.log (max 1 (2 * rho ^ 2 * energy c z₀ / multiplierBound ^ 2)) /
          (-Real.log (contractionFactor hreg barL)) + 1 := by
  -- The step-size condition puts the contraction factor strictly between zero and one.
  have hmodulusLt : (hreg.licqModulus : ℝ) ^ 2 < barL :=
    (le_max_left _ _).trans_lt h_barL
  have hmodulusSqPos : 0 < (hreg.licqModulus : ℝ) ^ 2 :=
    sq_pos_of_pos (NNReal.coe_pos.2 hreg.licqModulus_pos)
  have hbarLPos : 0 < barL := hmodulusSqPos.trans hmodulusLt
  have hfactorPos : 0 < contractionFactor hreg barL := by
    rw [contractionFactor_def]
    exact sub_pos.mpr ((div_lt_one hbarLPos).mpr hmodulusLt)
  have hfactorLtOne : contractionFactor hreg barL < 1 := by
    rw [contractionFactor_def]
    exact sub_lt_self _ (div_pos hmodulusSqPos hbarLPos)
  have hnegativeLogPos : 0 < -Real.log (contractionFactor hreg barL) :=
    neg_pos.mpr (Real.log_neg hfactorPos hfactorLtOne)
  have hlogNonneg :
      0 ≤ Real.log (max 1
        (2 * rho ^ 2 * energy c z₀ / multiplierBound ^ 2)) := by
    apply Real.log_nonneg
    exact le_max_left _ _
  have hquotientNonneg :
      0 ≤ Real.log (max 1
        (2 * rho ^ 2 * energy c z₀ / multiplierBound ^ 2)) /
          (-Real.log (contractionFactor hreg barL)) :=
    div_nonneg hlogNonneg hnegativeLogPos.le
  -- The defining natural ceiling is always strictly below its argument plus one.
  rw [stepCount_def]
  exact Nat.ceil_lt_add_one hquotientNonneg

/-- legacy restoration result (5): the stopped iterate and zero multiplier satisfy both initialization bounds. -/
theorem initializationBounds (hreg : EqualityConstrained.Regularity f c)
    (z₀ : EuclideanSpace ℝ (Fin n)) (barL : ℝ)
    (rho multiplierBound : NNRealˣ)
    (h_barL : StepSizeCondition hreg z₀ barL)
    (h_region : RegionCondition hreg z₀ barL) :
    ‖(0 : EuclideanSpace ℝ (Fin m))‖ ≤ multiplierBound ∧
      rho * ‖c (iterate c barL z₀ (stepCount hreg z₀ barL rho multiplierBound))‖ ≤
        multiplierBound := by
  -- Name the geometric factor and target ratio used by the stopping-time definition.
  let q : ℝ := contractionFactor hreg barL
  let A : ℝ := max 1 (2 * rho ^ 2 * energy c z₀ / multiplierBound ^ 2)
  have hmodulusLt : (hreg.licqModulus : ℝ) ^ 2 < barL :=
    (le_max_left _ _).trans_lt h_barL
  have hmodulusSqPos : 0 < (hreg.licqModulus : ℝ) ^ 2 :=
    sq_pos_of_pos (NNReal.coe_pos.2 hreg.licqModulus_pos)
  have hbarLPos : 0 < barL := hmodulusSqPos.trans hmodulusLt
  have hqPos : 0 < q := by
    simp only [q, contractionFactor_def]
    exact sub_pos.mpr ((div_lt_one hbarLPos).mpr hmodulusLt)
  have hqLtOne : q < 1 := by
    simp only [q, contractionFactor_def]
    exact sub_lt_self _ (div_pos hmodulusSqPos hbarLPos)
  have hA : 1 ≤ A := by
    simp only [A]
    exact le_max_left _ _
  have hAPos : 0 < A := zero_lt_one.trans_le hA
  have hrhoPos : (0 : ℝ) < rho :=
    NNReal.coe_pos.2 (pos_iff_ne_zero.2 rho.ne_zero)
  have hmultiplierPos : (0 : ℝ) < multiplierBound :=
    NNReal.coe_pos.2 (pos_iff_ne_zero.2 multiplierBound.ne_zero)
  have hpower : q ^ stepCount hreg z₀ barL rho multiplierBound ≤ A⁻¹ := by
    rw [stepCount_def]
    exact pow_ceil_logDiv_negLog_le_inv hqPos hqLtOne hA
  have hinitialEnergyNonneg : 0 ≤ energy c z₀ := by
    rw [energy_def]
    positivity
  -- Geometric contraction and the ceiling bound control the stopped energy by `A⁻¹`.
  have henergyGeometric := energy_iterate_le_pow hreg z₀ barL h_barL h_region
    (stepCount hreg z₀ barL rho multiplierBound)
  have henergyInv :
      energy c (iterate c barL z₀ (stepCount hreg z₀ barL rho multiplierBound)) ≤
        A⁻¹ * energy c z₀ := by
    calc
      energy c (iterate c barL z₀ (stepCount hreg z₀ barL rho multiplierBound)) ≤
          q ^ stepCount hreg z₀ barL rho multiplierBound * energy c z₀ := by
        simpa only [q] using henergyGeometric
      _ ≤ A⁻¹ * energy c z₀ :=
        mul_le_mul_of_nonneg_right hpower hinitialEnergyNonneg
  have hratio :
      2 * (rho : ℝ) ^ 2 * energy c z₀ / (multiplierBound : ℝ) ^ 2 ≤ A := by
    simp only [A]
    exact le_max_right _ _
  have hmultiplierSqPos : 0 < (multiplierBound : ℝ) ^ 2 :=
    sq_pos_of_pos hmultiplierPos
  have htwoRhoSqPos : 0 < 2 * (rho : ℝ) ^ 2 := by positivity
  have hscaledRatio :
      2 * (rho : ℝ) ^ 2 * energy c z₀ ≤ A * (multiplierBound : ℝ) ^ 2 :=
    (div_le_iff₀ hmultiplierSqPos).mp hratio
  have henergyFraction :
      energy c z₀ / A ≤ (multiplierBound : ℝ) ^ 2 / (2 * (rho : ℝ) ^ 2) := by
    apply (div_le_div_iff₀ hAPos htwoRhoSqPos).mpr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaledRatio
  have hstoppedEnergy :
      energy c (iterate c barL z₀ (stepCount hreg z₀ barL rho multiplierBound)) ≤
        (multiplierBound : ℝ) ^ 2 / (2 * (rho : ℝ) ^ 2) := by
    calc
      energy c (iterate c barL z₀ (stepCount hreg z₀ barL rho multiplierBound)) ≤
          A⁻¹ * energy c z₀ := henergyInv
      _ = energy c z₀ / A := by ring
      _ ≤ (multiplierBound : ℝ) ^ 2 / (2 * (rho : ℝ) ^ 2) := henergyFraction
  -- Finally, expand the energy and compare squares of the two nonnegative quantities.
  constructor
  · simpa only [norm_zero] using hmultiplierPos.le
  · apply (sq_le_sq₀
      (mul_nonneg hrhoPos.le (norm_nonneg _)) hmultiplierPos.le).mp
    have hscaledEnergy := (le_div_iff₀ htwoRhoSqPos).mp hstoppedEnergy
    rw [energy_def] at hscaledEnergy
    nlinarith

end LALM.Restoration

end
