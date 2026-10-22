/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Definition_6_1_extra_3

noncomputable section

open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- Helper for Chapter06 Lemma 6.1.4: the predicted reduction along the steepest-descent ray
reduces to the usual scalar quadratic in the ray parameter. -/
lemma TrustRegionSubproblem.predictedReduction_eq_negGradientStep
    (P : TrustRegionSubproblem n) (α : ℝ) :
    P.predictedReduction (-(α : ℝ) • P.gradient) =
      α * ‖P.gradient‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * α ^ (2 : ℕ) * P.gradientCurvature := by
  have hnorm_sq : dotProduct P.gradient P.gradient = ‖P.gradient‖ ^ (2 : ℕ) := by
    calc
      dotProduct P.gradient P.gradient = ∑ i, P.gradient i * P.gradient i := by
        simp [dotProduct]
      _ = ∑ i, P.gradient i ^ (2 : ℕ) := by
        simp [pow_two]
      _ = ‖P.gradient‖ ^ (2 : ℕ) := by
        exact (EuclideanSpace.real_norm_sq_eq P.gradient).symm
  -- Expand the quadratic model at the scaled negative-gradient step and collect the scalar terms.
  calc
    P.predictedReduction (-(α : ℝ) • P.gradient)
        =
          -(dotProduct P.gradient (-(α : ℝ) • P.gradient)) -
            (1 / 2 : ℝ) *
              dotProduct (-(α : ℝ) • P.gradient)
                (P.hessianApprox.mulVec (-(α : ℝ) • P.gradient)) := by
          simp [TrustRegionSubproblem.predictedReduction_eq,
            TrustRegionSubproblem.quadraticModel_eq]
          ring
    _ =
        α * dotProduct P.gradient P.gradient -
          (1 / 2 : ℝ) * α ^ (2 : ℕ) * P.gradientCurvature := by
        rw [dotProduct_smul, Matrix.mulVec_smul, dotProduct_smul]
        simp [TrustRegionSubproblem.gradientCurvature, pow_two, mul_assoc, mul_left_comm,
          mul_comm, smul_dotProduct]
    _ = α * ‖P.gradient‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * α ^ (2 : ℕ) * P.gradientCurvature := by
        rw [hnorm_sq]

/-- Helper for Chapter06 Lemma 6.1.4: the curvature term `g_kᵀ B_k g_k` is controlled by the
operator norm `‖B_k‖₂` times `‖g_k‖²`. -/
lemma TrustRegionSubproblem.gradientCurvature_le_hessianOperatorNorm_mul_normSq
    (P : TrustRegionSubproblem n) :
    P.gradientCurvature ≤ P.hessianOperatorNorm * ‖P.gradient‖ ^ (2 : ℕ) := by
  let T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) P.hessianApprox
  have hinner :
      P.gradientCurvature =
        ⟪P.gradient, T P.gradient⟫ := by
    simpa [TrustRegionSubproblem.gradientCurvature] using
      (Matrix.inner_toEuclideanCLM P.hessianApprox P.gradient P.gradient).symm
  -- First apply Cauchy-Schwarz to the quadratic form, then the operator-norm bound.
  calc
    P.gradientCurvature ≤ |P.gradientCurvature| := le_abs_self _
    _ = |⟪P.gradient, T P.gradient⟫| := by
          rw [hinner]
    _ ≤ ‖P.gradient‖ * ‖T P.gradient‖ := by
          simpa [T] using abs_real_inner_le_norm P.gradient (T P.gradient)
    _ ≤ ‖P.gradient‖ * (‖T‖ * ‖P.gradient‖) := by
          exact mul_le_mul_of_nonneg_left (T.le_opNorm P.gradient)
            (norm_nonneg _)
    _ = ‖T‖ * ‖P.gradient‖ ^ (2 : ℕ) := by
          ring
    _ = P.hessianOperatorNorm * ‖P.gradient‖ ^ (2 : ℕ) := by
          simp [T, TrustRegionSubproblem.hessianOperatorNorm_eq, Matrix.l2_opNorm_toEuclideanCLM]

/-- Helper for Chapter06 Lemma 6.1.4: positive curvature forces the Hessian operator norm to be
strictly positive when `g_k ≠ 0`. -/
lemma TrustRegionSubproblem.hessianOperatorNorm_pos_of_pos_gradientCurvature
    (P : TrustRegionSubproblem n) (h_grad : P.gradient ≠ 0)
    (h_curv : 0 < P.gradientCurvature) :
    0 < P.hessianOperatorNorm := by
  have hnorm_sq_pos : 0 < ‖P.gradient‖ ^ (2 : ℕ) := by
    have hnorm_pos : 0 < ‖P.gradient‖ := norm_pos_iff.mpr h_grad
    nlinarith
  have hnorm_nonneg : 0 ≤ P.hessianOperatorNorm := by
    simp [TrustRegionSubproblem.hessianOperatorNorm_eq]
  -- If the operator norm vanished, the curvature estimate would force nonpositive curvature.
  by_contra h_not_pos
  have h_zero : P.hessianOperatorNorm = 0 := le_antisymm (not_lt.mp h_not_pos) hnorm_nonneg
  have h_le_zero : P.gradientCurvature ≤ 0 := by
    simpa [h_zero] using P.gradientCurvature_le_hessianOperatorNorm_mul_normSq
  linarith

/-- Helper for Chapter06 Lemma 6.1.4: in the nonpositive-curvature branch, the boundary
steepest-descent step already yields the required decrease. -/
lemma TrustRegionSubproblem.cauchyPointPredictedReductionLowerBound_of_nonposCurvature
    (P : TrustRegionSubproblem n) (h_grad : P.gradient ≠ 0)
    (h_curv : P.gradientCurvature ≤ 0) :
    P.predictedReduction P.cauchyPoint ≥ P.radius * ‖P.gradient‖ := by
  have hnorm_pos : 0 < ‖P.gradient‖ := norm_pos_iff.mpr h_grad
  have hquadratic_nonneg :
      0 ≤
        -((1 / 2 : ℝ) * (P.radius / ‖P.gradient‖) ^ (2 : ℕ) * P.gradientCurvature) := by
    have hsq_nonneg : 0 ≤ (P.radius / ‖P.gradient‖) ^ (2 : ℕ) := by
      simpa [pow_two] using sq_nonneg (P.radius / ‖P.gradient‖)
    nlinarith
  have hlinear :
      (P.radius / ‖P.gradient‖) * ‖P.gradient‖ ^ (2 : ℕ) = P.radius * ‖P.gradient‖ := by
    field_simp [hnorm_pos.ne']
  -- Rewrite the Cauchy point to the boundary step and discard the nonnegative quadratic correction.
  rw [P.cauchyPoint_eq_of_ne_zero h_grad,
    P.cauchyPointScale_eq_one_of_nonpos_curvature h_curv, one_mul,
    TrustRegionSubproblem.predictedReduction_eq_negGradientStep]
  rw [hlinear]
  nlinarith

/-- Helper for Chapter06 Lemma 6.1.4: when the positive-curvature ratio is at most `1`, the
Cauchy point takes the interior minimizer on the gradient ray and yields the operator-norm
version of the lower bound. -/
lemma TrustRegionSubproblem.cauchyPointPredictedReductionLowerBound_of_posCurvature_of_ratio_le_one
    (P : TrustRegionSubproblem n) (h_grad : P.gradient ≠ 0)
    (h_curv : 0 < P.gradientCurvature)
    (hratio : (‖P.gradient‖ ^ (3 : ℕ)) / (P.radius * P.gradientCurvature) ≤ 1) :
    P.predictedReduction P.cauchyPoint ≥
      (1 / 2 : ℝ) * ‖P.gradient‖ *
        min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) := by
  have hnorm_pos : 0 < ‖P.gradient‖ := norm_pos_iff.mpr h_grad
  have hnormSq_curv :
      P.cauchyPointScale * P.radius / ‖P.gradient‖ =
        ‖P.gradient‖ ^ (2 : ℕ) / P.gradientCurvature := by
    rw [P.cauchyPointScale_eq_min_of_pos_curvature h_curv, min_eq_left hratio]
    field_simp [hnorm_pos.ne', (ne_of_gt P.radius_pos), h_curv.ne']
  have hnorm_op_pos : 0 < P.hessianOperatorNorm :=
    P.hessianOperatorNorm_pos_of_pos_gradientCurvature h_grad h_curv
  have hratio_bound :
      (1 / 2 : ℝ) * ‖P.gradient‖ * (‖P.gradient‖ / P.hessianOperatorNorm) ≤
        (1 / 2 : ℝ) * ‖P.gradient‖ ^ (4 : ℕ) / P.gradientCurvature := by
    field_simp [hnorm_op_pos.ne', h_curv.ne']
    nlinarith [P.gradientCurvature_le_hessianOperatorNorm_mul_normSq]
  have hmin_bound :
      (1 / 2 : ℝ) * ‖P.gradient‖ *
          min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) ≤
        (1 / 2 : ℝ) * ‖P.gradient‖ * (‖P.gradient‖ / P.hessianOperatorNorm) := by
    have hmin :
        min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) ≤
          ‖P.gradient‖ / P.hessianOperatorNorm := min_le_right _ _
    nlinarith [hmin, hnorm_pos, hnorm_op_pos]
  -- In this branch the optimal ray parameter is `‖g_k‖² / (g_kᵀ B_k g_k)`.
  rw [P.cauchyPoint_eq_of_ne_zero h_grad, hnormSq_curv,
    TrustRegionSubproblem.predictedReduction_eq_negGradientStep]
  have hpred :
      ‖P.gradient‖ ^ (2 : ℕ) / P.gradientCurvature * ‖P.gradient‖ ^ (2 : ℕ) -
          (1 / 2 : ℝ) *
            (‖P.gradient‖ ^ (2 : ℕ) / P.gradientCurvature) ^ (2 : ℕ) * P.gradientCurvature =
        (1 / 2 : ℝ) * ‖P.gradient‖ ^ (4 : ℕ) / P.gradientCurvature := by
    field_simp [h_curv.ne']
    ring
  rw [hpred]
  exact le_trans hmin_bound hratio_bound

/-- Helper for Chapter06 Lemma 6.1.4: when the positive-curvature ratio exceeds `1`, the Cauchy
point stays on the trust-region boundary and still gives the required decrease. -/
lemma TrustRegionSubproblem.cauchyPointPredictedReductionLowerBound_of_posCurvature_of_one_lt_ratio
    (P : TrustRegionSubproblem n) (h_grad : P.gradient ≠ 0)
    (h_curv : 0 < P.gradientCurvature)
    (hratio : 1 < (‖P.gradient‖ ^ (3 : ℕ)) / (P.radius * P.gradientCurvature)) :
    P.predictedReduction P.cauchyPoint ≥
      (1 / 2 : ℝ) * ‖P.gradient‖ *
        min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) := by
  have hnorm_pos : 0 < ‖P.gradient‖ := norm_pos_iff.mpr h_grad
  have hnorm_op_pos : 0 < P.hessianOperatorNorm :=
    P.hessianOperatorNorm_pos_of_pos_gradientCurvature h_grad h_curv
  have hlinear :
      (P.radius / ‖P.gradient‖) * ‖P.gradient‖ ^ (2 : ℕ) = P.radius * ‖P.gradient‖ := by
    field_simp [hnorm_pos.ne']
  have hratio_bound :
      P.radius * P.gradientCurvature < ‖P.gradient‖ ^ (3 : ℕ) := by
    have hdenom_pos : 0 < P.radius * P.gradientCurvature := by
      nlinarith [P.radius_pos, h_curv]
    rcases (one_lt_div_iff).mp hratio with hpos | hneg
    · exact hpos.2
    · linarith
  have hratio_bound_sq :
      P.radius ^ (2 : ℕ) * P.gradientCurvature < P.radius * ‖P.gradient‖ ^ (3 : ℕ) := by
    nlinarith [hratio_bound, P.radius_pos]
  have hquadratic_bound :
      (1 / 2 : ℝ) * (P.radius / ‖P.gradient‖) ^ (2 : ℕ) * P.gradientCurvature ≤
        (1 / 2 : ℝ) * P.radius * ‖P.gradient‖ := by
    field_simp [hnorm_pos.ne', (ne_of_gt P.radius_pos)]
    exact le_of_lt hratio_bound_sq
  have hmin_bound :
      (1 / 2 : ℝ) * ‖P.gradient‖ *
          min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) ≤
        (1 / 2 : ℝ) * P.radius * ‖P.gradient‖ := by
    have hmin : min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) ≤ P.radius := min_le_left _ _
    nlinarith [hmin, hnorm_pos, hnorm_op_pos]
  -- Here the Cauchy parameter truncates to `1`, so the boundary-step estimate suffices.
  rw [P.cauchyPoint_eq_of_ne_zero h_grad,
    P.cauchyPointScale_eq_min_of_pos_curvature h_curv, min_eq_right (le_of_lt hratio), one_mul,
    TrustRegionSubproblem.predictedReduction_eq_negGradientStep]
  rw [hlinear]
  have hboundary :
      (1 / 2 : ℝ) * P.radius * ‖P.gradient‖ ≤
        P.radius * ‖P.gradient‖ -
          (1 / 2 : ℝ) * (P.radius / ‖P.gradient‖) ^ (2 : ℕ) * P.gradientCurvature := by
    nlinarith
  exact le_trans hmin_bound hboundary

/-- Chapter06 Lemma 6.1.4: the Cauchy point `s_k^c` satisfies the standard predicted-reduction
lower bound. To avoid Lean's `/ 0 = 0` convention from silently weakening the source statement,
the zero-operator-norm case is stated explicitly, while the positive-norm branch uses the
textbook quotient `‖g_k‖ / ‖B_k‖₂`. Here `q^(k)` is the quadratic model `P`,
`Pred_k (s) = P.predictedReduction s`, `s_k^c = P.cauchyPoint`, and
`‖B_k‖₂ = P.hessianOperatorNorm`. -/
theorem TrustRegionSubproblem.cauchyPointPredictedReductionLowerBound
    (P : TrustRegionSubproblem n) :
    P.predictedReduction P.cauchyPoint ≥
      if _ : P.hessianOperatorNorm = 0 then
        (1 / 2 : ℝ) * ‖P.gradient‖ * P.radius
      else
        (1 / 2 : ℝ) * ‖P.gradient‖ *
          min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) := by
  by_cases h_grad : P.gradient = 0
  · have hcauchy : P.cauchyPoint = 0 := by
      -- When the gradient vanishes, the boundary step and hence the Cauchy point are both zero.
      rw [P.cauchyPoint_eq, P.gradientBoundaryStep_eq_zero_of_eq_zero h_grad, smul_zero]
    -- Route correction: in Lean it is best to remove the zero-gradient denominators before the
    -- curvature split from the source proof.
    rw [hcauchy]
    by_cases h_norm : P.hessianOperatorNorm = 0 <;>
      simp [TrustRegionSubproblem.predictedReduction_eq, TrustRegionSubproblem.quadraticModel_eq,
        h_grad, h_norm]
  · by_cases h_curv : P.gradientCurvature ≤ 0
    · have hboundary :
        P.radius * ‖P.gradient‖ ≤ P.predictedReduction P.cauchyPoint :=
          P.cauchyPointPredictedReductionLowerBound_of_nonposCurvature h_grad h_curv
      by_cases h_norm : P.hessianOperatorNorm = 0
      · -- The explicit zero-operator branch is weaker than the full boundary-step estimate.
        have htarget :
            (1 / 2 : ℝ) * ‖P.gradient‖ * P.radius ≤ P.radius * ‖P.gradient‖ := by
          have hnorm_pos : 0 < ‖P.gradient‖ := norm_pos_iff.mpr h_grad
          nlinarith [P.radius_pos, hnorm_pos]
        simpa [h_norm, mul_comm, mul_left_comm, mul_assoc] using le_trans htarget hboundary
      · -- In the nonzero-operator branch, `min ≤ radius` reduces the target to the same estimate.
        have htarget :
            (1 / 2 : ℝ) * ‖P.gradient‖ *
                min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) ≤
              P.radius * ‖P.gradient‖ := by
          have hnorm_pos : 0 < ‖P.gradient‖ := norm_pos_iff.mpr h_grad
          have hmin : min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) ≤ P.radius :=
            min_le_left _ _
          nlinarith [hmin, P.radius_pos, hnorm_pos]
        simpa [h_norm, mul_comm, mul_left_comm, mul_assoc] using le_trans htarget hboundary
    · have h_curv_pos : 0 < P.gradientCurvature := lt_of_not_ge h_curv
      have h_norm_pos :
          0 < P.hessianOperatorNorm :=
        P.hessianOperatorNorm_pos_of_pos_gradientCurvature h_grad h_curv_pos
      have h_norm_ne : P.hessianOperatorNorm ≠ 0 := ne_of_gt h_norm_pos
      by_cases hratio :
          (‖P.gradient‖ ^ (3 : ℕ)) / (P.radius * P.gradientCurvature) ≤ 1
      · -- This is the interior-minimizer branch from the textbook proof.
        simpa [h_norm_ne] using
          P.cauchyPointPredictedReductionLowerBound_of_posCurvature_of_ratio_le_one
            h_grad h_curv_pos hratio
      · have hratio' :
            1 < (‖P.gradient‖ ^ (3 : ℕ)) / (P.radius * P.gradientCurvature) :=
          lt_of_not_ge hratio
        -- This is the truncated-to-boundary branch from the textbook proof.
        simpa [h_norm_ne] using
          P.cauchyPointPredictedReductionLowerBound_of_posCurvature_of_one_lt_ratio
            h_grad h_curv_pos hratio'

/-- Multiplying the Cauchy-point lower bound by a nonnegative factor preserves the source lower
bound shape used in branch inequalities such as `(6.1.39)`. -/
theorem TrustRegionSubproblem.cauchyPointPredictedReductionLowerBoundScaled
    (P : TrustRegionSubproblem n) (β₂ : ℝ) (hβ₂ : 0 ≤ β₂) :
    β₂ * P.predictedReduction P.cauchyPoint ≥
      if _ : P.hessianOperatorNorm = 0 then
        (1 / 2 : ℝ) * β₂ * ‖P.gradient‖ * P.radius
      else
        (1 / 2 : ℝ) * β₂ * ‖P.gradient‖ *
          min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) := by
  have hscale :
      β₂ *
          (if hB : P.hessianOperatorNorm = 0 then
            (1 / 2 : ℝ) * ‖P.gradient‖ * P.radius
          else
            (1 / 2 : ℝ) * ‖P.gradient‖ *
              min P.radius (‖P.gradient‖ / P.hessianOperatorNorm)) ≤
        β₂ * P.predictedReduction P.cauchyPoint :=
    mul_le_mul_of_nonneg_left P.cauchyPointPredictedReductionLowerBound hβ₂
  have hrewrite :
      (if hB : P.hessianOperatorNorm = 0 then
          (1 / 2 : ℝ) * β₂ * ‖P.gradient‖ * P.radius
        else
          (1 / 2 : ℝ) * β₂ * ‖P.gradient‖ *
            min P.radius (‖P.gradient‖ / P.hessianOperatorNorm)) =
        β₂ *
          (if hB : P.hessianOperatorNorm = 0 then
            (1 / 2 : ℝ) * ‖P.gradient‖ * P.radius
          else
            (1 / 2 : ℝ) * ‖P.gradient‖ *
              min P.radius (‖P.gradient‖ / P.hessianOperatorNorm)) := by
    by_cases hB : P.hessianOperatorNorm = 0 <;>
      simp [hB, mul_assoc, mul_left_comm, mul_comm]
  rw [hrewrite]
  exact hscale
