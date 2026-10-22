/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Definition_6_1_extra_3

noncomputable section

open scoped Matrix.Norms.L2Operator

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling for this refine pass:
-- * `Chapter06.Definition_6_1_extra_1.TrustRegionSubproblem` is the chapter-local owner for the
--   trust-region quadratic model, feasible set, and predicted reduction.
-- * `IsMinOn` / `isMinOn_iff` from `Mathlib.Order.Filter.Extr` is the canonical minimizer owner
--   for minimizing the quadratic model on the feasible set.
-- * the source proof compares the exact minimizer with an explicit feasible point on the
--   steepest-descent ray rather than with the later Cauchy-point construction.
-- Source/core/bridge triage:
-- * source-facing: the trust-region lower bound for a solution `sk` of the subproblem.
-- * core/canonical: `IsMinOn P P.feasibleSet sk`.
-- * bridge/view: `P.IsSolution sk`, the chapter-local owner that packages feasibility together
--   with the canonical minimizer predicate.

/-- Helper for Chapter06 Lemma 6.1.3: an exact trust-region solution has at least as much
predicted reduction as any feasible comparison step. -/
lemma predictedReduction_le_of_isSolution
    (P : TrustRegionSubproblem n) {sk s : Point}
    (hsol : P.IsSolution sk) (hs : s ∈ P.feasibleSet) :
    P.predictedReduction s ≤ P.predictedReduction sk := by
  -- Unpack the minimizer clause and compare model values on the feasible set.
  rcases hsol with ⟨_, hmin⟩
  have hmodel : P sk ≤ P s :=
    (isMinOn_iff.mp hmin) s hs
  simpa [TrustRegionSubproblem.predictedReduction_eq] using
    sub_le_sub_left hmodel (P 0)

/-- Helper for Chapter06 Lemma 6.1.3: the steepest-descent trial step with radius parameter `t`
stays feasible whenever `0 ≤ t ≤ Δ_k`. -/
lemma gradientTrialStep_mem_feasibleSet
    (P : TrustRegionSubproblem n) (hgrad : P.gradient ≠ 0) {t : ℝ}
    (ht0 : 0 ≤ t) (htΔ : t ≤ P.radius) :
    (-((t / ‖P.gradient‖) : ℝ) • P.gradient : Point) ∈ P.feasibleSet := by
  -- Reduce feasibility to the Euclidean norm bound and compute the trial-step norm exactly.
  rw [TrustRegionSubproblem.mem_feasibleSet_iff]
  have hgrad_norm : ‖P.gradient‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hgrad
  have hdiv_nonneg : 0 ≤ t / ‖P.gradient‖ := by
    exact div_nonneg ht0 (norm_nonneg _)
  have hnorm' : ‖((t / ‖P.gradient‖) : ℝ) • P.gradient‖ = t := by
    rw [norm_smul, Real.norm_of_nonneg hdiv_nonneg, div_eq_mul_inv, mul_assoc,
      inv_mul_cancel₀ hgrad_norm, mul_one]
  have hnorm : ‖(-((t / ‖P.gradient‖) : ℝ) • P.gradient : Point)‖ = t := by
    simpa [neg_smul] using hnorm'
  rw [hnorm]
  exact htΔ

/-- Helper for Chapter06 Lemma 6.1.3: expanding the predicted reduction on the explicit
steepest-descent ray isolates the linear and curvature terms. -/
lemma predictedReduction_gradientTrialStep_eq
    (P : TrustRegionSubproblem n) (t : ℝ) :
    P.predictedReduction (-((t / ‖P.gradient‖) : ℝ) • P.gradient) =
      (t / ‖P.gradient‖) * dotProduct P.gradient P.gradient -
        (1 / 2 : ℝ) * (t / ‖P.gradient‖) ^ 2 *
          dotProduct P.gradient (P.hessianApprox.mulVec P.gradient) := by
  -- Expand the quadratic model and collect the scalar factors on the gradient ray.
  simp [TrustRegionSubproblem.predictedReduction_eq, TrustRegionSubproblem.quadraticModel_eq,
    dotProduct_smul, smul_dotProduct, Matrix.mulVec_neg]
  rw [Matrix.mulVec_smul, dotProduct_smul]
  ring_nf

/-- Helper for Chapter06 Lemma 6.1.3: the curvature pairing `g_kᵀ B_k g_k` is controlled by the
operator norm `‖B_k‖₂ ‖g_k‖₂²`. -/
lemma gradientCurvature_le_operatorNorm_mul_norm_sq
    (P : TrustRegionSubproblem n) :
    dotProduct P.gradient (P.hessianApprox.mulVec P.gradient) ≤
      ‖P.hessianApprox‖ * ‖P.gradient‖ ^ 2 := by
  -- Rewrite the pairing as a real inner product and apply the operator-norm estimate.
  have hinner :
      dotProduct P.gradient (P.hessianApprox.mulVec P.gradient) =
        inner ℝ ((Matrix.toEuclideanLin P.hessianApprox) P.gradient) P.gradient := by
    have h :=
      EuclideanSpace.inner_eq_star_dotProduct
        ((Matrix.toEuclideanLin P.hessianApprox) P.gradient) P.gradient
    rw [Matrix.ofLp_toEuclideanLin_apply] at h
    simpa using h.symm
  have hmulVec :
      ‖(Matrix.toEuclideanLin P.hessianApprox) P.gradient‖ ≤
        ‖P.hessianApprox‖ * ‖P.gradient‖ := by
    simpa [Matrix.toEuclideanLin_apply] using
      Matrix.l2_opNorm_mulVec P.hessianApprox P.gradient
  calc
    dotProduct P.gradient (P.hessianApprox.mulVec P.gradient) =
        inner ℝ ((Matrix.toEuclideanLin P.hessianApprox) P.gradient) P.gradient := hinner
    _ ≤ ‖(Matrix.toEuclideanLin P.hessianApprox) P.gradient‖ * ‖P.gradient‖ :=
      real_inner_le_norm _ _
    _ ≤ (‖P.hessianApprox‖ * ‖P.gradient‖) * ‖P.gradient‖ := by
      exact mul_le_mul_of_nonneg_right hmulVec (norm_nonneg _)
    _ = ‖P.hessianApprox‖ * ‖P.gradient‖ ^ 2 := by
      ring

/-- Helper for Chapter06 Lemma 6.1.3: the explicit gradient-ray trial step achieves at least the
linear-minus-quadratic decrease bound from the textbook comparison estimate `(6.1.26)`. -/
lemma predictedReduction_gradientTrialStep_ge_linearMinusQuadratic
    (P : TrustRegionSubproblem n) (hgrad : P.gradient ≠ 0) (t : ℝ) :
    t * ‖P.gradient‖ - (1 / 2 : ℝ) * t ^ 2 * ‖P.hessianApprox‖ ≤
      P.predictedReduction (-((t / ‖P.gradient‖) : ℝ) • P.gradient) := by
  -- Convert the exact ray formula into the textbook lower bound using `‖B_k‖₂`.
  have hgrad_norm : ‖P.gradient‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hgrad
  have hdot : dotProduct P.gradient P.gradient = ‖P.gradient‖ ^ 2 := by
    have h := EuclideanSpace.inner_eq_star_dotProduct P.gradient P.gradient
    simpa [real_inner_self_eq_norm_sq] using h.symm
  have hlinear :
      (t / ‖P.gradient‖) * dotProduct P.gradient P.gradient = t * ‖P.gradient‖ := by
    rw [hdot]
    field_simp [hgrad_norm]
  have hquadratic :
      (1 / 2 : ℝ) * (t / ‖P.gradient‖) ^ 2 *
          dotProduct P.gradient (P.hessianApprox.mulVec P.gradient) ≤
        (1 / 2 : ℝ) * t ^ 2 * ‖P.hessianApprox‖ := by
    have hcoeff_nonneg : 0 ≤ (1 / 2 : ℝ) * (t / ‖P.gradient‖) ^ 2 := by
      positivity
    calc
      (1 / 2 : ℝ) * (t / ‖P.gradient‖) ^ 2 *
          dotProduct P.gradient (P.hessianApprox.mulVec P.gradient)
        ≤ (1 / 2 : ℝ) * (t / ‖P.gradient‖) ^ 2 *
            (‖P.hessianApprox‖ * ‖P.gradient‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_left
            (gradientCurvature_le_operatorNorm_mul_norm_sq P) hcoeff_nonneg
      _ = (1 / 2 : ℝ) * t ^ 2 * ‖P.hessianApprox‖ := by
        field_simp [hgrad_norm]
  calc
    t * ‖P.gradient‖ - (1 / 2 : ℝ) * t ^ 2 * ‖P.hessianApprox‖
      ≤ (t / ‖P.gradient‖) * dotProduct P.gradient P.gradient -
          (1 / 2 : ℝ) * (t / ‖P.gradient‖) ^ 2 *
            dotProduct P.gradient (P.hessianApprox.mulVec P.gradient) := by
        nlinarith [hlinear, hquadratic]
    _ = P.predictedReduction (-((t / ‖P.gradient‖) : ℝ) • P.gradient) := by
      rw [predictedReduction_gradientTrialStep_eq]

/-- Helper for Chapter06 Lemma 6.1.3: at the canonical scale
`min {Δ_k, ‖g_k‖₂ / ‖B_k‖₂}`, the scalar linear-minus-quadratic bound is at least
`(1 / 2) ‖g_k‖₂ t`. -/
lemma halfGradientMinRadiusQuotient_le_trialLowerBound
    (P : TrustRegionSubproblem n) (hB : ‖P.hessianApprox‖ ≠ 0) :
    let t := min P.radius (‖P.gradient‖ / ‖P.hessianApprox‖)
    (1 / 2 : ℝ) * ‖P.gradient‖ * t ≤
      t * ‖P.gradient‖ - (1 / 2 : ℝ) * t ^ 2 * ‖P.hessianApprox‖ := by
  -- Convert the `min` bound into `t * ‖B_k‖₂ ≤ ‖g_k‖₂` and finish by scalar arithmetic.
  dsimp
  have hBpos : 0 < ‖P.hessianApprox‖ := by
    exact lt_of_le_of_ne (norm_nonneg _) (by simpa [eq_comm] using hB)
  have ht_nonneg : 0 ≤ min P.radius (‖P.gradient‖ / ‖P.hessianApprox‖) := by
    refine le_min P.radius_pos.le ?_
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  have ht_le : min P.radius (‖P.gradient‖ / ‖P.hessianApprox‖) ≤
      ‖P.gradient‖ / ‖P.hessianApprox‖ :=
    min_le_right _ _
  have hscaled :
      min P.radius (‖P.gradient‖ / ‖P.hessianApprox‖) * ‖P.hessianApprox‖ ≤
        ‖P.gradient‖ := by
    exact (le_div_iff₀ hBpos).mp ht_le
  nlinarith

/-- Chapter06 Lemma 6.1.3: if `s_k` solves the trust-region subproblem `(6.1.1)`, expressed on
the chapter-local owner surface `P.IsSolution s_k`, then the
predicted reduction `q^(k) 0 - q^(k) s_k` is bounded below by the standard trust-region Cauchy
decrease estimate. To avoid Lean's `/ 0 = 0` convention from silently weakening the source
statement, the case `‖B_k‖₂ = 0` is stated explicitly, while the nonzero branch keeps the
textbook quotient `‖g_k‖ / ‖B_k‖₂`. Here `q^(k)` is the quadratic model `P`, and `‖B_k‖₂` is
`‖P.hessianApprox‖`, as identified by `Matrix.l2_opNorm_def`. -/
theorem TrustRegionSubproblem.predictedReductionLowerBound
    (P : TrustRegionSubproblem n) (sk : Point)
    (hsol : P.IsSolution sk) :
    P.predictedReduction sk ≥
      if hB : ‖P.hessianApprox‖ = 0 then
        (1 / 2 : ℝ) * ‖P.gradient‖ * P.radius
      else
        (1 / 2 : ℝ) * ‖P.gradient‖ * min P.radius (‖P.gradient‖ / ‖P.hessianApprox‖) := by
  -- Route correction: compare the exact minimizer with an explicit gradient-ray trial step
  -- instead of the later Cauchy-point construction.
  by_cases hgrad : P.gradient = 0
  · -- When the gradient vanishes, the target lower bound is zero and feasibility of `0` suffices.
    have hzero_feasible : (0 : Point) ∈ P.feasibleSet := by
      rw [TrustRegionSubproblem.mem_feasibleSet_iff]
      simpa using P.radius_pos.le
    have hpred_nonneg : 0 ≤ P.predictedReduction sk := by
      simpa [TrustRegionSubproblem.predictedReduction_eq] using
        predictedReduction_le_of_isSolution P hsol hzero_feasible
    simpa [hgrad] using hpred_nonneg
  · -- For `g_k ≠ 0`, compare `sk` with a feasible trial step on the gradient ray.
    by_cases hB : ‖P.hessianApprox‖ = 0
    · have htrial_feasible :
          (-((P.radius / ‖P.gradient‖) : ℝ) • P.gradient : Point) ∈ P.feasibleSet := by
        exact gradientTrialStep_mem_feasibleSet P hgrad P.radius_pos.le le_rfl
      have htrial_compare :
          P.predictedReduction (-((P.radius / ‖P.gradient‖) : ℝ) • P.gradient) ≤
            P.predictedReduction sk :=
        predictedReduction_le_of_isSolution P hsol htrial_feasible
      have htrial_lower :
          P.radius * ‖P.gradient‖ -
              (1 / 2 : ℝ) * P.radius ^ 2 * ‖P.hessianApprox‖ ≤
            P.predictedReduction (-((P.radius / ‖P.gradient‖) : ℝ) • P.gradient) :=
        predictedReduction_gradientTrialStep_ge_linearMinusQuadratic P hgrad P.radius
      have hbranch_lower :
          (1 / 2 : ℝ) * ‖P.gradient‖ * P.radius ≤
            P.radius * ‖P.gradient‖ -
              (1 / 2 : ℝ) * P.radius ^ 2 * ‖P.hessianApprox‖ := by
        rw [hB]
        nlinarith [P.radius_pos, norm_nonneg P.gradient]
      have hbound :
          (1 / 2 : ℝ) * ‖P.gradient‖ * P.radius ≤ P.predictedReduction sk :=
        le_trans (le_trans hbranch_lower htrial_lower) htrial_compare
      simpa [hB] using hbound
    · let t : ℝ := min P.radius (‖P.gradient‖ / ‖P.hessianApprox‖)
      have ht0 : 0 ≤ t := by
        dsimp [t]
        refine le_min P.radius_pos.le ?_
        exact div_nonneg (norm_nonneg _) (norm_nonneg _)
      have htΔ : t ≤ P.radius := by
        dsimp [t]
        exact min_le_left _ _
      have htrial_feasible :
          (-((t / ‖P.gradient‖) : ℝ) • P.gradient : Point) ∈ P.feasibleSet := by
        exact gradientTrialStep_mem_feasibleSet P hgrad ht0 htΔ
      have htrial_compare :
          P.predictedReduction (-((t / ‖P.gradient‖) : ℝ) • P.gradient) ≤
            P.predictedReduction sk :=
        predictedReduction_le_of_isSolution P hsol htrial_feasible
      have htrial_lower :
          t * ‖P.gradient‖ - (1 / 2 : ℝ) * t ^ 2 * ‖P.hessianApprox‖ ≤
            P.predictedReduction (-((t / ‖P.gradient‖) : ℝ) • P.gradient) :=
        predictedReduction_gradientTrialStep_ge_linearMinusQuadratic P hgrad t
      have hbranch_lower :
          (1 / 2 : ℝ) * ‖P.gradient‖ * t ≤
            t * ‖P.gradient‖ - (1 / 2 : ℝ) * t ^ 2 * ‖P.hessianApprox‖ := by
        simpa [t] using halfGradientMinRadiusQuotient_le_trialLowerBound P hB
      simpa [hB, t] using le_trans (le_trans hbranch_lower htrial_lower) htrial_compare

end
