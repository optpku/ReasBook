/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Function
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_6_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_6_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_6_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Theorem_14_1_8

noncomputable section

open scoped CompositeNonsmooth

section Chapter14Theorem1464

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain-style sampling:
-- * primary domain: composite nonsmooth optimization in Chapter 14.6
-- * source-facing layer kept here: the strict-local-minimum theorem for the Chapter 14.6
--   composite problem owner
-- * core/canonical owners reused here:
--   `CompositeNonsmoothOptimizationProblem`,
--   `CompositeNonsmoothOptimizationProblem.firstOrderModel`, `DF[problem](x, d)`,
--   `IsStrictLocalMin`
-- * inspected related declarations:
--   `CompositeNonsmoothOptimizationProblem`,
--   `CompositeNonsmoothOptimizationProblem.objective`,
--   `CompositeNonsmoothOptimizationProblem.coe_apply`, `compositeNonsmoothDF`,
--   `IsStrictLocalMin`
-- * primitive data for this theorem: the Chapter 14.6 problem owner and the positivity
--   hypothesis on the source first-order model `DF(xStar, d)`
-- * derived API reused from the owner/bridge files: the composite objective coercion and the
--   Section 14.6 first-order model `problem.firstOrderModel`, written as
--   `DF[problem](xStar, d)`

/-- Helper for Chapter14 Theorem 14.6.4: the first-order model depends continuously on the
direction variable. -/
lemma continuous_firstOrderModelInDirection
    (problem : CompositeNonsmoothOptimizationProblem n m) (xStar : Point) :
    Continuous (fun d : Point ↦ DF[problem](xStar, d)) := by
  -- Rewrite `DF` through the Clarke derivative of the convex outer function and use the existing
  -- Lipschitz-in-direction estimate on that canonical owner.
  have h_outer_local :
      LocallyLipschitzAt problem.outerFunction (problem.smoothMap xStar) :=
    convexOn_univ_locallyLipschitzAt
      problem.outerFunction (problem.smoothMap xStar) problem.outerFunction_convex
  rcases locallyLipschitzAt_iff.mp h_outer_local with ⟨ε, hε, K, hK⟩
  let A : Point →L[ℝ] EuclideanSpace ℝ (Fin m) := fderiv ℝ problem.smoothMap xStar
  have hClarke :
      Continuous
        (fun v : EuclideanSpace ℝ (Fin m) ↦
          clarkeDirectionalDerivReal
            problem.outerFunction
            (problem.smoothMap xStar)
            v) :=
    (clarkeDirectionalDerivReal_lipschitzWith_of_closedBallLipschitz
      h_outer_local ⟨ε, hε, hK⟩).continuous
  have hA : Continuous fun d : Point ↦ A d := A.continuous
  convert hClarke.comp hA using 1
  ext d
  simpa [A] using
    (compositeNonsmoothDF_eq_clarkeDirectionalDerivReal
      problem.outerFunction problem.smoothMap xStar d problem.outerFunction_convex)

/-- Helper for Chapter14 Theorem 14.6.4: positivity of `DF[problem](xStar, d)` on nonzero
directions yields a uniform positive lower bound on the unit sphere. -/
lemma exists_positiveLowerBound_firstOrderModel_onUnitSphere
    [Nontrivial Point]
    (problem : CompositeNonsmoothOptimizationProblem n m) (xStar : Point)
    (h_positive :
      ∀ d : Point, d ≠ 0 →
        0 < DF[problem](xStar, d)) :
    ∃ δ > 0, ∀ d : Point, d ∈ Metric.sphere (0 : Point) 1 → δ ≤ DF[problem](xStar, d) := by
  let g : Point → ℝ := fun d ↦ DF[problem](xStar, d)
  have hgCont : Continuous g := continuous_firstOrderModelInDirection problem xStar
  have hsphereCompact : IsCompact (Metric.sphere (0 : Point) 1) := isCompact_sphere (0 : Point) 1
  have hsphereNonempty : (Metric.sphere (0 : Point) 1).Nonempty := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Point)
    exact ⟨‖v‖⁻¹ • v, invNorm_smul_mem_sphere_zero_one hv⟩
  obtain ⟨dMin, hdMinSphere, hdMin⟩ :=
    hsphereCompact.exists_isMinOn hsphereNonempty hgCont.continuousOn
  refine ⟨g dMin, ?_, ?_⟩
  · -- The minimizing direction is nonzero because it lies on the unit sphere.
    exact h_positive dMin (ne_zero_of_mem_sphere_zero_one hdMinSphere)
  · intro d hd
    simpa [g] using hdMin hd

/-- Helper for Chapter14 Theorem 14.6.4: the affine outer-model increment dominates
`α * DF[problem](xStar, d)` for every nonnegative step size `α`. -/
lemma firstOrderModel_secant_lowerBound
    (problem : CompositeNonsmoothOptimizationProblem n m)
    (xStar d : Point) {α : ℝ} (hα : 0 ≤ α) :
    α * DF[problem](xStar, d) ≤
      problem.outerFunction
          (problem.smoothMap xStar + α • ((fderiv ℝ problem.smoothMap xStar) d)) -
        problem xStar := by
  -- Compare the secant of the convex outer function against the model derivative, then rewrite
  -- the scaled direction through positive homogeneity of `DF`.
  have hchi :=
    compositeNonsmoothChi_le_neg_compositeNonsmoothDF
      problem.outerFunction problem.smoothMap xStar (α • d) problem.outerFunction_convex
  rw [compositeNonsmoothChi_ray_eq_sub_fderiv_smul] at hchi
  rw [compositeNonsmoothDF_smul_nonneg
    problem.outerFunction problem.smoothMap xStar d problem.outerFunction_convex hα] at hchi
  have hsecant :
      α * DF[problem](xStar, d) ≤
        problem.outerFunction
            (problem.smoothMap xStar + α • ((fderiv ℝ problem.smoothMap xStar) d)) -
          problem.outerFunction (problem.smoothMap xStar) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using neg_le_neg hchi
  simpa using hsecant

/-- Helper for Chapter14 Theorem 14.6.4: along every unit direction, sufficiently small positive
steps increase the composite objective strictly. -/
lemma objectiveStrictIncrease_on_smallNormalizedSteps
    [Nontrivial Point]
    (problem : CompositeNonsmoothOptimizationProblem n m) (xStar : Point)
    (h_positive :
      ∀ d : Point, d ≠ 0 →
        0 < DF[problem](xStar, d)) :
    ∃ ε > 0,
      ∀ d : Point, d ∈ Metric.sphere (0 : Point) 1 →
        ∀ {α : ℝ}, 0 < α → α < ε → problem xStar < problem (xStar + α • d) := by
  -- First freeze the source lower bound `DF ≥ δ` on the unit sphere.
  rcases
      exists_positiveLowerBound_firstOrderModel_onUnitSphere
        problem xStar h_positive with
    ⟨δ, hδpos, hδle⟩
  have h_outer_local :
      LocallyLipschitzAt problem.outerFunction (problem.smoothMap xStar) :=
    convexOn_univ_locallyLipschitzAt
      problem.outerFunction (problem.smoothMap xStar) problem.outerFunction_convex
  rcases locallyLipschitzAt_iff.mp h_outer_local with ⟨ρ, hρ, K, hK⟩
  let A : Point →L[ℝ] EuclideanSpace ℝ (Fin m) := fderiv ℝ problem.smoothMap xStar
  let L : ℝ := max (K : ℝ) 1
  let M : ℝ := max ‖A‖ 1
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right (K : ℝ) 1)
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right ‖A‖ 1)
  have hKleL : (K : ℝ) ≤ L := le_max_left (K : ℝ) 1
  have hdiff : DifferentiableAt ℝ problem.smoothMap xStar :=
    problem.smoothMap_contDiff.contDiffAt.differentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hA : HasFDerivAt problem.smoothMap A xStar := by
    simpa [A] using hdiff.hasFDerivAt
  have hremainderEvent :
      ∀ᶠ y in nhds xStar,
        ‖problem.smoothMap y - problem.smoothMap xStar - A (y - xStar)‖ ≤
          (δ / (2 * L)) * ‖y - xStar‖ := by
    simpa [A] using hA.isLittleO.bound (show 0 < δ / (2 * L) by positivity)
  rcases Metric.eventually_nhds_iff_ball.mp hremainderEvent with ⟨εrem, hεrem, hremainder⟩
  have hcontSmooth : ContinuousAt problem.smoothMap xStar :=
    problem.smoothMap_contDiff.contDiffAt.continuousAt
  have himageSet :
      {y : Point | problem.smoothMap y ∈ Metric.ball (problem.smoothMap xStar) (ρ / 2)} ∈
        nhds xStar := by
    simpa [Set.preimage] using
      (hcontSmooth (Metric.ball_mem_nhds (problem.smoothMap xStar) (by positivity)) :
        problem.smoothMap ⁻¹' Metric.ball (problem.smoothMap xStar) (ρ / 2) ∈ nhds xStar)
  rcases Metric.eventually_nhds_iff_ball.mp himageSet with ⟨εimg, hεimg, himage⟩
  let ε : ℝ := min εrem (min εimg (ρ / (2 * M)))
  have hεpos : 0 < ε := by
    dsimp [ε]
    refine lt_min hεrem ?_
    refine lt_min hεimg ?_
    positivity
  refine ⟨ε, hεpos, ?_⟩
  intro d hd α hαpos hαlt
  have hd_norm : ‖d‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hd
  have hαlt_rem : α < εrem := by
    exact lt_of_lt_of_le hαlt (min_le_left _ _)
  have hαlt_rest : α < min εimg (ρ / (2 * M)) := by
    exact lt_of_lt_of_le hαlt (min_le_right _ _)
  have hαlt_img : α < εimg := by
    exact lt_of_lt_of_le hαlt_rest (min_le_left _ _)
  have hαlt_lin : α < ρ / (2 * M) := by
    exact lt_of_lt_of_le hαlt_rest (min_le_right _ _)
  have hy_sub : xStar + α • d - xStar = α • d := by
    abel
  have hy_ball : xStar + α • d ∈ Metric.ball xStar εimg := by
    -- The step length equals `α` because `d` is a unit vector.
    rw [Metric.mem_ball, dist_eq_norm, hy_sub]
    simpa [norm_smul, hd_norm, Real.norm_of_nonneg hαpos.le] using hαlt_img
  have hactual_ball :
      problem.smoothMap (xStar + α • d) ∈ Metric.ball (problem.smoothMap xStar) (ρ / 2) :=
    himage _ hy_ball
  have hactual_closed :
      problem.smoothMap (xStar + α • d) ∈ Metric.closedBall (problem.smoothMap xStar) ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm] at ⊢
    rw [Metric.mem_ball, dist_eq_norm] at hactual_ball
    linarith
  have hlin_bound :
      ‖α • A d‖ ≤ ρ / 2 := by
    have hAd : ‖A d‖ ≤ ‖A‖ * ‖d‖ := A.le_opNorm d
    have hαMlt : α * M < ρ / 2 := by
      have htmp : α * M < (ρ / (2 * M)) * M :=
        mul_lt_mul_of_pos_right hαlt_lin hMpos
      have hMne : M ≠ 0 := ne_of_gt hMpos
      calc
        α * M < (ρ / (2 * M)) * M := htmp
        _ = ρ / 2 := by
              field_simp [hMne]
    calc
      ‖α • A d‖ = α * ‖A d‖ := by
        rw [norm_smul, Real.norm_of_nonneg hαpos.le]
      _ ≤ α * (‖A‖ * ‖d‖) := by
        gcongr
      _ = α * ‖A‖ := by rw [hd_norm, mul_one]
      _ ≤ α * M := by
        gcongr
        exact le_max_left ‖A‖ 1
      _ ≤ ρ / 2 := le_of_lt hαMlt
  have hmodel_closed :
      problem.smoothMap xStar + α • A d ∈ Metric.closedBall (problem.smoothMap xStar) ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hmodel_sub :
        problem.smoothMap xStar + α • A d - problem.smoothMap xStar = α • A d := by
      abel
    rw [hmodel_sub]
    linarith
  have hremainder_step :
      ‖problem.smoothMap (xStar + α • d) -
            (problem.smoothMap xStar + α • A d)‖ ≤
        (δ / (2 * L)) * α := by
    -- Evaluate the Fréchet remainder bound on the small step `xStar + α • d`.
    have hy_ball_rem : xStar + α • d ∈ Metric.ball xStar εrem := by
      rw [Metric.mem_ball, dist_eq_norm, hy_sub]
      simpa [norm_smul, hd_norm, Real.norm_of_nonneg hαpos.le] using hαlt_rem
    have hrem := hremainder _ hy_ball_rem
    have hrew :
        problem.smoothMap (xStar + α • d) -
            (problem.smoothMap xStar + α • A d) =
          problem.smoothMap (xStar + α • d) - problem.smoothMap xStar -
            A ((xStar + α • d) - xStar) := by
      rw [hy_sub, map_smul]
      abel
    calc
      ‖problem.smoothMap (xStar + α • d) -
            (problem.smoothMap xStar + α • A d)‖
        =
          ‖problem.smoothMap (xStar + α • d) - problem.smoothMap xStar -
              A ((xStar + α • d) - xStar)‖ := by
            rw [hrew]
      _ ≤ (δ / (2 * L)) * ‖(xStar + α • d) - xStar‖ := hrem
      _ = (δ / (2 * L)) * α := by
            rw [hy_sub, norm_smul, hd_norm, Real.norm_of_nonneg hαpos.le, mul_one]
  have herror_abs :
      |problem (xStar + α • d) -
          problem.outerFunction (problem.smoothMap xStar + α • A d)| ≤
        (K : ℝ) *
          dist (problem.smoothMap (xStar + α • d))
            (problem.smoothMap xStar + α • A d) := by
    -- The outer function is Lipschitz on the chosen closed ball containing both comparison
    -- points.
    simpa [Real.dist_eq, sub_eq_add_neg, abs_sub_comm] using
      hK.dist_le_mul
        (problem.smoothMap (xStar + α • d)) hactual_closed
        (problem.smoothMap xStar + α • A d) hmodel_closed
  have herror_lower :
      -((δ / 2) * α) ≤
        problem (xStar + α • d) -
          problem.outerFunction (problem.smoothMap xStar + α • A d) := by
    have herror_lower' :
        -((K : ℝ) *
            dist (problem.smoothMap (xStar + α • d))
              (problem.smoothMap xStar + α • A d)) ≤
          problem (xStar + α • d) -
            problem.outerFunction (problem.smoothMap xStar + α • A d) :=
      (abs_le.mp herror_abs).1
    have herror_upper' :
        (K : ℝ) *
            dist (problem.smoothMap (xStar + α • d))
              (problem.smoothMap xStar + α • A d) ≤
          (δ / 2) * α := by
      have hLne : L ≠ 0 := ne_of_gt hLpos
      have hcancel : L * (δ / (2 * L)) = δ / 2 := by
        field_simp [hLne]
      calc
        (K : ℝ) *
            dist (problem.smoothMap (xStar + α • d))
              (problem.smoothMap xStar + α • A d)
          ≤ L *
              dist (problem.smoothMap (xStar + α • d))
                (problem.smoothMap xStar + α • A d) := by
                gcongr
        _ = L *
              ‖problem.smoothMap (xStar + α • d) -
                  (problem.smoothMap xStar + α • A d)‖ := by
              simp [dist_eq_norm]
        _ ≤ L * ((δ / (2 * L)) * α) := by
              gcongr
        _ = (L * (δ / (2 * L))) * α := by ring
        _ = (δ / 2) * α := by rw [hcancel]
    linarith
  have hmodel_lower :
      α * δ ≤
        problem.outerFunction (problem.smoothMap xStar + α • A d) - problem xStar := by
    have hsecant := firstOrderModel_secant_lowerBound problem xStar d hαpos.le
    have hδdir : δ ≤ DF[problem](xStar, d) := hδle d hd
    nlinarith
  have htotal :
      (δ / 2) * α ≤ problem (xStar + α • d) - problem xStar := by
    linarith
  have htotal_pos : 0 < problem (xStar + α • d) - problem xStar := by
    have : 0 < (δ / 2) * α := by positivity
    linarith
  linarith

/-- Chapter14 Theorem 14.6.4: for a composite nonsmooth problem `problem`, if the source
first-order quantity `DF(xStar, d)` represented in Lean by `DF[problem](xStar, d)` is strictly
positive for every nonzero direction `d`, then `xStar` is a strict local minimizer of the
composite objective `problem`. -/
theorem isStrictLocalMin_of_pos_compositeFirstOrderModel
    (problem : CompositeNonsmoothOptimizationProblem n m) (xStar : Point)
    (h_positive :
      ∀ d : Point, d ≠ 0 →
        0 < DF[problem](xStar, d)) :
    IsStrictLocalMin problem xStar := by
  rcases subsingleton_or_nontrivial Point with hPoint | hPoint
  · letI : Subsingleton Point := hPoint
    -- In the degenerate ambient space there are no punctured neighbors of `xStar`.
    refine (isStrictLocalMin_iff_exists_forall_norm_sub_lt problem xStar).2 ?_
    refine ⟨1, zero_lt_one, ?_⟩
    intro x hx _
    exact False.elim (hx (Subsingleton.elim _ _))
  · letI : Nontrivial Point := hPoint
    rcases
        objectiveStrictIncrease_on_smallNormalizedSteps
          problem xStar h_positive with
      ⟨ε, hε, hstep⟩
    refine (isStrictLocalMin_iff_exists_forall_norm_sub_lt problem xStar).2 ?_
    refine ⟨ε, hε, ?_⟩
    intro x hx hnorm
    -- Normalize the nonzero displacement to the unit sphere and reuse the small-step estimate.
    let α : ℝ := ‖x - xStar‖
    let d : Point := α⁻¹ • (x - xStar)
    have hxsub_ne : x - xStar ≠ 0 := sub_ne_zero.mpr hx
    have hαpos : 0 < α := by
      dsimp [α]
      exact norm_pos_iff.mpr hxsub_ne
    have hdSphere : d ∈ Metric.sphere (0 : Point) 1 := by
      dsimp [d, α]
      exact invNorm_smul_mem_sphere_zero_one hxsub_ne
    have hstrict := hstep d hdSphere hαpos (by simpa [α] using hnorm)
    have hxrepr : xStar + α • d = x := by
      dsimp [α, d]
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hxsub_ne), one_smul]
      abel
    simpa [hxrepr] using hstrict

#print axioms isStrictLocalMin_of_pos_compositeFirstOrderModel

end Chapter14Theorem1464
