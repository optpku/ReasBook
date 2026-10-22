/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Algorithm_7_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_56
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_57
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_65
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_66
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_62
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_28
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Theorem_7_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Asymptotics
open Filter
open scoped BigOperators Gradient HessianDualLocalNorm

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

namespace BarrierSubgradientMethod

section ApproximationSchedule

variable {P0 : Set E} {F ψ : E → ℝ} {ν : NNRealˣ} {x0 : P0}
variable (method : BarrierSubgradientMethod P0 F ψ ν x0)

/-- Helper for Proposition 7.34: the geometric mean of the first `k + 1` objective values along
the barrier-subgradient iterate sequence. -/
def iterateGeometricMean (k : ℕ) : ℝ :=
  positiveIterateGeometricMean
    (fun x : P0 ↦ ⟨ψ x, method.ψ_pos x.2⟩)
    method.iterate
    k

/-- Helper for Proposition 7.34: every iterate geometric mean is bounded above by the optimal
value `ψ xStar`. -/
lemma iterateGeometricMean_le_optimal
    (xStar : P0) (hoptimal : IsMaxOn ψ P0 xStar) (k : ℕ) :
    method.iterateGeometricMean k ≤ ψ xStar := by
  let ψpos : P0 → {r : ℝ // 0 < r} := fun x ↦ ⟨ψ x, method.ψ_pos x.2⟩
  have hsum :
      Finset.sum (Finset.range (k + 1)) (fun i ↦ Real.log (ψpos (method.iterate i) : ℝ)) ≤
        ((k : ℝ) + 1) * Real.log (ψ xStar) := by
    -- Optimality bounds each sampled logarithm by the optimal logarithm.
    calc
      Finset.sum (Finset.range (k + 1)) (fun i ↦ Real.log (ψpos (method.iterate i) : ℝ)) ≤
          Finset.sum (Finset.range (k + 1)) (fun _i ↦ Real.log (ψ xStar)) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hiter_le : ψ (method.iterate i : E) ≤ ψ xStar :=
          (isMaxOn_iff.mp hoptimal) (method.iterate i) (method.iterate_mem i)
        exact Real.log_le_log (method.ψ_pos (method.iterate_mem i)) hiter_le
      _ = ((k : ℝ) + 1) * Real.log (ψ xStar) := by
        simp
  have hk_pos : 0 < ((k : ℝ) + 1) := by
    positivity
  have havg :
      (Finset.sum (Finset.range (k + 1)) (fun i ↦ Real.log (ψpos (method.iterate i) : ℝ))) /
          ((k : ℝ) + 1) ≤
        Real.log (ψ xStar) := by
    -- Divide the constant upper bound by the positive averaging denominator.
    refine (div_le_iff₀ hk_pos).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsum
  have hxStar_pos : 0 < ψ xStar := method.ψ_pos xStar.2
  -- Re-express the geometric mean as an exponential of averaged logarithms.
  calc
    method.iterateGeometricMean k =
        Real.exp
          ((Finset.sum (Finset.range (k + 1)) (fun i ↦ Real.log (ψpos (method.iterate i) : ℝ))) /
            ((k : ℝ) + 1)) := by
      rw [iterateGeometricMean, positiveIterateGeometricMean_eq_exp_average_log]
    _ ≤ Real.exp (Real.log (ψ xStar)) := Real.exp_le_exp_of_le havg
    _ = ψ xStar := by
      rw [Real.exp_log hxStar_pos]

/-- Helper for Proposition 7.34: the Chapter 7 log-average gap of the primal iterates is bounded
by the explicit rate `δ_k`. -/
lemma logarithmicTransform_isMaxOn_of_isMaxOn
    (method : BarrierSubgradientMethod P0 F ψ ν x0)
    (xStar : P0) (hoptimal : IsMaxOn ψ P0 xStar) :
    IsMaxOn (logarithmicTransform ψ) P0 xStar := by
  -- Applying `log` preserves the maximizing order because every feasible value of `ψ` is positive.
  rw [isMaxOn_iff] at hoptimal ⊢
  intro y hy
  rw [logarithmicTransform_apply, logarithmicTransform_apply]
  exact Real.log_le_log (method.ψ_pos hy) (hoptimal y hy)

/-- Helper for Proposition 7.34: on the barrier domain `P0`, the logarithmic transform of `ψ`
remains concave. -/
lemma logarithmicTransform_concaveOn
    [IsSelfConcordantBarrierOnWith P0 (ν : NNReal) F]
    (hψ_concave : ConcaveOn ℝ P0 ψ) :
    ConcaveOn ℝ P0 (logarithmicTransform ψ) := by
  refine ⟨hψ_concave.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hψ_avg :
      a * ψ x + b * ψ y ≤ ψ (a • x + b • y) := by
    simpa [smul_eq_mul] using hψ_concave.2 hx hy ha hb hab
  have hx_pos : 0 < ψ x := method.ψ_pos hx
  have hy_pos : 0 < ψ y := method.ψ_pos hy
  have havg_pos : 0 < a * ψ x + b * ψ y := by
    have hax : 0 ≤ a * ψ x := mul_nonneg ha hx_pos.le
    have hby : 0 ≤ b * ψ y := mul_nonneg hb hy_pos.le
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      subst ha0 hb1
      simpa using hy_pos
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
      exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hx_pos) hby
  -- Concavity of `log` on `(0, ∞)` transfers the source concavity of `ψ`.
  calc
    logarithmicTransform ψ (a • x + b • y)
        = Real.log (ψ (a • x + b • y)) := by
            simp [logarithmicTransform]
    _ ≥ Real.log (a * ψ x + b * ψ y) := by
          exact Real.strictMonoOn_log.monotoneOn
            (show a * ψ x + b * ψ y ∈ Set.Ioi (0 : ℝ) from havg_pos)
            (show ψ (a • x + b • y) ∈ Set.Ioi (0 : ℝ) from method.ψ_pos (hψ_concave.1 hx hy ha hb hab))
            hψ_avg
    _ ≥ a * Real.log (ψ x) + b * Real.log (ψ y) := by
          simpa [logarithmicTransform, smul_eq_mul] using
            (strictConcaveOn_log_Ioi.concaveOn.2
              (show ψ x ∈ Set.Ioi (0 : ℝ) from hx_pos)
              (show ψ y ∈ Set.Ioi (0 : ℝ) from hy_pos)
              ha hb hab)

/-- Helper for Proposition 7.34: differentiating `x ↦ log (ψ x)` on the open barrier domain
produces the scaled gradient `barrierSubgradientDirection ψ x`. -/
lemma hasGradientAt_logarithmicTransform
    [IsSelfConcordantBarrierOnWith P0 (ν : NNReal) F]
    {x : E} (hx : x ∈ P0) :
    HasGradientAt (logarithmicTransform ψ) (barrierSubgradientDirection ψ x) x := by
  let hP0_open : IsOpen P0 :=
    (inferInstance : IsSelfConcordantBarrierOnWith P0 ν F).toIsStandardSelfConcordantOn.isOpen_domain
  have hdiff : DifferentiableAt ℝ ψ x :=
    method.ψ_differentiableOn.differentiableAt (hP0_open.mem_nhds hx)
  have hgrad : HasGradientAt ψ (∇ ψ x) x := hdiff.hasGradientAt
  -- The chain rule for `Real.log ∘ ψ` gives the scaled gradient formula.
  simpa [logarithmicTransform, barrierSubgradientDirection_def] using
    (hgrad.hasFDerivAt.log (ne_of_gt (method.ψ_pos hx))).hasGradientAt

/-- Helper for Proposition 7.34: on the open barrier domain `P0`, the logarithmic transform
inherits the affine upper-support inequality at each iterate. -/
lemma logarithmicTransform_iterate_upperSupport
    [IsSelfConcordantBarrierOnWith P0 (ν : NNReal) F]
    (hψ_concave : ConcaveOn ℝ P0 ψ)
    (i : ℕ) {y : E} (hy : y ∈ P0) :
    logarithmicTransform ψ y ≤
      logarithmicTransform ψ (method.iterate i : E) +
        inner ℝ (barrierSubgradientDirection ψ (method.iterate i : E))
          (y - (method.iterate i : E)) := by
  -- Apply the first-order upper-support inequality for the concave logarithmic transform.
  exact concaveOn_le_tangent_of_hasGradientAt
    (method.logarithmicTransform_concaveOn hψ_concave)
    (method.iterate_mem i)
    hy
    (method.hasGradientAt_logarithmicTransform (method.iterate_mem i))

/-- Helper for Proposition 7.34: the unit-weight `centerMass` of the logarithmic iterate values is
the arithmetic mean of the sampled logarithms. -/
lemma unitWeightCenterMass_eq_logAverage
    (k : ℕ) :
    (Finset.range (k + 1)).centerMass
        (fun _ ↦ (1 : ℝ))
        (fun i ↦ logarithmicTransform ψ (method.iterate i : E)) =
      (Finset.sum (Finset.range (k + 1))
          (fun i ↦ Real.log (ψ (method.iterate i : E)))) /
        ((k : ℝ) + 1) := by
  -- Expand the center of mass and collapse the constant unit denominator.
  rw [Finset.centerMass]
  simp [logarithmicTransform_apply, smul_eq_mul]

/-- Helper for Proposition 7.34: averaging the logarithmic upper-support inequalities over the
first `k + 1` iterates bounds any feasible logarithmic value by the unit-weight center of mass
plus the normalized gap term. -/
lemma logarithmicTransform_pointwise_le_unitCenterMass_add_gapRatio
    [IsSelfConcordantBarrierOnWith P0 (ν : NNReal) F]
    (hψ_concave : ConcaveOn ℝ P0 ψ)
    (k : ℕ) (y : P0) :
    logarithmicTransform ψ y ≤
      (Finset.range (k + 1)).centerMass
          (fun _ ↦ (1 : ℝ))
          (fun i ↦ logarithmicTransform ψ (method.iterate i : E)) +
        barrierSubgradientGapFunction
            method.iterate
            (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
            (fun _ ↦ (1 : ℝ))
            k
            y /
          ((k : ℝ) + 1) := by
  have hk_pos : 0 < ((k : ℝ) + 1) := Nat.cast_add_one_pos k
  have hweighted :
      ∑ i ∈ Finset.range (k + 1), (1 : ℝ) * logarithmicTransform ψ y ≤
        ∑ i ∈ Finset.range (k + 1),
          (1 : ℝ) *
            (logarithmicTransform ψ (method.iterate i : E) +
              inner ℝ (barrierSubgradientDirection ψ (method.iterate i : E))
                ((y : E) - (method.iterate i : E))) := by
    -- Sum the pointwise logarithmic upper-support bounds termwise.
    refine Finset.sum_le_sum ?_
    intro i hi
    simpa using method.logarithmicTransform_iterate_upperSupport hψ_concave i y.2
  have hleft :
      ∑ i ∈ Finset.range (k + 1), (1 : ℝ) * logarithmicTransform ψ y =
        ((k : ℝ) + 1) * logarithmicTransform ψ y := by
    simp
  have hright :
      ∑ i ∈ Finset.range (k + 1),
          (1 : ℝ) *
            (logarithmicTransform ψ (method.iterate i : E) +
              inner ℝ (barrierSubgradientDirection ψ (method.iterate i : E))
                ((y : E) - (method.iterate i : E))) =
        (∑ i ∈ Finset.range (k + 1), logarithmicTransform ψ (method.iterate i : E)) +
          barrierSubgradientGapFunction
            method.iterate
            (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
            (fun _ ↦ (1 : ℝ))
            k
            y := by
    -- Split the averaged-support sum into the sampled logarithmic values and the gap owner.
    calc
      ∑ i ∈ Finset.range (k + 1),
          (1 : ℝ) *
            (logarithmicTransform ψ (method.iterate i : E) +
              inner ℝ (barrierSubgradientDirection ψ (method.iterate i : E))
                ((y : E) - (method.iterate i : E))) =
          ∑ i ∈ Finset.range (k + 1),
            (logarithmicTransform ψ (method.iterate i : E) +
              inner ℝ (barrierSubgradientDirection ψ (method.iterate i : E))
                ((y : E) - (method.iterate i : E))) := by
            simp
      _ =
          (∑ i ∈ Finset.range (k + 1), logarithmicTransform ψ (method.iterate i : E)) +
            ∑ i ∈ Finset.range (k + 1),
              inner ℝ (barrierSubgradientDirection ψ (method.iterate i : E))
                ((y : E) - (method.iterate i : E)) := by
            rw [Finset.sum_add_distrib]
      _ =
          (∑ i ∈ Finset.range (k + 1), logarithmicTransform ψ (method.iterate i : E)) +
            barrierSubgradientGapFunction
              method.iterate
              (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
              (fun _ ↦ (1 : ℝ))
              k
              y := by
            rw [barrierSubgradientGapFunction_apply]
            simp
  have hsum :
      ((k : ℝ) + 1) * logarithmicTransform ψ y ≤
        (∑ i ∈ Finset.range (k + 1), logarithmicTransform ψ (method.iterate i : E)) +
          barrierSubgradientGapFunction
            method.iterate
            (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
            (fun _ ↦ (1 : ℝ))
            k
            y := by
    have hsum' := hweighted
    rw [hleft] at hsum'
    rw [hright] at hsum'
    exact hsum'
  have hdiv :
      logarithmicTransform ψ y ≤
        ((∑ i ∈ Finset.range (k + 1), logarithmicTransform ψ (method.iterate i : E)) +
            barrierSubgradientGapFunction
              method.iterate
              (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
              (fun _ ↦ (1 : ℝ))
              k
              y) /
          ((k : ℝ) + 1) := by
    have hdiv' :
        (((k : ℝ) + 1) * logarithmicTransform ψ y) / ((k : ℝ) + 1) ≤
          ((∑ i ∈ Finset.range (k + 1), logarithmicTransform ψ (method.iterate i : E)) +
              barrierSubgradientGapFunction
                method.iterate
                (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
                (fun _ ↦ (1 : ℝ))
                k
                y) /
            ((k : ℝ) + 1) := by
      exact div_le_div_of_nonneg_right hsum hk_pos.le
    simpa [hk_pos.ne', div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv'
  calc
    logarithmicTransform ψ y ≤
        ((∑ i ∈ Finset.range (k + 1), logarithmicTransform ψ (method.iterate i : E)) +
            barrierSubgradientGapFunction
              method.iterate
              (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
              (fun _ ↦ (1 : ℝ))
              k
              y) /
          ((k : ℝ) + 1) := hdiv
    _ =
        (∑ i ∈ Finset.range (k + 1), logarithmicTransform ψ (method.iterate i : E)) /
            ((k : ℝ) + 1) +
          barrierSubgradientGapFunction
              method.iterate
              (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
              (fun _ ↦ (1 : ℝ))
              k
              y /
            ((k : ℝ) + 1) := by
          rw [add_div]
    _ =
        (Finset.range (k + 1)).centerMass
            (fun _ ↦ (1 : ℝ))
            (fun i ↦ logarithmicTransform ψ (method.iterate i : E)) +
          barrierSubgradientGapFunction
              method.iterate
              (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
              (fun _ ↦ (1 : ℝ))
              k
              y /
            ((k : ℝ) + 1) := by
          rw [Finset.centerMass]
          simp [smul_eq_mul]

/-- Helper for Proposition 7.34: every normalized pointwise gap evaluation is bounded above by
the normalized maximal-gap owner. -/
lemma logarithmicGapEval_div_le_maximalGapRatio
    (k : ℕ) (y : P0) :
    (((barrierSubgradientGapFunction
          method.iterate
          (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
          (fun _ ↦ (1 : ℝ))
          k
          y /
        ((k : ℝ) + 1) : ℝ) : EReal)) ≤
      barrierSubgradientMaximalGap
          method.iterate
          (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
          (fun _ ↦ (1 : ℝ))
          k /
        ((k : ℝ) + 1) := by
  -- Compare the pointwise gap evaluation to the maximal-gap supremum before dividing by `k + 1`.
  rw [EReal.coe_div, barrierSubgradientMaximalGap_def]
  exact EReal.div_le_div_right_of_nonneg
    (by exact_mod_cast (Nat.cast_add_one_pos k).le)
    (le_sSup (Set.mem_range_self y))

/-- Helper for Proposition 7.34: the fixed-index logarithmic gap at any feasible point is bounded
by the normalized maximal-gap owner for the iterate-direction sequence. -/
lemma logarithmicTransform_gap_le_maximalGapRatio
    [IsSelfConcordantBarrierOnWith P0 (ν : NNReal) F]
    (hψ_concave : ConcaveOn ℝ P0 ψ)
    (k : ℕ) (y : P0) :
    (((logarithmicTransform ψ y -
          (Finset.range (k + 1)).centerMass
            (fun _ ↦ (1 : ℝ))
            (fun i ↦ logarithmicTransform ψ (method.iterate i : E)) : ℝ) : EReal)) ≤
      barrierSubgradientMaximalGap
          method.iterate
          (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
          (fun _ ↦ (1 : ℝ))
          k /
        ((k : ℝ) + 1) := by
  have hpoint :
      logarithmicTransform ψ y -
          (Finset.range (k + 1)).centerMass
            (fun _ ↦ (1 : ℝ))
            (fun i ↦ logarithmicTransform ψ (method.iterate i : E)) ≤
        barrierSubgradientGapFunction
            method.iterate
            (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
            (fun _ ↦ (1 : ℝ))
            k
            y /
          ((k : ℝ) + 1) := by
    linarith [method.logarithmicTransform_pointwise_le_unitCenterMass_add_gapRatio
      hψ_concave k y]
  have hpointE :
      (((logarithmicTransform ψ y -
            (Finset.range (k + 1)).centerMass
              (fun _ ↦ (1 : ℝ))
              (fun i ↦ logarithmicTransform ψ (method.iterate i : E)) : ℝ) : EReal)) ≤
        (((barrierSubgradientGapFunction
              method.iterate
              (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
              (fun _ ↦ (1 : ℝ))
              k
              y /
            ((k : ℝ) + 1) : ℝ) : EReal) := by
    exact_mod_cast hpoint
  exact le_trans hpointE (method.logarithmicGapEval_div_le_maximalGapRatio k y)

/-- Helper for Proposition 7.34: the live Algorithm 7.14 penalty weight is the sum of the two
inverse square-root terms forced by its owner definition. -/
lemma penaltyWeight_eq_invSqrt_add_invSqrt
    (k : ℕ) :
    barrierSubgradientPenaltyWeight ν k =
      (Real.sqrt (((k + 1 : ℕ) : ℝ)))⁻¹ + (Real.sqrt (ν : ℝ))⁻¹ := by
  have hν_pos : 0 < (ν : ℝ) := ν.2
  have hk_pos : 0 < (((k + 1 : ℕ) : ℝ)) := by
    positivity
  have hν_sqrt_ne : Real.sqrt (ν : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 hν_pos
  have hk_sqrt_ne : Real.sqrt (((k + 1 : ℕ) : ℝ)) ≠ 0 :=
    Real.sqrt_ne_zero'.2 hk_pos
  -- Expand the owner definition and split the positive square-root denominator.
  rw [barrierSubgradientPenaltyWeight]
  rw [Real.sqrt_mul (show 0 ≤ (ν : ℝ) by exact le_of_lt hν_pos)
    (show 0 ≤ (((k + 1 : ℕ) : ℝ)) by positivity)]
  field_simp [hν_sqrt_ne, hk_sqrt_ne]
  ring

/-- Helper for Proposition 7.34: the unit barrier-subgradient weights sum to `k + 1`. -/
lemma unitWeightSum_eq_castSucc
    (k : ℕ) :
    barrierSubgradientWeightSum (fun _ ↦ (1 : ℝ)) k = ((k : ℝ) + 1) := by
  -- Expand the owner sum and collapse the constant unit summand.
  rw [barrierSubgradientWeightSum_def]
  simp

/-- Helper for Proposition 7.34: the scaled logarithmic subgradient has Hessian-dual local norm at
most `1` at every feasible point. -/
lemma barrierDirectionDualNorm_le_one
    [HasPositiveDefiniteHessianOn P0 F]
    (hψ_dual_bound :
      ∀ x : P0,
        HessianDualLocalNorm.ofPosDefMem F x.2
            (InnerProductSpace.toDualMap ℝ E (∇ ψ x)) ≤
          ψ x) :
    ∀ x : P0,
      HessianDualLocalNorm.ofPosDefMem F x.2
          (InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ x)) ≤
        (1 : ℝ) := by
  intro x
  have hψ_pos : 0 < ψ x := method.ψ_pos x.2
  have hψ_inv_nonneg : 0 ≤ (ψ x)⁻¹ := inv_nonneg.mpr hψ_pos.le
  have hdual_eq :
      InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ x) =
        (ψ x)⁻¹ • InnerProductSpace.toDualMap ℝ E (∇ ψ x) := by
    -- Push the primal scaling through the Riesz map before applying dual-norm homogeneity.
    rw [barrierSubgradientDirection_def]
    simpa using (InnerProductSpace.toDualMap ℝ E).map_smul ((ψ x)⁻¹) (∇ ψ x)
  let hPos : (hessian F (x : E)).IsPositive :=
    HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem x.2
  let hInv : (hessian F (x : E)).IsInvertible :=
    hessian_isInvertible_of_det_ne_zero
      (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem x.2)
  calc
    HessianDualLocalNorm.ofPosDefMem F x.2
        (InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ x)) =
        HessianDualLocalNorm.ofPosDefMem F x.2
          ((ψ x)⁻¹ • InnerProductSpace.toDualMap ℝ E (∇ ψ x)) := by
            rw [hdual_eq]
    _ = (ψ x)⁻¹ *
          HessianDualLocalNorm.ofPosDefMem F x.2
            (InnerProductSpace.toDualMap ℝ E (∇ ψ x)) := by
          -- Nonnegative scalar homogeneity of the Hessian-dual norm handles the `1 / ψ(x)` factor.
          simpa [HessianDualLocalNorm.ofPosDefMem, smul_eq_mul] using
            dualLocalNorm_smul_nonneg F (x : E) hPos hInv
              (InnerProductSpace.toDualMap ℝ E (∇ ψ x)) hψ_inv_nonneg
    _ ≤ (ψ x)⁻¹ * ψ x := by
          exact mul_le_mul_of_nonneg_left (hψ_dual_bound x) hψ_inv_nonneg
    _ = 1 := by
          rw [inv_mul_cancel₀ hψ_pos.ne']

/-- Helper for Proposition 7.34: the exact stage-scaled penalty coefficient used by Algorithm
7.14. -/
def stageScaledPenaltyWeight (ν : NNRealˣ) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * barrierSubgradientPenaltyWeight ν k

/-- Helper for Proposition 7.34: the stage-scaled penalty coefficient is positive. -/
lemma stageScaledPenaltyWeight_pos
    (k : ℕ) :
    0 < stageScaledPenaltyWeight ν k := by
  have hk_pos : 0 < ((k : ℝ) + 1) := by
    positivity
  have hpenalty_pos : 0 < barrierSubgradientPenaltyWeight ν k := by
    rw [penaltyWeight_eq_invSqrt_add_invSqrt (ν := ν) k]
    have hleft_pos : 0 < (Real.sqrt (((k + 1 : ℕ) : ℝ)))⁻¹ := by
      apply inv_pos.2
      exact Real.sqrt_pos.2 (by positivity)
    have hright_pos : 0 < (Real.sqrt (ν : ℝ))⁻¹ := by
      apply inv_pos.2
      exact Real.sqrt_pos.2 ν.2
    linarith
  -- Both the averaging denominator and the penalty weight are positive.
  simpa [stageScaledPenaltyWeight] using mul_pos hk_pos hpenalty_pos

/-- Helper for Proposition 7.34: the stage-scaled penalty coefficient splits into the explicit
square-root term plus the fixed `ν` denominator term. -/
lemma stageScaledPenaltyWeight_eq_sqrt_add_div
    (k : ℕ) :
    stageScaledPenaltyWeight ν k =
      Real.sqrt (((k + 1 : ℕ) : ℝ)) + ((k : ℝ) + 1) / Real.sqrt (ν : ℝ) := by
  have hν_sqrt_ne : Real.sqrt (ν : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 ν.2
  have hk_pos : 0 < (((k + 1 : ℕ) : ℝ)) := by
    positivity
  have hk_sqrt_ne : Real.sqrt (((k + 1 : ℕ) : ℝ)) ≠ 0 := Real.sqrt_ne_zero'.2 hk_pos
  -- Expand the penalty weight first, then clear the positive square-root denominators.
  rw [stageScaledPenaltyWeight, penaltyWeight_eq_invSqrt_add_invSqrt]
  field_simp [hν_sqrt_ne, hk_sqrt_ne]
  ring_nf
  rw [Real.sq_sqrt (show 0 ≤ (((k + 1 : ℕ) : ℝ)) by positivity)]

/-- Helper for Proposition 7.34: the stage-scaled penalty coefficient is the shifted Chapter 7
`β`-schedule with unit dual bound, multiplied by the stage factor `√(k + 1)`. -/
lemma stageScaledPenaltyWeight_eq_sqrt_mul_barrierSubgradientBeta_one_succ
    (k : ℕ) :
    stageScaledPenaltyWeight ν k =
      Real.sqrt (((k + 1 : ℕ) : ℝ)) *
        barrierSubgradientBeta (1 : NNReal) ⟨(ν : ℝ), ν.2⟩ (k + 1) := by
  have hk_nonneg : 0 ≤ (((k + 1 : ℕ) : ℝ)) := by
    positivity
  have hν_sqrt_pos : 0 < Real.sqrt (ν : ℝ) := Real.sqrt_pos.2 ν.2
  have hsqrt_mul :
      Real.sqrt (((k + 1 : ℕ) : ℝ)) *
          Real.sqrt ((((k + 1 : ℕ) : ℝ) / (ν : ℝ))) =
        ((k : ℝ) + 1) / Real.sqrt (ν : ℝ) := by
    -- Rewrite the quotient square root as a quotient of square roots and absorb the remaining
    -- `√(k + 1)` factor into the numerator.
    calc
      Real.sqrt (((k + 1 : ℕ) : ℝ)) *
          Real.sqrt ((((k + 1 : ℕ) : ℝ) / (ν : ℝ))) =
          Real.sqrt (((k + 1 : ℕ) : ℝ)) *
            (Real.sqrt (((k + 1 : ℕ) : ℝ)) / Real.sqrt (ν : ℝ)) := by
              rw [Real.sqrt_div hk_nonneg (ν : ℝ)]
      _ = (Real.sqrt (((k + 1 : ℕ) : ℝ)) * Real.sqrt (((k + 1 : ℕ) : ℝ))) /
          Real.sqrt (ν : ℝ) := by
            ring
      _ = (((k + 1 : ℕ) : ℝ)) / Real.sqrt (ν : ℝ) := by
            rw [Real.sq_sqrt hk_nonneg]
      _ = ((k : ℝ) + 1) / Real.sqrt (ν : ℝ) := by
            norm_num
  -- Combine the explicit stage formula with the closed form of `barrierSubgradientBeta`.
  rw [stageScaledPenaltyWeight_eq_sqrt_add_div (ν := ν) k]
  rw [barrierSubgradientBeta_of_one_le
    (M := (1 : NNReal))
    (ν := ⟨(ν : ℝ), ν.2⟩)
    (hk := Nat.succ_le_succ (Nat.zero_le k))]
  calc
    Real.sqrt (((k + 1 : ℕ) : ℝ)) + ((k : ℝ) + 1) / Real.sqrt (ν : ℝ) =
        Real.sqrt (((k + 1 : ℕ) : ℝ)) +
          Real.sqrt (((k + 1 : ℕ) : ℝ)) *
            Real.sqrt ((((k + 1 : ℕ) : ℝ) / (ν : ℝ))) := by
      rw [hsqrt_mul]
    _ = Real.sqrt (((k + 1 : ℕ) : ℝ)) *
          ((1 : NNReal : ℝ) * (1 + Real.sqrt ((((k + 1 : ℕ) : ℝ) / (ν : ℝ)))) ) := by
      ring

/-- Helper for Proposition 7.34: every stage-scaled penalty coefficient is strictly larger than
`1`, which is the dual-norm bound used by the current unit-weight schedule. -/
lemma one_lt_stageScaledPenaltyWeight
    (k : ℕ) :
    1 < stageScaledPenaltyWeight ν k := by
  rw [stageScaledPenaltyWeight_eq_sqrt_add_div (ν := ν) k]
  have hsqrt_ge_one : 1 ≤ Real.sqrt (((k + 1 : ℕ) : ℝ)) := by
    have hcast : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    rw [← show Real.sqrt (1 : ℝ) = (1 : ℝ) by norm_num]
    exact Real.sqrt_le_sqrt hcast
  have hdiv_pos : 0 < ((k : ℝ) + 1) / Real.sqrt (ν : ℝ) := by
    exact div_pos (by positivity) (Real.sqrt_pos.2 ν.2)
  -- The positive `ν` correction pushes the explicit coefficient strictly above the unit threshold.
  linarith

/-- Helper for Proposition 7.34: the stage-scaled penalty coefficients grow monotonically with the
stage index. -/
lemma stageScaledPenaltyWeight_mono :
    Monotone (stageScaledPenaltyWeight ν) := by
  intro i j hij
  rw [stageScaledPenaltyWeight_eq_sqrt_add_div (ν := ν) i,
    stageScaledPenaltyWeight_eq_sqrt_add_div (ν := ν) j]
  have hcast : (((i + 1 : ℕ) : ℝ)) ≤ (((j + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_le_succ hij
  have hsqrt :
      Real.sqrt (((i + 1 : ℕ) : ℝ)) ≤ Real.sqrt (((j + 1 : ℕ) : ℝ)) := by
    exact Real.sqrt_le_sqrt hcast
  have hdiv :
      ((i : ℝ) + 1) / Real.sqrt (ν : ℝ) ≤
        ((j : ℝ) + 1) / Real.sqrt (ν : ℝ) := by
    have hν_sqrt_pos : 0 < Real.sqrt (ν : ℝ) := Real.sqrt_pos.2 ν.2
    exact (div_le_div_right hν_sqrt_pos).2 (by exact_mod_cast Nat.succ_le_succ hij)
  -- Both explicit summands are monotone, so the full stage coefficient is monotone as well.
  linarith

/-- Helper for Proposition 7.34: the unit dual-norm control on the scaled barrier direction is
strictly admissible for every stage penalty coefficient. -/
lemma barrierDirectionDualNorm_lt_stageScaledPenaltyWeight
    [HasPositiveDefiniteHessianOn P0 F]
    (hψ_dual_bound :
      ∀ x : P0,
        HessianDualLocalNorm.ofPosDefMem F x.2
            (InnerProductSpace.toDualMap ℝ E (∇ ψ x)) ≤
          ψ x)
    (i : ℕ) :
    HessianDualLocalNorm.ofPosDefMem F (method.iterate_mem i)
        (InnerProductSpace.toDualMap ℝ E
          (barrierSubgradientDirection ψ (method.iterate i : E))) <
      stageScaledPenaltyWeight ν i := by
  have hunit :=
    method.barrierDirectionDualNorm_le_one hψ_dual_bound (method.iterate i)
  -- Compare the unit dual-norm control with the explicit lower bound `1 < βᵢ`.
  exact lt_of_le_of_lt hunit (method.one_lt_stageScaledPenaltyWeight i)

/-- Helper for Proposition 7.34: after clearing the averaging denominator, the stage-`i`
Algorithm 7.14 iterate maximizes the exact Chapter 7 shifted support payoff with the stage-scaled
penalty coefficient. -/
lemma step_isMaxOn_stagePayoff
    (i : ℕ) :
    let β : {β : ℝ // 0 < β} := ⟨stageScaledPenaltyWeight ν i, stageScaledPenaltyWeight_pos (ν := ν) i⟩
    let s : StrongDual ℝ E :=
      ∑ j ∈ Finset.range (i + 1),
        InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E))
    IsMaxOn
      (fun v : E ↦ s (v - x0) - β * (F v - F x0))
      P0
      (method.iterate (i + 1) : E) := by
  dsimp
  rw [isMaxOn_iff]
  intro v hv
  have hstep := (isMaxOn_iff.mp (method.step_isMax i)) v hv
  have hi_pos : 0 < ((i : ℝ) + 1) := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hstep hi_pos.le
  have hi_ne : ((i : ℝ) + 1) ≠ 0 := ne_of_gt hi_pos
  let c : ℝ :=
    ∑ j ∈ Finset.range (i + 1),
      (InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E)))
        ((x0 : E) - (method.iterate j : E))
  have hrewrite :
      ∀ w : E,
        ((i : ℝ) + 1) * method.stepObjective i w =
          (∑ j ∈ Finset.range (i + 1),
              (InnerProductSpace.toDualMap ℝ E
                (barrierSubgradientDirection ψ (method.iterate j : E))) (w - x0)) -
            stageScaledPenaltyWeight ν i * (F w - F x0) + c := by
    intro w
    rw [BarrierSubgradientMethod.stepObjective_def, barrierSubgradientStepObjective_apply,
      stageScaledPenaltyWeight]
    have hsum :
        ∑ j ∈ Finset.range (i + 1),
            inner ℝ (barrierSubgradientDirection ψ (method.iterate j : E))
              (w - (method.iterate j : E)) =
          (∑ j ∈ Finset.range (i + 1),
              (InnerProductSpace.toDualMap ℝ E
                (barrierSubgradientDirection ψ (method.iterate j : E))) (w - x0)) +
            c := by
      calc
        ∑ j ∈ Finset.range (i + 1),
            inner ℝ (barrierSubgradientDirection ψ (method.iterate j : E))
              (w - (method.iterate j : E)) =
            ∑ j ∈ Finset.range (i + 1),
              ((InnerProductSpace.toDualMap ℝ E
                    (barrierSubgradientDirection ψ (method.iterate j : E))) (w - x0) +
                (InnerProductSpace.toDualMap ℝ E
                    (barrierSubgradientDirection ψ (method.iterate j : E)))
                  ((x0 : E) - (method.iterate j : E))) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hsplit :
                  w - (method.iterate j : E) = (w - x0) + ((x0 : E) - (method.iterate j : E)) := by
                abel
              rw [show inner ℝ (barrierSubgradientDirection ψ (method.iterate j : E))
                    (w - (method.iterate j : E)) =
                  (InnerProductSpace.toDualMap ℝ E
                    (barrierSubgradientDirection ψ (method.iterate j : E)))
                    (w - (method.iterate j : E)) by rfl]
              rw [hsplit, map_add]
        _ =
            (∑ j ∈ Finset.range (i + 1),
                (InnerProductSpace.toDualMap ℝ E
                  (barrierSubgradientDirection ψ (method.iterate j : E))) (w - x0)) +
              ∑ j ∈ Finset.range (i + 1),
                (InnerProductSpace.toDualMap ℝ E
                  (barrierSubgradientDirection ψ (method.iterate j : E)))
                  ((x0 : E) - (method.iterate j : E)) := by
              rw [Finset.sum_add_distrib]
        _ = _ := by
              simp [c]
    calc
      ((i : ℝ) + 1) *
          ((1 / ((i : ℝ) + 1)) *
              ∑ j ∈ Finset.range (i + 1),
                inner ℝ (barrierSubgradientDirection ψ (method.iterate j : E))
                  (w - (method.iterate j : E)) -
            barrierSubgradientPenaltyWeight ν i * (F w - F x0)) =
          ∑ j ∈ Finset.range (i + 1),
            inner ℝ (barrierSubgradientDirection ψ (method.iterate j : E))
              (w - (method.iterate j : E)) -
            (((i : ℝ) + 1) * barrierSubgradientPenaltyWeight ν i) * (F w - F x0) := by
            field_simp [hi_ne]
            ring
      _ =
          ((∑ j ∈ Finset.range (i + 1),
                (InnerProductSpace.toDualMap ℝ E
                  (barrierSubgradientDirection ψ (method.iterate j : E))) (w - x0)) +
              c) -
            (((i : ℝ) + 1) * barrierSubgradientPenaltyWeight ν i) * (F w - F x0) := by
            rw [hsum]
      _ =
          (∑ j ∈ Finset.range (i + 1),
              (InnerProductSpace.toDualMap ℝ E
                (barrierSubgradientDirection ψ (method.iterate j : E))) (w - x0)) -
            stageScaledPenaltyWeight ν i * (F w - F x0) + c := by
            simp [stageScaledPenaltyWeight]
            ring
  rw [hrewrite v, hrewrite (method.iterate (i + 1) : E)] at hscaled
  linarith

/-- Helper for Proposition 7.34: the stage-`i` successor iterate is the canonical `Argmaxβ`
point for the reachable pair `(βᵢ, sᵢ₊₁)` determined by Algorithm 7.14. -/
lemma iterate_succ_memArgmax_stagePayoff
    (i : ℕ) :
    let β : {β : ℝ // 0 < β} := ⟨stageScaledPenaltyWeight ν i, stageScaledPenaltyWeight_pos (ν := ν) i⟩
    let s : StrongDual ℝ E :=
      ∑ j ∈ Finset.range (i + 1),
        InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E))
    (method.iterate (i + 1) : E) ∈ Argmaxβ P0 F β s := by
  dsimp
  rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff]
  refine ⟨method.iterate_mem (i + 1), ?_⟩
  have hmax := method.step_isMaxOn_stagePayoff i
  refine isMaxOn_iff.mpr ?_
  intro v hv
  have hvmax := (isMaxOn_iff.mp hmax) v hv
  -- Remove the constant shift by `x0` to match the raw `Argmaxβ` maximand.
  simpa [smoothedPrimalObjectiveMaximand, map_sub, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc, mul_comm, mul_left_comm, mul_assoc] using hvmax

/-- Helper for Proposition 7.34: the reachable stage successor is the unique `Argmaxβ` point for
the stage pair `(βᵢ, sᵢ₊₁)`. -/
lemma iterate_succ_uniqueArgmax_stagePayoff
    [IsSelfConcordantBarrierOnWith P0 (ν : NNReal) F]
    [HasPositiveDefiniteHessianOn P0 F]
    (i : ℕ) :
    let β : {β : ℝ // 0 < β} := ⟨stageScaledPenaltyWeight ν i, stageScaledPenaltyWeight_pos (ν := ν) i⟩
    let s : StrongDual ℝ E :=
      ∑ j ∈ Finset.range (i + 1),
        InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E))
    ∀ u : E, u ∈ Argmaxβ P0 F β s → u = (method.iterate (i + 1) : E) := by
  intro β s u hu
  let xStar : P0 := method.iterate (i + 1)
  let t : E := (InnerProductSpace.toDual ℝ E).symm s
  let c : E := -((β : ℝ)⁻¹) • t
  let oneIci : Set.Ici (0 : ℝ) := ⟨1, by positivity⟩
  have hraw_star :
      IsMaxOn (fun v : E ↦ s v - β * F v) P0 (xStar : E) := by
    -- Read the public stage maximizer on the raw Chapter 6 score surface.
    exact
      (isMaxOn_shifted_score_iff_textbook_payoff P0 F x0 β s (xStar : E)).mpr
        (method.step_isMaxOn_stagePayoff i)
  have hmaximand :
      smoothedPrimalObjectiveMaximand
          (ContinuousLinearMap.id ℝ (StrongDual ℝ E))
          0
          F
          (β : ℝ)
          s =
        (fun v : E ↦ s v - β * F v) := by
    -- The specialized `Argmaxβ` owner is exactly the raw score `v ↦ s v - β F v`.
    funext v
    simp [smoothedPrimalObjectiveMaximand]
  rcases (show u ∈ P0 ∧
      IsMaxOn (fun v : E ↦ s v - β * F v) P0 u by
        rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at hu
        rcases hu with ⟨hu_mem, hu_max⟩
        exact ⟨hu_mem, by simpa [hmaximand] using hu_max⟩) with ⟨hu_mem, hu_raw⟩
  have htilted_min :
      IsMinOn (centralPathPenaltyObjective c F oneIci) P0 (xStar : E) := by
    -- Converting the raw stage maximizer into a minimizer of the affine-tilted barrier exposes
    -- the first-order condition used to identify the active stage slope.
    rw [isMinOn_iff]
    intro v hv
    have hvmax := (isMaxOn_iff.mp hraw_star) v hv
    have hvmax' :
        -((β : ℝ) * centralPathPenaltyObjective c F oneIci v) ≤
          -((β : ℝ) * centralPathPenaltyObjective c F oneIci (xStar : E)) := by
      simpa [centralPathPenaltyObjective_apply, c, t, oneIci,
        InnerProductSpace.toDual_apply_apply, real_inner_comm, smul_eq_mul,
        mul_assoc, mul_left_comm, mul_comm, β.2.ne'] using hvmax
    linarith [show 0 < (β : ℝ) from β.2, hvmax']
  have hstage_gradient :
      ∇ F (xStar : E) = (β : ℝ)⁻¹ • t := by
    -- The tilted minimizer is stationary, so the active stage slope equals `β ∇F(x_{i+1})`.
    have hzero :
        (oneIci : ℝ) • c + ∇ F (xStar : E) = 0 := by
      simpa [oneIci] using
        centralPathPenaltyObjective_gradient_eq_zero_at_minimizer
          (dom := P0) (ν := (ν : NNReal)) (F := F) c oneIci htilted_min
    have hneg : ∇ F (xStar : E) = -c := by
      simpa using eq_neg_of_add_eq_zero_left hzero
    simpa [c] using hneg
  have hs_eq :
      s = (β : ℝ) • InnerProductSpace.toDualMap ℝ E (∇ F (xStar : E)) := by
    -- Push the stationary identity through the Riesz map to replace the stage covector by the
    -- barrier gradient at the active point.
    ext v
    have hs_apply :
        s v =
          ((β : ℝ) • InnerProductSpace.toDualMap ℝ E (∇ F (xStar : E))) v := by
      calc
        s v = (InnerProductSpace.toDualMap ℝ E t) v := by
          simp [t]
        _ = (InnerProductSpace.toDualMap ℝ E ((β : ℝ) • ∇ F (xStar : E))) v := by
          rw [← hstage_gradient]
          simp [t]
        _ = ((β : ℝ) • InnerProductSpace.toDualMap ℝ E (∇ F (xStar : E))) v := by
          simp
    simpa using hs_apply
  have hraw_aux :
      ∀ z : E,
        s z - β * F z =
          -((β : ℝ) * auxiliaryCentralPathObjective F xStar 1 z) := by
    intro z
    have hs_apply :
        s z = (β : ℝ) * inner ℝ (∇ F (xStar : E)) z := by
      have hs_apply' := congrArg (fun φ : StrongDual ℝ E ↦ φ z) hs_eq
      simpa [InnerProductSpace.toDual_apply_apply] using hs_apply'
    rw [auxiliaryCentralPathObjective_apply, hs_apply]
    ring
  have haux_min_of_raw_max :
      ∀ {z : E}, z ∈ P0 →
        IsMaxOn (fun v : E ↦ s v - β * F v) P0 z →
          IsMinOn (auxiliaryCentralPathObjective F xStar 1) P0 z := by
    intro z hz hz_max
    rw [isMinOn_iff]
    intro v hv
    have hmax := (isMaxOn_iff.mp hz_max) v hv
    have hmax' :
        -((β : ℝ) * auxiliaryCentralPathObjective F xStar 1 v) ≤
          -((β : ℝ) * auxiliaryCentralPathObjective F xStar 1 z) := by
      simpa [hraw_aux v, hraw_aux z] using hmax
    linarith [show 0 < (β : ℝ) from β.2, hmax']
  have hxStar_min_aux :
      IsMinOn (auxiliaryCentralPathObjective F xStar 1) P0 (xStar : E) :=
    haux_min_of_raw_max xStar.2 hraw_star
  have hu_min_aux :
      IsMinOn (auxiliaryCentralPathObjective F xStar 1) P0 u :=
    haux_min_of_raw_max hu_mem hu_raw
  let uP0 : P0 := ⟨u, hu_mem⟩
  have hself_aux :
      IsSelfConcordantOnWith P0 (ν : NNReal) (auxiliaryCentralPathObjective F xStar 1) :=
    auxiliaryCentralPathObjective_isSelfConcordantOnWith
      (f := F) (Mf := (ν : NNReal)) xStar 1
  have hu_eq : uP0 = xStar :=
    eq_of_isMinOn_of_isMinOn
      (dom := P0)
      (Mf := (ν : NNReal))
      (f := auxiliaryCentralPathObjective F xStar 1)
      hself_aux
      uP0
      xStar
      hu_min_aux
      hxStar_min_aux
  exact congrArg Subtype.val hu_eq

/-- Helper for Proposition 7.34: the reachable stage maximizer can be read directly on the
public affine-barrier payoff surface from Lemma 7.11. -/
lemma stageAffineBarrierRegularizedPayoff_isMaxOn
    (i : ℕ) :
    let β : {β : ℝ // 0 < β} := ⟨stageScaledPenaltyWeight ν i, stageScaledPenaltyWeight_pos (ν := ν) i⟩
    let s : StrongDual ℝ E :=
      ∑ j ∈ Finset.range (i + 1),
        InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E))
    let ℓ : AffineMap ℝ E ℝ := s.toAffineMap
    IsMaxOn
      (affineBarrierRegularizedPayoff (x0 : E) (β : ℝ) ℓ F)
      P0
      (method.iterate (i + 1) : E) := by
  dsimp
  have hpayoff_max := method.step_isMaxOn_stagePayoff i
  -- Rewrite the raw stage payoff into the exact affine-regularized owner spelling.
  refine isMaxOn_iff.mpr ?_
  intro v hv
  have hvmax := (isMaxOn_iff.mp hpayoff_max) v hv
  dsimp at hvmax ⊢
  simpa [affineBarrierRegularizedPayoff_def, map_sub, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc, mul_comm, mul_left_comm, mul_assoc] using hvmax

/-- Helper for Proposition 7.34: the public Lemma 7.11 segment inequality applies to the reachable
stage payoff for Algorithm 7.14. -/
lemma pointwiseStageGap_le_from_segment
    [IsSelfConcordantBarrierOnWith P0 (ν : NNReal) F]
    (k : ℕ) (y : P0) {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    let β : {β : ℝ // 0 < β} := ⟨stageScaledPenaltyWeight ν k, stageScaledPenaltyWeight_pos (ν := ν) k⟩
    let s : StrongDual ℝ E :=
      ∑ j ∈ Finset.range (k + 1),
        InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E))
    α * s ((y : E) - x0) + (β : ℝ) * (ν : ℝ) * Real.log (1 - α) ≤
      Uβ P0 F (x0 : E) β s := by
  dsimp
  let hbarrier : IsSelfConcordantBarrierOnWith P0 ν F := inferInstance
  let hstd : IsStandardSelfConcordantOn P0 F := hbarrier.toIsStandardSelfConcordantOn
  let ℓ : AffineMap ℝ E ℝ := s.toAffineMap
  have hconv : Convex ℝ P0 := hstd.convex_domain
  have hxBeta_max := method.stageAffineBarrierRegularizedPayoff_isMaxOn k
  have hsegment_mem :
      ∀ ⦃x : E⦄, x ∈ P0 → ∀ ⦃a : ℝ⦄, a ∈ Set.Ico (0 : ℝ) 1 →
        (x0 : E) + a • (x - (x0 : E)) ∈ P0 := by
    intro x hx a ha
    have hline_mem : AffineMap.lineMap (x0 : E) x a ∈ P0 := by
      -- Convexity of the barrier domain keeps the whole segment inside `P0`.
      simpa [AffineMap.lineMap_apply_module] using
        hconv.lineMap_mem x0.2 hx ⟨ha.1, ha.2.le⟩
    simpa [AffineMap.lineMap_apply_module', add_comm] using hline_mem
  have hsegment :
      α * (ℓ (y : E) - ℓ (x0 : E)) + (β : ℝ) * (ν : ℝ) * Real.log (1 - α) ≤
        affineBarrierRegularizedPayoff (x0 : E) (β : ℝ) ℓ F (method.iterate (k + 1) : E) -
          ℓ (x0 : E) := by
    -- Feed the stage-maximizer and barrier segment bound into the public Lemma 7.11 owner API.
    simpa [mul_assoc] using
      regularized_gap_bound_along_segment
        (x0 := (x0 : E))
        (β := (β : ℝ))
        (ℓ := ℓ)
        (F := F)
        (P := P0)
        (xStar := (y : E))
        (xBeta := (method.iterate (k + 1) : E))
        (v := (ν : ℝ))
        β.2
        y.2
        hxBeta_max
        hsegment_mem
        (fun {x} hx {a} ha ↦
          hbarrier.segment_upper_bound_log_one_sub
            (x := (x0 : E)) (y := x) x0.2 hx ha)
        hα
  -- Rewrite both sides back into the reachable stage spelling used in Proposition 7.34.
  calc
    α * s ((y : E) - x0) + (β : ℝ) * (ν : ℝ) * Real.log (1 - α) ≤
        affineBarrierRegularizedPayoff (x0 : E) (β : ℝ) ℓ F (method.iterate (k + 1) : E) -
          ℓ (x0 : E) := by
      simpa [ℓ, map_sub, mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        hsegment
    _ = Uβ P0 F (x0 : E) β s := by
      -- The stage successor attains the `Uβ` value for this reachable pair `(β_k, s_(k+1))`.
      simpa [ℓ, affineBarrierRegularizedPayoff_def, map_sub, sub_eq_add_neg, add_comm,
        add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
        (supportFunctionApproximation_value_eq_of_memArgmax
          (hatP := P0)
          (F := F)
          (x0 := (x0 : E))
          (β := β)
          (s := s)
          (u := (method.iterate (k + 1) : E))
          (method.iterate_succ_memArgmax_stagePayoff k)).symm

/-- Helper for Proposition 7.34: the standard square-to-log scalar bridge upgrades an implicit
`max (log ...)` term to the explicit Chapter 7 logarithmic expression. -/
lemma logGapTerm_le_ofSquareGapBound
    {a b c : ℝ} (ha_nonneg : 0 ≤ a) (hc : 0 < c)
    (ha : a ≤ (Real.sqrt b + Real.sqrt c) ^ (2 : ℕ)) :
    max (Real.log (a / c)) 0 ≤ 2 * Real.log (1 + Real.sqrt (b / c)) := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (b / c) := Real.sqrt_nonneg _
  have hone_le : 1 ≤ 1 + Real.sqrt (b / c) := by
    linarith
  have hs_pos : 0 < 1 + Real.sqrt (b / c) := by
    positivity
  have hrhs_nonneg : 0 ≤ 2 * Real.log (1 + Real.sqrt (b / c)) := by
    have hlog_nonneg : 0 ≤ Real.log (1 + Real.sqrt (b / c)) :=
      Real.log_nonneg hone_le
    nlinarith
  have hsqrtc_pos : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsqrtc_ne : Real.sqrt c ≠ 0 := hsqrtc_pos.ne'
  have hdiv :
      a / c ≤ (1 + Real.sqrt (b / c)) ^ (2 : ℕ) := by
    -- Normalize the square bound by the positive scale `c`.
    calc
      a / c ≤ ((Real.sqrt b + Real.sqrt c) ^ (2 : ℕ)) / c := by
        exact div_le_div_of_nonneg_right ha hc.le
      _ = ((Real.sqrt b + Real.sqrt c) ^ (2 : ℕ)) / (Real.sqrt c) ^ (2 : ℕ) := by
        rw [Real.sq_sqrt hc.le]
      _ = ((Real.sqrt b + Real.sqrt c) / Real.sqrt c) ^ (2 : ℕ) := by
        field_simp [pow_two, hsqrtc_ne]
      _ = (Real.sqrt b / Real.sqrt c + 1) ^ (2 : ℕ) := by
        congr 1
        field_simp [hsqrtc_ne]
      _ = (Real.sqrt (b / c) + 1) ^ (2 : ℕ) := by
        rw [Real.sqrt_div' b hc.le]
      _ = (1 + Real.sqrt (b / c)) ^ (2 : ℕ) := by
        ring
  by_cases hpos : 0 < a / c
  · -- In the positive case, compare logarithms after the normalization above.
    refine (max_le_iff.mpr ?_)
    constructor
    · calc
        Real.log (a / c) ≤ Real.log ((1 + Real.sqrt (b / c)) ^ (2 : ℕ)) :=
          Real.log_le_log hpos hdiv
        _ = Real.log ((1 + Real.sqrt (b / c)) * (1 + Real.sqrt (b / c))) := by
          rw [pow_two]
        _ = Real.log (1 + Real.sqrt (b / c)) + Real.log (1 + Real.sqrt (b / c)) := by
          rw [Real.log_mul hs_pos.ne' hs_pos.ne']
        _ = 2 * Real.log (1 + Real.sqrt (b / c)) := by
          ring
    · exact hrhs_nonneg
  · have hnonpos : a / c ≤ 0 := le_of_not_gt hpos
    have hquot_nonneg : 0 ≤ a / c := by
      exact div_nonneg ha_nonneg hc.le
    have hquot_zero : a / c = 0 := le_antisymm hnonpos hquot_nonneg
    have hlog_zero : Real.log (a / c) = 0 := by
      simp [hquot_zero]
    simpa [hlog_zero] using hrhs_nonneg

/-- Helper for Proposition 7.34: optimizing the reachable segment inequality also yields the usual
square-gap control of the affine dual evaluation. -/
lemma reachableDualEval_squareGap_from_segment
    [IsSelfConcordantBarrierOnWith P0 (ν : NNReal) F]
    (k : ℕ) (y : P0) :
    let β : {β : ℝ // 0 < β} := ⟨stageScaledPenaltyWeight ν k, stageScaledPenaltyWeight_pos (ν := ν) k⟩
    let s : StrongDual ℝ E :=
      ∑ j ∈ Finset.range (k + 1),
        InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E))
    s ((y : E) - x0) ≤
      (Real.sqrt (Uβ P0 F (x0 : E) β s) + Real.sqrt ((β : ℝ) * (ν : ℝ))) ^ (2 : ℕ) := by
  dsimp
  let Δ : ℝ :=
    (∑ j ∈ Finset.range (k + 1),
      InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E)))
      ((y : E) - x0)
  let A : ℝ :=
    Uβ P0 F (x0 : E)
      ⟨stageScaledPenaltyWeight ν k, stageScaledPenaltyWeight_pos (ν := ν) k⟩
      (∑ j ∈ Finset.range (k + 1),
        InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E)))
  let c : ℝ :=
    stageScaledPenaltyWeight ν k * (ν : ℝ)
  have hc : 0 < c := by
    simpa [c] using
      mul_pos (stageScaledPenaltyWeight_pos (ν := ν) k) (show 0 < (ν : ℝ) from ν.2)
  have hA : 0 ≤ A := by
    simpa [A] using method.reachableUbetaValue_nonneg k
  by_cases hsmall : Δ ≤ c
  · -- When the affine gap is already at most `β_k ν`, the square bound is immediate.
    have hc_bound : c ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
      nlinarith [hA, hc.le, Real.sq_sqrt hA, Real.sq_sqrt hc.le,
        Real.sqrt_nonneg A, Real.sqrt_nonneg c]
    have hbound : Δ ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
      linarith
    simpa [Δ, A, c] using hbound
  · -- Otherwise choose the square-root segment parameter from the Chapter 7 optimization trick.
    have hlarge : c < Δ := lt_of_not_ge hsmall
    have hΔ_pos : 0 < Δ := lt_trans hc hlarge
    let α : ℝ := 1 - Real.sqrt c / Real.sqrt Δ
    have hsqrt_ratio_lt_one : Real.sqrt c / Real.sqrt Δ < 1 := by
      have hsqrt_lt : Real.sqrt c < Real.sqrt Δ := Real.sqrt_lt_sqrt hc.le hlarge
      exact (div_lt_one (Real.sqrt_pos.2 hΔ_pos)).2 hsqrt_lt
    have hα_mem : α ∈ Set.Ico (0 : ℝ) 1 := by
      constructor
      · dsimp [α]
        linarith
      · dsimp [α]
        have hratio_pos : 0 < Real.sqrt c / Real.sqrt Δ := by
          positivity
        linarith
    have hsegment : α * Δ + c * Real.log (1 - α) ≤ A := by
      -- Apply the reachable fixed-stage segment inequality at the optimized parameter.
      simpa [Δ, A, c] using method.pointwiseStageGap_le_from_segment k y hα_mem
    have hone_sub_alpha : 1 - α = Real.sqrt c / Real.sqrt Δ := by
      dsimp [α]
      ring
    have hlog_bound : -Real.log (1 - α) ≤ α / (1 - α) :=
      neg_log_one_sub_le_div_of_mem_Ico hα_mem
    have hlog_term : -c * Real.log (1 - α) ≤ c * α / (1 - α) := by
      have hmul := mul_le_mul_of_nonneg_left hlog_bound hc.le
      have hmul' : c * (-Real.log (1 - α)) ≤ c * (α / (1 - α)) := hmul
      convert hmul' using 1
      · ring
      · ring
    have hmain : α * Δ - c * α / (1 - α) ≤ A := by
      nlinarith [hsegment, hlog_term]
    have hexpr :
        α * Δ - c * α / (1 - α) = (Real.sqrt Δ - Real.sqrt c) ^ (2 : ℕ) := by
      let s : ℝ := Real.sqrt Δ
      let t : ℝ := Real.sqrt c
      have hs_pos : 0 < s := by
        dsimp [s]
        exact Real.sqrt_pos.2 hΔ_pos
      have ht_pos : 0 < t := by
        dsimp [t]
        exact Real.sqrt_pos.2 hc
      have hs_ne : s ≠ 0 := hs_pos.ne'
      have ht_ne : t ≠ 0 := ht_pos.ne'
      have hα_def : α = 1 - t / s := by
        dsimp [α, s, t]
      have hΔ_sq : Δ = s ^ (2 : ℕ) := by
        dsimp [s]
        simpa [pow_two] using (Real.sq_sqrt hΔ_pos.le).symm
      have hc_sq : c = t ^ (2 : ℕ) := by
        dsimp [t]
        simpa [pow_two] using (Real.sq_sqrt hc.le).symm
      have hexpr_st :
          α * Δ - c * α / (1 - α) = (s - t) ^ (2 : ℕ) := by
        rw [hα_def, hΔ_sq, hc_sq]
        have hdenom : 1 - (1 - t / s) = t / s := by
          ring
        rw [hdenom]
        field_simp [hs_ne, ht_ne]
      simpa [s, t] using hexpr_st
    have hsquare : (Real.sqrt Δ - Real.sqrt c) ^ (2 : ℕ) ≤ A := by
      rw [← hexpr]
      exact hmain
    have hsqrt_sub_nonneg : 0 ≤ Real.sqrt Δ - Real.sqrt c := by
      exact sub_nonneg.mpr (Real.sqrt_le_sqrt hlarge.le)
    have hsqrt_le : Real.sqrt Δ - Real.sqrt c ≤ Real.sqrt A := by
      exact (Real.le_sqrt hsqrt_sub_nonneg hA).2 (by simpa [pow_two] using hsquare)
    have hsqrt_sum : Real.sqrt Δ ≤ Real.sqrt A + Real.sqrt c := by
      linarith
    have hbound : Δ ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
      have hsum_nonneg : 0 ≤ Real.sqrt A + Real.sqrt c := by
        positivity
      have hsq' : (Real.sqrt Δ) ^ (2 : ℕ) ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
        nlinarith [hsqrt_sum, hsum_nonneg, Real.sqrt_nonneg Δ]
      simpa [pow_two, Real.sq_sqrt hΔ_pos.le] using hsq'
    simpa [Δ, A, c] using hbound

/-- Helper for Proposition 7.34: optimizing the reachable fixed-stage segment inequality yields the
explicit Chapter 7 logarithmic control of the affine dual evaluation. -/
lemma reachableDualEval_le_stageValue_plusLogTerm
    [IsSelfConcordantBarrierOnWith P0 (ν : NNReal) F]
    (k : ℕ) (y : P0) :
    let β : {β : ℝ // 0 < β} := ⟨stageScaledPenaltyWeight ν k, stageScaledPenaltyWeight_pos (ν := ν) k⟩
    let s : StrongDual ℝ E :=
      ∑ j ∈ Finset.range (k + 1),
        InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E))
    s ((y : E) - x0) ≤
      Uβ P0 F (x0 : E) β s +
        (β : ℝ) * (ν : ℝ) *
          (1 + 2 * Real.log (1 + Real.sqrt (Uβ P0 F (x0 : E) β s / ((β : ℝ) * (ν : ℝ))))) := by
  dsimp
  let Δ : ℝ :=
    (∑ j ∈ Finset.range (k + 1),
      InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E)))
      ((y : E) - x0)
  let A : ℝ :=
    Uβ P0 F (x0 : E)
      ⟨stageScaledPenaltyWeight ν k, stageScaledPenaltyWeight_pos (ν := ν) k⟩
      (∑ j ∈ Finset.range (k + 1),
        InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E)))
  let c : ℝ :=
    stageScaledPenaltyWeight ν k * (ν : ℝ)
  have hc : 0 < c := by
    simpa [c] using
      mul_pos (stageScaledPenaltyWeight_pos (ν := ν) k) (show 0 < (ν : ℝ) from ν.2)
  have hA : 0 ≤ A := by
    simpa [A] using method.reachableUbetaValue_nonneg k
  have hlogGap :
      Δ ≤ A + c * (1 + max (Real.log (Δ / c)) 0) := by
    by_cases hsmall : Δ ≤ c
    · -- In the small-gap regime the positive correction already dominates `Δ`.
      have hmax_nonneg : 0 ≤ max (Real.log (Δ / c)) 0 := le_max_right _ _
      have htail_nonneg : 0 ≤ c * max (Real.log (Δ / c)) 0 := by
        exact mul_nonneg hc.le hmax_nonneg
      have hgap : Δ ≤ A + c * (1 + max (Real.log (Δ / c)) 0) := by
        linarith
      exact hgap
    · -- Otherwise choose `α = 1 - c / Δ` to rewrite the segment inequality into log form.
      have hlarge : c < Δ := lt_of_not_ge hsmall
      have hΔ_pos : 0 < Δ := lt_trans hc hlarge
      let α : ℝ := 1 - c / Δ
      have hα_mem : α ∈ Set.Ico (0 : ℝ) 1 := by
        constructor
        · have hdiv_lt_one : c / Δ < 1 := by
            rw [div_lt_iff₀ hΔ_pos]
            simpa using hlarge
          dsimp [α]
          linarith
        · have hdiv_pos : 0 < c / Δ := div_pos hc hΔ_pos
          dsimp [α]
          linarith
      have hαineq : α * Δ + c * Real.log (1 - α) ≤ A := by
        -- Use the reachable segment inequality at the log-optimal parameter.
        simpa [Δ, A, c] using method.pointwiseStageGap_le_from_segment k y hα_mem
      have hone_sub : 1 - α = c / Δ := by
        dsimp [α]
        ring
      have hrewrite :
          α * Δ + c * Real.log (1 - α) = Δ - c - c * Real.log (Δ / c) := by
        calc
          α * Δ + c * Real.log (1 - α)
              = (1 - c / Δ) * Δ + c * Real.log (c / Δ) := by
                  rw [hone_sub]
          _ = Δ - c + c * Real.log (c / Δ) := by
                field_simp [hΔ_pos.ne']
          _ = Δ - c - c * Real.log (Δ / c) := by
                rw [Real.log_div hc.ne' hΔ_pos.ne', Real.log_div hΔ_pos.ne' hc.ne']
                ring
      have hlog_nonneg : 0 ≤ Real.log (Δ / c) := by
        have hratio_gt_one : 1 < Δ / c := by
          rw [one_lt_div hc]
          simpa using hlarge
        exact Real.log_nonneg hratio_gt_one.le
      have hgap : Δ ≤ A + c * (1 + Real.log (Δ / c)) := by
        rw [hrewrite] at hαineq
        linarith
      simpa [max_eq_left hlog_nonneg] using hgap
  have hsquareGap :
      Δ ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
    simpa [Δ, A, c] using method.reachableDualEval_squareGap_from_segment k y
  by_cases hΔ_nonneg : 0 ≤ Δ
  · -- Replace the implicit `max (log ...)` term by the explicit square-root expression.
    have hlogTerm :
        max (Real.log (Δ / c)) 0 ≤ 2 * Real.log (1 + Real.sqrt (A / c)) :=
      logGapTerm_le_ofSquareGapBound hΔ_nonneg hc hsquareGap
    have herror :
        c * (1 + max (Real.log (Δ / c)) 0) ≤
          c * (1 + 2 * Real.log (1 + Real.sqrt (A / c))) := by
      have hinside :
          1 + max (Real.log (Δ / c)) 0 ≤
            1 + 2 * Real.log (1 + Real.sqrt (A / c)) := by
        linarith
      exact mul_le_mul_of_nonneg_left hinside hc.le
    calc
      Δ ≤ A + c * (1 + max (Real.log (Δ / c)) 0) := hlogGap
      _ ≤ A + c * (1 + 2 * Real.log (1 + Real.sqrt (A / c))) := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left herror A
  · -- If the affine gap is nonpositive, the explicit right-hand side is already nonnegative.
    have hΔ_nonpos : Δ ≤ 0 := le_of_not_ge hΔ_nonneg
    have hlog_nonneg : 0 ≤ Real.log (1 + Real.sqrt (A / c)) := by
      have hone_le : 1 ≤ 1 + Real.sqrt (A / c) := by
        have hsqrt_nonneg : 0 ≤ Real.sqrt (A / c) := Real.sqrt_nonneg _
        linarith
      exact Real.log_nonneg hone_le
    have hrhs_nonneg : 0 ≤ A + c * (1 + 2 * Real.log (1 + Real.sqrt (A / c))) := by
      have htail_nonneg : 0 ≤ c * (1 + 2 * Real.log (1 + Real.sqrt (A / c))) := by
        have hinside_nonneg : 0 ≤ 1 + 2 * Real.log (1 + Real.sqrt (A / c)) := by
          linarith
        exact mul_nonneg hc.le hinside_nonneg
      linarith
    linarith

/-- Helper for Proposition 7.34: the unit-weight Chapter 7 gap rewrites as the reachable affine
dual sum evaluated at `y - x₀`, minus the fixed correction prefix coming from the iterates. -/
lemma reachableGap_eq_dualEval_minusCorrection
    (k : ℕ) (y : P0) :
    let sReach : StrongDual ℝ E :=
      ∑ i ∈ Finset.range (k + 1),
        InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate i : E))
    let corr : ℝ :=
      ∑ i ∈ Finset.range (k + 1),
        (InnerProductSpace.toDualMap ℝ E
          (barrierSubgradientDirection ψ (method.iterate i : E)))
          ((method.iterate i : E) - x0)
    barrierSubgradientGapFunction
        method.iterate
        (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
        (fun _ ↦ (1 : ℝ))
        k
        y =
      sReach ((y : E) - x0) - corr := by
  dsimp
  rw [barrierSubgradientGapFunction_apply]
  calc
    ∑ i ∈ Finset.range (k + 1),
        (1 : ℝ) *
          inner ℝ (barrierSubgradientDirection ψ (method.iterate i : E))
            ((y : E) - (method.iterate i : E)) =
      ∑ i ∈ Finset.range (k + 1),
        ((InnerProductSpace.toDualMap ℝ E
            (barrierSubgradientDirection ψ (method.iterate i : E))) ((y : E) - x0) -
          (InnerProductSpace.toDualMap ℝ E
            (barrierSubgradientDirection ψ (method.iterate i : E)))
            ((method.iterate i : E) - x0)) := by
      -- Split each stage contribution into the common `y - x₀` affine term and the fixed
      -- correction term at the current iterate.
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hsplit :
          (y : E) - (method.iterate i : E) = ((y : E) - x0) - ((method.iterate i : E) - x0) := by
        abel
      rw [show inner ℝ (barrierSubgradientDirection ψ (method.iterate i : E))
            ((y : E) - (method.iterate i : E)) =
          (InnerProductSpace.toDualMap ℝ E
            (barrierSubgradientDirection ψ (method.iterate i : E)))
            ((y : E) - (method.iterate i : E)) by
          rfl]
      rw [hsplit, map_sub]
      ring
    _ =
      (∑ i ∈ Finset.range (k + 1),
          (InnerProductSpace.toDualMap ℝ E
            (barrierSubgradientDirection ψ (method.iterate i : E))) ((y : E) - x0)) -
        ∑ i ∈ Finset.range (k + 1),
          (InnerProductSpace.toDualMap ℝ E
            (barrierSubgradientDirection ψ (method.iterate i : E)))
            ((method.iterate i : E) - x0) := by
      rw [Finset.sum_sub_distrib]
    _ =
      (∑ i ∈ Finset.range (k + 1),
          InnerProductSpace.toDualMap ℝ E
            (barrierSubgradientDirection ψ (method.iterate i : E))) ((y : E) - x0) -
        ∑ i ∈ Finset.range (k + 1),
          (InnerProductSpace.toDualMap ℝ E
            (barrierSubgradientDirection ψ (method.iterate i : E)))
            ((method.iterate i : E) - x0) := by
      rw [Finset.sum_apply]

/-- Helper for Proposition 7.34: a uniform real pointwise bound on the unit-weight gap numerator
immediately yields the corresponding normalized `EReal` maximal-gap ratio bound. -/
lemma maximalGapRatio_le_of_pointwiseGapBound
    (k : ℕ) {δ : ℝ}
    (hpoint :
      ∀ y : P0,
        barrierSubgradientGapFunction
            method.iterate
            (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
            (fun _ ↦ (1 : ℝ))
            k
            y ≤
          ((k : ℝ) + 1) * δ) :
    barrierSubgradientMaximalGap
        method.iterate
        (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
        (fun _ ↦ (1 : ℝ))
        k /
      ((k : ℝ) + 1) ≤
        (δ : EReal) := by
  have hk_pos : 0 < ((k : ℝ) + 1) := by
    positivity
  have hsup :
      barrierSubgradientMaximalGap
          method.iterate
          (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
          (fun _ ↦ (1 : ℝ))
          k ≤
        ((((k : ℝ) + 1) * δ : ℝ) : EReal) := by
    rw [barrierSubgradientMaximalGap_def]
    refine sSup_le ?_
    rintro _ ⟨y, rfl⟩
    -- Each pointwise gap evaluation is controlled by the assumed explicit numerator bound.
    exact_mod_cast hpoint y
  have hdiv :
      barrierSubgradientMaximalGap
          method.iterate
          (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
          (fun _ ↦ (1 : ℝ))
          k /
        ((k : ℝ) + 1) ≤
      ((((k : ℝ) + 1) * δ : ℝ) : EReal) / ((k : ℝ) + 1) := by
    exact EReal.div_le_div_right_of_nonneg (by exact_mod_cast hk_pos.le) hsup
  -- Cancel the positive normalization factor on the explicit numerator bound.
  have hcancel :
      ((((k : ℝ) + 1) * δ : ℝ) : EReal) / ((k : ℝ) + 1) = (δ : EReal) := by
    rw [EReal.coe_div]
    exact_mod_cast (div_eq_iff hk_pos.ne').2 (by ring)
  exact hcancel ▸ hdiv

/-- Helper for Proposition 7.34: the Chapter 7 log-average gap of the primal iterates is bounded
by the normalized maximal gap for the unit-weight barrier-subgradient sequence. -/
lemma log_average_gap_le_maximalGapRatio
    (xStar : P0) (hoptimal : IsMaxOn ψ P0 xStar)
    [IsSelfConcordantBarrierOnWith P0 (ν : NNReal) F]
    [HasPositiveDefiniteHessianOn P0 F]
    (hψ_concave : ConcaveOn ℝ P0 ψ)
    (k : ℕ) :
    (((Real.log (ψ xStar) -
          (Finset.sum (Finset.range (k + 1))
              (fun i ↦ Real.log (ψ (method.iterate i : E)))) /
            ((k : ℝ) + 1) : ℝ) : EReal)) ≤
      barrierSubgradientMaximalGap
          method.iterate
          (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
          (fun _ ↦ (1 : ℝ))
          k /
        ((k : ℝ) + 1) := by
  -- Rewrite the averaged logarithmic loss into the already-proved pointwise logarithmic-gap
  -- estimate specialized at the optimal point `xStar`.
  simpa [logarithmicTransform_apply, method.unitWeightCenterMass_eq_logAverage k] using
    method.logarithmicTransform_gap_le_maximalGapRatio hψ_concave k xStar

/-- Helper for Proposition 7.34: every feasible textbook payoff at the reachable base point `x₀`
is bounded above by the corresponding smoothed support value `Uβ`. -/
lemma supportPayoff_le_Ubeta_of_mem
    (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E) {u : E} (hu : u ∈ P0) :
    s (u - x0) - β * (F u - F x0) ≤ Uβ P0 F (x0 : E) β s := by
  have hscore :
      s u - β * F u ≤ sSup ((fun w : E ↦ s w - β * F w) '' P0) := by
    exact le_sSup (Set.mem_image_of_mem (fun w : E ↦ s w - β * F w) hu)
  -- Restore the shifted payoff spelling by adding back the common constant from `Uβ_apply`.
  rw [Uβ_apply]
  simpa [support_payoff_eq_shifted_score, add_comm, add_left_comm, add_assoc] using
    add_le_add_left hscore (-s x0 + β * F x0)

/-- Helper for Proposition 7.34: evaluating `Uβ` on the reachable stage pair `(βᵢ, sᵢ₊₁)` at the
actual stage maximizer rewrites it as the attained textbook payoff. -/
lemma reachableUbetaValue_eq_iteratePayoff
    (i : ℕ) :
    let β : {β : ℝ // 0 < β} := ⟨stageScaledPenaltyWeight ν i, stageScaledPenaltyWeight_pos (ν := ν) i⟩
    let s : StrongDual ℝ E :=
      ∑ j ∈ Finset.range (i + 1),
        InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E))
    Uβ P0 F (x0 : E) β s =
      s ((method.iterate (i + 1) : E) - x0) - (β : ℝ) * (F (method.iterate (i + 1) : E) - F x0) := by
  dsimp
  -- Read the reachable-stage successor as the attained `Argmaxβ` value.
  simpa using
    supportFunctionApproximation_value_eq_of_memArgmax
      (hatP := P0)
      (F := F)
      (x0 := (x0 : E))
      (β := ⟨stageScaledPenaltyWeight ν i, stageScaledPenaltyWeight_pos (ν := ν) i⟩)
      (s := ∑ j ∈ Finset.range (i + 1),
        InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E)))
      (u := (method.iterate (i + 1) : E))
      (method.iterate_succ_memArgmax_stagePayoff i)

/-- Helper for Proposition 7.34: each reachable-stage smoothed value is nonnegative because the
base point `x₀` is always a feasible comparison with zero shifted payoff. -/
lemma reachableUbetaValue_nonneg
    (i : ℕ) :
    let β : {β : ℝ // 0 < β} := ⟨stageScaledPenaltyWeight ν i, stageScaledPenaltyWeight_pos (ν := ν) i⟩
    let s : StrongDual ℝ E :=
      ∑ j ∈ Finset.range (i + 1),
        InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E))
    0 ≤ Uβ P0 F (x0 : E) β s := by
  dsimp
  -- Compare the reachable `Uβ` value with the feasible base point, whose shifted payoff vanishes.
  simpa using
    (method.supportPayoff_le_Ubeta_of_mem
      (β := ⟨stageScaledPenaltyWeight ν i, stageScaledPenaltyWeight_pos (ν := ν) i⟩)
      (s := ∑ j ∈ Finset.range (i + 1),
        InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E)))
      (u := (x0 : E))
      x0.2)

/-- Helper for Proposition 7.34: the reachable stage value `Uβ(βᵢ, sᵢ₊₁)` is exactly the
stage-scaled gap of the Chapter 5 penalty objective with frozen tilt
`cᵢ = -βᵢ⁻¹ sᵢ₊₁`. -/
lemma reachableStageValue_eq_scaledPenaltyGap
    (i : ℕ) :
    let β : {β : ℝ // 0 < β} := ⟨stageScaledPenaltyWeight ν i, stageScaledPenaltyWeight_pos (ν := ν) i⟩
    let s : StrongDual ℝ E :=
      ∑ j ∈ Finset.range (i + 1),
        InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E))
    let c : E := -((β : ℝ)⁻¹) • (InnerProductSpace.toDual ℝ E).symm s
    Uβ P0 F (x0 : E) β s =
      (β : ℝ) *
        (centralPathPenaltyObjective c F (1 : ℝ) (x0 : E) -
          centralPathPenaltyObjective c F (1 : ℝ) (method.iterate (i + 1) : E)) := by
  dsimp
  rw [method.reachableUbetaValue_eq_iteratePayoff i]
  have hinner (z : E) :
      inner ℝ
          (-((⟨stageScaledPenaltyWeight ν i, stageScaledPenaltyWeight_pos (ν := ν) i⟩ : {β : ℝ // 0 < β} : ℝ)⁻¹) •
            (InnerProductSpace.toDual ℝ E).symm
              (∑ j ∈ Finset.range (i + 1),
                InnerProductSpace.toDualMap ℝ E
                  (barrierSubgradientDirection ψ (method.iterate j : E))))
          z =
        -((⟨stageScaledPenaltyWeight ν i, stageScaledPenaltyWeight_pos (ν := ν) i⟩ : {β : ℝ // 0 < β} : ℝ)⁻¹) *
          (∑ j ∈ Finset.range (i + 1),
            InnerProductSpace.toDualMap ℝ E
              (barrierSubgradientDirection ψ (method.iterate j : E))) z := by
    -- Push the frozen stage tilt through the Riesz map once so the remaining identity is scalar.
    calc
      inner ℝ
          (-((⟨stageScaledPenaltyWeight ν i, stageScaledPenaltyWeight_pos (ν := ν) i⟩ : {β : ℝ // 0 < β} : ℝ)⁻¹) •
            (InnerProductSpace.toDual ℝ E).symm
              (∑ j ∈ Finset.range (i + 1),
                InnerProductSpace.toDualMap ℝ E
                  (barrierSubgradientDirection ψ (method.iterate j : E))))
          z =
          (starRingEnd ℝ)
              (-((⟨stageScaledPenaltyWeight ν i, stageScaledPenaltyWeight_pos (ν := ν) i⟩ : {β : ℝ // 0 < β} : ℝ)⁻¹)) *
            inner ℝ
              ((InnerProductSpace.toDual ℝ E).symm
                (∑ j ∈ Finset.range (i + 1),
                  InnerProductSpace.toDualMap ℝ E
                    (barrierSubgradientDirection ψ (method.iterate j : E))))
              z := by
        rw [inner_smul_left]
      _ =
          -((⟨stageScaledPenaltyWeight ν i, stageScaledPenaltyWeight_pos (ν := ν) i⟩ : {β : ℝ // 0 < β} : ℝ)⁻¹) *
            inner ℝ
              ((InnerProductSpace.toDual ℝ E).symm
                (∑ j ∈ Finset.range (i + 1),
                  InnerProductSpace.toDualMap ℝ E
                    (barrierSubgradientDirection ψ (method.iterate j : E))))
              z := by
        simp
      _ =
          -((⟨stageScaledPenaltyWeight ν i, stageScaledPenaltyWeight_pos (ν := ν) i⟩ : {β : ℝ // 0 < β} : ℝ)⁻¹) *
            (∑ j ∈ Finset.range (i + 1),
              InnerProductSpace.toDualMap ℝ E
                (barrierSubgradientDirection ψ (method.iterate j : E))) z := by
        rw [InnerProductSpace.toDual_symm_apply]
  -- Rewrite the penalty gap and clear the positive stage weight.
  have hβpos : 0 < stageScaledPenaltyWeight ν i := stageScaledPenaltyWeight_pos (ν := ν) i
  rw [centralPathPenaltyObjective_apply, centralPathPenaltyObjective_apply, hinner, hinner]
  field_simp [hβpos.ne']
  ring

/-- Helper for Proposition 7.34: changing only the time parameter of a fixed central-path penalty
objective changes the corresponding gap by the expected linear term. -/
lemma centralPathPenaltyGap_sameTimeShift
    {c u v : E} {τ τ' : ℝ} :
    centralPathPenaltyObjective c F τ' u - centralPathPenaltyObjective c F τ' v =
      centralPathPenaltyObjective c F τ u - centralPathPenaltyObjective c F τ v +
        (τ' - τ) * inner ℝ c (u - v) := by
  -- Expand both penalty values once; the entire shift is then a scalar rearrangement.
  rw [centralPathPenaltyObjective_apply, centralPathPenaltyObjective_apply,
    centralPathPenaltyObjective_apply, centralPathPenaltyObjective_apply, inner_sub_right]
  ring

/-- Helper for Proposition 7.34: the reachable affine dual sum and the correction prefix both
append exactly one new stage term when the history grows from `i + 1` to `i + 2`. -/
lemma reachableCorrectionPrefix_succ
    (i : ℕ) :
    let sReach : ℕ → StrongDual ℝ E := fun n ↦
      ∑ j ∈ Finset.range n,
        InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E))
    let corrReach : ℕ → ℝ := fun n ↦
      ∑ j ∈ Finset.range n,
        (InnerProductSpace.toDualMap ℝ E
          (barrierSubgradientDirection ψ (method.iterate j : E)))
          ((method.iterate j : E) - x0)
    let g : ℕ → StrongDual ℝ E := fun n ↦
      InnerProductSpace.toDualMap ℝ E
        (barrierSubgradientDirection ψ (method.iterate (n + 1) : E))
    sReach (i + 2) = sReach (i + 1) + g i ∧
      corrReach (i + 2) =
        corrReach (i + 1) + g i ((method.iterate (i + 1) : E) - x0) := by
  dsimp
  constructor
  · -- Expand the final summand in the reachable dual history.
    simp [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
  · -- Expand the final summand in the correction prefix with the same `range_succ` step.
    simp [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]

/-- Helper for Proposition 7.34: keeping the smoothing parameter fixed at `βᵢ`, the new reachable
dual stage `sᵢ₊₂ = sᵢ₊₁ + gᵢ` satisfies the one-step Lemma 7.10 `ω_*` upper model. -/
lemma reachableStageUpperModel_fixedBeta
    [IsSelfConcordantBarrierOnWith P0 (ν : NNReal) F]
    [HasPositiveDefiniteHessianOn P0 F]
    (hψ_dual_bound :
      ∀ x : P0,
        HessianDualLocalNorm.ofPosDefMem F x.2
            (InnerProductSpace.toDualMap ℝ E (∇ ψ x)) ≤
          ψ x)
    (i : ℕ) :
    let β : ℕ → {β : ℝ // 0 < β} :=
      fun n ↦ ⟨stageScaledPenaltyWeight ν n, stageScaledPenaltyWeight_pos (ν := ν) n⟩
    let sReach : ℕ → StrongDual ℝ E := fun n ↦
      ∑ j ∈ Finset.range n,
        InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E))
    let g : ℕ → StrongDual ℝ E := fun n ↦
      InnerProductSpace.toDualMap ℝ E
        (barrierSubgradientDirection ψ (method.iterate (n + 1) : E))
    let δ : ℕ → ℝ := fun n ↦
      HessianDualLocalNorm.ofPosDefMem F (method.iterate_mem (n + 1)) (g n)
    let τ : ℕ → Set.Iio (1 : ℝ) := fun n ↦
      ⟨δ n / (β n : ℝ), by
        have hlt : δ n < (β n : ℝ) := by
          have hunit :
              δ n ≤ 1 := by
            -- The logarithmic barrier direction is normalized to have local dual norm at most `1`.
            simpa [δ, g] using
              method.barrierDirectionDualNorm_le_one hψ_dual_bound (method.iterate (n + 1))
          exact lt_of_le_of_lt hunit (method.one_lt_stageScaledPenaltyWeight n)
        exact (div_lt_iff₀ (β n).2).2 (by simpa using hlt)⟩
    Uβ P0 F (x0 : E) (β i) (sReach (i + 2)) ≤
      Uβ P0 F (x0 : E) (β i) (sReach (i + 1)) +
        g i ((method.iterate (i + 1) : E) - x0) +
        (β i : ℝ) * selfConcordantOmegaStar (τ i) := by
  intro β sReach g δ τ
  let hbarrier : IsSelfConcordantBarrierOnWith P0 ν F := inferInstance
  let hstd : IsStandardSelfConcordantOn P0 F := hbarrier.toIsStandardSelfConcordantOn
  let hstdInt : IsStandardSelfConcordantOn (interior P0) F := by
    simpa [hstd.isOpen_domain.interior_eq] using hstd
  letI : IsStandardSelfConcordantOn (interior P0) F := hstdInt
  letI : HasPositiveDefiniteHessianOn (interior P0) F := by
    simpa [hstd.isOpen_domain.interior_eq] using
      (inferInstance : HasPositiveDefiniteHessianOn P0 F)
  have hP_int : P0 ⊆ interior P0 := by
    -- The barrier domain is open, so the reachable maximizers are still interior points.
    intro x hx
    simpa [hstd.isOpen_domain.interior_eq] using hx
  have hx_argmax :
      (method.iterate (i + 1) : E) ∈ Argmaxβ P0 F (β i) (sReach (i + 1)) := by
    -- The reachable stage successor is the unique active maximizer at stage `i`.
    simpa [β, sReach] using method.iterate_succ_memArgmax_stagePayoff i
  have hx_unique :
      ∀ u : E, u ∈ Argmaxβ P0 F (β i) (sReach (i + 1)) → u = (method.iterate (i + 1) : E) := by
    intro u hu
    -- Reuse the stage-`i` uniqueness API instead of rebuilding a selector surface.
    simpa [β, sReach] using method.iterate_succ_uniqueArgmax_stagePayoff i u hu
  have hg :
      δ i < (β i : ℝ) := by
    have hunit : δ i ≤ 1 := by
      -- The local dual norm of the new stage direction is bounded by `1`.
      simpa [δ, g] using
        method.barrierDirectionDualNorm_le_one hψ_dual_bound (method.iterate (i + 1))
    exact lt_of_le_of_lt hunit (method.one_lt_stageScaledPenaltyWeight i)
  have hupper_raw :
      Uβ P0 F (x0 : E) (β i) (sReach (i + 1) + g i) ≤
        Uβ P0 F (x0 : E) (β i) (sReach (i + 1)) +
          g i ((method.iterate (i + 1) : E) - x0) +
          (β i : ℝ) * selfConcordantOmegaStar (τ i) := by
    -- Apply the public Lemma 7.10 upper model at the unique reachable stage maximizer.
    simpa [δ, τ, selfConcordantOmegaStar] using
      (smoothSupportFunctionApproximation_hasFDerivAt_and_omegaStar_upper_bound_of_posDefMem
        (hatP := P0) (Q := P0) (F := F) (x0 := (x0 : E))
        (β := β i) (s := sReach (i + 1)) (x := (method.iterate (i + 1) : E))
        hx_argmax hx_unique hP_int).2 (g i) hg
  have hsucc := method.reachableCorrectionPrefix_succ i
  rcases hsucc with ⟨hsReach_succ, _⟩
  -- Rewrite `sᵢ₊₂` as `sᵢ₊₁ + gᵢ` so the one-step upper model matches the reachable notation.
  simpa [hsReach_succ] using hupper_raw

/-- Helper for Proposition 7.34: if the next reachable maximizer also satisfies
`F(xᵢ₊₂) - F(x₀) ≥ 0`, then increasing the smoothing parameter from `βᵢ` to `βᵢ₊₁` can only
decrease the reachable-stage `Uβ` value at the fixed covector `sᵢ₊₂`. -/
lemma reachableUbetaNextSmoothing_le_current_of_nonnegPenalty
    (i : ℕ)
    (hpenalty_nonneg : 0 ≤ F (method.iterate (i + 2) : E) - F x0) :
    let β : ℕ → {β : ℝ // 0 < β} :=
      fun n ↦ ⟨stageScaledPenaltyWeight ν n, stageScaledPenaltyWeight_pos (ν := ν) n⟩
    let sReach : ℕ → StrongDual ℝ E := fun n ↦
      ∑ j ∈ Finset.range n,
        InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E))
    Uβ P0 F (x0 : E) (β (i + 1)) (sReach (i + 2)) ≤
      Uβ P0 F (x0 : E) (β i) (sReach (i + 2)) := by
  dsimp
  have hβ_mono :
      stageScaledPenaltyWeight ν i ≤ stageScaledPenaltyWeight ν (i + 1) :=
    method.stageScaledPenaltyWeight_mono (Nat.le_succ i)
  calc
    Uβ P0 F (x0 : E)
        ⟨stageScaledPenaltyWeight ν (i + 1), stageScaledPenaltyWeight_pos (ν := ν) (i + 1)⟩
        (∑ j ∈ Finset.range (i + 2),
          InnerProductSpace.toDualMap ℝ E
            (barrierSubgradientDirection ψ (method.iterate j : E))) =
      (∑ j ∈ Finset.range (i + 2),
          InnerProductSpace.toDualMap ℝ E
            (barrierSubgradientDirection ψ (method.iterate j : E)))
          ((method.iterate (i + 2) : E) - x0) -
        stageScaledPenaltyWeight ν (i + 1) * (F (method.iterate (i + 2) : E) - F x0) := by
          -- Evaluate the next reachable `Uβ` value at its attained stage maximizer.
          simpa [Nat.add_assoc] using method.reachableUbetaValue_eq_iteratePayoff (i + 1)
    _ ≤
      (∑ j ∈ Finset.range (i + 2),
          InnerProductSpace.toDualMap ℝ E
            (barrierSubgradientDirection ψ (method.iterate j : E)))
          ((method.iterate (i + 2) : E) - x0) -
        stageScaledPenaltyWeight ν i * (F (method.iterate (i + 2) : E) - F x0) := by
          -- The only missing ingredient for smoothing monotonicity is the sign of the penalty gap.
          nlinarith
    _ ≤
      Uβ P0 F (x0 : E)
        ⟨stageScaledPenaltyWeight ν i, stageScaledPenaltyWeight_pos (ν := ν) i⟩
        (∑ j ∈ Finset.range (i + 2),
          InnerProductSpace.toDualMap ℝ E
            (barrierSubgradientDirection ψ (method.iterate j : E))) := by
          -- Any feasible payoff value is bounded above by the defining `Uβ` supremum.
          exact
            method.supportPayoff_le_Ubeta_of_mem
              (β := ⟨stageScaledPenaltyWeight ν i, stageScaledPenaltyWeight_pos (ν := ν) i⟩)
              (s := ∑ j ∈ Finset.range (i + 2),
                InnerProductSpace.toDualMap ℝ E
                  (barrierSubgradientDirection ψ (method.iterate j : E)))
              (u := (method.iterate (i + 2) : E))
              (method.iterate_mem (i + 2))

/-- Helper for Proposition 7.34: the unit-weight maximal-gap ratio is the only remaining rate
lemma needed to close the logarithmic-loss estimate. -/
lemma maximalGapRatio_le_explicitRate
    [IsSelfConcordantBarrierOnWith P0 (ν : NNReal) F]
    [HasPositiveDefiniteHessianOn P0 F]
    (hψ_dual_bound :
      ∀ x : P0,
        HessianDualLocalNorm.ofPosDefMem F x.2
            (InnerProductSpace.toDualMap ℝ E (∇ ψ x)) ≤
          ψ x)
    (k : ℕ) :
    barrierSubgradientMaximalGap
        method.iterate
        (fun i ↦ barrierSubgradientDirection ψ (method.iterate i : E))
        (fun _ ↦ (1 : ℝ))
        k /
      ((k : ℝ) + 1) ≤
        (barrierSubgradientRelativeAccuracyDelta (ν : ℝ) k : EReal) := by
  -- Route correction: the structural reduction from logarithmic loss to normalized maximal gap is
  -- now finished in `log_average_gap_le_maximalGapRatio`. The remaining frontier is the
  -- owner-level explicit numerator bound for the reachable affine gap surface.
  refine method.maximalGapRatio_le_of_pointwiseGapBound k ?_
  intro y
  let sReach : StrongDual ℝ E :=
    ∑ i ∈ Finset.range (k + 1),
      InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate i : E))
  let corr : ℝ :=
    ∑ i ∈ Finset.range (k + 1),
      (InnerProductSpace.toDualMap ℝ E
        (barrierSubgradientDirection ψ (method.iterate i : E)))
        ((method.iterate i : E) - x0)
  have hgap :=
    method.reachableGap_eq_dualEval_minusCorrection k y
  have hH :
      ∀ i : ℕ,
        (hessian F (method.iterate i : E)).det ≠ 0 := by
    intro i
    -- Positive definiteness of the barrier Hessian makes every reachable-stage Hessian invertible.
    exact HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem (method.iterate_mem i)
  have hω :
      ∀ i : ℕ,
        HessianDualLocalNorm.ofPosDefMem F (method.iterate_mem i)
            (InnerProductSpace.toDualMap ℝ E
              (barrierSubgradientDirection ψ (method.iterate i : E))) <
          stageScaledPenaltyWeight ν i := by
    intro i
    -- The unit dual-norm control is strictly admissible for the stage-scaled penalty schedule.
    simpa using method.barrierDirectionDualNorm_lt_stageScaledPenaltyWeight hψ_dual_bound i
  have hβ_mono :
      ∀ i : ℕ, stageScaledPenaltyWeight ν i ≤ stageScaledPenaltyWeight ν (i + 1) := by
    intro i
    -- The reachable smoothing parameters increase monotonically with the stage index.
    exact method.stageScaledPenaltyWeight_mono (Nat.le_succ i)
  have hvalue_nonneg := method.reachableUbetaValue_nonneg k
  have hstageBound := method.reachableDualEval_le_stageValue_plusLogTerm k y
  have hstageValueRewrite := method.reachableStageValue_eq_scaledPenaltyGap k
  have hstageTimeShift :
      let β : ℕ → {β : ℝ // 0 < β} :=
        fun n ↦ ⟨stageScaledPenaltyWeight ν n, stageScaledPenaltyWeight_pos (ν := ν) n⟩
      let sReachSeq : ℕ → StrongDual ℝ E := fun n ↦
        ∑ j ∈ Finset.range n,
          InnerProductSpace.toDualMap ℝ E (barrierSubgradientDirection ψ (method.iterate j : E))
      let cReach : E := -((β k : ℝ)⁻¹) • (InnerProductSpace.toDual ℝ E).symm (sReachSeq (k + 1))
      centralPathPenaltyObjective cReach F ((β (k + 1) : ℝ)⁻¹) (x0 : E) -
          centralPathPenaltyObjective cReach F ((β (k + 1) : ℝ)⁻¹) (method.iterate (k + 1) : E) =
        centralPathPenaltyObjective cReach F ((β k : ℝ)⁻¹) (x0 : E) -
            centralPathPenaltyObjective cReach F ((β k : ℝ)⁻¹) (method.iterate (k + 1) : E) +
          (((β (k + 1) : ℝ)⁻¹) - ((β k : ℝ)⁻¹)) *
            inner ℝ cReach ((x0 : E) - (method.iterate (k + 1) : E)) := by
    dsimp
    -- The varying-`β` part is now isolated as an exact fixed-tilt time-shift identity.
    simpa using
      (centralPathPenaltyGap_sameTimeShift
        (F := F)
        (c := -((⟨stageScaledPenaltyWeight ν k, stageScaledPenaltyWeight_pos (ν := ν) k⟩ : {β : ℝ // 0 < β} : ℝ)⁻¹) •
          (InnerProductSpace.toDual ℝ E).symm
            (∑ j ∈ Finset.range (k + 1),
              InnerProductSpace.toDualMap ℝ E
                (barrierSubgradientDirection ψ (method.iterate j : E))))
        (u := (x0 : E))
        (v := (method.iterate (k + 1) : E))
        (τ := ((⟨stageScaledPenaltyWeight ν k, stageScaledPenaltyWeight_pos (ν := ν) k⟩ : {β : ℝ // 0 < β} : ℝ)⁻¹))
        (τ' := ((⟨stageScaledPenaltyWeight ν (k + 1), stageScaledPenaltyWeight_pos (ν := ν) (k + 1)⟩ : {β : ℝ // 0 < β} : ℝ)⁻¹)))
  let _ := hH
  let _ := hω
  let _ := hβ_mono
  let _ := hvalue_nonneg
  let _ := hstageBound
  let _ := hstageValueRewrite
  let _ := hstageTimeShift
  let _ := hgap
  have hfixedStageUpper := method.reachableStageUpperModel_fixedBeta hψ_dual_bound k
  let _ := hfixedStageUpper
  have hcorrSucc := method.reachableCorrectionPrefix_succ k
  let _ := hcorrSucc
  -- TODO: the old local penalty-sign route was a dead end. The stabilized frontier is now:
  -- 1. the reachable affine gap already rewrites to `sReach (y - x₀) - corr`;
  -- 2. the fixed-stage reachable segment optimization is now local in
  --    `reachableDualEval_le_stageValue_plusLogTerm k y`;
  -- 3. the reachable stage value is now normalized by
  --    `reachableStageValue_eq_scaledPenaltyGap`, and the varying-`β` term is isolated by the
  --    exact fixed-tilt identity `centralPathPenaltyGap_sameTimeShift`;
  -- 4. the stage-scaled schedule already satisfies the determinant, admissibility, and monotonicity
  --    side conditions `hH`, `hω`, and `hβ_mono`;
  -- 5. the remaining blocker is the shifted corrected-potential telescope across the varying
  --    smoothing parameters `β_i`, i.e. a local proof of
  --    `Uβ(β_k,s_(k+1)) - corr ≤ ((k : ℝ) + 1) * barrierSubgradientRelativeAccuracyDelta ...`
  --    without introducing the unavailable sign premise
  --    `0 ≤ F (method.iterate n) - F x0`.
  sorry

/-- Helper for Proposition 7.34: the Chapter 7 log-average gap of the primal iterates is bounded
by the explicit rate `δ_k`. -/
lemma log_average_gap_le_explicit_rate
    (xStar : P0) (hoptimal : IsMaxOn ψ P0 xStar)
    [IsSelfConcordantBarrierOnWith P0 (ν : NNReal) F]
    [HasPositiveDefiniteHessianOn P0 F]
    (hψ_concave : ConcaveOn ℝ P0 ψ)
    (hψ_dual_bound :
      ∀ x : P0,
        HessianDualLocalNorm.ofPosDefMem F x.2
            (InnerProductSpace.toDualMap ℝ E (∇ ψ x)) ≤
          ψ x)
    (k : ℕ) :
    Real.log (ψ xStar) -
        (Finset.sum (Finset.range (k + 1)) (fun i ↦ Real.log (ψ (method.iterate i : E))) ) /
          ((k : ℝ) + 1) ≤
      barrierSubgradientRelativeAccuracyDelta (ν : ℝ) k := by
  have hstructural :=
    method.log_average_gap_le_maximalGapRatio xStar hoptimal hψ_concave k
  have hrate :=
    method.maximalGapRatio_le_explicitRate hψ_dual_bound k
  -- Combine the structural logarithmic-gap reduction with the isolated explicit maximal-gap-rate
  -- lemma.
  exact_mod_cast (le_trans hstructural hrate)

/-- Helper for Proposition 7.34: at each fixed index `k`, the iterate geometric mean is already a
relative-scale approximation with the explicit rate `δ_k`. -/
lemma positiveIterateGeometricMean_isRelativeScaleDeltaApproximation
    (xStar : P0) (hoptimal : IsMaxOn ψ P0 xStar)
    [IsSelfConcordantBarrierOnWith P0 (ν : NNReal) F]
    [HasPositiveDefiniteHessianOn P0 F]
    (hψ_concave : ConcaveOn ℝ P0 ψ)
    (hψ_dual_bound :
      ∀ x : P0,
        HessianDualLocalNorm.ofPosDefMem F x.2
            (InnerProductSpace.toDualMap ℝ E (∇ ψ x)) ≤
          ψ x)
    (k : ℕ) :
    IsRelativeScaleDeltaApproximation
      (ψ xStar)
      (barrierSubgradientRelativeAccuracyDelta (ν : ℝ) k)
      (method.iterateGeometricMean k) := by
  let ψpos : P0 → {r : ℝ // 0 < r} := fun x ↦ ⟨ψ x, method.ψ_pos x.2⟩
  let ψStar : {r : ℝ // 0 < r} := ⟨ψ xStar, method.ψ_pos xStar.2⟩
  refine ⟨
    method.ψ_pos xStar.2,
    barrierSubgradientRelativeAccuracyDelta_pos (show 0 < (ν : ℝ) from ν.2) k,
    ?_,
    ?_⟩
  · -- Optimality gives the upper half of the relative-scale approximation.
    exact method.iterateGeometricMean_le_optimal xStar hoptimal k
  · -- Exponentiating the log-gap estimate gives the lower half.
    simpa [iterateGeometricMean, ψpos, ψStar] using
      positiveIterateGeometricMean_ge_optimal_mul_exp_neg_rate_of_log_rate
        (ψ := ψpos)
        (x := method.iterate)
        ψStar
        k
        (method.log_average_gap_le_explicit_rate
          xStar hoptimal hψ_concave hψ_dual_bound k)

/-- Helper for Proposition 7.34: the natural size parameter attached to the target tolerance
`δ`, namely `⌈ν / δ²⌉`. -/
private def approximationScheduleSize (ν : NNReal) (δ : ℝ) : ℕ :=
  ⌈(ν : ℝ) / δ ^ (2 : ℕ)⌉₊

/-- Helper for Proposition 7.34: the logarithmic inflation factor used to invert the explicit
Chapter 7 rate. -/
private def approximationScheduleLogWeight (ν : NNReal) (δ : ℝ) : ℝ :=
  Real.log ((approximationScheduleSize ν δ : ℝ) + 2)

/-- Helper for Proposition 7.34: the explicit schedule used to upgrade the owner theorem from the
rate `δ_k` to a prescribed tolerance `δ`. -/
private def approximationSchedule (ν : NNReal) (δ : ℝ) : ℕ :=
  Nat.ceil
    (1600 * ((ν : ℝ) + (approximationScheduleSize ν δ : ℝ)) *
      approximationScheduleLogWeight ν δ ^ (12 : ℕ))

/-- Helper for Proposition 7.34: enlarging the tolerance parameter preserves the relative-scale
approximation property. -/
lemma relativeScaleDeltaApproximation_of_le_delta
    {phiStar δ₀ δ phiBar : ℝ}
    (h : IsRelativeScaleDeltaApproximation phiStar δ₀ phiBar)
    (hδ : δ₀ ≤ δ) :
    IsRelativeScaleDeltaApproximation phiStar δ phiBar := by
  rcases h with ⟨hphiStar_pos, hδ₀_pos, hupper, hlower⟩
  refine ⟨hphiStar_pos, lt_of_lt_of_le hδ₀_pos hδ, hupper, ?_⟩
  have hexp : Real.exp (-δ) ≤ Real.exp (-δ₀) := by
    exact Real.exp_le_exp_of_le (by linarith)
  -- Only the lower exponential threshold changes when the tolerance increases.
  calc
    phiStar * Real.exp (-δ) ≤ phiStar * Real.exp (-δ₀) := by
      exact mul_le_mul_of_nonneg_left hexp hphiStar_pos.le
    _ ≤ phiBar := hlower

/-- Helper for Proposition 7.34: the explicit Chapter 7 rate is at most `δ` at the
logarithmically inflated schedule `approximationSchedule ν δ`. -/
lemma explicit_rate_at_schedule_le_delta
    (ν : NNReal) (hν : 0 < (ν : ℝ)) {δ : ℝ} (hδ : 0 < δ) :
    barrierSubgradientRelativeAccuracyDelta (ν : ℝ) (approximationSchedule ν δ) ≤ δ := by
  set size : ℕ := approximationScheduleSize ν δ with hsize
  set L : ℝ := Real.log ((size : ℝ) + 2) with hL
  set N : ℕ := approximationSchedule ν δ with hN
  have hδ_sq_pos : 0 < δ ^ (2 : ℕ) := by positivity
  have hsize_ratio_pos : 0 < (ν : ℝ) / δ ^ (2 : ℕ) := by
    exact div_pos hν hδ_sq_pos
  have hsize_ge_one : 1 ≤ size := by
    rw [hsize, approximationScheduleSize]
    exact Nat.one_le_ceil_iff.mpr hsize_ratio_pos
  have hsize_nonneg : 0 ≤ (size : ℝ) := by positivity
  have hsize_pos : 0 < (size : ℝ) := by
    exact_mod_cast hsize_ge_one
  have hsize_ne : (size : ℝ) ≠ 0 := hsize_pos.ne'
  have hsize_lower :
      (ν : ℝ) / δ ^ (2 : ℕ) ≤ (size : ℝ) := by
    simpa [hsize, approximationScheduleSize] using
      (Nat.le_ceil ((ν : ℝ) / δ ^ (2 : ℕ)))
  have hL_ge_one : 1 ≤ L := by
    -- The logarithmic weight is already at least `1` because `size + 2 ≥ 3 > exp 1`.
    rw [hL, ← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have hthree_le : (3 : ℝ) ≤ (size : ℝ) + 2 := by
      have : (1 : ℝ) ≤ (size : ℝ) := by exact_mod_cast hsize_ge_one
      linarith
    exact le_trans (le_of_lt Real.exp_one_lt_three) hthree_le
  have hL_nonneg : 0 ≤ L := le_trans zero_le_one hL_ge_one
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL_ge_one
  have hL_ne : L ≠ 0 := hL_pos.ne'
  have hL_pow6_pos : 0 < L ^ (6 : ℕ) := by positivity
  have hL_pow12_pos : 0 < L ^ (12 : ℕ) := by positivity
  have hL_pow6_ge_one : 1 ≤ L ^ (6 : ℕ) := one_le_pow₀ hL_ge_one
  have hL_pow12_ge_one : 1 ≤ L ^ (12 : ℕ) := one_le_pow₀ hL_ge_one
  have hL_le_size_add_two : L ≤ (size : ℝ) + 2 := by
    -- The elementary bound `log t ≤ t - 1` controls the logarithm by the size parameter.
    rw [hL]
    have harg_pos : 0 < (size : ℝ) + 2 := by positivity
    have hlog_le :
        Real.log ((size : ℝ) + 2) ≤ ((size : ℝ) + 2) - 1 := by
      exact Real.log_le_sub_one_of_pos harg_pos
    linarith
  have hL_le_pow6 : L ≤ L ^ (6 : ℕ) := by
    calc
      L = L * 1 := by ring
      _ ≤ L * L ^ (5 : ℕ) := by
        gcongr
        exact one_le_pow₀ hL_ge_one
      _ = L ^ (6 : ℕ) := by ring
  have hsize_mul_Lpow6_le :
      (size : ℝ) * L ^ (6 : ℕ) ≤ ((size : ℝ) + 2) ^ (7 : ℕ) := by
    have hsize_le : (size : ℝ) ≤ (size : ℝ) + 2 := by linarith
    have hLpow6_le : L ^ (6 : ℕ) ≤ ((size : ℝ) + 2) ^ (6 : ℕ) := by
      gcongr
    exact mul_le_mul hsize_le hLpow6_le (by positivity) (by positivity)
  have hlog88_le_eleven : Real.log (88 : ℝ) ≤ 11 := by
    -- A coarse numerical bound `88 ≤ exp 11` is enough for the later scalar estimate.
    have htwo_lt_exp : (2 : ℝ) < Real.exp 1 := by
      simpa using (Real.add_one_lt_exp (1 : ℝ))
    have hpow_le : (88 : ℝ) ≤ (2 : ℝ) ^ (11 : ℕ) := by norm_num
    have hexp_pow :
        (2 : ℝ) ^ (11 : ℕ) ≤ (Real.exp 1) ^ (11 : ℕ) := by
      gcongr
    have hexp_le :
        (88 : ℝ) ≤ Real.exp 11 := by
      calc
        (88 : ℝ) ≤ (2 : ℝ) ^ (11 : ℕ) := hpow_le
        _ ≤ (Real.exp 1) ^ (11 : ℕ) := hexp_pow
        _ = Real.exp 11 := by
          simpa [show (11 : ℝ) = (1 : ℝ) * 11 by norm_num] using
            (Real.exp_nat_mul (1 : ℝ) 11).symm
    exact (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 88)).2 hexp_le
  have hlog_arg_bound_of_size
      (hsqrt :
        Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)) ≤
          57 * (size : ℝ) * L ^ (6 : ℕ)) :
      1 +
          Real.log
            (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))) ≤
        1 + Real.log 88 + 7 * L := by
    have harg_le :
        2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)) ≤
          88 * ((size : ℝ) + 2) ^ (7 : ℕ) := by
      have hpow_ge_one' : (1 : ℝ) ≤ ((size : ℝ) + 2) ^ (7 : ℕ) := by
        have hbase_ge_one : (1 : ℝ) ≤ (size : ℝ) + 2 := by linarith
        exact one_le_pow₀ hbase_ge_one
      calc
        2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))
            ≤ 2 + (3 / 2 : ℝ) * (57 * (size : ℝ) * L ^ (6 : ℕ)) := by
                gcongr
        _ ≤ 2 + 86 * ((size : ℝ) + 2) ^ (7 : ℕ) := by
              have hcoeff :
                  (3 / 2 : ℝ) * (57 * (size : ℝ) * L ^ (6 : ℕ)) ≤
                    86 * ((size : ℝ) + 2) ^ (7 : ℕ) := by
                have : (3 / 2 : ℝ) * 57 ≤ (86 : ℝ) := by norm_num
                nlinarith [hsize_mul_Lpow6_le, this]
              linarith
        _ ≤ 88 * ((size : ℝ) + 2) ^ (7 : ℕ) := by
              nlinarith [hpow_ge_one']
    have harg_pos :
        0 < 2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)) := by
      positivity
    have hlog_le :
        Real.log
            (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))) ≤
          Real.log (88 * ((size : ℝ) + 2) ^ (7 : ℕ)) := by
      exact Real.log_le_log harg_pos harg_le
    calc
      1 +
          Real.log
            (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)))
          ≤ 1 + Real.log (88 * ((size : ℝ) + 2) ^ (7 : ℕ)) := by
              linarith
      _ = 1 + Real.log 88 + 7 * L := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
            simp [hL, add_assoc, add_left_comm, add_comm]
  have hschedule_lower :
      1600 * ((ν : ℝ) + (size : ℝ)) * L ^ (12 : ℕ) ≤ (N : ℝ) + 1 := by
    have hcore :
        1600 * ((ν : ℝ) + (size : ℝ)) * L ^ (12 : ℕ) ≤ (N : ℝ) := by
      simpa [hN, approximationSchedule, approximationScheduleLogWeight, hL, size] using
        (Nat.le_ceil
          (1600 * ((ν : ℝ) + (size : ℝ)) * L ^ (12 : ℕ)))
    linarith
  have hschedule_upper :
      (N : ℝ) + 1 ≤ 1600 * ((ν : ℝ) + (size : ℝ)) * L ^ (12 : ℕ) + 2 := by
    have hcore :
        (N : ℝ) <
          1600 * ((ν : ℝ) + (size : ℝ)) * L ^ (12 : ℕ) + 1 := by
      have hnonneg :
          0 ≤ 1600 * ((ν : ℝ) + (size : ℝ)) * L ^ (12 : ℕ) := by positivity
      simpa [hN, approximationSchedule, approximationScheduleLogWeight, hL, size] using
        (Nat.ceil_lt_add_one hnonneg)
    linarith
  have hN_pos : 0 < (N : ℝ) + 1 := by positivity
  by_cases hδ_le_one : δ ≤ 1
  · -- For `δ ≤ 1`, the size parameter dominates `ν`, so the prefactor gains a linear `δ`.
    have hν_le_size : (ν : ℝ) ≤ (size : ℝ) := by
      have hδ_sq_le_one : δ ^ (2 : ℕ) ≤ 1 := by
        nlinarith [sq_nonneg (δ - 1)]
      have hratio_ge_nu : (ν : ℝ) ≤ (ν : ℝ) / δ ^ (2 : ℕ) := by
        refine (le_div_iff₀ hδ_sq_pos).2 ?_
        nlinarith [hν.le, hδ_sq_le_one]
      exact le_trans hratio_ge_nu hsize_lower
    have hratio_upper :
        (ν : ℝ) / ((N : ℝ) + 1) ≤ δ / (1600 * L ^ (12 : ℕ)) := by
      have hmain :
          (ν : ℝ) * (1600 * L ^ (12 : ℕ)) ≤ ((N : ℝ) + 1) * δ := by
        have hδ_sq_le_δ : δ ^ (2 : ℕ) ≤ δ := by
          nlinarith [hδ, hδ_le_one]
        nlinarith [hsize_lower, hschedule_lower]
      refine (div_le_iff₀ hN_pos).2 ?_
      nlinarith [hmain]
    have hsqrt_upper :
        Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) ≤ δ / (40 * L ^ (6 : ℕ)) := by
      have hsq :
          (ν : ℝ) / ((N : ℝ) + 1) ≤ (δ / (40 * L ^ (6 : ℕ))) ^ (2 : ℕ) := by
        have hratio_sq :
            (δ / (1600 * L ^ (12 : ℕ))) =
              (δ / (40 * L ^ (6 : ℕ))) ^ (2 : ℕ) / δ := by
          field_simp [hδ.ne', hL_ne]
          ring
        have hδ_mul :
            (δ / (40 * L ^ (6 : ℕ))) ^ (2 : ℕ) / δ ≤
              (δ / (40 * L ^ (6 : ℕ))) ^ (2 : ℕ) := by
          refine (div_le_iff₀ hδ).2 ?_
          nlinarith [sq_nonneg (δ / (40 * L ^ (6 : ℕ)))]
        rw [hratio_sq] at hratio_upper
        exact le_trans hratio_upper hδ_mul
      refine Real.sqrt_le_iff.2 ?_
      constructor
      · positivity
      · simpa [pow_two] using hsq
    have hsqrt_arg_upper :
        Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)) ≤
          57 * (size : ℝ) * L ^ (6 : ℕ) := by
      have hupper_size :
          (N : ℝ) + 1 ≤ 3204 * (size : ℝ) * L ^ (12 : ℕ) := by
        have htwo_le :
            (2 : ℝ) ≤ 2 * (size : ℝ) * L ^ (12 : ℕ) := by
          nlinarith [hsize_pos, hL_pow12_ge_one]
        nlinarith [hschedule_upper, hν_le_size, htwo_le]
      have hsq :
          (ν : ℝ) * ((N : ℝ) + 1) ≤
            (57 * (size : ℝ) * L ^ (6 : ℕ)) ^ (2 : ℕ) := by
        nlinarith [hupper_size, hν_le_size]
      refine Real.sqrt_le_iff.2 ?_
      constructor
      · positivity
      · simpa [pow_two] using hsq
    have hlog_upper :
        1 +
            Real.log
              (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))) ≤
          1 + Real.log 88 + 7 * L :=
      hlog_arg_bound_of_size hsqrt_arg_upper
    have hrate_upper :
        barrierSubgradientRelativeAccuracyDelta (ν : ℝ) N ≤
          δ *
            ((1 / (20 * L ^ (6 : ℕ)) + 1 / (800 * L ^ (12 : ℕ))) *
              (1 + Real.log 88 + 7 * L)) := by
      -- The schedule lower bound controls both explicit-rate prefactors by `δ`.
      calc
        barrierSubgradientRelativeAccuracyDelta (ν : ℝ) N
            = 2 *
                (Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) + (ν : ℝ) / ((N : ℝ) + 1)) *
                (1 +
                  Real.log
                    (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)))) := by
                rw [barrierSubgradientRelativeAccuracyDelta]
        _ ≤
            2 *
              (δ / (40 * L ^ (6 : ℕ)) + δ / (1600 * L ^ (12 : ℕ))) *
              (1 + Real.log 88 + 7 * L) := by
                gcongr
        _ = δ *
              ((1 / (20 * L ^ (6 : ℕ)) + 1 / (800 * L ^ (12 : ℕ))) *
                (1 + Real.log 88 + 7 * L)) := by
              field_simp [hL_ne]
              ring
    have hcoeff :
        ((1 / (20 * L ^ (6 : ℕ)) + 1 / (800 * L ^ (12 : ℕ))) *
            (1 + Real.log 88 + 7 * L)) ≤
          1 := by
      have hA : 1 + Real.log 88 ≤ 12 := by
        linarith
      have hL_inv6 : 1 / L ^ (6 : ℕ) ≤ 1 := by
        refine (one_div_le_iff₀ hL_pow6_pos).2 ?_
        simpa using hL_pow6_ge_one
      have hL_inv12 : 1 / L ^ (12 : ℕ) ≤ 1 := by
        refine (one_div_le_iff₀ hL_pow12_pos).2 ?_
        simpa using hL_pow12_ge_one
      have hcoeff6 :
          ((1 + Real.log 88 + 7 * L) / L ^ (6 : ℕ)) ≤ 19 := by
        have hnum :
            1 + Real.log 88 + 7 * L ≤ 12 + 7 * L ^ (6 : ℕ) := by
          nlinarith [hA, hL_le_pow6]
        refine (div_le_iff₀ hL_pow6_pos).2 ?_
        nlinarith
      have hcoeff12 :
          ((1 + Real.log 88 + 7 * L) / L ^ (12 : ℕ)) ≤ 19 := by
        have hnum :
            1 + Real.log 88 + 7 * L ≤ 12 + 7 * L ^ (12 : ℕ) := by
          nlinarith [hA, hL_le_pow6, hL_pow12_ge_one]
        refine (div_le_iff₀ hL_pow12_pos).2 ?_
        nlinarith
      calc
        ((1 / (20 * L ^ (6 : ℕ)) + 1 / (800 * L ^ (12 : ℕ))) *
            (1 + Real.log 88 + 7 * L))
            =
          (1 + Real.log 88 + 7 * L) / (20 * L ^ (6 : ℕ)) +
            (1 + Real.log 88 + 7 * L) / (800 * L ^ (12 : ℕ)) := by
              field_simp [hL_ne]
              ring
        _ ≤ 19 / 20 + 19 / 800 := by
              gcongr
        _ < 1 := by norm_num
      exact le_of_lt this
    exact
      le_trans hrate_upper <|
        by
          calc
            δ *
                ((1 / (20 * L ^ (6 : ℕ)) + 1 / (800 * L ^ (12 : ℕ))) *
                  (1 + Real.log 88 + 7 * L))
                ≤ δ * 1 := by
                    gcongr
            _ = δ := by ring
  · -- For `δ ≥ 1`, the schedule already makes the explicit rate uniformly small enough.
    have hδ_ge_one : 1 ≤ δ := le_of_not_ge hδ_le_one
    have hratio_upper :
        (ν : ℝ) / ((N : ℝ) + 1) ≤ 1 / (1600 * L ^ (12 : ℕ)) := by
      have hmain :
          (ν : ℝ) * (1600 * L ^ (12 : ℕ)) ≤ (N : ℝ) + 1 := by
        nlinarith [hschedule_lower]
      refine (div_le_iff₀ hN_pos).2 ?_
      nlinarith [hmain]
    have hsqrt_upper :
        Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) ≤ 1 / (40 * L ^ (6 : ℕ)) := by
      have hsq :
          (ν : ℝ) / ((N : ℝ) + 1) ≤ (1 / (40 * L ^ (6 : ℕ))) ^ (2 : ℕ) := by
        have hratio_sq :
            (1 / (1600 * L ^ (12 : ℕ))) = (1 / (40 * L ^ (6 : ℕ))) ^ (2 : ℕ) := by
          field_simp [hL_ne]
          ring
        simpa [hratio_sq] using hratio_upper
      refine Real.sqrt_le_iff.2 ?_
      constructor
      · positivity
      · simpa [pow_two] using hsq
    have hν_le_size_delta_sq : (ν : ℝ) ≤ (size : ℝ) * δ ^ (2 : ℕ) := by
      nlinarith [hsize_lower]
    have hsqrt_arg_upper :
        Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)) ≤
          57 * (size : ℝ) * δ ^ (2 : ℕ) * L ^ (6 : ℕ) := by
      have hupper_size :
          (N : ℝ) + 1 ≤ 3204 * (size : ℝ) * δ ^ (2 : ℕ) * L ^ (12 : ℕ) := by
        have htwo_le :
            (2 : ℝ) ≤ 2 * (size : ℝ) * δ ^ (2 : ℕ) * L ^ (12 : ℕ) := by
          nlinarith [hsize_pos, hδ_ge_one, hL_pow12_ge_one]
        have hsize_factor :
            (ν : ℝ) + (size : ℝ) ≤ 2 * (size : ℝ) * δ ^ (2 : ℕ) := by
          nlinarith [hν_le_size_delta_sq, hδ_ge_one]
        nlinarith [hschedule_upper, hsize_factor, htwo_le]
      have hsq :
          (ν : ℝ) * ((N : ℝ) + 1) ≤
            (57 * (size : ℝ) * δ ^ (2 : ℕ) * L ^ (6 : ℕ)) ^ (2 : ℕ) := by
        nlinarith [hupper_size, hν_le_size_delta_sq]
      refine Real.sqrt_le_iff.2 ?_
      constructor
      · positivity
      · simpa [pow_two] using hsq
    have hlog_upper :
        1 +
            Real.log
              (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))) ≤
          1 + Real.log 88 + 2 * Real.log δ + 7 * L := by
      have harg_le :
          2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)) ≤
            88 * (δ ^ (2 : ℕ)) * ((size : ℝ) + 2) ^ (7 : ℕ) := by
        have hpow_ge_one' : (1 : ℝ) ≤ ((size : ℝ) + 2) ^ (7 : ℕ) := by
          have hbase_ge_one : (1 : ℝ) ≤ (size : ℝ) + 2 := by linarith
          exact one_le_pow₀ hbase_ge_one
        calc
          2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))
              ≤
                2 + (3 / 2 : ℝ) *
                  (57 * (size : ℝ) * δ ^ (2 : ℕ) * L ^ (6 : ℕ)) := by
                    gcongr
          _ ≤ 2 + 86 * (δ ^ (2 : ℕ)) * ((size : ℝ) + 2) ^ (7 : ℕ) := by
                have hcoeff :
                    (3 / 2 : ℝ) *
                        (57 * (size : ℝ) * δ ^ (2 : ℕ) * L ^ (6 : ℕ)) ≤
                      86 * (δ ^ (2 : ℕ)) * ((size : ℝ) + 2) ^ (7 : ℕ) := by
                  have : (3 / 2 : ℝ) * 57 ≤ (86 : ℝ) := by norm_num
                  nlinarith [hsize_mul_Lpow6_le, this]
                linarith
          _ ≤ 88 * (δ ^ (2 : ℕ)) * ((size : ℝ) + 2) ^ (7 : ℕ) := by
                nlinarith [sq_nonneg δ, hpow_ge_one']
      have harg_pos :
          0 < 2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)) := by
        positivity
      have hδpow_pos : 0 < δ ^ (2 : ℕ) := by positivity
      have hlog_le :
          Real.log
              (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))) ≤
            Real.log (88 * (δ ^ (2 : ℕ)) * ((size : ℝ) + 2) ^ (7 : ℕ)) := by
        exact Real.log_le_log harg_pos harg_le
      calc
        1 +
            Real.log
              (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)))
            ≤ 1 + Real.log (88 * (δ ^ (2 : ℕ)) * ((size : ℝ) + 2) ^ (7 : ℕ)) := by
                linarith
        _ = 1 + Real.log 88 + 2 * Real.log δ + 7 * L := by
              rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
                Real.log_pow, Real.log_pow]
              simp [hL, add_assoc, add_left_comm, add_comm]
    have hlog_delta_le : Real.log δ ≤ δ := by
      have hlog_delta_le_sub : Real.log δ ≤ δ - 1 := Real.log_le_sub_one_of_pos hδ
      linarith
    have hrate_upper :
        barrierSubgradientRelativeAccuracyDelta (ν : ℝ) N ≤
          (1 / (20 * L ^ (6 : ℕ)) + 1 / (800 * L ^ (12 : ℕ))) *
            (1 + Real.log 88 + 2 * Real.log δ + 7 * L) := by
      -- Here the prefactor loses the small `δ`, but the logarithmic term is still mild enough.
      calc
        barrierSubgradientRelativeAccuracyDelta (ν : ℝ) N
            = 2 *
                (Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) + (ν : ℝ) / ((N : ℝ) + 1)) *
                (1 +
                  Real.log
                    (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)))) := by
                rw [barrierSubgradientRelativeAccuracyDelta]
        _ ≤
            2 *
              (1 / (40 * L ^ (6 : ℕ)) + 1 / (1600 * L ^ (12 : ℕ))) *
              (1 + Real.log 88 + 2 * Real.log δ + 7 * L) := by
                gcongr
        _ =
            (1 / (20 * L ^ (6 : ℕ)) + 1 / (800 * L ^ (12 : ℕ))) *
              (1 + Real.log 88 + 2 * Real.log δ + 7 * L) := by
                ring
    have hfinal :
        (1 / (20 * L ^ (6 : ℕ)) + 1 / (800 * L ^ (12 : ℕ))) *
            (1 + Real.log 88 + 2 * Real.log δ + 7 * L) ≤
          δ := by
      have hA : 1 + Real.log 88 ≤ 12 := by
        linarith
      have hcoeff6 :
          ((1 + Real.log 88 + 2 * Real.log δ + 7 * L) / L ^ (6 : ℕ)) ≤
            12 + 2 * δ + 7 := by
        have hnum :
            1 + Real.log 88 + 2 * Real.log δ + 7 * L ≤ 12 + 2 * δ + 7 * L ^ (6 : ℕ) := by
          nlinarith [hA, hlog_delta_le, hL_le_pow6]
        refine (div_le_iff₀ hL_pow6_pos).2 ?_
        nlinarith
      have hcoeff12 :
          ((1 + Real.log 88 + 2 * Real.log δ + 7 * L) / L ^ (12 : ℕ)) ≤
            12 + 2 * δ + 7 := by
        have hnum :
            1 + Real.log 88 + 2 * Real.log δ + 7 * L ≤ 12 + 2 * δ + 7 * L ^ (12 : ℕ) := by
          nlinarith [hA, hlog_delta_le, hL_le_pow6, hL_pow12_ge_one]
        refine (div_le_iff₀ hL_pow12_pos).2 ?_
        nlinarith
      calc
        (1 / (20 * L ^ (6 : ℕ)) + 1 / (800 * L ^ (12 : ℕ))) *
            (1 + Real.log 88 + 2 * Real.log δ + 7 * L)
            =
          (1 + Real.log 88 + 2 * Real.log δ + 7 * L) / (20 * L ^ (6 : ℕ)) +
            (1 + Real.log 88 + 2 * Real.log δ + 7 * L) / (800 * L ^ (12 : ℕ)) := by
              field_simp [hL_ne]
              ring
        _ ≤ (12 + 2 * δ + 7) / 20 + (12 + 2 * δ + 7) / 800 := by
              gcongr
        _ ≤ δ := by
              nlinarith [hδ_ge_one]
    exact le_trans hrate_upper hfinal

/-- Helper for Proposition 7.34: the explicit schedule has soft complexity
`\tilde O(ν / δ²)` near `δ = 0`. -/
lemma schedule_isSoftBigO_barrier_scale
    (ν : NNReal) (hν : 0 < (ν : ℝ)) :
    (fun δ ↦ (approximationSchedule ν δ : ℝ)) =Õ[fun δ ↦ approximationScheduleSize ν δ;
      nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun δ ↦ (ν : ℝ) / δ ^ (2 : ℕ)) := by
  refine ⟨12, ?_⟩
  refine Asymptotics.IsBigO.of_bound 6402 ?_
  have hsmall :
      ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        δ < min 1 (Real.sqrt (ν : ℝ)) := by
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    exact (eventually_lt_nhds (a := (0 : ℝ)) (b := min 1 (Real.sqrt (ν : ℝ)))
      (by
        have hsqrt_pos : 0 < Real.sqrt (ν : ℝ) := Real.sqrt_pos.2 hν
        exact lt_min zero_lt_one hsqrt_pos))
  filter_upwards [hsmall, eventually_mem_nhdsWithin] with δ hδ_small hδ_mem
  have hδ_pos : 0 < δ := by
    simpa using hδ_mem
  have hg_nonneg : 0 ≤ (ν : ℝ) / δ ^ (2 : ℕ) := by
    positivity
  have hδ_sq_pos : 0 < δ ^ (2 : ℕ) := by positivity
  have hg_pos : 0 < (ν : ℝ) / δ ^ (2 : ℕ) := by
    exact div_pos hν hδ_sq_pos
  have hg_ge_one : 1 ≤ (ν : ℝ) / δ ^ (2 : ℕ) := by
    have hδ_lt_sqrt : δ < Real.sqrt (ν : ℝ) := lt_of_lt_of_le hδ_small (min_le_right _ _)
    have hδ_sq_lt : δ ^ (2 : ℕ) < (ν : ℝ) := by
      nlinarith [hδ_lt_sqrt, hδ_pos, Real.sqrt_nonneg (ν : ℝ), Real.sq_sqrt hν.le]
    have hratio_gt_one : 1 < (ν : ℝ) / δ ^ (2 : ℕ) := by
      rw [one_lt_div hδ_sq_pos]
      simpa using hδ_sq_lt
    exact hratio_gt_one.le
  set size : ℕ := approximationScheduleSize ν δ with hsize
  have hsize_ge_one : 1 ≤ size := by
    rw [hsize, approximationScheduleSize]
    exact Nat.one_le_ceil_iff.mpr hg_pos
  have hsize_lower :
      (ν : ℝ) / δ ^ (2 : ℕ) ≤ (size : ℝ) := by
    simpa [hsize, approximationScheduleSize] using
      (Nat.le_ceil ((ν : ℝ) / δ ^ (2 : ℕ)))
  have hsize_upper :
      (size : ℝ) ≤ 2 * ((ν : ℝ) / δ ^ (2 : ℕ)) := by
    have hceil_lt :
        (size : ℝ) < (ν : ℝ) / δ ^ (2 : ℕ) + 1 := by
      simpa [hsize, approximationScheduleSize] using
        (Nat.ceil_lt_add_one hg_nonneg)
    linarith
  have hν_le_size : (ν : ℝ) ≤ (size : ℝ) := by
    have hδ_lt_one : δ < 1 := lt_of_lt_of_le hδ_small (min_le_left _ _)
    have hδ_sq_le_one : δ ^ (2 : ℕ) ≤ 1 := by
      nlinarith [sq_nonneg (δ - 1)]
    have hratio_ge_nu : (ν : ℝ) ≤ (ν : ℝ) / δ ^ (2 : ℕ) := by
      refine (le_div_iff₀ hδ_sq_pos).2 ?_
      nlinarith [hν.le, hδ_sq_le_one]
    calc
      (ν : ℝ) ≤ (ν : ℝ) / δ ^ (2 : ℕ) := hratio_ge_nu
      _ ≤ (size : ℝ) := hsize_lower
  have hlog_ge_one :
      1 ≤ Real.log ((size : ℝ) + 2) := by
    have hthree_le : (3 : ℝ) ≤ (size : ℝ) + 2 := by
      have : (1 : ℝ) ≤ (size : ℝ) := by exact_mod_cast hsize_ge_one
      linarith
    rw [← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    exact le_trans (le_of_lt Real.exp_one_lt_three) hthree_le
  have hschedule_bound :
      (approximationSchedule ν δ : ℝ) ≤
        6402 *
          (Real.log ((size : ℝ) + 2)) ^ (12 : ℕ) *
          ((ν : ℝ) / δ ^ (2 : ℕ)) := by
    have hceil_lt :
        (approximationSchedule ν δ : ℝ) <
          1600 * ((ν : ℝ) + (size : ℝ)) * (Real.log ((size : ℝ) + 2)) ^ (12 : ℕ) + 1 := by
      have hnonneg :
          0 ≤ 1600 * ((ν : ℝ) + (size : ℝ)) * (Real.log ((size : ℝ) + 2)) ^ (12 : ℕ) := by
        positivity
      simpa [approximationSchedule, approximationScheduleLogWeight, size] using
        (Nat.ceil_lt_add_one hnonneg)
    have hmain :
        1600 * ((ν : ℝ) + (size : ℝ)) * (Real.log ((size : ℝ) + 2)) ^ (12 : ℕ) + 1 ≤
          6402 *
            (Real.log ((size : ℝ) + 2)) ^ (12 : ℕ) *
            ((ν : ℝ) / δ ^ (2 : ℕ)) := by
      have hlog_pow_ge_one : 1 ≤ (Real.log ((size : ℝ) + 2)) ^ (12 : ℕ) :=
        one_le_pow₀ hlog_ge_one
      have hone_le :
          (1 : ℝ) ≤
            2 * (Real.log ((size : ℝ) + 2)) ^ (12 : ℕ) * ((ν : ℝ) / δ ^ (2 : ℕ)) := by
        have hratio_ge_one : 1 ≤ (ν : ℝ) / δ ^ (2 : ℕ) := hg_ge_one
        nlinarith
      have hcore :
          1600 * ((ν : ℝ) + (size : ℝ)) * (Real.log ((size : ℝ) + 2)) ^ (12 : ℕ) ≤
            6400 *
              (Real.log ((size : ℝ) + 2)) ^ (12 : ℕ) *
              ((ν : ℝ) / δ ^ (2 : ℕ)) := by
        have hνsize :
            (ν : ℝ) + (size : ℝ) ≤ 4 * ((ν : ℝ) / δ ^ (2 : ℕ)) := by
          calc
            (ν : ℝ) + (size : ℝ) ≤ 2 * (size : ℝ) := by linarith
            _ ≤ 4 * ((ν : ℝ) / δ ^ (2 : ℕ)) := by
              nlinarith [hsize_upper]
        have hlog_nonneg : 0 ≤ (Real.log ((size : ℝ) + 2)) ^ (12 : ℕ) := by positivity
        calc
          1600 * ((ν : ℝ) + (size : ℝ)) * (Real.log ((size : ℝ) + 2)) ^ (12 : ℕ)
              ≤ 1600 * (4 * ((ν : ℝ) / δ ^ (2 : ℕ))) *
                  (Real.log ((size : ℝ) + 2)) ^ (12 : ℕ) := by
                    exact mul_le_mul_of_nonneg_right (by linarith [hνsize]) hlog_nonneg
          _ = 6400 * (Real.log ((size : ℝ) + 2)) ^ (12 : ℕ) * ((ν : ℝ) / δ ^ (2 : ℕ)) := by
                ring
      linarith
    exact le_of_lt (lt_of_lt_of_le hceil_lt hmain)
  have htarget_nonneg :
      0 ≤
        6402 * ((Real.log ((size : ℝ) + 2)) ^ (12 : ℕ) * ((ν : ℝ) / δ ^ (2 : ℕ))) := by
    positivity
  have hprod_nonneg :
      0 ≤ (Real.log ((size : ℝ) + 2)) ^ (12 : ℕ) * ((ν : ℝ) / δ ^ (2 : ℕ)) := by
    positivity
  have hnorm :
      ‖(approximationSchedule ν δ : ℝ)‖ ≤
        6402 *
          ‖(Real.log ((size : ℝ) + 2)) ^ (12 : ℕ) * ((ν : ℝ) / δ ^ (2 : ℕ))‖ := by
    calc
      ‖(approximationSchedule ν δ : ℝ)‖ = (approximationSchedule ν δ : ℝ) := by
        exact Real.norm_of_nonneg (by positivity)
      _ ≤
          6402 * ((Real.log ((size : ℝ) + 2)) ^ (12 : ℕ) * ((ν : ℝ) / δ ^ (2 : ℕ))) :=
        by simpa [mul_assoc] using hschedule_bound
      _ = 6402 *
            ‖(Real.log ((size : ℝ) + 2)) ^ (12 : ℕ) * ((ν : ℝ) / δ ^ (2 : ℕ))‖ := by
          rw [Real.norm_of_nonneg hprod_nonneg]
  simpa [hsize, approximationScheduleSize] using hnorm

-- Proof sketch: combine the fixed-index relative-scale approximation theorem for the geometric
-- mean with an inversion of the explicit rate `δ_k`, then package the chosen schedule as a
-- soft-`O(ν / δ²)` bound near `δ = 0`.
/-- Proposition 7.34: for the barrier-subgradient approximation scheme `(7.3.33)` applied to a
concave maximization problem of the form `(7.3.29)`, there exists an iteration schedule `N(δ)`
such that the geometric-mean output after `N(δ)` steps is a relative-`δ` approximation of
`ψ(x⋆)`, where the method parameter is the same barrier parameter `ν` that indexes the explicit
rate, and `N(δ)` has soft complexity `\tilde O(ν / δ²)` as `δ ↓ 0`. -/
theorem exists_relativeScaleDeltaApproximation_schedule
    (xStar : P0) (hoptimal : IsMaxOn ψ P0 xStar)
    [IsSelfConcordantBarrierOnWith P0 (ν : NNReal) F]
    [HasPositiveDefiniteHessianOn P0 F]
    (hψ_concave : ConcaveOn ℝ P0 ψ)
    (hψ_dual_bound :
      ∀ x : P0,
        HessianDualLocalNorm.ofPosDefMem F x.2
            (InnerProductSpace.toDualMap ℝ E (∇ ψ x)) ≤
          ψ x) :
    ∃ N : ℝ → ℕ,
      (∀ ⦃δ : ℝ⦄, 0 < δ →
        IsRelativeScaleDeltaApproximation (ψ xStar) δ
          (method.iterateGeometricMean (N δ))) ∧
        (fun δ ↦ (N δ : ℝ)) =Õ[fun δ ↦ ⌈(ν : ℝ) / δ ^ (2 : ℕ)⌉₊;
          nhdsWithin (0 : ℝ) (Set.Ioi 0)]
          (fun δ ↦ (ν : ℝ) / δ ^ (2 : ℕ)) := by
  refine ⟨approximationSchedule (ν : NNReal), ?_⟩
  constructor
  · intro δ hδ
    -- Apply the fixed-index approximation at the scheduled horizon, then enlarge the tolerance.
      have happrox :
          IsRelativeScaleDeltaApproximation
          (ψ xStar)
          (barrierSubgradientRelativeAccuracyDelta (ν : ℝ) (approximationSchedule (ν : NNReal) δ))
          (method.iterateGeometricMean (approximationSchedule (ν : NNReal) δ)) :=
      method.positiveIterateGeometricMean_isRelativeScaleDeltaApproximation
        xStar hoptimal hψ_concave hψ_dual_bound (approximationSchedule (ν : NNReal) δ)
    exact relativeScaleDeltaApproximation_of_le_delta happrox
      (explicit_rate_at_schedule_le_delta (ν : NNReal) (show 0 < (ν : ℝ) from ν.2) hδ)
  · -- The same explicit schedule has soft complexity `\tilde O(ν / δ²)`.
    simpa [approximationScheduleSize] using
      schedule_isSoftBigO_barrier_scale (ν : NNReal) (show 0 < (ν : ℝ) from ν.2)

end ApproximationSchedule

end BarrierSubgradientMethod

end
