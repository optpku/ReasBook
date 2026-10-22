/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_28
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.MetricSpace.Lipschitz

open Set
open scoped Interval

section Theorem124

variable {E G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

-- Source/core/bridge triage:
-- * source-facing: the three textbook first-order linearization-error bounds
-- * core/canonical owner: `norm_image_sub_sub_le_of_segment_fderiv_deviation_bound`
-- * bridge/view: the `C¹` specialization via `ContDiffOn ℝ 1 F D` and the
--   derivative-Lipschitz corollaries used later in the chapter

-- Semantic recall: Chapter 1 already contains the more general derivative-field
-- deviation estimate in `Definition_1_2_28.lean`; this file keeps the `C¹`
-- surface used later in the chapter, together with the supremum and Lipschitz
-- corollaries stated in the text. The source `ℝⁿ → ℝᵐ` statement is the
-- Euclidean specialization of the intrinsic real normed-space formulation below.

/-- First displayed bound for Theorem 1.2.24 in Chapter01: on an open convex
set `D`, the first-order
linearization error of a `C¹` map at `x` is bounded by the supremum of the
derivative deviation along the segment from `v` to `u`, times `‖u - v‖`. -/
theorem linearizationError_le_segmentFDerivDeviationSup
    (D : Set E)
    (F : E → G)
    {u v x : E}
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hF : ContDiffOn ℝ 1 F D)
    (hu : u ∈ D)
    (hv : v ∈ D)
    (hx : x ∈ D) :
    ‖F u - F v - (fderiv ℝ F x) (u - v)‖ ≤
      sSup ((fun t : ℝ ↦ ‖fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F x‖) ''
        Set.Icc (0 : ℝ) 1) * ‖u - v‖ := by
  have hdiff : DifferentiableOn ℝ F D := hF.differentiableOn_one
  have hcont : ContinuousOn (fderiv ℝ F) D :=
    hF.continuousOn_fderiv_of_isOpen hD_open le_rfl
  have hx_fderiv : fderivWithin ℝ F D x = fderiv ℝ F x :=
    fderivWithin_of_isOpen hD_open hx
  let deviations : Set ℝ :=
    (fun t : ℝ ↦ ‖fderiv ℝ F (v + t • (u - v)) - fderivWithin ℝ F D x‖) '' Set.Icc (0 : ℝ) 1
  simpa [deviations, hx_fderiv] using
    norm_image_sub_sub_le_of_segment_fderiv_deviation_bound F (fderiv ℝ F)
      hD_convex
      (fun y hy e ↦ by
        simpa [fderivWithin_of_isOpen hD_open hy] using
          ((hdiff y hy).hasFDerivWithinAt.hasLineDerivWithinAt e))
      (fun t ht ↦ by
        change ‖fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F x‖ ≤
          sSup ((fun t : ℝ ↦ ‖fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F x‖) ''
            Set.Icc (0 : ℝ) 1)
        let g : ℝ → ℝ := fun s ↦ ‖fderiv ℝ F (v + s • (u - v)) - fderivWithin ℝ F D x‖
        have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
          have hline :
              ContinuousOn (fun s : ℝ ↦ v + s • (u - v)) (Set.Icc (0 : ℝ) 1) := by
            fun_prop
          have hline_maps :
              MapsTo (fun s : ℝ ↦ v + s • (u - v)) (Set.Icc (0 : ℝ) 1) D := by
            intro s hs
            exact hD_convex.add_smul_sub_mem hv hu hs
          have hderiv_cont :
              ContinuousOn (fun s : ℝ ↦ fderiv ℝ F (v + s • (u - v))) (Set.Icc (0 : ℝ) 1) :=
            hcont.comp hline hline_maps
          simpa [g] using (hderiv_cont.sub continuousOn_const).norm
        simpa [deviations, g, hx_fderiv] using hg_cont.le_sSup_image_Icc ht)
      hu
      hv

section LipschitzDerivativeBounds

variable (D : Set E) (F : E → G) (γ : NNReal)
variable {u v x : E}
variable (hD_open : IsOpen D)
variable (hD_convex : Convex ℝ D)
variable (hF : ContDiffOn ℝ 1 F D)
variable (hu : u ∈ D) (hv : v ∈ D) (hx : x ∈ D)
variable (hLip : LipschitzOnWith γ (fderiv ℝ F) D)

/-- Helper for Theorem 1.2.24 in Chapter01: on the open set `D`, the ambient derivative
`fderiv ℝ F` gives the chapter's Gateaux derivative data. -/
lemma isGateauxDerivativeWithinAt_fderiv_of_contDiffOn
    (hD_open : IsOpen D)
    (hF : ContDiffOn ℝ 1 F D)
    {y : E} (hy : y ∈ D) :
    IsGateauxDerivativeWithinAt ℝ D F y (fderiv ℝ F y) := by
  have hdiff : DifferentiableOn ℝ F D := hF.differentiableOn_one
  -- Convert the ambient Fréchet derivative into the linewise within-set owner used downstream.
  intro e
  simpa [fderivWithin_of_isOpen hD_open hy] using
    ((hdiff y hy).hasFDerivWithinAt.hasLineDerivWithinAt e)

/-- Helper for Theorem 1.2.24 in Chapter01: the segment point `v + t • (u - v)`, measured from `x`,
is the affine combination `(1 - t) • (v - x) + t • (u - x)`. -/
lemma segmentPoint_sub_eq_endpointConvexCombination
    (t : ℝ) :
    (v + t • (u - v)) - x = (1 - t) • (v - x) + t • (u - x) := by
  -- Rewrite the source segment as an affine line map and then shift both endpoints by `-x`.
  calc
    (v + t • (u - v)) - x = AffineMap.lineMap v u t - x := by
      simp [AffineMap.lineMap_apply_module', add_comm]
    _ = AffineMap.lineMap (v - x) (u - x) t := by
      simp [AffineMap.lineMap_apply_module, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        smul_add, add_smul]
      abel_nf
    _ = (1 - t) • (v - x) + t • (u - x) := by
      simp [AffineMap.lineMap_apply_module]

/-- Helper for Theorem 1.2.24 in Chapter01: every point on the segment from `v` to `u` has distance
from `x` bounded by the corresponding convex combination of the endpoint distances. -/
lemma segmentPoint_norm_sub_le_endpointConvexCombination
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(v + t • (u - v)) - x‖ ≤ (1 - t) * ‖v - x‖ + t * ‖u - x‖ := by
  have ht_nonneg : 0 ≤ t := ht.1
  have h_one_sub_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  -- Normalize the segment point relative to `x`, then apply the triangle inequality.
  rw [segmentPoint_sub_eq_endpointConvexCombination t]
  calc
    ‖(1 - t) • (v - x) + t • (u - x)‖ ≤ ‖(1 - t) • (v - x)‖ + ‖t • (u - x)‖ :=
      norm_add_le _ _
    _ = (1 - t) * ‖v - x‖ + t * ‖u - x‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg h_one_sub_nonneg, Real.norm_of_nonneg ht_nonneg]

/-- Helper for Theorem 1.2.24 in Chapter01: along the segment from `v` to `u`, the derivative
deviation from `x` is bounded by the affine endpoint-distance majorant coming from the
`γ`-Lipschitz hypothesis on `fderiv ℝ F`. -/
lemma fderivDeviation_le_segmentEndpointConvexCombination
    (hD_convex : Convex ℝ D)
    (hu : u ∈ D) (hv : v ∈ D) (hx : x ∈ D)
    (hLip : LipschitzOnWith γ (fderiv ℝ F) D)
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F x‖ ≤
      (γ : ℝ) * ((1 - t) * ‖v - x‖ + t * ‖u - x‖) := by
  have hseg_mem : v + t • (u - v) ∈ D := hD_convex.add_smul_sub_mem hv hu ht
  have hlip_bound :
      ‖fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F x‖ ≤
        (γ : ℝ) * ‖(v + t • (u - v)) - x‖ := by
    -- Apply the ambient Lipschitz bound to the current segment point and the basepoint `x`.
    simpa [dist_eq_norm] using hLip.dist_le_mul (v + t • (u - v)) hseg_mem x hx
  -- Replace the segment distance by the affine endpoint majorant.
  exact hlip_bound.trans <|
    mul_le_mul_of_nonneg_left
      (segmentPoint_norm_sub_le_endpointConvexCombination ht)
      (NNReal.coe_nonneg γ)

/-- Helper for Theorem 1.2.24 in Chapter01: after scalarizing by `g`, the linearization error equals
the interval integral of the scalarized derivative deviation along the segment from `v` to `u`. -/
lemma scalarizedLinearizationError_eq_segmentIntegral
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hF : ContDiffOn ℝ 1 F D)
    (hu : u ∈ D) (hv : v ∈ D)
    (g : G →L[ℝ] ℝ) :
    g (F u - F v - (fderiv ℝ F x) (u - v)) =
      ∫ t in 0..1, (g.comp (fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F x)) (u - v) := by
  let φ : E → ℝ := fun z ↦ g (F z - (fderiv ℝ F x) z)
  let ψ : E → E →L[ℝ] ℝ := fun z ↦ g.comp (fderiv ℝ F z - fderiv ℝ F x)
  have hFderivCont : ContinuousOn (fderiv ℝ F) D :=
    hF.continuousOn_fderiv_of_isOpen hD_open le_rfl
  have hψcont : ContinuousOn ψ D := by
    -- The scalarized derivative field inherits continuity from `fderiv ℝ F`.
    exact ContinuousOn.clm_comp continuousOn_const (hFderivCont.sub continuousOn_const)
  have hψhemi : ∀ z ∈ D, AlongLineWithinAt ContinuousWithinAt D ψ z := by
    intro z hz
    -- Convert ambient continuity into the chapter's along-line continuity owner.
    exact alongLineWithinAt_of_continuousOn hz hψcont
  have hψgateaux : ∀ z ∈ D, IsGateauxDerivativeWithinAt ℝ D φ z (ψ z) := by
    intro z hz
    -- First subtract the frozen linear model, then compose with the scalar functional `g`.
    exact
      isGateauxDerivativeWithinAt_comp_clm g
        (isGateauxDerivativeWithinAt_sub_clm (fderiv ℝ F x)
          (isGateauxDerivativeWithinAt_fderiv_of_contDiffOn D F hD_open hF hz))
  have hFTC :=
    segmentIntegral_eq_sub φ ψ hD_convex
      hψgateaux
      hψhemi
      hv
      hu
  have hleft : φ u - φ v = g (F u - F v - (fderiv ℝ F x) (u - v)) := by
    -- Rewrite the endpoint difference into the scalarized first-order remainder.
    change g (F u - (fderiv ℝ F x) u) - g (F v - (fderiv ℝ F x) v) =
      g (F u - F v - (fderiv ℝ F x) (u - v))
    calc
      g (F u - (fderiv ℝ F x) u) - g (F v - (fderiv ℝ F x) v) =
          (g (F u) - g ((fderiv ℝ F x) u)) - (g (F v) - g ((fderiv ℝ F x) v)) := by
            rw [map_sub, map_sub]
      _ = g (F u) - g (F v) - (g ((fderiv ℝ F x) u) - g ((fderiv ℝ F x) v)) := by
            ring
      _ = g (F u - F v) - (g ((fderiv ℝ F x) u) - g ((fderiv ℝ F x) v)) := by
            rw [← map_sub]
      _ = g (F u - F v) - g ((fderiv ℝ F x) u - (fderiv ℝ F x) v) := by
            rw [← map_sub]
      _ = g (F u - F v) - g ((fderiv ℝ F x) (u - v)) := by
            congr 2
            rw [map_sub]
      _ = g (F u - F v - (fderiv ℝ F x) (u - v)) := by
            rw [← map_sub]
  -- Apply the scalar-valued segment FTC theorem to the shifted map `φ`.
  calc
    g (F u - F v - (fderiv ℝ F x) (u - v)) = φ u - φ v := hleft.symm
    _ = ∫ t in 0..1, ψ (v + t • (u - v)) (u - v) := hFTC
    _ = ∫ t in 0..1, (g.comp (fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F x)) (u - v) := by
          rfl

section

omit [NormedSpace ℝ E]

/-- Helper for Theorem 1.2.24 in Chapter01: on `[0, 1]`, the affine combination of the endpoint
distances from `x` is bounded by their maximum. -/
lemma segmentEndpointConvexCombination_le_maxDistance
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1 - t) * ‖v - x‖ + t * ‖u - x‖ ≤ max ‖u - x‖ ‖v - x‖ := by
  have ht_nonneg : 0 ≤ t := ht.1
  have h_one_sub_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hv_le : ‖v - x‖ ≤ max ‖u - x‖ ‖v - x‖ := le_max_right _ _
  have hu_le : ‖u - x‖ ≤ max ‖u - x‖ ‖v - x‖ := le_max_left _ _
  -- Bound each weighted endpoint term by the same maximum and then collapse the convex weights.
  calc
    (1 - t) * ‖v - x‖ + t * ‖u - x‖ ≤
        (1 - t) * max ‖u - x‖ ‖v - x‖ + t * max ‖u - x‖ ‖v - x‖ := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hv_le h_one_sub_nonneg)
            (mul_le_mul_of_nonneg_left hu_le ht_nonneg)
    _ = max ‖u - x‖ ‖v - x‖ := by
          ring

end

/-- Helper for Theorem 1.2.24 in Chapter01: the derivative deviation along the segment from `v` to
`u` is uniformly bounded by `γ` times the maximum endpoint distance from `x`. -/
lemma fderivDeviation_le_segmentMaxDistance
    (hD_convex : Convex ℝ D)
    (hu : u ∈ D) (hv : v ∈ D) (hx : x ∈ D)
    (hLip : LipschitzOnWith γ (fderiv ℝ F) D)
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F x‖ ≤
      (γ : ℝ) * max ‖u - x‖ ‖v - x‖ := by
  -- First use the affine endpoint-distance majorant, then dominate it by the endpoint maximum.
  refine (fderivDeviation_le_segmentEndpointConvexCombination
    (D := D) (F := F) (γ := γ) hD_convex hu hv hx hLip ht).trans ?_
  exact mul_le_mul_of_nonneg_left
    (segmentEndpointConvexCombination_le_maxDistance (u := u) (v := v) (x := x) ht)
    (NNReal.coe_nonneg γ)

/-- Helper for Theorem 1.2.24 in Chapter01: the affine endpoint-distance majorant integrates over
`[0, 1]` to the arithmetic mean of its endpoint values. -/
lemma affineEndpointDistanceIntegral_eq_average
    (a b : ℝ) :
    ∫ t in 0..1, ((1 - t) * a + t * b) = (a + b) / 2 := by
  have hIntegralId :
      ∫ t in 0..1, t = (1 : ℝ) / 2 := by
    calc
      ∫ t in 0..1, t = (1 ^ (1 + 1) - 0 ^ (1 + 1)) / (1 + 1) := by
        simpa using integral_rpow (a := (0 : ℝ)) (b := 1) (r := (1 : ℝ))
          (Or.inl (by norm_num : (-1 : ℝ) < 1))
      _ = (1 : ℝ) / 2 := by norm_num
  have hConstInt :
      IntervalIntegrable (fun _ : ℝ ↦ a) MeasureTheory.volume 0 1 :=
    intervalIntegrable_const
  have hLinearInt :
      IntervalIntegrable (fun t : ℝ ↦ t * (b - a)) MeasureTheory.volume 0 1 := by
    exact (continuousOn_id.mul continuousOn_const).intervalIntegrable_of_Icc zero_le_one
  -- Rewrite the affine function as `a + t * (b - a)` and integrate termwise.
  calc
    ∫ t in 0..1, ((1 - t) * a + t * b) = ∫ t in 0..1, (a + t * (b - a)) := by
      congr with t
      ring
    _ = (∫ t in 0..1, a) + ∫ t in 0..1, t * (b - a) := by
      exact intervalIntegral.integral_add hConstInt hLinearInt
    _ = a + (∫ t in 0..1, t) * (b - a) := by
      simp [intervalIntegral.integral_const, intervalIntegral.integral_mul_const]
    _ = a + ((1 : ℝ) / 2) * (b - a) := by rw [hIntegralId]
    _ = (a + b) / 2 := by ring

/-- Helper for Theorem 1.2.24 in Chapter01: after scalarizing by a dual functional of norm at most
`1`, the segment integrand is controlled by the affine endpoint-distance majorant. -/
lemma scalarizedSegmentIntegrand_abs_le_endpointAverageMajorant
    (g : G →L[ℝ] ℝ)
    (hg_norm : ‖g‖ ≤ 1)
    (hD_convex : Convex ℝ D)
    (hu : u ∈ D) (hv : v ∈ D) (hx : x ∈ D)
    (hLip : LipschitzOnWith γ (fderiv ℝ F) D)
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |(g.comp (fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F x)) (u - v)| ≤
      (γ : ℝ) * ((1 - t) * ‖v - x‖ + t * ‖u - x‖) * ‖u - v‖ := by
  -- Convert the scalar quantity to a norm and then use operator-norm bounds twice.
  calc
    |(g.comp (fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F x)) (u - v)| =
        ‖g ((fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F x) (u - v))‖ := by
          simp [Real.norm_eq_abs]
    _ ≤ ‖g‖ * ‖(fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F x) (u - v)‖ := by
          simpa using ContinuousLinearMap.le_opNorm g
            ((fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F x) (u - v))
    _ ≤ ‖g‖ * (‖fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F x‖ * ‖u - v‖) := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * (‖fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F x‖ * ‖u - v‖) := by
          gcongr
    _ = ‖fderiv ℝ F (v + t • (u - v)) - fderiv ℝ F x‖ * ‖u - v‖ := by ring
    _ ≤ ((γ : ℝ) * ((1 - t) * ‖v - x‖ + t * ‖u - x‖)) * ‖u - v‖ := by
          gcongr
          exact fderivDeviation_le_segmentEndpointConvexCombination
            (D := D) (F := F) (γ := γ) hD_convex hu hv hx hLip ht
    _ = (γ : ℝ) * ((1 - t) * ‖v - x‖ + t * ‖u - x‖) * ‖u - v‖ := by
          ring

/-- Chapter01 Theorem 1.2.24: if `F` is continuously differentiable on the
open convex set `D` and `fderiv ℝ F` is `γ`-Lipschitz there, then the
first-order linearization error at `x` is bounded by
`γ * max ‖u - x‖ ‖v - x‖ * ‖u - v‖`. -/
theorem linearizationError_le_lipschitz_maxDistance
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hF : ContDiffOn ℝ 1 F D)
    (hu : u ∈ D)
    (hv : v ∈ D)
    (hx : x ∈ D)
    (hLip : LipschitzOnWith γ (fderiv ℝ F) D)
    :
    ‖F u - F v - (fderiv ℝ F x) (u - v)‖ ≤
      (γ : ℝ) * max ‖u - x‖ ‖v - x‖ * ‖u - v‖ := by
  -- Route correction: the theorem already has the needed hypotheses, so apply the generic
  -- segment remainder bound after replacing the affine endpoint majorant by the endpoint max.
  exact
    norm_image_sub_sub_le_of_segment_fderiv_deviation_bound F (fderiv ℝ F)
      hD_convex
      (fun y hy ↦
        isGateauxDerivativeWithinAt_fderiv_of_contDiffOn
          (D := D) (F := F) hD_open hF hy)
      (fun t ht ↦
        fderivDeviation_le_segmentMaxDistance
          (D := D) (F := F) (γ := γ) hD_convex hu hv hx hLip ht)
      hu
      hv

/-- Average-distance companion for Theorem 1.2.24 in Chapter01: under the same open-set, convexity,
continuous differentiability, membership, and derivative-Lipschitz hypotheses
as part (2), the first-order linearization error at `x` is bounded by
`γ * ((‖u - x‖ + ‖v - x‖) / 2) * ‖u - v‖`. This is the sharper companion bound,
whose specialization `v = x` recovers the quadratic remainder form used earlier
in the chapter. -/
theorem linearizationError_le_lipschitz_averageDistance
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hF : ContDiffOn ℝ 1 F D)
    (hu : u ∈ D)
    (hv : v ∈ D)
    (hx : x ∈ D)
    (hLip : LipschitzOnWith γ (fderiv ℝ F) D)
    :
    ‖F u - F v - (fderiv ℝ F x) (u - v)‖ ≤
      (γ : ℝ) * ((‖u - x‖ + ‖v - x‖) / 2) * ‖u - v‖ := by
  let r : G := F u - F v - (fderiv ℝ F x) (u - v)
  obtain ⟨g, hg_norm, hg_eval⟩ := exists_dual_vector'' (𝕜 := ℝ) r
  let ψ : E → E →L[ℝ] ℝ := fun z ↦ g.comp (fderiv ℝ F z - fderiv ℝ F x)
  have hFderivCont : ContinuousOn (fderiv ℝ F) D :=
    hF.continuousOn_fderiv_of_isOpen hD_open le_rfl
  have hψcont : ContinuousOn ψ D := by
    -- The scalarized derivative field inherits continuity from `fderiv ℝ F`.
    exact ContinuousOn.clm_comp continuousOn_const (hFderivCont.sub continuousOn_const)
  have hψhemi : ∀ z ∈ D, AlongLineWithinAt ContinuousWithinAt D ψ z := by
    intro z hz
    -- Convert ambient continuity into the chapter's along-line continuity owner.
    exact alongLineWithinAt_of_continuousOn hz hψcont
  have hsegment :
      g r = ∫ t in 0..1, ψ (v + t • (u - v)) (u - v) := by
    -- Scalarize the remainder and rewrite it as the segment integral from the imported FTC owner.
    simpa [r, ψ] using
      scalarizedLinearizationError_eq_segmentIntegral
        (D := D) (F := F) (u := u) (v := v) (x := x)
        hD_open hD_convex hF hu hv g
  have hpointwise :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |ψ (v + t • (u - v)) (u - v)| ≤
          (γ : ℝ) * ((1 - t) * ‖v - x‖ + t * ‖u - x‖) * ‖u - v‖ := by
    intro t ht
    -- Control each scalarized integrand value by the affine endpoint-distance majorant.
    simpa [ψ] using
      scalarizedSegmentIntegrand_abs_le_endpointAverageMajorant
        (D := D) (F := F) (γ := γ) (u := u) (v := v) (x := x)
        g hg_norm hD_convex hu hv hx hLip ht
  have hsegmentCont :
      ContinuousOn
        (fun t ↦ ψ (v + t • (u - v)) (u - v))
        (Set.Icc (0 : ℝ) 1) :=
    segmentIntegrandContinuousOn_of_alongLine (F' := ψ) hD_convex hψhemi hv hu
  have habsInt :
      IntervalIntegrable
        (fun t ↦ |ψ (v + t • (u - v)) (u - v)|)
        MeasureTheory.volume
        0
        1 := by
    -- Absolute values preserve continuity of the segment integrand, hence interval integrability.
    exact hsegmentCont.abs.intervalIntegrable_of_Icc zero_le_one
  have hupperCont :
      ContinuousOn
        (fun t : ℝ ↦ (γ : ℝ) * ((1 - t) * ‖v - x‖ + t * ‖u - x‖) * ‖u - v‖)
        (Set.Icc (0 : ℝ) 1) := by
    -- The affine scalar majorant is continuous on the compact interval `[0, 1]`.
    fun_prop
  have hupperInt :
      IntervalIntegrable
        (fun t : ℝ ↦ (γ : ℝ) * ((1 - t) * ‖v - x‖ + t * ‖u - x‖) * ‖u - v‖)
        MeasureTheory.volume
        0
        1 := by
    exact hupperCont.intervalIntegrable_of_Icc zero_le_one
  -- Compare the scalar integral with the affine majorant and then evaluate the latter exactly.
  calc
    ‖r‖ = |∫ t in 0..1, ψ (v + t • (u - v)) (u - v)| := by
      have hgr_nonneg : 0 ≤ g r := by
        rw [hg_eval]
        exact norm_nonneg r
      calc
        ‖r‖ = g r := by simpa [r] using hg_eval.symm
        _ = |g r| := by symm; exact abs_of_nonneg hgr_nonneg
        _ = |∫ t in 0..1, ψ (v + t • (u - v)) (u - v)| := by rw [hsegment]
    _ ≤ ∫ t in 0..1, |ψ (v + t • (u - v)) (u - v)| := by
      exact intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in 0..1, (γ : ℝ) * ((1 - t) * ‖v - x‖ + t * ‖u - x‖) * ‖u - v‖ := by
      exact intervalIntegral.integral_mono_on zero_le_one habsInt hupperInt hpointwise
    _ = (γ : ℝ) * ((‖v - x‖ + ‖u - x‖) / 2) * ‖u - v‖ := by
      calc
        ∫ t in 0..1, (γ : ℝ) * ((1 - t) * ‖v - x‖ + t * ‖u - x‖) * ‖u - v‖ =
            ∫ t in 0..1,
              (((γ : ℝ) * ‖u - v‖) * ((1 - t) * ‖v - x‖ + t * ‖u - x‖)) := by
                congr with t
                ring
        _ = ((γ : ℝ) * ‖u - v‖) *
              ∫ t in 0..1, ((1 - t) * ‖v - x‖ + t * ‖u - x‖) := by
                rw [intervalIntegral.integral_const_mul]
        _ = ((γ : ℝ) * ‖u - v‖) * ((‖v - x‖ + ‖u - x‖) / 2) := by
                rw [affineEndpointDistanceIntegral_eq_average]
        _ = (γ : ℝ) * ((‖v - x‖ + ‖u - x‖) / 2) * ‖u - v‖ := by
                ring
    _ = (γ : ℝ) * ((‖u - x‖ + ‖v - x‖) / 2) * ‖u - v‖ := by
      ring_nf

end LipschitzDerivativeBounds

end Theorem124
