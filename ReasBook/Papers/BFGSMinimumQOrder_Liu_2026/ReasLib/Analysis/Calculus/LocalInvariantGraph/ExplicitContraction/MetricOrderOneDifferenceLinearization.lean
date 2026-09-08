module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricOrderOneSlopeOperator
import all ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricOrderOneSlopeOperator

public section

noncomputable section

open scoped NNReal Topology

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-!
# Exact difference linearization of the order-one slope operator

This leaf isolates the rational finite-difference identity used in the `C¹ → C²` secant
recurrence.  The denominator is evaluated at the candidate section, while the center-feedback
term contains the output of a fixed slope section.  No second derivative of the graph is used.
-/

/-- Helper for Infrastructure I.16a: the selected inverse center map cancels the center map. -/
theorem MetricGraphTransformData.inverseCenter_centerMap
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) (u : ℝ) :
    d.inverseCenter zeta (d.centerMap zeta u) = u := by
  rw [d.inverseCenter_eq zeta]
  exact Function.leftInverse_invFun (d.centerMap_bijective zeta).1 u

/-- Helper for Infrastructure I.16a: before using the cone self-map inequality, the explicit
order-one slope value satisfies the sharper numerator-over-denominator bound. -/
theorem norm_metricOrderOneSlopeValue_le_sharp
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (y : ℝ) :
    ‖metricOrderOneSlopeValue d zeta b y‖ ≤
      ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
        (d.lower : ℝ)⁻¹ := by
  let source := d.inverseCenter zeta y
  have hinverse := abs_inv_metricOrderOneDenominator_le d zeta b source
  have hnumerator := norm_metricOrderOneNumerator_le d zeta b source
  have hlower_inv_nonneg : 0 ≤ (d.lower : ℝ)⁻¹ := by
    positivity
  rw [metricOrderOneSlopeValue, norm_smul, Real.norm_eq_abs]
  calc
    |(metricOrderOneDenominator d zeta b source)⁻¹| *
        ‖metricOrderOneNumerator d zeta b source‖ ≤
      (d.lower : ℝ)⁻¹ *
        ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) := by
      exact mul_le_mul hinverse hnumerator (norm_nonneg _) hlower_inv_nonneg
    _ = ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
        (d.lower : ℝ)⁻¹ := by
      ring

/-- Helper for Infrastructure I.16a: a fixed slope section obeys the sharp pointwise
numerator-over-denominator bound, without assuming differentiability of the section. -/
theorem MetricSlopeSection.norm_apply_le_sharp_of_fixed
    {d : MetricGraphTransformData X}
    {zeta : SmallLipschitzGraph X d.radius d.slope}
    (b : MetricSlopeSection d)
    (hb : metricOrderOneSlopeOperator d zeta b = b) (y : ℝ) :
    ‖b.1 y‖ ≤
      ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
        (d.lower : ℝ)⁻¹ := by
  have hb_apply : (metricOrderOneSlopeOperator d zeta b).1 y = b.1 y :=
    congrArg (fun c : MetricSlopeSection d ↦ c.1 y) hb
  calc
    ‖b.1 y‖ = ‖(metricOrderOneSlopeOperator d zeta b).1 y‖ :=
      congrArg norm hb_apply.symm
    _ = ‖metricOrderOneSlopeValue d zeta b y‖ := by
      rw [metricOrderOneSlopeOperator_apply]
    _ ≤ ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
        (d.lower : ℝ)⁻¹ := norm_metricOrderOneSlopeValue_le_sharp d zeta b y

/-- Helper for Infrastructure I.16a: at a fixed slope section, the numerator equals the
candidate denominator times the fixed output over the corresponding center coordinate. -/
theorem metricOrderOneNumerator_eq_denominator_smul_fixedValue
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d)
    (hb : metricOrderOneSlopeOperator d zeta b = b) (u : ℝ) :
    metricOrderOneNumerator d zeta b u =
      metricOrderOneDenominator d zeta b u • b.1 (d.centerMap zeta u) := by
  have hb_apply :
      metricOrderOneSlopeValue d zeta b (d.centerMap zeta u) =
        b.1 (d.centerMap zeta u) := by
    have hfixed_apply :=
      congrArg (fun c : MetricSlopeSection d ↦ c.1 (d.centerMap zeta u)) hb
    rw [metricOrderOneSlopeOperator_apply] at hfixed_apply
    exact hfixed_apply
  rw [metricOrderOneSlopeValue, d.inverseCenter_centerMap zeta u] at hb_apply
  have hscaled := congrArg
    (fun w : X ↦ metricOrderOneDenominator d zeta b u • w) hb_apply
  have hdenominator_ne : metricOrderOneDenominator d zeta b u ≠ 0 :=
    metricOrderOneDenominator_ne_zero d zeta b u
  rw [smul_smul, mul_inv_cancel₀ hdenominator_ne, one_smul] at hscaled
  exact hscaled

/-- Helper for Infrastructure I.16a: the exact finite-difference coefficient of the rational
order-one slope transform.  Its denominator is taken at the candidate `c`, and its rank-one
feedback uses the fixed output `b (centerMap zeta u)`. -/
def metricOrderOneDifferenceCoefficient
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b c : MetricSlopeSection d) (u : ℝ) : X →L[ℝ] X :=
  (metricOrderOneDenominator d zeta c u)⁻¹ •
    (d.L + derivFiber d zeta u -
      (derivCenterFiber d zeta u).smulRight (b.1 (d.centerMap zeta u)))

/-- Helper for Infrastructure I.16a: application of the order-one difference coefficient
exposes its fiber term and fixed-output center feedback. -/
theorem metricOrderOneDifferenceCoefficient_apply
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b c : MetricSlopeSection d) (u : ℝ) (w : X) :
    metricOrderOneDifferenceCoefficient d zeta b c u w =
      (metricOrderOneDenominator d zeta c u)⁻¹ •
        (d.L w + derivFiber d zeta u w -
          (derivCenterFiber d zeta u w) • b.1 (d.centerMap zeta u)) := by
  rfl

/-- Helper for Infrastructure I.16a: at `y = centerMap zeta u`, subtracting a fixed slope
section from the transformed candidate is the difference coefficient applied to `c u - b u`. -/
theorem metricOrderOneSlopeOperator_sub_fixed_apply_centerMap
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b c : MetricSlopeSection d)
    (hb : metricOrderOneSlopeOperator d zeta b = b) (u : ℝ) :
    (metricOrderOneSlopeOperator d zeta c).1 (d.centerMap zeta u) -
        b.1 (d.centerMap zeta u) =
      metricOrderOneDifferenceCoefficient d zeta b c u (c.1 u - b.1 u) := by
  have hnumerator_fixed :=
    metricOrderOneNumerator_eq_denominator_smul_fixedValue d zeta b hb u
  have hnumerator_sub := metricOrderOneNumerator_sub_eq d zeta c b u
  have hdenominator_sub := metricOrderOneDenominator_sub_eq d zeta c b u
  have hcollapse :
      metricOrderOneNumerator d zeta c u - metricOrderOneNumerator d zeta b u -
          (metricOrderOneDenominator d zeta c u -
            metricOrderOneDenominator d zeta b u) • b.1 (d.centerMap zeta u) =
        metricOrderOneNumerator d zeta c u -
          metricOrderOneDenominator d zeta c u • b.1 (d.centerMap zeta u) := by
    rw [hnumerator_fixed, sub_smul]
    module
  have hdenominator_ne : metricOrderOneDenominator d zeta c u ≠ 0 :=
    metricOrderOneDenominator_ne_zero d zeta c u
  rw [metricOrderOneSlopeOperator_apply, metricOrderOneSlopeValue,
    d.inverseCenter_centerMap zeta u, metricOrderOneDifferenceCoefficient_apply,
    ← hnumerator_sub, ← hdenominator_sub, hcollapse, smul_sub, smul_smul,
    inv_mul_cancel₀ hdenominator_ne, one_smul]

/-- Helper for Infrastructure I.16a: the exact order-one difference coefficient has the sharp
pointwise bound `metricGraphTransformRate * lower⁻¹`, paid for by the fixed slope output bound. -/
theorem metricOrderOneDifferenceCoefficient_apply_norm_le
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b c : MetricSlopeSection d)
    (hb : metricOrderOneSlopeOperator d zeta b = b) (u : ℝ) (w : X) :
    ‖metricOrderOneDifferenceCoefficient d zeta b c u w‖ ≤
      ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹) * ‖w‖ := by
  have hinverse := abs_inv_metricOrderOneDenominator_le d zeta c u
  have hlinear : ‖d.L w‖ ≤ (d.linearRate : ℝ) * ‖w‖ := by
    calc
      ‖d.L w‖ ≤ ‖d.L‖ * ‖w‖ := d.L.le_opNorm w
      _ ≤ (d.linearRate : ℝ) * ‖w‖ :=
        mul_le_mul_of_nonneg_right d.hL (norm_nonneg _)
  have hfiber : ‖derivFiber d zeta u w‖ ≤ (d.epsilon : ℝ) * ‖w‖ := by
    calc
      ‖derivFiber d zeta u w‖ ≤ ‖derivFiber d zeta u‖ * ‖w‖ :=
        (derivFiber d zeta u).le_opNorm w
      _ ≤ (d.epsilon : ℝ) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (norm_derivFiber_le d zeta u) (norm_nonneg _)
  have hcenter : ‖derivCenterFiber d zeta u w‖ ≤ (d.epsilon : ℝ) * ‖w‖ := by
    calc
      ‖derivCenterFiber d zeta u w‖ ≤ ‖derivCenterFiber d zeta u‖ * ‖w‖ :=
        (derivCenterFiber d zeta u).le_opNorm w
      _ ≤ (d.epsilon : ℝ) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (norm_derivCenterFiber_le d zeta u) (norm_nonneg _)
  have hfixed_output :
      ‖b.1 (d.centerMap zeta u)‖ ≤
        ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
          (d.lower : ℝ)⁻¹ :=
    b.norm_apply_le_sharp_of_fixed hb (d.centerMap zeta u)
  have hcenter_bound_nonneg : (0 : ℝ) ≤ (d.epsilon : ℝ) * ‖w‖ := by
    positivity
  have hfeedback :
      ‖(derivCenterFiber d zeta u w) • b.1 (d.centerMap zeta u)‖ ≤
        (((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
          (d.lower : ℝ)⁻¹ * (d.epsilon : ℝ)) * ‖w‖ := by
    calc
      ‖(derivCenterFiber d zeta u w) • b.1 (d.centerMap zeta u)‖ =
          ‖derivCenterFiber d zeta u w‖ * ‖b.1 (d.centerMap zeta u)‖ :=
        norm_smul _ _
      _ ≤ ((d.epsilon : ℝ) * ‖w‖) *
          (((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
            (d.lower : ℝ)⁻¹) := by
        exact mul_le_mul hcenter hfixed_output (norm_nonneg _) hcenter_bound_nonneg
      _ = (((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
          (d.lower : ℝ)⁻¹ * (d.epsilon : ℝ)) * ‖w‖ := by
        ring
  have hfiber_cocycle :
      ‖d.L w + derivFiber d zeta u w‖ ≤
        ((d.linearRate : ℝ) + (d.epsilon : ℝ)) * ‖w‖ := by
    calc
      ‖d.L w + derivFiber d zeta u w‖ ≤ ‖d.L w‖ + ‖derivFiber d zeta u w‖ :=
        norm_add_le _ _
      _ ≤ (d.linearRate : ℝ) * ‖w‖ + (d.epsilon : ℝ) * ‖w‖ :=
        add_le_add hlinear hfiber
      _ = ((d.linearRate : ℝ) + (d.epsilon : ℝ)) * ‖w‖ := by
        ring
  have hcoefficient :
      ‖d.L w + derivFiber d zeta u w -
          (derivCenterFiber d zeta u w) • b.1 (d.centerMap zeta u)‖ ≤
        ((d.linearRate : ℝ) + (d.epsilon : ℝ) +
          ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
            (d.lower : ℝ)⁻¹ * (d.epsilon : ℝ)) * ‖w‖ := by
    calc
      ‖d.L w + derivFiber d zeta u w -
          (derivCenterFiber d zeta u w) • b.1 (d.centerMap zeta u)‖ ≤
          ‖d.L w + derivFiber d zeta u w‖ +
            ‖(derivCenterFiber d zeta u w) • b.1 (d.centerMap zeta u)‖ :=
        norm_sub_le _ _
      _ ≤ ((d.linearRate : ℝ) + (d.epsilon : ℝ)) * ‖w‖ +
          (((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
            (d.lower : ℝ)⁻¹ * (d.epsilon : ℝ)) * ‖w‖ :=
        add_le_add hfiber_cocycle hfeedback
      _ = ((d.linearRate : ℝ) + (d.epsilon : ℝ) +
          ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
            (d.lower : ℝ)⁻¹ * (d.epsilon : ℝ)) * ‖w‖ := by
        ring
  have hrate_real :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) =
        (d.linearRate : ℝ) + (d.epsilon : ℝ) +
          ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
            (d.lower : ℝ)⁻¹ * (d.epsilon : ℝ) := by
    exact metricGraphTransformRate_coe d.lower d.linearRate d.epsilon d.slope
  have hlower_inv_nonneg : (0 : ℝ) ≤ (d.lower : ℝ)⁻¹ := by
    positivity
  rw [metricOrderOneDifferenceCoefficient_apply, norm_smul, Real.norm_eq_abs]
  calc
    |(metricOrderOneDenominator d zeta c u)⁻¹| *
        ‖d.L w + derivFiber d zeta u w -
          (derivCenterFiber d zeta u w) • b.1 (d.centerMap zeta u)‖ ≤
      (d.lower : ℝ)⁻¹ *
        ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
          ‖w‖) := by
      rw [hrate_real]
      exact mul_le_mul hinverse hcoefficient (norm_nonneg _) hlower_inv_nonneg
    _ = ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹) * ‖w‖ := by
      ring

/-- Infrastructure I.16a: the operator norm of the exact order-one difference coefficient is
bounded by `metricGraphTransformRate * lower⁻¹`. -/
theorem norm_metricOrderOneDifferenceCoefficient_le
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b c : MetricSlopeSection d)
    (hb : metricOrderOneSlopeOperator d zeta b = b) (u : ℝ) :
    ‖metricOrderOneDifferenceCoefficient d zeta b c u‖ ≤
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ := by
  have hrate_nonneg :
      (0 : ℝ) ≤
        (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
          (d.lower : ℝ)⁻¹ := by
    positivity
  apply (metricOrderOneDifferenceCoefficient d zeta b c u).opNorm_le_bound hrate_nonneg
  intro w
  exact metricOrderOneDifferenceCoefficient_apply_norm_le d zeta b c hb u w

end LocalInvariantGraph
