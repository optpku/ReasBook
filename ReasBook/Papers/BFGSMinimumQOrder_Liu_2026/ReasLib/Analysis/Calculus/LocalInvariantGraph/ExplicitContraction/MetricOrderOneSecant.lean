module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricOrderOneSlopeOperator
import all ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricOrderOneSlopeOperator
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.RadiusEnvelope
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.UniformSpace.HeineCantor

public section

noncomputable section

open Filter Set
open scoped NNReal Topology

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-!
# The order-one secant bootstrap

The source increment in this file is always the increment selected by the inverse center map.
In particular, no comparison with a slope operator at a globally fixed source increment is used.
-/

/-- Helper for Infrastructure I.16a: the canonical bounded continuous slope selected by the
order-one contraction. -/
noncomputable def metricOrderOneFixedSlope
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1) : MetricSlopeSection d :=
  Classical.choose (existsUnique_metricOrderOneSlopeOperator_fixedPoint d zeta h_bunching)

/-- Helper for Infrastructure I.16a: the canonical order-one slope is fixed by the slope
operator. -/
theorem metricOrderOneFixedSlope_fixed
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1) :
    metricOrderOneSlopeOperator d zeta
        (metricOrderOneFixedSlope d zeta h_bunching) =
      metricOrderOneFixedSlope d zeta h_bunching := by
  exact (Classical.choose_spec
    (existsUnique_metricOrderOneSlopeOperator_fixedPoint d zeta h_bunching)).1

/-- Helper for Infrastructure I.16a: the fixed slope satisfies the explicit inverse-center
denominator/numerator equation at every output center. -/
theorem metricOrderOneFixedSlope_value
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (y : ℝ) :
    metricOrderOneSlopeValue d zeta
        (metricOrderOneFixedSlope d zeta h_bunching) y =
      (metricOrderOneFixedSlope d zeta h_bunching).1 y := by
  have hfixed := congrArg
    (fun b : MetricSlopeSection d ↦ b.1 y)
    (metricOrderOneFixedSlope_fixed d zeta h_bunching)
  simpa only [metricOrderOneSlopeOperator_apply] using hfixed

/-- Helper for Infrastructure I.16a: the source increment corresponding to the output increment
`t` at output center `y`. -/
def metricOrderOneSourceIncrement
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (y t : ℝ) : ℝ :=
  d.inverseCenter zeta (y + t) - d.inverseCenter zeta y

/-- Helper for Infrastructure I.16a: an inverse-center source increment is at most
`lower⁻¹` times its output increment. -/
theorem abs_metricOrderOneSourceIncrement_le
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (y t : ℝ) :
    |metricOrderOneSourceIncrement d zeta y t| ≤
      (d.lower : ℝ)⁻¹ * |t| := by
  have hinverse := (d.inverseCenter_lipschitzWith zeta).dist_le_mul (y + t) y
  simpa only [metricOrderOneSourceIncrement, Real.dist_eq, NNReal.coe_inv,
    add_sub_cancel_left] using hinverse

/-- Helper for Infrastructure I.16a: a nonzero output increment has a nonzero inverse-center
source increment. -/
theorem metricOrderOneSourceIncrement_ne_zero
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (y t : ℝ) (ht : t ≠ 0) :
    metricOrderOneSourceIncrement d zeta y t ≠ 0 := by
  intro hzero
  have hinverse_eq :
      d.inverseCenter zeta (y + t) = d.inverseCenter zeta y :=
    sub_eq_zero.mp hzero
  have hmap_eq := congrArg (d.centerMap zeta) hinverse_eq
  have hinverse_def : d.inverseCenter zeta = Function.invFun (d.centerMap zeta) :=
    d.inverseCenter_eq zeta
  have hsum_eq : y + t = y := by
    calc
      y + t = d.centerMap zeta (d.inverseCenter zeta (y + t)) := by
        rw [hinverse_def]
        exact (Function.rightInverse_invFun (d.centerMap_bijective zeta).2 (y + t)).symm
      _ = d.centerMap zeta (d.inverseCenter zeta y) := hmap_eq
      _ = y := by
        rw [hinverse_def]
        exact Function.rightInverse_invFun (d.centerMap_bijective zeta).2 y
  have ht_zero : t = 0 := by
    linarith [hsum_eq]
  exact ht ht_zero

/-- Helper for Infrastructure I.16a: adding the transported source increment reaches the inverse
center of the translated output point. -/
theorem inverseCenter_add_metricOrderOneSourceIncrement
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (y t : ℝ) :
    d.inverseCenter zeta y + metricOrderOneSourceIncrement d zeta y t =
      d.inverseCenter zeta (y + t) := by
  rw [metricOrderOneSourceIncrement]
  abel

/-- Helper for Infrastructure I.16a: the transported source endpoint maps exactly to the
translated output endpoint. -/
theorem centerMap_add_metricOrderOneSourceIncrement
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (y t : ℝ) :
    d.centerMap zeta
        (d.inverseCenter zeta y + metricOrderOneSourceIncrement d zeta y t) =
      y + t := by
  rw [inverseCenter_add_metricOrderOneSourceIncrement]
  rw [d.inverseCenter_eq zeta]
  exact Function.rightInverse_invFun (d.centerMap_bijective zeta).2 (y + t)

/-- Helper for Infrastructure I.16a: the base inverse center maps back to its output center. -/
theorem centerMap_inverseCenter
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (y : ℝ) :
    d.centerMap zeta (d.inverseCenter zeta y) = y := by
  rw [d.inverseCenter_eq zeta]
  exact Function.rightInverse_invFun (d.centerMap_bijective zeta).2 y

/-- Helper for Infrastructure I.16a: a nonzero translated secant recovers the original graph
increment after multiplication by its increment. -/
theorem smul_metricTranslatedSecantValue
    {d : MetricGraphTransformData X}
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (s u : ℝ) (hs : s ≠ 0) :
    s • metricTranslatedSecantValue zeta s u = zeta (u + s) - zeta u := by
  simp only [metricTranslatedSecantValue, if_neg hs, smul_smul, mul_inv_cancel₀ hs, one_smul]

/-- Helper for Infrastructure I.16a: the two-point Taylor residual of the smooth remainder along
the Lipschitz graph, expressed on the actual graph increment. -/
def metricOrderOneGraphRemainder
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (u s : ℝ) : ℝ × X :=
  d.R (u + s, zeta (u + s)) - d.R (u, zeta u) -
    fderiv ℝ d.R (u, zeta u) (s, zeta (u + s) - zeta u)

/-- Helper for Infrastructure I.16a: the remainder difference is its linearization on the actual
graph increment plus the named two-point Taylor residual. -/
theorem metricOrderOneGraphRemainder_spec
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (u s : ℝ) :
    d.R (u + s, zeta (u + s)) - d.R (u, zeta u) =
      fderiv ℝ d.R (u, zeta u) (s, zeta (u + s) - zeta u) +
        metricOrderOneGraphRemainder d zeta u s := by
  rw [metricOrderOneGraphRemainder]
  abel

/-- Helper for Infrastructure I.16a: a graph increment has product norm no larger than its scalar
increment because the graph-cone slope is at most one. -/
theorem norm_metricOrderOneGraphIncrement_le
    {d : MetricGraphTransformData X}
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (u s : ℝ) :
    ‖((s : ℝ), zeta (u + s) - zeta u)‖ ≤ |s| := by
  have hzeta := (SmallLipschitzGraph.lipschitzWith zeta).dist_le_mul (u + s) u
  have hzeta_slope :
      ‖zeta (u + s) - zeta u‖ ≤ (d.slope : ℝ) * |s| := by
    simpa only [dist_eq_norm, Real.dist_eq, Real.norm_eq_abs, add_sub_cancel_left] using hzeta
  have hslope_one : (d.slope : ℝ) ≤ 1 := by
    exact_mod_cast d.hslope_one
  have hzeta_one : ‖zeta (u + s) - zeta u‖ ≤ |s| := by
    calc
      ‖zeta (u + s) - zeta u‖ ≤ (d.slope : ℝ) * |s| := hzeta_slope
      _ ≤ 1 * |s| := mul_le_mul_of_nonneg_right hslope_one (abs_nonneg s)
      _ = |s| := one_mul _
  rw [Prod.norm_def, Real.norm_eq_abs]
  exact max_le le_rfl hzeta_one

/-- Helper for Infrastructure I.16a: compact support and `C²` regularity make the derivative of
the smooth remainder uniformly continuous on the whole product space. -/
theorem uniformContinuous_metricOrderOneRDerivative
    (d : MetricGraphTransformData X) :
    UniformContinuous (fderiv ℝ d.R) := by
  have hnu_pos : 0 < d.nu := Nat.zero_lt_two.trans_le d.hnu
  have hcontinuous : Continuous (fderiv ℝ d.R) :=
    d.hR_smooth.continuous_fderiv (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnu_pos))
  have hsupport : HasCompactSupport (fderiv ℝ d.R) :=
    d.hR_support.fderiv ℝ
  exact hcontinuous.uniformContinuous_of_tendsto_cocompact
    hsupport.is_zero_at_infty

/-- Helper for Infrastructure I.16a: the two-point remainder of `R` along every admissible
Lipschitz graph is uniformly `o(|s|)` in the scalar graph increment. -/
theorem metricOrderOneGraphRemainder_uniform
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ delta > 0, ∀ u s : ℝ, |s| < delta →
      ‖metricOrderOneGraphRemainder d zeta u s‖ ≤ kappa * |s| := by
  obtain ⟨delta, hdelta, hmodulus⟩ :=
    Metric.uniformContinuous_iff.mp (uniformContinuous_metricOrderOneRDerivative d)
      kappa hkappa
  refine ⟨delta, hdelta, ?_⟩
  intro u s hs
  let p : ℝ × X := (u, zeta u)
  let q : ℝ × X := (u + s, zeta (u + s))
  let A : (ℝ × X) →L[ℝ] (ℝ × X) := fderiv ℝ d.R p
  let g : (ℝ × X) → (ℝ × X) := fun w ↦ d.R w - A w
  have hnu_ne : ((d.nu : ℕ) : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_two.trans_le d.hnu)
  have hR_differentiable : Differentiable ℝ d.R :=
    d.hR_smooth.differentiable hnu_ne
  have hchord : q - p = ((s : ℝ), zeta (u + s) - zeta u) := by
    dsimp only [q, p]
    apply Prod.ext
    · simp only [Prod.fst_sub]
      ring
    · simp only [Prod.snd_sub]
  have hpq_norm : ‖q - p‖ ≤ |s| := by
    calc
      ‖q - p‖ = ‖((s : ℝ), zeta (u + s) - zeta u)‖ :=
        congrArg (fun z : ℝ × X ↦ ‖z‖) hchord
      _ ≤ |s| := norm_metricOrderOneGraphIncrement_le zeta u s
  have hpq_dist : dist p q < delta := by
    rw [dist_comm, dist_eq_norm]
    exact hpq_norm.trans_lt hs
  have hderivative_bound : ∀ w ∈ segment ℝ p q,
      ‖fderiv ℝ d.R w - A‖ ≤ kappa := by
    intro w hw
    have hwp_norm : ‖w - p‖ ≤ ‖q - p‖ := norm_sub_le_of_mem_segment hw
    have hpq_norm_lt : ‖q - p‖ < delta := by
      simpa only [dist_comm p q, dist_eq_norm] using hpq_dist
    have hwp_dist : dist w p < delta := by
      rw [dist_eq_norm]
      exact hwp_norm.trans_lt hpq_norm_lt
    have hclose := hmodulus hwp_dist
    simpa only [A, dist_eq_norm] using hclose.le
  have hg_derivative : ∀ w ∈ segment ℝ p q,
      HasFDerivWithinAt g (fderiv ℝ d.R w - A) (segment ℝ p q) w := by
    intro w hw
    exact ((hR_differentiable w).hasFDerivAt.sub A.hasFDerivAt).hasFDerivWithinAt
  have hmean := (convex_segment p q).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hg_derivative hderivative_bound (left_mem_segment ℝ p q) (right_mem_segment ℝ p q)
  have hvec :
      metricOrderOneGraphRemainder d zeta u s = g q - g p := by
    rw [metricOrderOneGraphRemainder, ← hchord]
    change d.R q - d.R p - A (q - p) = (d.R q - A q) - (d.R p - A p)
    rw [map_sub]
    abel
  have hmean_graph :
      ‖metricOrderOneGraphRemainder d zeta u s‖ ≤ kappa * ‖q - p‖ := by
    rw [hvec]
    exact hmean
  exact hmean_graph.trans
    (mul_le_mul_of_nonneg_left hpq_norm hkappa.le)

/-- Helper for Infrastructure I.16a: on a nonzero graph increment, the derivative of `R` on the
actual graph chord is the increment times the derivative on the translated secant direction. -/
theorem metricOrderOneGraphDerivative_eq_smul
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (u s : ℝ) (hs : s ≠ 0) :
    fderiv ℝ d.R (u, zeta u) (s, zeta (u + s) - zeta u) =
      s • fderiv ℝ d.R (u, zeta u)
        (1, metricTranslatedSecantValue zeta s u) := by
  have hdirection :
      ((s : ℝ), zeta (u + s) - zeta u) =
        s • ((1 : ℝ), metricTranslatedSecantValue zeta s u) := by
    ext
    · simp only [Prod.smul_fst, smul_eq_mul, mul_one]
    · exact (smul_metricTranslatedSecantValue zeta s u hs).symm
  rw [hdirection, map_smul]

/-- Helper for Infrastructure I.16a: the center output increment is the source increment times the
candidate secant denominator, plus the center Taylor residual. -/
theorem metricOrderOneCenterIncrement_eq
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (y t : ℝ) (ht : t ≠ 0) :
    let u := d.inverseCenter zeta y
    let s := metricOrderOneSourceIncrement d zeta y t
    let a := metricTranslatedSecantSection zeta s
    t = s * metricOrderOneDenominator d zeta a u +
      (metricOrderOneGraphRemainder d zeta u s).1 := by
  dsimp only
  let u := d.inverseCenter zeta y
  let s := metricOrderOneSourceIncrement d zeta y t
  let a := metricTranslatedSecantSection zeta s
  have hs : s ≠ 0 := metricOrderOneSourceIncrement_ne_zero d zeta y t ht
  have ha_apply : a.1 u = metricTranslatedSecantValue zeta s u := by
    simpa only [a, metricTranslatedSecantSection] using
      metricTranslatedSecantBoundedSection_apply zeta s u
  have hsource_add :
      u + s = d.inverseCenter zeta y +
        metricOrderOneSourceIncrement d zeta y t := by
    rfl
  have hcenterDifference :
      t = s + (d.R (u + s, zeta (u + s)) - d.R (u, zeta u)).1 := by
    calc
      t = (y + t) - y := by ring
      _ = d.centerMap zeta (u + s) - d.centerMap zeta u := by
        rw [hsource_add]
        rw [centerMap_add_metricOrderOneSourceIncrement, centerMap_inverseCenter]
      _ = s + (d.R (u + s, zeta (u + s)) - d.R (u, zeta u)).1 := by
        rw [d.centerMap_eq zeta, Prod.fst_sub]
        ring
  calc
    t = s + (d.R (u + s, zeta (u + s)) - d.R (u, zeta u)).1 :=
      hcenterDifference
    _ = s +
        (s • fderiv ℝ d.R (u, zeta u)
          (1, metricTranslatedSecantValue zeta s u)).1 +
        (metricOrderOneGraphRemainder d zeta u s).1 := by
      rw [metricOrderOneGraphRemainder_spec,
        metricOrderOneGraphDerivative_eq_smul d zeta u s hs]
      simp only [Prod.fst_add]
      ring
    _ = s * metricOrderOneDenominator d zeta a u +
        (metricOrderOneGraphRemainder d zeta u s).1 := by
      rw [metricOrderOneDenominator_eq, ha_apply]
      simp only [Prod.smul_fst, smul_eq_mul]
      ring

/-- Helper for Infrastructure I.16a: fixed-graph invariance transports the stable output increment
to the source secant numerator, up to the stable Taylor residual. -/
theorem metricOrderOneStableIncrement_eq
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (y t : ℝ) (ht : t ≠ 0) :
    let u := d.inverseCenter zeta y
    let s := metricOrderOneSourceIncrement d zeta y t
    let a := metricTranslatedSecantSection zeta s
    zeta (y + t) - zeta y =
      s • metricOrderOneNumerator d zeta a u +
        (metricOrderOneGraphRemainder d zeta u s).2 := by
  dsimp only
  let u := d.inverseCenter zeta y
  let s := metricOrderOneSourceIncrement d zeta y t
  let a := metricTranslatedSecantSection zeta s
  have hs : s ≠ 0 := metricOrderOneSourceIncrement_ne_zero d zeta y t ht
  have ha_apply : a.1 u = metricTranslatedSecantValue zeta s u := by
    simpa only [a, metricTranslatedSecantSection] using
      metricTranslatedSecantBoundedSection_apply zeta s u
  have hsourceSecant :
      zeta (u + s) - zeta u = s • a.1 u := by
    rw [ha_apply]
    exact (smul_metricTranslatedSecantValue zeta s u hs).symm
  have hnext_center : d.centerMap zeta (u + s) = y + t := by
    exact centerMap_add_metricOrderOneSourceIncrement d zeta y t
  have hbase_center : d.centerMap zeta u = y := by
    exact centerMap_inverseCenter d zeta y
  have hinvarianceDifference :
      zeta (y + t) - zeta y =
        d.L (zeta (u + s) - zeta u) +
          (d.R (u + s, zeta (u + s)) - d.R (u, zeta u)).2 := by
    have hnext := d.fixedGraph_equation zeta hfixed (u + s)
    have hbase := d.fixedGraph_equation zeta hfixed u
    rw [hnext_center] at hnext
    rw [hbase_center] at hbase
    rw [hnext, hbase, map_sub, Prod.snd_sub]
    abel
  calc
    zeta (y + t) - zeta y =
        d.L (zeta (u + s) - zeta u) +
          (d.R (u + s, zeta (u + s)) - d.R (u, zeta u)).2 :=
      hinvarianceDifference
    _ = d.L (s • a.1 u) +
        (s • fderiv ℝ d.R (u, zeta u) (1, a.1 u)).2 +
          (metricOrderOneGraphRemainder d zeta u s).2 := by
      rw [hsourceSecant, metricOrderOneGraphRemainder_spec,
        metricOrderOneGraphDerivative_eq_smul d zeta u s hs]
      rw [← ha_apply]
      simp only [Prod.snd_add]
      abel
    _ = s • metricOrderOneNumerator d zeta a u +
        (metricOrderOneGraphRemainder d zeta u s).2 := by
      rw [map_smul, metricOrderOneNumerator_eq]
      simp only [Prod.smul_snd, smul_add]

/-- Helper for Infrastructure I.16a: multiplying a slope value by its nonzero denominator recovers
the corresponding numerator. -/
theorem metricOrderOneDenominator_smul_slopeValue
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (y : ℝ) :
    metricOrderOneDenominator d zeta b (d.inverseCenter zeta y) •
        metricOrderOneSlopeValue d zeta b y =
      metricOrderOneNumerator d zeta b (d.inverseCenter zeta y) := by
  rw [metricOrderOneSlopeValue, smul_smul,
    mul_inv_cancel₀ (metricOrderOneDenominator_ne_zero d zeta b (d.inverseCenter zeta y)),
    one_smul]

/-- Helper for Infrastructure I.16a: after multiplying by the first candidate denominator, the
slope-value difference has only one inverse denominator. -/
theorem metricOrderOneDenominator_smul_slopeValue_sub_eq
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (a b : MetricSlopeSection d) (y : ℝ) :
    let u := d.inverseCenter zeta y
    metricOrderOneDenominator d zeta a u •
        (metricOrderOneSlopeValue d zeta a y -
          metricOrderOneSlopeValue d zeta b y) =
      metricOrderOneNumerator d zeta a u - metricOrderOneNumerator d zeta b u +
        ((metricOrderOneDenominator d zeta b u -
            metricOrderOneDenominator d zeta a u) *
          (metricOrderOneDenominator d zeta b u)⁻¹) •
            metricOrderOneNumerator d zeta b u := by
  dsimp only
  have hdenominator_a :=
    metricOrderOneDenominator_ne_zero d zeta a (d.inverseCenter zeta y)
  have hdenominator_b :=
    metricOrderOneDenominator_ne_zero d zeta b (d.inverseCenter zeta y)
  rw [metricOrderOneSlopeValue, metricOrderOneSlopeValue, smul_sub,
    smul_smul, smul_smul, mul_inv_cancel₀ hdenominator_a, one_smul]
  have hscalar :
      metricOrderOneDenominator d zeta a (d.inverseCenter zeta y) *
          (metricOrderOneDenominator d zeta b (d.inverseCenter zeta y))⁻¹ =
        1 - ((metricOrderOneDenominator d zeta b (d.inverseCenter zeta y) -
            metricOrderOneDenominator d zeta a (d.inverseCenter zeta y)) *
          (metricOrderOneDenominator d zeta b (d.inverseCenter zeta y))⁻¹) := by
    field_simp [hdenominator_b]
    ring
  rw [hscalar, sub_smul, one_smul]
  abel

/-- Helper for Infrastructure I.16a: denominator cancellation improves the normalized slope
contraction to the raw graph-transform rate before the inverse-center scale is applied. -/
theorem norm_metricOrderOneDenominator_smul_slopeValue_sub_le
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (a b : MetricSlopeSection d) (y : ℝ) :
    let u := d.inverseCenter zeta y
    ‖metricOrderOneDenominator d zeta a u •
        (metricOrderOneSlopeValue d zeta a y -
          metricOrderOneSlopeValue d zeta b y)‖ ≤
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        ‖a.1 u - b.1 u‖ := by
  dsimp only
  let u := d.inverseCenter zeta y
  have hnumDifference := norm_metricOrderOneNumerator_sub_le d zeta a b u
  have hdenDifference_raw := abs_metricOrderOneDenominator_sub_le d zeta b a u
  have hdenDifference :
      |metricOrderOneDenominator d zeta b u -
        metricOrderOneDenominator d zeta a u| ≤
      (d.epsilon : ℝ) * ‖a.1 u - b.1 u‖ := by
    simpa only [norm_sub_rev] using hdenDifference_raw
  have hinverse := abs_inv_metricOrderOneDenominator_le d zeta b u
  have hnum := norm_metricOrderOneNumerator_le d zeta b u
  have hcoefficient :
      |(metricOrderOneDenominator d zeta b u -
          metricOrderOneDenominator d zeta a u) *
        (metricOrderOneDenominator d zeta b u)⁻¹| ≤
      (d.epsilon : ℝ) * (d.lower : ℝ)⁻¹ * ‖a.1 u - b.1 u‖ := by
    rw [abs_mul]
    calc
      |metricOrderOneDenominator d zeta b u -
          metricOrderOneDenominator d zeta a u| *
          |(metricOrderOneDenominator d zeta b u)⁻¹| ≤
        ((d.epsilon : ℝ) * ‖a.1 u - b.1 u‖) * (d.lower : ℝ)⁻¹ := by
          exact mul_le_mul hdenDifference hinverse (abs_nonneg _)
            (mul_nonneg d.epsilon.coe_nonneg (norm_nonneg _))
      _ = (d.epsilon : ℝ) * (d.lower : ℝ)⁻¹ *
          ‖a.1 u - b.1 u‖ := by ring
  have hcorrection :
      ‖((metricOrderOneDenominator d zeta b u -
            metricOrderOneDenominator d zeta a u) *
          (metricOrderOneDenominator d zeta b u)⁻¹) •
            metricOrderOneNumerator d zeta b u‖ ≤
        (((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
          (d.lower : ℝ)⁻¹ * (d.epsilon : ℝ)) *
            ‖a.1 u - b.1 u‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |(metricOrderOneDenominator d zeta b u -
            metricOrderOneDenominator d zeta a u) *
          (metricOrderOneDenominator d zeta b u)⁻¹| *
            ‖metricOrderOneNumerator d zeta b u‖ ≤
        ((d.epsilon : ℝ) * (d.lower : ℝ)⁻¹ * ‖a.1 u - b.1 u‖) *
          ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) := by
            exact mul_le_mul hcoefficient hnum (norm_nonneg _)
              (mul_nonneg
                (mul_nonneg d.epsilon.coe_nonneg (inv_nonneg.mpr d.lower.coe_nonneg))
                (norm_nonneg _))
      _ = (((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
          (d.lower : ℝ)⁻¹ * (d.epsilon : ℝ)) *
            ‖a.1 u - b.1 u‖ := by ring
  rw [metricOrderOneDenominator_smul_slopeValue_sub_eq]
  calc
    ‖metricOrderOneNumerator d zeta a u - metricOrderOneNumerator d zeta b u +
        ((metricOrderOneDenominator d zeta b u -
            metricOrderOneDenominator d zeta a u) *
          (metricOrderOneDenominator d zeta b u)⁻¹) •
            metricOrderOneNumerator d zeta b u‖ ≤
      ‖metricOrderOneNumerator d zeta a u - metricOrderOneNumerator d zeta b u‖ +
        ‖((metricOrderOneDenominator d zeta b u -
              metricOrderOneDenominator d zeta a u) *
            (metricOrderOneDenominator d zeta b u)⁻¹) •
              metricOrderOneNumerator d zeta b u‖ := norm_add_le _ _
    _ ≤ ((d.linearRate : ℝ) + (d.epsilon : ℝ)) * ‖a.1 u - b.1 u‖ +
        (((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
          (d.lower : ℝ)⁻¹ * (d.epsilon : ℝ)) *
            ‖a.1 u - b.1 u‖ := add_le_add hnumDifference hcorrection
    _ = (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        ‖a.1 u - b.1 u‖ := by
      rw [metricGraphTransformRate_coe]
      ring

/-! The preceding endpoint formulas are deliberately separated from the following algebraic
residual identity.  This keeps the source finite-difference calculation independent of any
already-established differentiability of the fixed graph. -/

/-- Helper for Infrastructure I.16a: the variable-increment graph secant differs from the
order-one slope value by the two Taylor residuals.  The source increment is the inverse-center
increment selected by `(y,t)`, so no fixed-increment or differentiability hypothesis is hidden in
this identity. -/
theorem metricOrderOneVariableIncrement_residual_eq
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (y t : ℝ) (ht : t ≠ 0) :
    let u := d.inverseCenter zeta y
    let s := metricOrderOneSourceIncrement d zeta y t
    let a := metricTranslatedSecantSection zeta s
    metricTranslatedSecantValue zeta t y -
        metricOrderOneSlopeValue d zeta a y =
      t⁻¹ • (metricOrderOneGraphRemainder d zeta u s).2 +
        (t⁻¹ * s - (metricOrderOneDenominator d zeta a u)⁻¹) •
          metricOrderOneNumerator d zeta a u := by
  dsimp only
  let u := d.inverseCenter zeta y
  let s := metricOrderOneSourceIncrement d zeta y t
  let a := metricTranslatedSecantSection zeta s
  have hstable := metricOrderOneStableIncrement_eq d zeta hfixed y t ht
  have hstable' :
      zeta (y + t) - zeta y =
        s • metricOrderOneNumerator d zeta a u +
          (metricOrderOneGraphRemainder d zeta u s).2 := by
    simpa only [u, s, a] using hstable
  rw [metricTranslatedSecantValue, if_neg ht, hstable']
  change t⁻¹ •
      (s • metricOrderOneNumerator d zeta a u +
        (metricOrderOneGraphRemainder d zeta u s).2) -
      (metricOrderOneDenominator d zeta a u)⁻¹ •
        metricOrderOneNumerator d zeta a u = _
  rw [smul_add, smul_smul]
  module

/-- Helper for Infrastructure I.16a: the center-coordinate residual scalar can be eliminated from
the variable-increment identity.  The resulting expression exposes both Taylor components and is
the form used for uniform residual estimates. -/
theorem metricOrderOneVariableIncrement_residual_eq_center
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (y t : ℝ) (ht : t ≠ 0) :
    let u := d.inverseCenter zeta y
    let s := metricOrderOneSourceIncrement d zeta y t
    let a := metricTranslatedSecantSection zeta s
    metricTranslatedSecantValue zeta t y -
        metricOrderOneSlopeValue d zeta a y =
      t⁻¹ • (metricOrderOneGraphRemainder d zeta u s).2 +
        (-(t⁻¹ * (metricOrderOneGraphRemainder d zeta u s).1 *
          (metricOrderOneDenominator d zeta a u)⁻¹)) •
          metricOrderOneNumerator d zeta a u := by
  dsimp only
  let u := d.inverseCenter zeta y
  let s := metricOrderOneSourceIncrement d zeta y t
  let a := metricTranslatedSecantSection zeta s
  have hres := metricOrderOneVariableIncrement_residual_eq d zeta hfixed y t ht
  have hres' :
      metricTranslatedSecantValue zeta t y -
          metricOrderOneSlopeValue d zeta a y =
        t⁻¹ • (metricOrderOneGraphRemainder d zeta u s).2 +
          (t⁻¹ * s - (metricOrderOneDenominator d zeta a u)⁻¹) •
            metricOrderOneNumerator d zeta a u := by
    simpa only [u, s, a] using hres
  have hcenter := metricOrderOneCenterIncrement_eq d zeta y t ht
  have hcenter' :
      t = s * metricOrderOneDenominator d zeta a u +
        (metricOrderOneGraphRemainder d zeta u s).1 := by
    simpa only [u, s, a] using hcenter
  have hden : metricOrderOneDenominator d zeta a u ≠ 0 :=
    metricOrderOneDenominator_ne_zero d zeta a u
  have hscalar :
      t⁻¹ * s - (metricOrderOneDenominator d zeta a u)⁻¹ =
        -(t⁻¹ * (metricOrderOneGraphRemainder d zeta u s).1 *
          (metricOrderOneDenominator d zeta a u)⁻¹) := by
    field_simp [ht, hden]
    nlinarith [hcenter']
  rw [hres', hscalar]

/-- Helper for Infrastructure I.16a: a norm-level residual estimate for the variable-increment
secant.  This is intentionally stated before any limit argument, so it can be consumed by either
the contraction bootstrap or a later `Tendsto` adapter. -/
theorem norm_metricOrderOneVariableIncrement_residual_le
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (y t : ℝ) (ht : t ≠ 0) :
    let u := d.inverseCenter zeta y
    let s := metricOrderOneSourceIncrement d zeta y t
    let a := metricTranslatedSecantSection zeta s
    ‖metricTranslatedSecantValue zeta t y -
        metricOrderOneSlopeValue d zeta a y‖ ≤
      |t|⁻¹ * ‖(metricOrderOneGraphRemainder d zeta u s).2‖ +
        |t⁻¹ * (metricOrderOneGraphRemainder d zeta u s).1 *
            (metricOrderOneDenominator d zeta a u)⁻¹| *
          ‖metricOrderOneNumerator d zeta a u‖ := by
  dsimp only
  let u := d.inverseCenter zeta y
  let s := metricOrderOneSourceIncrement d zeta y t
  let a := metricTranslatedSecantSection zeta s
  have hres := metricOrderOneVariableIncrement_residual_eq_center d zeta hfixed y t ht
  have hres' :
      metricTranslatedSecantValue zeta t y -
          metricOrderOneSlopeValue d zeta a y =
        t⁻¹ • (metricOrderOneGraphRemainder d zeta u s).2 +
          (-(t⁻¹ * (metricOrderOneGraphRemainder d zeta u s).1 *
            (metricOrderOneDenominator d zeta a u)⁻¹)) •
            metricOrderOneNumerator d zeta a u := by
    simpa only [u, s, a] using hres
  rw [hres']
  calc
    ‖t⁻¹ • (metricOrderOneGraphRemainder d zeta u s).2 +
        (-(t⁻¹ * (metricOrderOneGraphRemainder d zeta u s).1 *
          (metricOrderOneDenominator d zeta a u)⁻¹)) •
          metricOrderOneNumerator d zeta a u‖ ≤
      ‖t⁻¹ • (metricOrderOneGraphRemainder d zeta u s).2‖ +
        ‖(-(t⁻¹ * (metricOrderOneGraphRemainder d zeta u s).1 *
          (metricOrderOneDenominator d zeta a u)⁻¹)) •
          metricOrderOneNumerator d zeta a u‖ := norm_add_le _ _
    _ = |t|⁻¹ * ‖(metricOrderOneGraphRemainder d zeta u s).2‖ +
        |t⁻¹ * (metricOrderOneGraphRemainder d zeta u s).1 *
            (metricOrderOneDenominator d zeta a u)⁻¹| *
          ‖metricOrderOneNumerator d zeta a u‖ := by
      rw [norm_smul, norm_smul, norm_neg, Real.norm_eq_abs, abs_inv]
      rw [Real.norm_eq_abs]

/-- Helper for Infrastructure I.16a: the explicit epsilon bridge for a variable-increment
secant.  The only analytic input is the displayed two-point remainder estimate; all denominator
and numerator constants come from the closed slope-section certificate. -/
theorem norm_metricOrderOneVariableIncrement_residual_le_of_remainder
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    {kappa : ℝ} (hkappa : 0 ≤ kappa)
    (y t : ℝ) (ht : t ≠ 0)
    (hrem :
      let u := d.inverseCenter zeta y
      let s := metricOrderOneSourceIncrement d zeta y t
      ‖metricOrderOneGraphRemainder d zeta u s‖ ≤ kappa * |s|) :
    let u := d.inverseCenter zeta y
    let s := metricOrderOneSourceIncrement d zeta y t
    let a := metricTranslatedSecantSection zeta s
    ‖metricTranslatedSecantValue zeta t y -
        metricOrderOneSlopeValue d zeta a y‖ ≤
      |t|⁻¹ * (kappa * |s|) +
        (|t|⁻¹ * (kappa * |s|) * (d.lower : ℝ)⁻¹) *
          ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) := by
  dsimp only at hrem ⊢
  let u := d.inverseCenter zeta y
  let s := metricOrderOneSourceIncrement d zeta y t
  let a := metricTranslatedSecantSection zeta s
  have hrem' :
      ‖metricOrderOneGraphRemainder d zeta u s‖ ≤ kappa * |s| := by
    simpa only [u, s] using hrem
  have hbase := norm_metricOrderOneVariableIncrement_residual_le
    d zeta hfixed y t ht
  have hbase' :
      ‖metricTranslatedSecantValue zeta t y -
          metricOrderOneSlopeValue d zeta a y‖ ≤
        |t|⁻¹ * ‖(metricOrderOneGraphRemainder d zeta u s).2‖ +
          |t⁻¹ * (metricOrderOneGraphRemainder d zeta u s).1 *
              (metricOrderOneDenominator d zeta a u)⁻¹| *
            ‖metricOrderOneNumerator d zeta a u‖ := by
    simpa only [u, s, a] using hbase
  have hE2 :
      ‖(metricOrderOneGraphRemainder d zeta u s).2‖ ≤ kappa * |s| := by
    exact (norm_snd_le (metricOrderOneGraphRemainder d zeta u s)).trans hrem'
  have hE1 :
      |(metricOrderOneGraphRemainder d zeta u s).1| ≤ kappa * |s| := by
    simpa only [Real.norm_eq_abs] using
      (norm_fst_le (metricOrderOneGraphRemainder d zeta u s)).trans hrem'
  have hden_inv :
      |(metricOrderOneDenominator d zeta a u)⁻¹| ≤ (d.lower : ℝ)⁻¹ :=
    abs_inv_metricOrderOneDenominator_le d zeta a u
  have hnum :
      ‖metricOrderOneNumerator d zeta a u‖ ≤
        (d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ) :=
    norm_metricOrderOneNumerator_le d zeta a u
  have ht_inv_nonneg : 0 ≤ |t|⁻¹ := inv_nonneg.mpr (abs_nonneg t)
  have hks_nonneg : 0 ≤ kappa * |s| :=
    mul_nonneg hkappa (abs_nonneg s)
  have hfirst :
      |t|⁻¹ * ‖(metricOrderOneGraphRemainder d zeta u s).2‖ ≤
        |t|⁻¹ * (kappa * |s|) :=
    mul_le_mul_of_nonneg_left hE2 ht_inv_nonneg
  have hcoeff :
      |t⁻¹ * (metricOrderOneGraphRemainder d zeta u s).1 *
          (metricOrderOneDenominator d zeta a u)⁻¹| ≤
        |t|⁻¹ * (kappa * |s|) * (d.lower : ℝ)⁻¹ := by
    calc
      |t⁻¹ * (metricOrderOneGraphRemainder d zeta u s).1 *
          (metricOrderOneDenominator d zeta a u)⁻¹| =
          |t⁻¹| * |(metricOrderOneGraphRemainder d zeta u s).1| *
            |(metricOrderOneDenominator d zeta a u)⁻¹| := by
        rw [abs_mul, abs_mul]
      _ ≤ |t⁻¹| * (kappa * |s|) *
          |(metricOrderOneDenominator d zeta a u)⁻¹| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hE1 (abs_nonneg _)) (abs_nonneg _)
      _ ≤ |t⁻¹| * (kappa * |s|) * (d.lower : ℝ)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hden_inv
          (mul_nonneg (abs_nonneg _) hks_nonneg)
      _ = |t|⁻¹ * (kappa * |s|) * (d.lower : ℝ)⁻¹ := by
        rw [abs_inv]
  have hconstant_nonneg :
      0 ≤ |t|⁻¹ * (kappa * |s|) * (d.lower : ℝ)⁻¹ := by
    positivity
  have hnum_nonneg :
      0 ≤ (d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ) := by
    positivity
  have hsecond :
      |t⁻¹ * (metricOrderOneGraphRemainder d zeta u s).1 *
          (metricOrderOneDenominator d zeta a u)⁻¹| *
          ‖metricOrderOneNumerator d zeta a u‖ ≤
        (|t|⁻¹ * (kappa * |s|) * (d.lower : ℝ)⁻¹) *
          ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) := by
    exact mul_le_mul hcoeff hnum (norm_nonneg _)
      hconstant_nonneg
  exact hbase'.trans (add_le_add hfirst hsecond)

/-- Helper for Infrastructure I.16a: a majorant tending to zero turns the variable-increment
secant residual into a genuine punctured-neighborhood `Tendsto` statement.  The majorant is an
explicit input so source-side reindexing or denominator estimates cannot be hidden in this bridge.
-/
theorem tendsto_metricOrderOneVariableIncrement_residual_of_majorant
    {y : ℝ} (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (majorant : ℝ → ℝ)
    (hbound :
      ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        ‖metricTranslatedSecantValue zeta t y -
            metricOrderOneSlopeValue d zeta
              (metricTranslatedSecantSection zeta
                (metricOrderOneSourceIncrement d zeta y t)) y‖ ≤
          majorant t)
    (hmajorant : Tendsto majorant (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    Tendsto
      (fun t : ℝ =>
        metricTranslatedSecantValue zeta t y -
          metricOrderOneSlopeValue d zeta
            (metricTranslatedSecantSection zeta
              (metricOrderOneSourceIncrement d zeta y t)) y)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  exact squeeze_zero_norm' hbound hmajorant

end LocalInvariantGraph
