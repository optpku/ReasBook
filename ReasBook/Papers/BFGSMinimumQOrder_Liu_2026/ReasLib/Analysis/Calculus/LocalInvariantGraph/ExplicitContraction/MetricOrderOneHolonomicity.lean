module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricOrderOneSecant
import all ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricOrderOneSecant
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricRawDefectEnvelope

public section

noncomputable section

open Filter
open scoped NNReal Topology

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-!
# The non-circular order-one holonomicity bootstrap

The proof controls the untranslated first-order defect directly.  Its recurrence is transported
through the inverse center map, with the denominator cancelled before the inverse-coordinate
Lipschitz loss is paid.  Thus no differentiability of the fixed graph is used in constructing its
derivative.
-/

/-- Helper for Infrastructure I.16a: the raw first-order defect of the fixed graph relative to
the canonical slope section. -/
noncomputable def metricOrderOneRawDefect
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (y t : ℝ) : X :=
  zeta (y + t) - zeta y -
    t • (metricOrderOneFixedSlope d zeta h_bunching).1 y

/-- Helper for Infrastructure I.16a: the order-one raw defect vanishes at the zero increment. -/
theorem metricOrderOneRawDefect_zero
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (y : ℝ) :
    metricOrderOneRawDefect d zeta h_bunching y 0 = 0 := by
  simp only [metricOrderOneRawDefect, add_zero, sub_self, zero_smul, sub_zero]

/-- Helper for Infrastructure I.16a: the raw defect splits into the denominator-cancelled slope
difference and the two components of the graph Taylor remainder. -/
theorem metricOrderOneRawDefect_decomposition
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (y t : ℝ) (ht : t ≠ 0) :
    let sourceCenter := d.inverseCenter zeta y
    let sourceIncrement := metricOrderOneSourceIncrement d zeta y t
    let secant := metricTranslatedSecantSection zeta sourceIncrement
    let fixedSlope := metricOrderOneFixedSlope d zeta h_bunching
    let remainder := metricOrderOneGraphRemainder d zeta sourceCenter sourceIncrement
    metricOrderOneRawDefect d zeta h_bunching y t =
      sourceIncrement •
          (metricOrderOneDenominator d zeta secant sourceCenter •
            (metricOrderOneSlopeValue d zeta secant y -
              metricOrderOneSlopeValue d zeta fixedSlope y)) +
        remainder.2 - remainder.1 • fixedSlope.1 y := by
  dsimp only
  let sourceCenter := d.inverseCenter zeta y
  let sourceIncrement := metricOrderOneSourceIncrement d zeta y t
  let secant := metricTranslatedSecantSection zeta sourceIncrement
  let fixedSlope := metricOrderOneFixedSlope d zeta h_bunching
  let remainder := metricOrderOneGraphRemainder d zeta sourceCenter sourceIncrement
  have hstable := metricOrderOneStableIncrement_eq d zeta hfixed y t ht
  have hstable' :
      zeta (y + t) - zeta y =
        sourceIncrement • metricOrderOneNumerator d zeta secant sourceCenter +
          remainder.2 := by
    simpa only [sourceCenter, sourceIncrement, secant, remainder] using hstable
  have hcenter := metricOrderOneCenterIncrement_eq d zeta y t ht
  have hcenter' :
      t = sourceIncrement *
          metricOrderOneDenominator d zeta secant sourceCenter + remainder.1 := by
    simpa only [sourceCenter, sourceIncrement, secant, remainder] using hcenter
  have hdenominator :
      metricOrderOneDenominator d zeta secant sourceCenter •
          metricOrderOneSlopeValue d zeta secant y =
        metricOrderOneNumerator d zeta secant sourceCenter := by
    simpa only [sourceCenter] using
      metricOrderOneDenominator_smul_slopeValue d zeta secant y
  have hfixedValue :
      metricOrderOneSlopeValue d zeta fixedSlope y = fixedSlope.1 y := by
    exact metricOrderOneFixedSlope_value d zeta h_bunching y
  rw [metricOrderOneRawDefect]
  calc
    zeta (y + t) - zeta y - t • fixedSlope.1 y =
        (sourceIncrement • metricOrderOneNumerator d zeta secant sourceCenter +
            remainder.2) - t • fixedSlope.1 y := by
      rw [hstable']
    _ = (sourceIncrement • metricOrderOneNumerator d zeta secant sourceCenter +
            remainder.2) -
          (sourceIncrement * metricOrderOneDenominator d zeta secant sourceCenter +
            remainder.1) • fixedSlope.1 y := by
      rw [hcenter']
    _ = sourceIncrement •
          (metricOrderOneDenominator d zeta secant sourceCenter •
            (metricOrderOneSlopeValue d zeta secant y -
              metricOrderOneSlopeValue d zeta fixedSlope y)) +
          remainder.2 - remainder.1 • fixedSlope.1 y := by
      rw [← hdenominator, ← hfixedValue]
      simp only [smul_sub, smul_smul, add_smul]
      module

/-- Helper for Infrastructure I.16a: at the inverse-center increment, the transported raw defect
is exactly the source increment times the difference between the secant and fixed slope fields. -/
theorem metricOrderOneRawDefect_source_identity
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (y t : ℝ) (ht : t ≠ 0) :
    let sourceCenter := d.inverseCenter zeta y
    let sourceIncrement := metricOrderOneSourceIncrement d zeta y t
    let secant := metricTranslatedSecantSection zeta sourceIncrement
    let fixedSlope := metricOrderOneFixedSlope d zeta h_bunching
    metricOrderOneRawDefect d zeta h_bunching sourceCenter sourceIncrement =
      sourceIncrement • (secant.1 sourceCenter - fixedSlope.1 sourceCenter) := by
  dsimp only
  let sourceCenter := d.inverseCenter zeta y
  let sourceIncrement := metricOrderOneSourceIncrement d zeta y t
  let secant := metricTranslatedSecantSection zeta sourceIncrement
  let fixedSlope := metricOrderOneFixedSlope d zeta h_bunching
  have hsourceIncrement : sourceIncrement ≠ 0 :=
    metricOrderOneSourceIncrement_ne_zero d zeta y t ht
  have hsecantValue :
      secant.1 sourceCenter =
        metricTranslatedSecantValue zeta sourceIncrement sourceCenter := by
    dsimp only [secant, metricTranslatedSecantSection]
    exact metricTranslatedSecantBoundedSection_apply zeta sourceIncrement sourceCenter
  have hsecant :
      sourceIncrement • secant.1 sourceCenter =
        zeta (sourceCenter + sourceIncrement) - zeta sourceCenter := by
    rw [hsecantValue]
    exact smul_metricTranslatedSecantValue zeta sourceIncrement sourceCenter hsourceIncrement
  rw [metricOrderOneRawDefect, ← hsecant, smul_sub]

/-- Helper for Infrastructure I.16a: the Taylor-remainder contribution to the raw defect is at
most twice the product-space remainder norm. -/
theorem norm_metricOrderOneRemainderCorrection_le
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (u s y : ℝ) :
    let remainder := metricOrderOneGraphRemainder d zeta u s
    let fixedSlope := metricOrderOneFixedSlope d zeta h_bunching
    ‖remainder.2 - remainder.1 • fixedSlope.1 y‖ ≤ 2 * ‖remainder‖ := by
  dsimp only
  let remainder := metricOrderOneGraphRemainder d zeta u s
  let fixedSlope := metricOrderOneFixedSlope d zeta h_bunching
  have hslopeBound : ‖fixedSlope.1 y‖ ≤ (d.slope : ℝ) :=
    fixedSlope.norm_apply_le y
  have hslopeOne : ‖fixedSlope.1 y‖ ≤ 1 := by
    exact hslopeBound.trans (by exact_mod_cast d.hslope_one)
  have hfirst : ‖remainder.1‖ ≤ ‖remainder‖ := norm_fst_le remainder
  have hsecond : ‖remainder.2‖ ≤ ‖remainder‖ := norm_snd_le remainder
  have hsmul : ‖remainder.1 • fixedSlope.1 y‖ ≤ ‖remainder‖ := by
    rw [norm_smul]
    calc
      ‖remainder.1‖ * ‖fixedSlope.1 y‖ ≤ ‖remainder‖ * 1 := by
        exact mul_le_mul hfirst hslopeOne (norm_nonneg _) (norm_nonneg _)
      _ = ‖remainder‖ := mul_one _
  calc
    ‖remainder.2 - remainder.1 • fixedSlope.1 y‖ ≤
        ‖remainder.2‖ + ‖remainder.1 • fixedSlope.1 y‖ := norm_sub_le _ _
    _ ≤ ‖remainder‖ + ‖remainder‖ := add_le_add hsecond hsmul
    _ = 2 * ‖remainder‖ := by ring

/-- Helper for Infrastructure I.16a: denominator cancellation yields the raw inverse-center
recurrence with graph-transform rate before estimating the Taylor remainder. -/
theorem norm_metricOrderOneRawDefect_le
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (y t : ℝ) (ht : t ≠ 0) :
    let sourceCenter := d.inverseCenter zeta y
    let sourceIncrement := metricOrderOneSourceIncrement d zeta y t
    let remainder := metricOrderOneGraphRemainder d zeta sourceCenter sourceIncrement
    ‖metricOrderOneRawDefect d zeta h_bunching y t‖ ≤
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
          ‖metricOrderOneRawDefect d zeta h_bunching sourceCenter sourceIncrement‖ +
        2 * ‖remainder‖ := by
  dsimp only
  let sourceCenter := d.inverseCenter zeta y
  let sourceIncrement := metricOrderOneSourceIncrement d zeta y t
  let secant := metricTranslatedSecantSection zeta sourceIncrement
  let fixedSlope := metricOrderOneFixedSlope d zeta h_bunching
  let remainder := metricOrderOneGraphRemainder d zeta sourceCenter sourceIncrement
  have hdecomposition :=
    metricOrderOneRawDefect_decomposition d zeta hfixed h_bunching y t ht
  have hdecomposition' :
      metricOrderOneRawDefect d zeta h_bunching y t =
        sourceIncrement •
            (metricOrderOneDenominator d zeta secant sourceCenter •
              (metricOrderOneSlopeValue d zeta secant y -
                metricOrderOneSlopeValue d zeta fixedSlope y)) +
          remainder.2 - remainder.1 • fixedSlope.1 y := by
    simpa only [sourceCenter, sourceIncrement, secant, fixedSlope, remainder] using
      hdecomposition
  have hcancel :=
    norm_metricOrderOneDenominator_smul_slopeValue_sub_le
      d zeta secant fixedSlope y
  have hcancel' :
      ‖metricOrderOneDenominator d zeta secant sourceCenter •
          (metricOrderOneSlopeValue d zeta secant y -
            metricOrderOneSlopeValue d zeta fixedSlope y)‖ ≤
        (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
          ‖secant.1 sourceCenter - fixedSlope.1 sourceCenter‖ := by
    simpa only [sourceCenter] using hcancel
  have hsource :=
    metricOrderOneRawDefect_source_identity d zeta h_bunching y t ht
  have hsource' :
      metricOrderOneRawDefect d zeta h_bunching sourceCenter sourceIncrement =
        sourceIncrement •
          (secant.1 sourceCenter - fixedSlope.1 sourceCenter) := by
    simpa only [sourceCenter, sourceIncrement, secant, fixedSlope] using hsource
  have hprincipal :
      ‖sourceIncrement •
          (metricOrderOneDenominator d zeta secant sourceCenter •
            (metricOrderOneSlopeValue d zeta secant y -
              metricOrderOneSlopeValue d zeta fixedSlope y))‖ ≤
        (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
          ‖metricOrderOneRawDefect d zeta h_bunching sourceCenter sourceIncrement‖ := by
    calc
      ‖sourceIncrement •
          (metricOrderOneDenominator d zeta secant sourceCenter •
            (metricOrderOneSlopeValue d zeta secant y -
              metricOrderOneSlopeValue d zeta fixedSlope y))‖ =
          |sourceIncrement| *
            ‖metricOrderOneDenominator d zeta secant sourceCenter •
              (metricOrderOneSlopeValue d zeta secant y -
                metricOrderOneSlopeValue d zeta fixedSlope y)‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |sourceIncrement| *
          ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
            ‖secant.1 sourceCenter - fixedSlope.1 sourceCenter‖) := by
        exact mul_le_mul_of_nonneg_left hcancel' (abs_nonneg sourceIncrement)
      _ = (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
          ‖sourceIncrement •
            (secant.1 sourceCenter - fixedSlope.1 sourceCenter)‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        ring
      _ = (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
          ‖metricOrderOneRawDefect d zeta h_bunching sourceCenter sourceIncrement‖ := by
        rw [hsource']
  have hremainder :
      ‖remainder.2 - remainder.1 • fixedSlope.1 y‖ ≤ 2 * ‖remainder‖ := by
    simpa only [remainder, fixedSlope] using
      norm_metricOrderOneRemainderCorrection_le d zeta h_bunching sourceCenter sourceIncrement y
  calc
    ‖metricOrderOneRawDefect d zeta h_bunching y t‖ =
        ‖sourceIncrement •
            (metricOrderOneDenominator d zeta secant sourceCenter •
              (metricOrderOneSlopeValue d zeta secant y -
                metricOrderOneSlopeValue d zeta fixedSlope y)) +
          (remainder.2 - remainder.1 • fixedSlope.1 y)‖ := by
      rw [hdecomposition']
      congr 1
      module
    _ ≤
        ‖sourceIncrement •
            (metricOrderOneDenominator d zeta secant sourceCenter •
              (metricOrderOneSlopeValue d zeta secant y -
                metricOrderOneSlopeValue d zeta fixedSlope y))‖ +
          ‖remainder.2 - remainder.1 • fixedSlope.1 y‖ := norm_add_le _ _
    _ ≤
        (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
            ‖metricOrderOneRawDefect d zeta h_bunching sourceCenter sourceIncrement‖ +
          2 * ‖remainder‖ := add_le_add hprincipal hremainder

/-- Helper for Infrastructure I.16a: the raw defect is globally bounded by a linear function of
its scalar increment, uniformly in the base point. -/
theorem norm_metricOrderOneRawDefect_le_linear
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (y t : ℝ) :
    ‖metricOrderOneRawDefect d zeta h_bunching y t‖ ≤
      2 * (d.slope : ℝ) * |t| := by
  let fixedSlope := metricOrderOneFixedSlope d zeta h_bunching
  have hgraph := (SmallLipschitzGraph.lipschitzWith zeta).dist_le_mul (y + t) y
  have hgraph' :
      ‖zeta (y + t) - zeta y‖ ≤ (d.slope : ℝ) * |t| := by
    simpa only [dist_eq_norm, Real.dist_eq, Real.norm_eq_abs,
      add_sub_cancel_left] using hgraph
  have hslope : ‖fixedSlope.1 y‖ ≤ (d.slope : ℝ) :=
    fixedSlope.norm_apply_le y
  calc
    ‖metricOrderOneRawDefect d zeta h_bunching y t‖ ≤
        ‖zeta (y + t) - zeta y‖ + ‖t • fixedSlope.1 y‖ := by
      rw [metricOrderOneRawDefect]
      exact norm_sub_le _ _
    _ ≤ (d.slope : ℝ) * |t| + |t| * (d.slope : ℝ) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add hgraph' (mul_le_mul_of_nonneg_left hslope (abs_nonneg t))
    _ = 2 * (d.slope : ℝ) * |t| := by ring

/-- Helper for Infrastructure I.16a: the order-one raw defect is uniformly bounded on a fixed
neighborhood of the zero increment. -/
theorem metricOrderOneRawDefect_locallyUniformlyBounded
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1) :
    ∃ cutoff > 0, ∃ bound ≥ 0, ∀ y t : ℝ, ‖t‖ < cutoff →
      ‖metricOrderOneRawDefect d zeta h_bunching y t‖ ≤ bound := by
  refine ⟨1, zero_lt_one, 2 * (d.slope : ℝ), ?_, ?_⟩
  · positivity
  · intro y t ht
    have ht_abs : |t| < 1 := by
      simpa only [Real.norm_eq_abs] using ht
    calc
      ‖metricOrderOneRawDefect d zeta h_bunching y t‖ ≤
          2 * (d.slope : ℝ) * |t| :=
        norm_metricOrderOneRawDefect_le_linear d zeta h_bunching y t
      _ ≤ 2 * (d.slope : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left ht_abs.le (by positivity)
      _ = 2 * (d.slope : ℝ) := mul_one _

/-- Helper for Infrastructure I.16a: the inverse-center transport has Lipschitz factor
`lower⁻¹` on every scalar increment. -/
theorem norm_metricOrderOneInverseCenterIncrement_le
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (y t : ℝ) :
    ‖d.inverseCenter zeta (y + t) - d.inverseCenter zeta y‖ ≤
      (d.lower : ℝ)⁻¹ * ‖t‖ := by
  have hsourceIncrement :
      metricOrderOneSourceIncrement d zeta y t =
        d.inverseCenter zeta (y + t) - d.inverseCenter zeta y := by
    have htransport := inverseCenter_add_metricOrderOneSourceIncrement d zeta y t
    linarith
  rw [← hsourceIncrement]
  simpa only [Real.norm_eq_abs] using
    abs_metricOrderOneSourceIncrement_le d zeta y t

/-- Helper for Infrastructure I.16a: uniform smallness of the graph Taylor remainder turns the
raw identity into the affine recurrence required by the radius-envelope theorem. -/
theorem metricOrderOneRawDefect_inverseRecurrence
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1) :
    ∀ e > 0, ∃ delta > 0, ∀ y t : ℝ, t ≠ 0 → ‖t‖ < delta →
      ‖metricOrderOneRawDefect d zeta h_bunching y t‖ ≤
        (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
            ‖metricOrderOneRawDefect d zeta h_bunching (d.inverseCenter zeta y)
              (d.inverseCenter zeta (y + t) - d.inverseCenter zeta y)‖ +
          e * ‖t‖ := by
  intro e he
  let transportFactor : ℝ := (d.lower : ℝ)⁻¹
  have htransportFactor : 0 < transportFactor := by
    exact inv_pos.mpr (by exact_mod_cast d.hlower_pos)
  let kappa : ℝ := e / (2 * transportFactor)
  have hkappa : 0 < kappa := by
    exact div_pos he (mul_pos two_pos htransportFactor)
  obtain ⟨remainderRadius, hremainderRadius, hremainder⟩ :=
    metricOrderOneGraphRemainder_uniform d zeta hkappa
  let delta : ℝ := remainderRadius / transportFactor
  have hdelta : 0 < delta := div_pos hremainderRadius htransportFactor
  refine ⟨delta, hdelta, ?_⟩
  intro y t ht ht_delta
  let sourceCenter := d.inverseCenter zeta y
  let sourceIncrement := metricOrderOneSourceIncrement d zeta y t
  let remainder := metricOrderOneGraphRemainder d zeta sourceCenter sourceIncrement
  have hsourceIncrement_value :
      sourceIncrement = metricOrderOneSourceIncrement d zeta y t := by
    rfl
  have hsource_le : |sourceIncrement| ≤ transportFactor * |t| := by
    rw [hsourceIncrement_value]
    simpa only [transportFactor] using
      abs_metricOrderOneSourceIncrement_le d zeta y t
  have ht_abs : |t| < delta := by
    simpa only [Real.norm_eq_abs] using ht_delta
  have hsource_small : |sourceIncrement| < remainderRadius := by
    calc
      |sourceIncrement| ≤ transportFactor * |t| := hsource_le
      _ < transportFactor * delta :=
        mul_lt_mul_of_pos_left ht_abs htransportFactor
      _ = remainderRadius := by
        dsimp only [delta]
        field_simp [ne_of_gt htransportFactor]
  have hremainderBound : ‖remainder‖ ≤ kappa * |sourceIncrement| := by
    exact hremainder sourceCenter sourceIncrement hsource_small
  have hbase := norm_metricOrderOneRawDefect_le d zeta hfixed h_bunching y t ht
  have hbase' :
      ‖metricOrderOneRawDefect d zeta h_bunching y t‖ ≤
        (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
            ‖metricOrderOneRawDefect d zeta h_bunching sourceCenter sourceIncrement‖ +
          2 * ‖remainder‖ := by
    simpa only [sourceCenter, sourceIncrement, remainder] using hbase
  have hkappa_identity : 2 * (kappa * transportFactor) = e := by
    dsimp only [kappa]
    field_simp [ne_of_gt htransportFactor]
  have hremainderSmall : 2 * ‖remainder‖ ≤ e * ‖t‖ := by
    calc
      2 * ‖remainder‖ ≤ 2 * (kappa * |sourceIncrement|) := by
        exact mul_le_mul_of_nonneg_left hremainderBound (by positivity)
      _ ≤ 2 * (kappa * (transportFactor * |t|)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsource_le hkappa.le) (by positivity)
      _ = (2 * (kappa * transportFactor)) * |t| := by ring
      _ = e * ‖t‖ := by rw [hkappa_identity, Real.norm_eq_abs]
  have hsourceCenter_eq : sourceCenter = d.inverseCenter zeta y := by
    rfl
  have hsourceIncrement_eq :
      sourceIncrement = d.inverseCenter zeta (y + t) - d.inverseCenter zeta y := by
    have htransport :
        d.inverseCenter zeta y + sourceIncrement =
          d.inverseCenter zeta (y + t) := by
      rw [hsourceIncrement_value]
      exact inverseCenter_add_metricOrderOneSourceIncrement d zeta y t
    linarith
  have hadd_swap_left :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
            ‖metricOrderOneRawDefect d zeta h_bunching sourceCenter sourceIncrement‖ +
          2 * ‖remainder‖ =
        2 * ‖remainder‖ +
          (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
            ‖metricOrderOneRawDefect d zeta h_bunching sourceCenter sourceIncrement‖ := by
    ring
  have hadd_swap_right :
      e * ‖t‖ +
          (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
            ‖metricOrderOneRawDefect d zeta h_bunching sourceCenter sourceIncrement‖ =
        (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
            ‖metricOrderOneRawDefect d zeta h_bunching sourceCenter sourceIncrement‖ +
          e * ‖t‖ := by
    ring
  calc
    ‖metricOrderOneRawDefect d zeta h_bunching y t‖ ≤
        (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
            ‖metricOrderOneRawDefect d zeta h_bunching sourceCenter sourceIncrement‖ +
          2 * ‖remainder‖ := hbase'
    _ ≤
        (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
            ‖metricOrderOneRawDefect d zeta h_bunching sourceCenter sourceIncrement‖ +
          e * ‖t‖ := by
      calc
        (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
              ‖metricOrderOneRawDefect d zeta h_bunching sourceCenter sourceIncrement‖ +
            2 * ‖remainder‖ =
          2 * ‖remainder‖ +
            (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
              ‖metricOrderOneRawDefect d zeta h_bunching sourceCenter sourceIncrement‖ :=
          hadd_swap_left
        _ ≤ e * ‖t‖ +
            (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
              ‖metricOrderOneRawDefect d zeta h_bunching sourceCenter sourceIncrement‖ :=
          add_le_add hremainderSmall (le_refl _)
        _ =
            (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
                ‖metricOrderOneRawDefect d zeta h_bunching sourceCenter sourceIncrement‖ +
              e * ‖t‖ := hadd_swap_right
    _ =
        (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
            ‖metricOrderOneRawDefect d zeta h_bunching
                (d.inverseCenter zeta y)
                (d.inverseCenter zeta (y + t) - d.inverseCenter zeta y)‖ +
          e * ‖t‖ := by
      rw [← hsourceCenter_eq, ← hsourceIncrement_eq]

/-- Helper for Infrastructure I.16a: the raw first-order defect is little-o of its increment at
every base point. -/
theorem metricOrderOneRawDefect_isLittleO
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1) :
    ∀ y : ℝ,
      (fun t : ℝ ↦ metricOrderOneRawDefect d zeta h_bunching y t) =o[𝓝 0]
        (fun t : ℝ ↦ t) := by
  apply LocalCutoff.GraphTransform.rawDefect_isLittleO_of_inverseRecurrence
    (metricOrderOneRawDefect d zeta h_bunching) (d.inverseCenter zeta)
    (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ)
    (d.lower : ℝ)⁻¹
  · exact metricOrderOneRawDefect_zero d zeta h_bunching
  · exact metricOrderOneRawDefect_locallyUniformlyBounded d zeta h_bunching
  · exact norm_metricOrderOneInverseCenterIncrement_le d zeta
  · exact (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope).coe_nonneg
  · exact_mod_cast d.hrate
  · exact inv_pos.mpr (by exact_mod_cast d.hlower_pos)
  · exact h_bunching
  · exact metricOrderOneRawDefect_inverseRecurrence d zeta hfixed h_bunching

/-- Helper for Infrastructure I.16a: the canonical fixed slope is the derivative of the fixed
Lipschitz graph at every center. -/
theorem metricFixedGraph_hasDerivAt_orderOne
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1) :
    ∀ y : ℝ,
      HasDerivAt (zeta : ℝ → X)
        ((metricOrderOneFixedSlope d zeta h_bunching).1 y) y := by
  apply LocalCutoff.GraphTransform.predecessorHasDerivAt_of_rawDefectLittleO
    (zeta : ℝ → X) (metricOrderOneFixedSlope d zeta h_bunching).1
  intro y
  simpa only [metricOrderOneRawDefect] using
    metricOrderOneRawDefect_isLittleO d zeta hfixed h_bunching y

/-- Helper for Infrastructure I.16a: the derivative of the fixed graph is the canonical
continuous slope field selected by the order-one contraction. -/
theorem metricFixedGraph_deriv_eq_orderOneSlope
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1) :
    deriv (zeta : ℝ → X) = (metricOrderOneFixedSlope d zeta h_bunching).1 := by
  funext y
  exact (metricFixedGraph_hasDerivAt_orderOne d zeta hfixed h_bunching y).deriv

/-- Infrastructure I.16a: the metric graph-transform fixed graph is continuously differentiable
under the order-one bunching inequality, without assuming differentiability in the construction
of its canonical slope. -/
theorem metricFixedGraph_contDiff_one_of_orderOneBunching
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1) :
    ContDiff ℝ 1 (zeta : ℝ → X) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro y
    exact (metricFixedGraph_hasDerivAt_orderOne d zeta hfixed h_bunching y).differentiableAt
  · rw [metricFixedGraph_deriv_eq_orderOneSlope d zeta hfixed h_bunching]
    exact (metricOrderOneFixedSlope d zeta h_bunching).1.continuous

end LocalInvariantGraph
