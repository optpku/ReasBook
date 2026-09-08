module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricFiberDerivative
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.SectionContraction

public section

noncomputable section

open scoped NNReal Topology

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-!
# The order-one slope operator

This file realizes the non-circular `r = 1` stage of the metric graph transform.  Its
operator acts only on the closed ball of bounded continuous slope fields.  This restriction is
mathematical: the lower bound for the scalar denominator uses the prescribed slope bound and is
not available for an arbitrary bounded section.

No differentiability of the fixed Lipschitz graph is assumed.  The derivative of the smooth
remainder is evaluated on a candidate direction `(1, b u)` instead.
-/

/-- Helper for Infrastructure I.16a: bounded continuous candidate slope fields whose uniform
norm is at most the graph-cone slope. -/
abbrev MetricSlopeSection (d : MetricGraphTransformData X) :=
  {b : BoundedContinuousFunction ℝ X // ‖b‖ ≤ (d.slope : ℝ)}

/-- Helper for Infrastructure I.16a: the uniform slope constraint cuts out a closed subset of
the bounded continuous section space. -/
theorem isClosed_metricSlopeSection (d : MetricGraphTransformData X) :
    IsClosed {b : BoundedContinuousFunction ℝ X | ‖b‖ ≤ (d.slope : ℝ)} := by
  exact isClosed_le continuous_norm continuous_const

/-- Helper for Infrastructure I.16a: the zero bounded section satisfies every nonnegative
slope bound. -/
theorem zero_mem_metricSlopeSection (d : MetricGraphTransformData X) :
    ‖(0 : BoundedContinuousFunction ℝ X)‖ ≤ (d.slope : ℝ) := by
  simpa only [norm_zero] using d.slope.coe_nonneg

/-- Helper for Infrastructure I.16a: the canonical zero candidate slope field. -/
def zeroMetricSlopeSection (d : MetricGraphTransformData X) : MetricSlopeSection d :=
  ⟨0, zero_mem_metricSlopeSection d⟩

/-- Helper for Infrastructure I.16a: every metric slope-section ball is inhabited by zero. -/
instance instNonemptyMetricSlopeSection (d : MetricGraphTransformData X) :
    Nonempty (MetricSlopeSection d) :=
  ⟨zeroMetricSlopeSection d⟩

/-- Helper for Infrastructure I.16a: the closed slope-section ball is complete whenever the
stable target space is complete. -/
instance instCompleteSpaceMetricSlopeSection [CompleteSpace X]
    (d : MetricGraphTransformData X) : CompleteSpace (MetricSlopeSection d) := by
  exact (isClosed_metricSlopeSection d).isComplete.completeSpace_coe

/-- Helper for Infrastructure I.16a: a slope section obeys its prescribed norm bound at every
center parameter. -/
theorem MetricSlopeSection.norm_apply_le
    {d : MetricGraphTransformData X} (b : MetricSlopeSection d) (u : ℝ) :
    ‖b.1 u‖ ≤ (d.slope : ℝ) := by
  exact (BoundedContinuousFunction.norm_coe_le_norm b.1 u).trans b.2

/-- Helper for Infrastructure I.16a: the translated secant value of a Lipschitz graph, with
the zero increment assigned the zero vector. -/
def metricTranslatedSecantValue
    {d : MetricGraphTransformData X}
    (zeta : SmallLipschitzGraph X d.radius d.slope) (t x : ℝ) : X :=
  if t = 0 then 0 else t⁻¹ • (zeta (x + t) - zeta x)

/-- Helper for Infrastructure I.16a: for each fixed increment, the translated secant varies
continuously with its base point. -/
theorem continuous_metricTranslatedSecantValue
    {d : MetricGraphTransformData X}
    (zeta : SmallLipschitzGraph X d.radius d.slope) (t : ℝ) :
    Continuous (metricTranslatedSecantValue zeta t) := by
  by_cases ht : t = 0
  · subst t
    have hvalue :
        metricTranslatedSecantValue zeta 0 = fun _ : ℝ ↦ (0 : X) := by
      funext x
      simp only [metricTranslatedSecantValue, if_pos]
    rw [hvalue]
    exact continuous_const
  · have hvalue :
        metricTranslatedSecantValue zeta t =
          fun x : ℝ ↦ t⁻¹ • (zeta (x + t) - zeta x) := by
      funext x
      simp only [metricTranslatedSecantValue, if_neg ht]
    have hscale : Continuous (fun _ : ℝ ↦ t⁻¹) :=
      continuous_const
    have hshift : Continuous (fun x : ℝ ↦ x + t) :=
      continuous_id.add continuous_const
    rw [hvalue]
    exact hscale.smul
      ((zeta.1.continuous.comp hshift).sub zeta.1.continuous)

/-- Helper for Infrastructure I.16a: every translated secant of a graph in the Lipschitz cone
has pointwise norm at most the cone slope. -/
theorem norm_metricTranslatedSecantValue_le
    {d : MetricGraphTransformData X}
    (zeta : SmallLipschitzGraph X d.radius d.slope) (t x : ℝ) :
    ‖metricTranslatedSecantValue zeta t x‖ ≤ (d.slope : ℝ) := by
  by_cases ht : t = 0
  · subst t
    simp only [metricTranslatedSecantValue, if_pos, norm_zero]
    exact d.slope.coe_nonneg
  · have hsecant := (SmallLipschitzGraph.lipschitzWith zeta).dist_le_mul (x + t) x
    have hdiff : ‖zeta (x + t) - zeta x‖ ≤ (d.slope : ℝ) * |t| := by
      simpa only [dist_eq_norm, Real.dist_eq, add_sub_cancel_left, Real.norm_eq_abs] using hsecant
    have htpos : 0 < |t| := abs_pos.mpr ht
    rw [metricTranslatedSecantValue, if_neg ht, norm_smul, Real.norm_eq_abs, abs_inv]
    calc
      |t|⁻¹ * ‖zeta (x + t) - zeta x‖ ≤
          |t|⁻¹ * ((d.slope : ℝ) * |t|) :=
        mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr htpos.le)
      _ = (d.slope : ℝ) := by
        field_simp

/-- Helper for Infrastructure I.16a: the translated secant bundled as a bounded continuous
section with the sharp uniform slope bound. -/
def metricTranslatedSecantBoundedSection
    {d : MetricGraphTransformData X}
    (zeta : SmallLipschitzGraph X d.radius d.slope) (t : ℝ) :
    BoundedContinuousFunction ℝ X :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (metricTranslatedSecantValue zeta t)
    (continuous_metricTranslatedSecantValue zeta t)
    d.slope
    (norm_metricTranslatedSecantValue_le zeta t)

/-- Helper for Infrastructure I.16a: evaluation of the bundled translated secant is the
pointwise translated secant value. -/
theorem metricTranslatedSecantBoundedSection_apply
    {d : MetricGraphTransformData X}
    (zeta : SmallLipschitzGraph X d.radius d.slope) (t x : ℝ) :
    metricTranslatedSecantBoundedSection zeta t x =
      metricTranslatedSecantValue zeta t x := by
  rfl

/-- Helper for Infrastructure I.16a: the bundled translated secant has uniform norm at most
the graph-cone slope. -/
theorem norm_metricTranslatedSecantBoundedSection_le
    {d : MetricGraphTransformData X}
    (zeta : SmallLipschitzGraph X d.radius d.slope) (t : ℝ) :
    ‖metricTranslatedSecantBoundedSection zeta t‖ ≤ (d.slope : ℝ) := by
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
    (continuous_metricTranslatedSecantValue zeta t) d.slope.coe_nonneg
    (norm_metricTranslatedSecantValue_le zeta t)

/-- Helper for Infrastructure I.16a: every translated secant is a member of the closed
slope-section ball, including the zero-increment section. -/
def metricTranslatedSecantSection
    {d : MetricGraphTransformData X}
    (zeta : SmallLipschitzGraph X d.radius d.slope) (t : ℝ) : MetricSlopeSection d :=
  ⟨metricTranslatedSecantBoundedSection zeta t,
    norm_metricTranslatedSecantBoundedSection_le zeta t⟩

/-- Helper for Infrastructure I.16a: the derivative of the smooth remainder, restricted to
the fixed graph, is continuous as a continuous-linear-map-valued function. -/
theorem continuous_metricOrderOneRDerivative
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) :
    Continuous (fun u : ℝ => fderiv ℝ d.R (u, (zeta : ℝ → X) u)) := by
  have hnu_pos : 0 < d.nu := Nat.zero_lt_two.trans_le d.hnu
  have hR_fderiv : Continuous (fderiv ℝ d.R) :=
    d.hR_smooth.continuous_fderiv (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnu_pos))
  have hgraph : Continuous (fun u : ℝ => (u, (zeta : ℝ → X) u)) :=
    continuous_id.prodMk zeta.1.continuous
  exact hR_fderiv.comp hgraph

/-- Helper for Infrastructure I.16a: the center-coordinate first-slot derivative of the
remainder along the graph. -/
def metricOrderOneCenterSource
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) (u : ℝ) : ℝ :=
  ((fderiv ℝ d.R (u, (zeta : ℝ → X) u)) (1, 0)).1

/-- Helper for Infrastructure I.16a: the stable-coordinate first-slot derivative of the
remainder along the graph. -/
def metricOrderOneStableSource
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) (u : ℝ) : X :=
  ((fderiv ℝ d.R (u, (zeta : ℝ → X) u)) (1, 0)).2

/-- Helper for Infrastructure I.16a: the center first-slot derivative varies continuously
along a Lipschitz graph. -/
theorem continuous_metricOrderOneCenterSource
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) :
    Continuous (metricOrderOneCenterSource d zeta) := by
  have happ := (continuous_metricOrderOneRDerivative d zeta).clm_apply
    (continuous_const : Continuous (fun _ : ℝ => ((1 : ℝ), (0 : X))))
  exact continuous_fst.comp happ

/-- Helper for Infrastructure I.16a: the stable first-slot derivative varies continuously
along a Lipschitz graph. -/
theorem continuous_metricOrderOneStableSource
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) :
    Continuous (metricOrderOneStableSource d zeta) := by
  have happ := (continuous_metricOrderOneRDerivative d zeta).clm_apply
    (continuous_const : Continuous (fun _ : ℝ => ((1 : ℝ), (0 : X))))
  exact continuous_snd.comp happ

/-- Helper for Infrastructure I.16a: the scalar derivative of the center change in a
candidate graph direction. -/
def metricOrderOneDenominator
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (u : ℝ) : ℝ :=
  1 + metricOrderOneCenterSource d zeta u + derivCenterFiber d zeta u (b.1 u)

/-- Helper for Infrastructure I.16a: the derivative of the stable output in a candidate
graph direction. -/
def metricOrderOneNumerator
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (u : ℝ) : X :=
  d.L (b.1 u) + metricOrderOneStableSource d zeta u + derivFiber d zeta u (b.1 u)

/-- Helper for Infrastructure I.16a: the split denominator equals the full derivative of the
center component on the candidate direction `(1, b u)`. -/
theorem metricOrderOneDenominator_eq
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (u : ℝ) :
    metricOrderOneDenominator d zeta b u =
      1 + ((fderiv ℝ d.R (u, (zeta : ℝ → X) u)) (1, b.1 u)).1 := by
  rw [metricOrderOneDenominator, metricOrderOneCenterSource, derivCenterFiber_apply]
  have hdirection : ((1 : ℝ), b.1 u) = ((1 : ℝ), (0 : X)) + (0, b.1 u) := by
    ext
    · simp only [Prod.fst_add, add_zero]
    · simp only [Prod.snd_add, zero_add]
  rw [hdirection, map_add]
  rw [Prod.fst_add]
  rw [add_assoc]

/-- Helper for Infrastructure I.16a: the split numerator equals the linear stable term plus
the full remainder derivative on the candidate direction `(1, b u)`. -/
theorem metricOrderOneNumerator_eq
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (u : ℝ) :
    metricOrderOneNumerator d zeta b u =
      d.L (b.1 u) +
        ((fderiv ℝ d.R (u, (zeta : ℝ → X) u)) (1, b.1 u)).2 := by
  rw [metricOrderOneNumerator, metricOrderOneStableSource, derivFiber_apply]
  have hdirection : ((1 : ℝ), b.1 u) = ((1 : ℝ), (0 : X)) + (0, b.1 u) := by
    ext
    · simp only [Prod.fst_add, add_zero]
    · simp only [Prod.snd_add, zero_add]
  rw [hdirection, map_add]
  rw [Prod.snd_add]
  rw [add_assoc]

/-- Helper for Infrastructure I.16a: every candidate direction `(1, b u)` has product norm at
most one because the cone slope is at most one. -/
theorem norm_metricOrderOneDirection_le_one
    (d : MetricGraphTransformData X)
    (b : MetricSlopeSection d) (u : ℝ) :
    ‖((1 : ℝ), b.1 u)‖ ≤ 1 := by
  have hb_slope : ‖b.1 u‖ ≤ (d.slope : ℝ) := b.norm_apply_le u
  have hslope_one : (d.slope : ℝ) ≤ 1 := by
    exact_mod_cast d.hslope_one
  have hone : ‖(1 : ℝ)‖ ≤ 1 := by
    norm_num
  rw [Prod.norm_def]
  exact max_le hone (hb_slope.trans hslope_one)

/-- Helper for Infrastructure I.16a: the derivative of the Lipschitz remainder has the
corresponding operator bound on every direction. -/
theorem norm_metricOrderOneRDerivative_apply_le
    (d : MetricGraphTransformData X) (p : ℝ × X) (w : ℝ × X) :
    ‖(fderiv ℝ d.R p) w‖ ≤ (d.epsilon : ℝ) * ‖w‖ := by
  have hfderiv : ‖fderiv ℝ d.R p‖ ≤ (d.epsilon : ℝ) :=
    norm_fderiv_le_of_lipschitz (𝕜 := ℝ) d.hR_lipschitz
  calc
    ‖(fderiv ℝ d.R p) w‖ ≤ ‖fderiv ℝ d.R p‖ * ‖w‖ :=
      (fderiv ℝ d.R p).le_opNorm w
    _ ≤ (d.epsilon : ℝ) * ‖w‖ :=
      mul_le_mul_of_nonneg_right hfderiv (norm_nonneg _)

/-- Helper for Infrastructure I.16a: the remainder derivative on a candidate slope direction
has norm at most `epsilon`. -/
theorem norm_metricOrderOneRDirection_le
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (u : ℝ) :
    ‖(fderiv ℝ d.R (u, (zeta : ℝ → X) u)) (1, b.1 u)‖ ≤
      (d.epsilon : ℝ) := by
  calc
    ‖(fderiv ℝ d.R (u, (zeta : ℝ → X) u)) (1, b.1 u)‖ ≤
        (d.epsilon : ℝ) * ‖((1 : ℝ), b.1 u)‖ :=
      norm_metricOrderOneRDerivative_apply_le d _ _
    _ ≤ (d.epsilon : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (norm_metricOrderOneDirection_le_one d b u)
        d.epsilon.coe_nonneg
    _ = (d.epsilon : ℝ) := mul_one _

/-- Helper for Infrastructure I.16a: the order-one scalar denominator is bounded away from
zero by the certified center lower bound. -/
theorem metricOrderOneDenominator_lower
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (u : ℝ) :
    (d.lower : ℝ) ≤ |metricOrderOneDenominator d zeta b u| := by
  let r : ℝ :=
    ((fderiv ℝ d.R (u, (zeta : ℝ → X) u)) (1, b.1 u)).1
  have hr_component : |r| ≤
      ‖fderiv ℝ d.R (u, (zeta : ℝ → X) u) (1, b.1 u)‖ := by
    simpa only [r, Real.norm_eq_abs] using
      (norm_fst_le
        (fderiv ℝ d.R (u, (zeta : ℝ → X) u) (1, b.1 u)))
  have hr : |r| ≤ (d.epsilon : ℝ) :=
    hr_component.trans (norm_metricOrderOneRDirection_le d zeta b u)
  have hlower_add : (d.lower : ℝ) + (d.epsilon : ℝ) = 1 := by
    exact_mod_cast d.hlower_add
  have hr_lower : -(d.epsilon : ℝ) ≤ r := neg_le_of_abs_le hr
  have hden_lower : (d.lower : ℝ) ≤ 1 + r := by
    nlinarith
  have hden_nonneg : 0 ≤ 1 + r := d.lower.coe_nonneg.trans hden_lower
  rw [metricOrderOneDenominator_eq]
  change (d.lower : ℝ) ≤ |1 + r|
  rw [abs_of_nonneg hden_nonneg]
  exact hden_lower

/-- Helper for Infrastructure I.16a: the order-one scalar denominator never vanishes on the
closed slope ball. -/
theorem metricOrderOneDenominator_ne_zero
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (u : ℝ) :
    metricOrderOneDenominator d zeta b u ≠ 0 := by
  have hlower_pos : 0 < (d.lower : ℝ) := by
    exact_mod_cast d.hlower_pos
  have habs_pos : 0 < |metricOrderOneDenominator d zeta b u| :=
    hlower_pos.trans_le (metricOrderOneDenominator_lower d zeta b u)
  exact abs_pos.mp habs_pos

/-- Helper for Infrastructure I.16a: the stable numerator stays within the sharp graph-cone
bound `linearRate * slope + epsilon`. -/
theorem norm_metricOrderOneNumerator_le
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (u : ℝ) :
    ‖metricOrderOneNumerator d zeta b u‖ ≤
      (d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ) := by
  have hlinear : ‖d.L (b.1 u)‖ ≤
      (d.linearRate : ℝ) * (d.slope : ℝ) := by
    calc
      ‖d.L (b.1 u)‖ ≤ ‖d.L‖ * ‖b.1 u‖ := d.L.le_opNorm _
      _ ≤ (d.linearRate : ℝ) * (d.slope : ℝ) :=
        mul_le_mul d.hL (b.norm_apply_le u) (norm_nonneg _) d.linearRate.coe_nonneg
  have hremainder :
      ‖((fderiv ℝ d.R (u, (zeta : ℝ → X) u)) (1, b.1 u)).2‖ ≤
        (d.epsilon : ℝ) := by
    have hsnd := norm_snd_le
      (fderiv ℝ d.R (u, (zeta : ℝ → X) u) (1, b.1 u))
    exact hsnd.trans (norm_metricOrderOneRDirection_le d zeta b u)
  rw [metricOrderOneNumerator_eq]
  exact (norm_add_le _ _).trans (add_le_add hlinear hremainder)

/-- Helper for Infrastructure I.16a: the denominator varies continuously with the source
center for every bounded continuous candidate slope field. -/
theorem continuous_metricOrderOneDenominator
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) :
    Continuous (metricOrderOneDenominator d zeta b) := by
  have hfiber := (continuous_derivCenterFiber d zeta).clm_apply b.1.continuous
  exact (continuous_const.add (continuous_metricOrderOneCenterSource d zeta)).add hfiber

/-- Helper for Infrastructure I.16a: the numerator varies continuously with the source
center for every bounded continuous candidate slope field. -/
theorem continuous_metricOrderOneNumerator
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) :
    Continuous (metricOrderOneNumerator d zeta b) := by
  have hlinear : Continuous (fun u : ℝ => d.L (b.1 u)) :=
    d.L.continuous.comp b.1.continuous
  have hfiber := (continuous_derivFiber d zeta).clm_apply b.1.continuous
  exact (hlinear.add (continuous_metricOrderOneStableSource d zeta)).add hfiber

/-- Helper for Infrastructure I.16a: the unbundled order-one slope transform evaluated in
output center coordinates. -/
def metricOrderOneSlopeValue
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (y : ℝ) : X :=
  let u := d.inverseCenter zeta y
  (metricOrderOneDenominator d zeta b u)⁻¹ • metricOrderOneNumerator d zeta b u

/-- Helper for Infrastructure I.16a: the unbundled slope transform is continuous in the
output center coordinate. -/
theorem continuous_metricOrderOneSlopeValue
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) :
    Continuous (metricOrderOneSlopeValue d zeta b) := by
  have hinverse : Continuous (d.inverseCenter zeta) :=
    (d.inverseCenter_lipschitzWith zeta).continuous
  have hden : Continuous
      (fun y : ℝ => metricOrderOneDenominator d zeta b (d.inverseCenter zeta y)) :=
    (continuous_metricOrderOneDenominator d zeta b).comp hinverse
  have hden_ne : ∀ y : ℝ,
      metricOrderOneDenominator d zeta b (d.inverseCenter zeta y) ≠ 0 := by
    intro y
    exact metricOrderOneDenominator_ne_zero d zeta b (d.inverseCenter zeta y)
  have hnum : Continuous
      (fun y : ℝ => metricOrderOneNumerator d zeta b (d.inverseCenter zeta y)) :=
    (continuous_metricOrderOneNumerator d zeta b).comp hinverse
  exact (hden.inv₀ hden_ne).smul hnum

/-- Helper for Infrastructure I.16a: inversion of the scalar denominator costs at most the
reciprocal certified lower bound. -/
theorem abs_inv_metricOrderOneDenominator_le
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (u : ℝ) :
    |(metricOrderOneDenominator d zeta b u)⁻¹| ≤ (d.lower : ℝ)⁻¹ := by
  have hlower_pos : 0 < (d.lower : ℝ) := by
    exact_mod_cast d.hlower_pos
  have hden := metricOrderOneDenominator_lower d zeta b u
  have hden_pos : 0 < |metricOrderOneDenominator d zeta b u| :=
    hlower_pos.trans_le hden
  rw [abs_inv]
  exact (inv_le_inv₀ hden_pos hlower_pos).2 hden

/-- Helper for Infrastructure I.16a: the unbundled slope transform remains in the prescribed
uniform slope ball. -/
theorem norm_metricOrderOneSlopeValue_le
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (y : ℝ) :
    ‖metricOrderOneSlopeValue d zeta b y‖ ≤ (d.slope : ℝ) := by
  let u := d.inverseCenter zeta y
  have hinv := abs_inv_metricOrderOneDenominator_le d zeta b u
  have hnum := norm_metricOrderOneNumerator_le d zeta b u
  have hslope :
      ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
          (d.lower : ℝ)⁻¹ ≤ (d.slope : ℝ) := by
    exact_mod_cast d.hslope
  have hlower_inv_nonneg : 0 ≤ (d.lower : ℝ)⁻¹ := by
    positivity
  rw [metricOrderOneSlopeValue, norm_smul, Real.norm_eq_abs]
  calc
    |(metricOrderOneDenominator d zeta b u)⁻¹| *
        ‖metricOrderOneNumerator d zeta b u‖ ≤
      (d.lower : ℝ)⁻¹ *
        ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) := by
      exact mul_le_mul hinv hnum (norm_nonneg _) hlower_inv_nonneg
    _ = ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
        (d.lower : ℝ)⁻¹ := by ring
    _ ≤ (d.slope : ℝ) := hslope

/-- Helper for Infrastructure I.16a: the order-one slope value bundled as a bounded continuous
section. -/
def metricOrderOneSlopeBoundedSection
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) : BoundedContinuousFunction ℝ X :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (metricOrderOneSlopeValue d zeta b)
    (continuous_metricOrderOneSlopeValue d zeta b)
    d.slope
    (norm_metricOrderOneSlopeValue_le d zeta b)

/-- Helper for Infrastructure I.16a: the bundled slope transform evaluates by the explicit
inverse-center denominator/numerator formula. -/
theorem metricOrderOneSlopeBoundedSection_apply
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (y : ℝ) :
    metricOrderOneSlopeBoundedSection d zeta b y =
      metricOrderOneSlopeValue d zeta b y := by
  rfl

/-- Helper for Infrastructure I.16a: the bundled slope transform obeys the sharp uniform
slope bound. -/
theorem norm_metricOrderOneSlopeBoundedSection_le
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) :
    ‖metricOrderOneSlopeBoundedSection d zeta b‖ ≤ (d.slope : ℝ) := by
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
    (continuous_metricOrderOneSlopeValue d zeta b) d.slope.coe_nonneg
    (norm_metricOrderOneSlopeValue_le d zeta b)

/-- Helper for Infrastructure I.16a: the order-one slope transform is a self-map of the
closed slope-section ball. -/
def metricOrderOneSlopeOperator
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) :
    MetricSlopeSection d → MetricSlopeSection d :=
  fun b => ⟨metricOrderOneSlopeBoundedSection d zeta b,
    norm_metricOrderOneSlopeBoundedSection_le d zeta b⟩

/-- Helper for Infrastructure I.16a: evaluation of the closed-ball slope operator is the
explicit slope-transform value. -/
theorem metricOrderOneSlopeOperator_apply
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (y : ℝ) :
    (metricOrderOneSlopeOperator d zeta b).1 y =
      metricOrderOneSlopeValue d zeta b y := by
  rfl

/-- Helper for Infrastructure I.16a: subtracting two candidate denominators cancels the
first-slot contribution and leaves only the center fiber derivative on the slope difference. -/
theorem metricOrderOneDenominator_sub_eq
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b c : MetricSlopeSection d) (u : ℝ) :
    metricOrderOneDenominator d zeta b u - metricOrderOneDenominator d zeta c u =
      derivCenterFiber d zeta u (b.1 u - c.1 u) := by
  rw [metricOrderOneDenominator, metricOrderOneDenominator, map_sub]
  module

/-- Helper for Infrastructure I.16a: subtracting two candidate numerators cancels the
first-slot contribution and leaves `L + derivFiber` on the slope difference. -/
theorem metricOrderOneNumerator_sub_eq
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b c : MetricSlopeSection d) (u : ℝ) :
    metricOrderOneNumerator d zeta b u - metricOrderOneNumerator d zeta c u =
      d.L (b.1 u - c.1 u) + derivFiber d zeta u (b.1 u - c.1 u) := by
  rw [metricOrderOneNumerator, metricOrderOneNumerator, map_sub, map_sub]
  module

/-- Helper for Infrastructure I.16a: candidate denominators vary by at most `epsilon` times
the pointwise slope difference. -/
theorem abs_metricOrderOneDenominator_sub_le
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b c : MetricSlopeSection d) (u : ℝ) :
    |metricOrderOneDenominator d zeta b u - metricOrderOneDenominator d zeta c u| ≤
      (d.epsilon : ℝ) * ‖b.1 u - c.1 u‖ := by
  have hcenter : ‖derivCenterFiber d zeta u (b.1 u - c.1 u)‖ ≤
      (d.epsilon : ℝ) * ‖b.1 u - c.1 u‖ := by
    calc
      ‖derivCenterFiber d zeta u (b.1 u - c.1 u)‖ ≤
          ‖derivCenterFiber d zeta u‖ * ‖b.1 u - c.1 u‖ :=
        (derivCenterFiber d zeta u).le_opNorm _
      _ ≤ (d.epsilon : ℝ) * ‖b.1 u - c.1 u‖ :=
        mul_le_mul_of_nonneg_right (norm_derivCenterFiber_le d zeta u) (norm_nonneg _)
  rw [metricOrderOneDenominator_sub_eq]
  simpa only [Real.norm_eq_abs] using hcenter

/-- Helper for Infrastructure I.16a: candidate numerators vary by at most
`linearRate + epsilon` times the pointwise slope difference. -/
theorem norm_metricOrderOneNumerator_sub_le
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b c : MetricSlopeSection d) (u : ℝ) :
    ‖metricOrderOneNumerator d zeta b u - metricOrderOneNumerator d zeta c u‖ ≤
      ((d.linearRate : ℝ) + (d.epsilon : ℝ)) * ‖b.1 u - c.1 u‖ := by
  have hlinear : ‖d.L (b.1 u - c.1 u)‖ ≤
      (d.linearRate : ℝ) * ‖b.1 u - c.1 u‖ := by
    calc
      ‖d.L (b.1 u - c.1 u)‖ ≤ ‖d.L‖ * ‖b.1 u - c.1 u‖ := d.L.le_opNorm _
      _ ≤ (d.linearRate : ℝ) * ‖b.1 u - c.1 u‖ :=
        mul_le_mul_of_nonneg_right d.hL (norm_nonneg _)
  have hfiber : ‖derivFiber d zeta u (b.1 u - c.1 u)‖ ≤
      (d.epsilon : ℝ) * ‖b.1 u - c.1 u‖ := by
    calc
      ‖derivFiber d zeta u (b.1 u - c.1 u)‖ ≤
          ‖derivFiber d zeta u‖ * ‖b.1 u - c.1 u‖ :=
        (derivFiber d zeta u).le_opNorm _
      _ ≤ (d.epsilon : ℝ) * ‖b.1 u - c.1 u‖ :=
        mul_le_mul_of_nonneg_right (norm_derivFiber_le d zeta u) (norm_nonneg _)
  rw [metricOrderOneNumerator_sub_eq]
  calc
    ‖d.L (b.1 u - c.1 u) + derivFiber d zeta u (b.1 u - c.1 u)‖ ≤
        ‖d.L (b.1 u - c.1 u)‖ + ‖derivFiber d zeta u (b.1 u - c.1 u)‖ :=
      norm_add_le _ _
    _ ≤ (d.linearRate : ℝ) * ‖b.1 u - c.1 u‖ +
        (d.epsilon : ℝ) * ‖b.1 u - c.1 u‖ := add_le_add hlinear hfiber
    _ = ((d.linearRate : ℝ) + (d.epsilon : ℝ)) * ‖b.1 u - c.1 u‖ := by
      ring

/-- Helper for Infrastructure I.16a: reciprocal scalars with a common positive absolute-value
lower bound satisfy the standard inverse-difference estimate. -/
private theorem abs_inv_sub_inv_le_of_lower_bound
    {a b lower : ℝ} (hlower : 0 < lower)
    (ha : lower ≤ |a|) (hb : lower ≤ |b|) :
    |a⁻¹ - b⁻¹| ≤ lower⁻¹ ^ 2 * |a - b| := by
  have ha_abs_pos : 0 < |a| := hlower.trans_le ha
  have hb_abs_pos : 0 < |b| := hlower.trans_le hb
  have ha_ne : a ≠ 0 := abs_pos.mp ha_abs_pos
  have hb_ne : b ≠ 0 := abs_pos.mp hb_abs_pos
  have hidentity : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
    field_simp
  have hproduct : lower ^ 2 ≤ |a| * |b| := by
    nlinarith [abs_nonneg a, abs_nonneg b]
  have hproduct_pos : 0 < |a| * |b| := mul_pos ha_abs_pos hb_abs_pos
  have hlower_sq_pos : 0 < lower ^ 2 := pow_pos hlower 2
  have hinverse_product : (|a| * |b|)⁻¹ ≤ (lower ^ 2)⁻¹ :=
    (inv_le_inv₀ hproduct_pos hlower_sq_pos).2 hproduct
  calc
    |a⁻¹ - b⁻¹| = |a - b| * (|a| * |b|)⁻¹ := by
      rw [hidentity, abs_div, abs_sub_comm, abs_mul, div_eq_mul_inv]
    _ ≤ |a - b| * (lower ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left hinverse_product (abs_nonneg _)
    _ = lower⁻¹ ^ 2 * |a - b| := by
      rw [inv_pow]
      ring

/-- Helper for Infrastructure I.16a: the inverse candidate denominators vary with the sharp
`lower⁻² * epsilon` factor. -/
theorem abs_inv_metricOrderOneDenominator_sub_le
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b c : MetricSlopeSection d) (u : ℝ) :
    |(metricOrderOneDenominator d zeta b u)⁻¹ -
        (metricOrderOneDenominator d zeta c u)⁻¹| ≤
      (d.lower : ℝ)⁻¹ ^ 2 * (d.epsilon : ℝ) * ‖b.1 u - c.1 u‖ := by
  have hlower_pos : 0 < (d.lower : ℝ) := by
    exact_mod_cast d.hlower_pos
  have hinverse := abs_inv_sub_inv_le_of_lower_bound hlower_pos
    (metricOrderOneDenominator_lower d zeta b u)
    (metricOrderOneDenominator_lower d zeta c u)
  have hdenominator := abs_metricOrderOneDenominator_sub_le d zeta b c u
  have hlower_inv_sq_nonneg : 0 ≤ (d.lower : ℝ)⁻¹ ^ 2 := by
    positivity
  calc
    |(metricOrderOneDenominator d zeta b u)⁻¹ -
        (metricOrderOneDenominator d zeta c u)⁻¹| ≤
        (d.lower : ℝ)⁻¹ ^ 2 *
          |metricOrderOneDenominator d zeta b u -
            metricOrderOneDenominator d zeta c u| := hinverse
    _ ≤ (d.lower : ℝ)⁻¹ ^ 2 *
        ((d.epsilon : ℝ) * ‖b.1 u - c.1 u‖) :=
      mul_le_mul_of_nonneg_left hdenominator hlower_inv_sq_nonneg
    _ = (d.lower : ℝ)⁻¹ ^ 2 * (d.epsilon : ℝ) *
        ‖b.1 u - c.1 u‖ := by ring

/-- Helper for Infrastructure I.16a: the difference of two slope-transform values separates
into a numerator difference and an inverse-denominator difference. -/
theorem metricOrderOneSlopeValue_sub_eq
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b c : MetricSlopeSection d) (y : ℝ) :
    metricOrderOneSlopeValue d zeta b y - metricOrderOneSlopeValue d zeta c y =
      (metricOrderOneDenominator d zeta b (d.inverseCenter zeta y))⁻¹ •
        (metricOrderOneNumerator d zeta b (d.inverseCenter zeta y) -
          metricOrderOneNumerator d zeta c (d.inverseCenter zeta y)) +
      ((metricOrderOneDenominator d zeta b (d.inverseCenter zeta y))⁻¹ -
        (metricOrderOneDenominator d zeta c (d.inverseCenter zeta y))⁻¹) •
          metricOrderOneNumerator d zeta c (d.inverseCenter zeta y) := by
  rw [metricOrderOneSlopeValue, metricOrderOneSlopeValue, smul_sub, sub_smul]
  abel

/-- Helper for Infrastructure I.16a: at a fixed output coordinate, the slope transform obeys
the exact full-rate estimate against the input difference at the inverse center. -/
theorem metricOrderOneSlopeValue_dist_le_source
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b c : MetricSlopeSection d) (y : ℝ) :
    dist (metricOrderOneSlopeValue d zeta b y) (metricOrderOneSlopeValue d zeta c y) ≤
      ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹) *
          dist (b.1 (d.inverseCenter zeta y)) (c.1 (d.inverseCenter zeta y)) := by
  let source := d.inverseCenter zeta y
  let slopeDifference := ‖b.1 source - c.1 source‖
  have hinverse := abs_inv_metricOrderOneDenominator_le d zeta b source
  have hnumDifference := norm_metricOrderOneNumerator_sub_le d zeta b c source
  have hinverseDifference :=
    abs_inv_metricOrderOneDenominator_sub_le d zeta b c source
  have hnum := norm_metricOrderOneNumerator_le d zeta c source
  have hinverse_nonneg :
      0 ≤ |(metricOrderOneDenominator d zeta b source)⁻¹| := abs_nonneg _
  have hlower_inv_nonneg : 0 ≤ (d.lower : ℝ)⁻¹ := by
    positivity
  have hnumDifference_nonneg :
      0 ≤ ‖metricOrderOneNumerator d zeta b source -
        metricOrderOneNumerator d zeta c source‖ := norm_nonneg _
  have hinverseDifference_nonneg :
      0 ≤ |(metricOrderOneDenominator d zeta b source)⁻¹ -
        (metricOrderOneDenominator d zeta c source)⁻¹| := abs_nonneg _
  have hlower_epsilon_difference_nonneg :
      0 ≤ (d.lower : ℝ)⁻¹ ^ 2 * (d.epsilon : ℝ) * slopeDifference := by
    positivity
  have hnum_nonneg : 0 ≤ ‖metricOrderOneNumerator d zeta c source‖ := norm_nonneg _
  have hrate_real :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) =
        (d.linearRate : ℝ) + (d.epsilon : ℝ) +
          ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
            (d.lower : ℝ)⁻¹ * (d.epsilon : ℝ) := by
    exact metricGraphTransformRate_coe d.lower d.linearRate d.epsilon d.slope
  rw [dist_eq_norm, metricOrderOneSlopeValue_sub_eq]
  calc
    ‖(metricOrderOneDenominator d zeta b source)⁻¹ •
          (metricOrderOneNumerator d zeta b source -
            metricOrderOneNumerator d zeta c source) +
        ((metricOrderOneDenominator d zeta b source)⁻¹ -
          (metricOrderOneDenominator d zeta c source)⁻¹) •
            metricOrderOneNumerator d zeta c source‖ ≤
        ‖(metricOrderOneDenominator d zeta b source)⁻¹ •
          (metricOrderOneNumerator d zeta b source -
            metricOrderOneNumerator d zeta c source)‖ +
        ‖((metricOrderOneDenominator d zeta b source)⁻¹ -
          (metricOrderOneDenominator d zeta c source)⁻¹) •
            metricOrderOneNumerator d zeta c source‖ := norm_add_le _ _
    _ = |(metricOrderOneDenominator d zeta b source)⁻¹| *
          ‖metricOrderOneNumerator d zeta b source -
            metricOrderOneNumerator d zeta c source‖ +
        |(metricOrderOneDenominator d zeta b source)⁻¹ -
          (metricOrderOneDenominator d zeta c source)⁻¹| *
            ‖metricOrderOneNumerator d zeta c source‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (d.lower : ℝ)⁻¹ *
          (((d.linearRate : ℝ) + (d.epsilon : ℝ)) * slopeDifference) +
        ((d.lower : ℝ)⁻¹ ^ 2 * (d.epsilon : ℝ) * slopeDifference) *
          ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) := by
      apply add_le_add
      · exact mul_le_mul hinverse hnumDifference hnumDifference_nonneg hlower_inv_nonneg
      · exact mul_le_mul hinverseDifference hnum hnum_nonneg
          hlower_epsilon_difference_nonneg
    _ = ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
          (d.lower : ℝ)⁻¹) * slopeDifference := by
      rw [hrate_real]
      ring
    _ = ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
          (d.lower : ℝ)⁻¹) *
        dist (b.1 source) (c.1 source) := by
      rw [dist_eq_norm]

/-- Infrastructure I.16a: the closed-ball order-one slope operator has the precise pointwise
contraction factor `metricGraphTransformRate * lower⁻¹`. -/
theorem metricOrderOneSlopeOperator_dist_apply_le
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b c : MetricSlopeSection d) (y : ℝ) :
    dist ((metricOrderOneSlopeOperator d zeta b).1 y)
        ((metricOrderOneSlopeOperator d zeta c).1 y) ≤
      ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹) * dist b c := by
  have hsource := metricOrderOneSlopeValue_dist_le_source d zeta b c y
  have heval :
      dist (b.1 (d.inverseCenter zeta y)) (c.1 (d.inverseCenter zeta y)) ≤
        dist b.1 c.1 :=
    BoundedContinuousFunction.dist_coe_le_dist
      (f := b.1) (g := c.1) (d.inverseCenter zeta y)
  have hfactor_nonneg :
      0 ≤ (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ := by
    positivity
  rw [metricOrderOneSlopeOperator_apply, metricOrderOneSlopeOperator_apply]
  change dist (metricOrderOneSlopeValue d zeta b y)
      (metricOrderOneSlopeValue d zeta c y) ≤
    ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
      (d.lower : ℝ)⁻¹) * dist b.1 c.1
  exact hsource.trans (mul_le_mul_of_nonneg_left heval hfactor_nonneg)

/-- Helper for Infrastructure I.16a: the real bunching inequality makes the closed-ball slope
operator a `ContractingWith` map. -/
theorem metricOrderOneSlopeOperator_contractingWith
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1) :
    ContractingWith
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope * d.lower⁻¹)
      (metricOrderOneSlopeOperator d zeta) := by
  have h_bunching_nnreal :
      metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope * d.lower⁻¹ < 1 := by
    exact_mod_cast h_bunching
  refine ⟨h_bunching_nnreal, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro b c
  change dist (metricOrderOneSlopeOperator d zeta b).1
      (metricOrderOneSlopeOperator d zeta c).1 ≤
    ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
      (d.lower : ℝ)⁻¹) * dist b c
  apply BoundedContinuousFunction.dist_le_iff_of_nonempty.mpr
  intro y
  exact metricOrderOneSlopeOperator_dist_apply_le d zeta b c y

/-- Helper for Infrastructure I.16a: first-order bunching gives a unique bounded continuous
fixed slope field in the prescribed closed ball. -/
theorem existsUnique_metricOrderOneSlopeOperator_fixedPoint
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1) :
    ∃! b : MetricSlopeSection d, metricOrderOneSlopeOperator d zeta b = b := by
  let hcontract := metricOrderOneSlopeOperator_contractingWith d zeta h_bunching
  refine ⟨ContractingWith.fixedPoint (metricOrderOneSlopeOperator d zeta) hcontract,
    hcontract.fixedPoint_isFixedPt, ?_⟩
  intro b hb
  exact hcontract.fixedPoint_unique hb

end LocalInvariantGraph
