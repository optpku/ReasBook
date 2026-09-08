module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricOrderOneDifferenceLinearization
import all ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricOrderOneDifferenceLinearization
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricOrderOneHolonomicity
import all ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricOrderOneSlopeOperator
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricReservedTopOperator
import all ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionCoreAssembly
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricRawDefectEnvelope
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.ProofSupport.AffineCocycle

public section

noncomputable section

open Filter
open scoped NNReal Topology

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-!
# The non-circular order-two holonomicity bootstrap

This leaf differentiates the canonical order-one fixed slope without assuming that slope is
already differentiable.  The exact rational difference coefficient isolates the transported raw
defect.  The remaining base variation is compared with the order-two reserved forcing before the
inverse-center radius envelope is applied.
-/

/-- Helper for Infrastructure I.16a: translation by a fixed scalar is continuous. -/
theorem continuous_metricOrderTwoTranslation (s : ℝ) :
    Continuous (fun x : ℝ ↦ x + s) :=
  continuous_id.add continuous_const

/-- Helper for Infrastructure I.16a: the continuous self-map of `ℝ` given by translation by
`s`. -/
def metricOrderTwoTranslation (s : ℝ) : C(ℝ, ℝ) :=
  ⟨fun x ↦ x + s, continuous_metricOrderTwoTranslation s⟩

/-- Helper for Infrastructure I.16a: translating a bounded slope field does not increase its
uniform norm beyond the metric slope bound. -/
theorem norm_metricOrderTwoTranslatedSlope_le
    {d : MetricGraphTransformData X} (b : MetricSlopeSection d) (s : ℝ) :
    ‖b.1.compContinuous (metricOrderTwoTranslation s)‖ ≤ (d.slope : ℝ) := by
  exact (BoundedContinuousFunction.norm_compContinuous_le b.1
    (metricOrderTwoTranslation s)).trans b.2

/-- Helper for Infrastructure I.16a: the order-one slope candidate obtained by translating a
bounded slope field in source coordinates. -/
def metricOrderTwoTranslatedSlope
    (d : MetricGraphTransformData X) (b : MetricSlopeSection d) (s : ℝ) :
    MetricSlopeSection d :=
  ⟨b.1.compContinuous (metricOrderTwoTranslation s),
    norm_metricOrderTwoTranslatedSlope_le b s⟩

/-- Helper for Infrastructure I.16a: evaluating the translated slope candidate shifts its source
coordinate by the prescribed increment. -/
theorem metricOrderTwoTranslatedSlope_apply
    (d : MetricGraphTransformData X) (b : MetricSlopeSection d) (s x : ℝ) :
    (metricOrderTwoTranslatedSlope d b s).1 x = b.1 (x + s) := by
  rfl

/-- Helper for Infrastructure I.16a: the frozen denominator evaluates the derivative of the
center component on a direction whose stable coordinate is held fixed. -/
def metricOrderTwoFrozenDenominator
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) (v : ℝ) (w : X) : ℝ :=
  1 + ((fderiv ℝ d.R (v, (zeta : ℝ → X) v)) (1, w)).1

/-- Helper for Infrastructure I.16a: the frozen numerator evaluates the derivative of the
stable component on a direction whose stable coordinate is held fixed. -/
def metricOrderTwoFrozenNumerator
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) (v : ℝ) (w : X) : X :=
  d.L w + ((fderiv ℝ d.R (v, (zeta : ℝ → X) v)) (1, w)).2

/-- Helper for Infrastructure I.16a: the frozen rational slope value varies only its source
base while retaining the prescribed stable direction. -/
def metricOrderTwoFrozenSlopeValue
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) (v : ℝ) (w : X) : X :=
  (metricOrderTwoFrozenDenominator d zeta v w)⁻¹ •
    metricOrderTwoFrozenNumerator d zeta v w

/-- Helper for Infrastructure I.16a: a frozen direction in the closed slope ball has product
norm at most one. -/
theorem norm_metricOrderTwoFrozenDirection_le_one
    (d : MetricGraphTransformData X) {w : X}
    (hw : ‖w‖ ≤ (d.slope : ℝ)) :
    ‖((1 : ℝ), w)‖ ≤ 1 := by
  have hslope_one : (d.slope : ℝ) ≤ 1 := by
    exact_mod_cast d.hslope_one
  have hw_one : ‖w‖ ≤ 1 := hw.trans hslope_one
  rw [Prod.norm_def]
  exact max_le (norm_one.le) hw_one

/-- Helper for Infrastructure I.16a: the derivative of the smooth remainder on any frozen
direction in the closed slope ball has norm at most epsilon. -/
theorem norm_metricOrderTwoFrozenRDirection_le
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (u : ℝ) {w : X} (hw : ‖w‖ ≤ (d.slope : ℝ)) :
    ‖(fderiv ℝ d.R (u, (zeta : ℝ → X) u)) (1, w)‖ ≤
      (d.epsilon : ℝ) := by
  calc
    ‖(fderiv ℝ d.R (u, (zeta : ℝ → X) u)) (1, w)‖ ≤
        (d.epsilon : ℝ) * ‖((1 : ℝ), w)‖ :=
      norm_metricOrderOneRDerivative_apply_le d _ _
    _ ≤ (d.epsilon : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left
        (norm_metricOrderTwoFrozenDirection_le_one d hw) d.epsilon.coe_nonneg
    _ = (d.epsilon : ℝ) := mul_one _

/-- Helper for Infrastructure I.16a: every frozen denominator over the closed slope ball is
bounded below by the certified center factor. -/
theorem metricOrderTwoFrozenDenominator_lower
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (u : ℝ) {w : X} (hw : ‖w‖ ≤ (d.slope : ℝ)) :
    (d.lower : ℝ) ≤ |metricOrderTwoFrozenDenominator d zeta u w| := by
  let r : ℝ :=
    ((fderiv ℝ d.R (u, (zeta : ℝ → X) u)) (1, w)).1
  have hr_component : |r| ≤
      ‖(fderiv ℝ d.R (u, (zeta : ℝ → X) u)) (1, w)‖ := by
    simpa only [r, Real.norm_eq_abs] using
      (norm_fst_le ((fderiv ℝ d.R (u, (zeta : ℝ → X) u)) (1, w)))
  have hr : |r| ≤ (d.epsilon : ℝ) :=
    hr_component.trans (norm_metricOrderTwoFrozenRDirection_le d zeta u hw)
  have hlower_add : (d.lower : ℝ) + (d.epsilon : ℝ) = 1 := by
    exact_mod_cast d.hlower_add
  have hr_lower : -(d.epsilon : ℝ) ≤ r := neg_le_of_abs_le hr
  have hden_lower : (d.lower : ℝ) ≤ 1 + r := by
    nlinarith
  have hden_nonneg : 0 ≤ 1 + r := d.lower.coe_nonneg.trans hden_lower
  rw [metricOrderTwoFrozenDenominator]
  change (d.lower : ℝ) ≤ |1 + r|
  rw [abs_of_nonneg hden_nonneg]
  exact hden_lower

/-- Helper for Infrastructure I.16a: every frozen denominator over the closed slope ball is
nonzero. -/
theorem metricOrderTwoFrozenDenominator_ne_zero
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (u : ℝ) {w : X} (hw : ‖w‖ ≤ (d.slope : ℝ)) :
    metricOrderTwoFrozenDenominator d zeta u w ≠ 0 := by
  have hlower_pos : 0 < (d.lower : ℝ) := by
    exact_mod_cast d.hlower_pos
  have habs_pos : 0 < |metricOrderTwoFrozenDenominator d zeta u w| :=
    hlower_pos.trans_le (metricOrderTwoFrozenDenominator_lower d zeta u hw)
  exact abs_pos.mp habs_pos

/-- Helper for Infrastructure I.16a: the frozen rational slope is jointly C¹ at every source
and every stable direction in the closed slope ball. -/
theorem metricOrderTwoFrozenSlopeValue_contDiffAt
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hzeta : ContDiff ℝ 1 (zeta : ℝ → X))
    (u : ℝ) {w : X} (hw : ‖w‖ ≤ (d.slope : ℝ)) :
    ContDiffAt ℝ 1
      (fun p : ℝ × X ↦ metricOrderTwoFrozenSlopeValue d zeta p.1 p.2)
      (u, w) := by
  have htwo_order : (2 : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast d.hnu
  have hR_two : ContDiff ℝ 2 d.R := d.hR_smooth.of_le htwo_order
  have hderivative_order :
      (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞) := by
    norm_num
  have hR_derivative : ContDiff ℝ 1 (fderiv ℝ d.R) :=
    hR_two.fderiv_right hderivative_order
  have hgraph : ContDiff ℝ 1
      (fun p : ℝ × X ↦ (p.1, (zeta : ℝ → X) p.1)) :=
    contDiff_fst.prodMk (hzeta.comp contDiff_fst)
  have hdirection : ContDiff ℝ 1
      (fun p : ℝ × X ↦ ((1 : ℝ), p.2)) :=
    contDiff_const.prodMk contDiff_snd
  have hevaluated : ContDiff ℝ 1
      (fun p : ℝ × X ↦
        (fderiv ℝ d.R (p.1, (zeta : ℝ → X) p.1)) (1, p.2)) :=
    (hR_derivative.comp hgraph).clm_apply hdirection
  have hdenominator : ContDiff ℝ 1
      (fun p : ℝ × X ↦ metricOrderTwoFrozenDenominator d zeta p.1 p.2) := by
    simpa only [metricOrderTwoFrozenDenominator] using
      contDiff_const.add hevaluated.fst
  have hlinear : ContDiff ℝ 1 (fun p : ℝ × X ↦ d.L p.2) :=
    d.L.contDiff.comp contDiff_snd
  have hnumerator : ContDiff ℝ 1
      (fun p : ℝ × X ↦ metricOrderTwoFrozenNumerator d zeta p.1 p.2) := by
    simpa only [metricOrderTwoFrozenNumerator] using hlinear.add hevaluated.snd
  have hdenominator_ne :
      metricOrderTwoFrozenDenominator d zeta u w ≠ 0 :=
    metricOrderTwoFrozenDenominator_ne_zero d zeta u hw
  have hdenominator_at :
      ContDiffAt ℝ 1
        (fun p : ℝ × X ↦ metricOrderTwoFrozenDenominator d zeta p.1 p.2)
        (u, w) :=
    hdenominator.contDiffAt
  have hnumerator_at :
      ContDiffAt ℝ 1
        (fun p : ℝ × X ↦ metricOrderTwoFrozenNumerator d zeta p.1 p.2)
        (u, w) :=
    hnumerator.contDiffAt
  have hsmul :=
    (hdenominator_at.inv hdenominator_ne).smul hnumerator_at
  have hsmul_fun :
      ((fun p : ℝ × X ↦ metricOrderTwoFrozenDenominator d zeta p.1 p.2)⁻¹ •
        (fun p : ℝ × X ↦ metricOrderTwoFrozenNumerator d zeta p.1 p.2)) =
      (fun p : ℝ × X ↦
        (metricOrderTwoFrozenDenominator d zeta p.1 p.2)⁻¹ •
          metricOrderTwoFrozenNumerator d zeta p.1 p.2) := by
    funext p
    rfl
  rw [hsmul_fun] at hsmul
  simpa only [metricOrderTwoFrozenSlopeValue] using hsmul

/-- Helper for Infrastructure I.16a: the source partial derivative of the frozen rational slope
is the joint Frechet derivative evaluated on the pure source direction. -/
def metricOrderTwoFrozenSourceDerivative
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) (u : ℝ) (w : X) : X :=
  (fderiv ℝ
      (fun p : ℝ × X ↦ metricOrderTwoFrozenSlopeValue d zeta p.1 p.2)
      (u, w)) ((1 : ℝ), (0 : X))

/-- Helper for Infrastructure I.16a: each frozen source slice has derivative given by the
source partial derivative whenever its direction lies in the closed slope ball. -/
theorem metricOrderTwoFrozenSlopeValue_hasDerivAt_sourceDerivative
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hzeta : ContDiff ℝ 1 (zeta : ℝ → X))
    (u : ℝ) {w : X} (hw : ‖w‖ ≤ (d.slope : ℝ)) :
    HasDerivAt
      (fun v ↦ metricOrderTwoFrozenSlopeValue d zeta v w)
      (metricOrderTwoFrozenSourceDerivative d zeta u w) u := by
  have hfrozen :=
    metricOrderTwoFrozenSlopeValue_contDiffAt d zeta hzeta u hw
  have hline : HasDerivAt (fun v : ℝ ↦ (v, w))
      ((1 : ℝ), (0 : X)) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u w)
  have hcomposition :=
    (hfrozen.differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt u hline
  simpa only [Function.comp_def, Function.comp_apply,
    metricOrderTwoFrozenSourceDerivative] using
    hcomposition

/-- Helper for Infrastructure I.16a: the frozen source partial derivative is continuous at
every stable direction in the closed slope ball. -/
theorem continuousAt_metricOrderTwoFrozenSourceDerivative
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hzeta : ContDiff ℝ 1 (zeta : ℝ → X))
    (u : ℝ) {w : X} (hw : ‖w‖ ≤ (d.slope : ℝ)) :
    ContinuousAt
      (fun p : ℝ × X ↦
        metricOrderTwoFrozenSourceDerivative d zeta p.1 p.2)
      (u, w) := by
  have hfrozen :=
    metricOrderTwoFrozenSlopeValue_contDiffAt d zeta hzeta u hw
  have hderivative := hfrozen.continuousAt_fderiv one_ne_zero
  have hevaluated := hderivative.clm_apply
    (continuousAt_const :
      ContinuousAt (fun _ : ℝ × X ↦ ((1 : ℝ), (0 : X))) (u, w))
  simpa only [metricOrderTwoFrozenSourceDerivative] using hevaluated

/-- Helper for Infrastructure I.16a: off the support of the smooth remainder, the frozen
rational slope is just the linear stable map. -/
theorem metricOrderTwoFrozenSlopeValue_eq_linear_of_notMem_tsupport
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    {u : ℝ} {w : X}
    (hu : (u, (zeta : ℝ → X) u) ∉ tsupport d.R) :
    metricOrderTwoFrozenSlopeValue d zeta u w = d.L w := by
  rw [metricOrderTwoFrozenSlopeValue, metricOrderTwoFrozenDenominator,
    metricOrderTwoFrozenNumerator, fderiv_of_notMem_tsupport ℝ hu]
  simp

/-- Helper for Infrastructure I.16a: off the support of the smooth remainder, the frozen
rational slope has zero source partial derivative. -/
theorem metricOrderTwoFrozenSourceDerivative_eq_zero_of_notMem_tsupport
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hzeta : ContDiff ℝ 1 (zeta : ℝ → X))
    {u : ℝ} {w : X} (hw : ‖w‖ ≤ (d.slope : ℝ))
    (hu : (u, (zeta : ℝ → X) u) ∉ tsupport d.R) :
    metricOrderTwoFrozenSourceDerivative d zeta u w = 0 := by
  have hpair : Continuous (fun v : ℝ ↦ (v, (zeta : ℝ → X) v)) :=
    continuous_id.prodMk hzeta.continuous
  have hopen : IsOpen ((tsupport d.R)ᶜ) :=
    (isClosed_tsupport d.R).isOpen_compl
  have hpreimage :
      IsOpen ((fun v : ℝ ↦ (v, (zeta : ℝ → X) v)) ⁻¹' (tsupport d.R)ᶜ) :=
    hopen.preimage hpair
  have hmem :
      u ∈ (fun v : ℝ ↦ (v, (zeta : ℝ → X) v)) ⁻¹' (tsupport d.R)ᶜ :=
    hu
  have heventually :
      (fun v : ℝ ↦ metricOrderTwoFrozenSlopeValue d zeta v w) =ᶠ[𝓝 u]
        (fun _ : ℝ ↦ d.L w) := by
    filter_upwards [hpreimage.mem_nhds hmem] with v hv
    apply metricOrderTwoFrozenSlopeValue_eq_linear_of_notMem_tsupport
    simpa only [Set.mem_preimage, Set.mem_compl_iff] using hv
  have hzero :
      HasDerivAt
        (fun v : ℝ ↦ metricOrderTwoFrozenSlopeValue d zeta v w) 0 u :=
    (heventually.hasDerivAt_iff).mpr (hasDerivAt_const u (d.L w))
  have hsource :=
    metricOrderTwoFrozenSlopeValue_hasDerivAt_sourceDerivative
      d zeta hzeta u hw
  exact hsource.unique hzero

/-- Helper for Infrastructure I.16a: an order-one derivative jet has the usual affine
Taylor remainder. -/
theorem finiteTaylorJet_one_remainder_eq
    (f : ℝ → X) (u s : ℝ) (hf : DifferentiableAt ℝ f u) :
    (FiniteTaylorJet.ofFunction ℝ 1 f u).remainder f u s =
      f (u + s) - f u - s • deriv f u := by
  rw [FiniteTaylorJet.remainder_def,
    FiniteTaylorJet.eval_eq_sum_smul_scalarCoeff, Fin.sum_univ_two]
  simp [FiniteTaylorJet.scalarCoeff_ofFunction, iteratedDeriv_zero,
    iteratedDeriv_one, sub_eq_add_neg, add_assoc]
  abel

/-- Helper for Infrastructure I.16a: the order-one Taylor remainder of a translated frozen
slope slice is its affine source-partial error. -/
theorem metricOrderTwoFrozenSlopeValue_translated_remainder_eq
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hzeta : ContDiff ℝ 1 (zeta : ℝ → X))
    (u s : ℝ) {w : X} (hw : ‖w‖ ≤ (d.slope : ℝ)) :
    (FiniteTaylorJet.ofFunction ℝ 1
        (fun h : ℝ ↦ metricOrderTwoFrozenSlopeValue d zeta (u + h) w) 0).remainder
        (fun h : ℝ ↦ metricOrderTwoFrozenSlopeValue d zeta (u + h) w) 0 s =
      metricOrderTwoFrozenSlopeValue d zeta (u + s) w -
        metricOrderTwoFrozenSlopeValue d zeta u w -
          s • metricOrderTwoFrozenSourceDerivative d zeta u w := by
  have hsource :=
    metricOrderTwoFrozenSlopeValue_hasDerivAt_sourceDerivative
      d zeta hzeta u hw
  have htranslation : HasDerivAt (fun h : ℝ ↦ u + h) 1 0 := by
    have hraw := (hasDerivAt_const 0 u).add (hasDerivAt_id 0)
    have hfun : ((fun _ : ℝ ↦ u) + id) = (fun h : ℝ ↦ u + h) := by
      funext h
      rfl
    rw [hfun] at hraw
    simpa only [zero_add] using hraw
  have hsource_at :
      HasDerivAt (fun v : ℝ ↦ metricOrderTwoFrozenSlopeValue d zeta v w)
        (metricOrderTwoFrozenSourceDerivative d zeta u w) (u + 0) := by
    simpa only [add_zero] using hsource
  have htranslated :
      HasDerivAt
        (fun h : ℝ ↦ metricOrderTwoFrozenSlopeValue d zeta (u + h) w)
        (metricOrderTwoFrozenSourceDerivative d zeta u w) 0 := by
    have hcomp := hsource_at.hasFDerivAt.comp_hasDerivAt 0 htranslation
    simpa only [Function.comp_def, add_zero, one_smul, mul_one,
      ContinuousLinearMap.toSpanSingleton_apply] using hcomp
  rw [finiteTaylorJet_one_remainder_eq _ 0 s htranslated.differentiableAt,
    htranslated.deriv, zero_add, add_zero]

/-- Helper for Infrastructure I.16a: differentiating an inverse scalar times a vector can be
written in denominator-cancelled quotient form. -/
theorem hasDerivAt_inv_smul_quotient
    {D : ℝ → ℝ} {N : ℝ → X} {u D' : ℝ} {N' : X}
    (hD : HasDerivAt D D' u) (hN : HasDerivAt N N' u) (hD_ne : D u ≠ 0) :
    HasDerivAt (fun v ↦ (D v)⁻¹ • N v)
      ((D u)⁻¹ • (N' - D' • ((D u)⁻¹ • N u))) u := by
  have hinverse := hD.inv hD_ne
  have hproduct := hinverse.smul hN
  apply hproduct.congr_deriv
  field_simp [hD_ne]
  module

/-- Helper for Infrastructure I.16a: freezing a slope candidate at its value over `u` recovers
the ordinary candidate denominator at `u`. -/
theorem metricOrderTwoFrozenDenominator_eq
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (u : ℝ) :
    metricOrderTwoFrozenDenominator d zeta u (b.1 u) =
      metricOrderOneDenominator d zeta b u := by
  rw [metricOrderTwoFrozenDenominator, metricOrderOneDenominator_eq]

/-- Helper for Infrastructure I.16a: freezing a slope candidate at its value over `u` recovers
the ordinary candidate numerator at `u`. -/
theorem metricOrderTwoFrozenNumerator_eq
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (u : ℝ) :
    metricOrderTwoFrozenNumerator d zeta u (b.1 u) =
      metricOrderOneNumerator d zeta b u := by
  rw [metricOrderTwoFrozenNumerator, metricOrderOneNumerator_eq]

/-- Helper for Infrastructure I.16a: source-coordinate evaluation of the slope transform is
the frozen rational value at the candidate direction. -/
theorem metricOrderOneSlopeOperator_apply_centerMap_eq_frozen
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (u : ℝ) :
    (metricOrderOneSlopeOperator d zeta b).1 (d.centerMap zeta u) =
      metricOrderTwoFrozenSlopeValue d zeta u (b.1 u) := by
  rw [metricOrderOneSlopeOperator_apply, metricOrderOneSlopeValue.eq_1,
    d.inverseCenter_centerMap zeta u, metricOrderTwoFrozenSlopeValue,
    metricOrderTwoFrozenDenominator_eq, metricOrderTwoFrozenNumerator_eq]

/-- Helper for Infrastructure I.16a: no ordered partition of two has length distinct from
both one and two. -/
theorem orderedFinpartition_two_residual_filter_eq_empty :
    Finset.univ.filter
        (fun c : OrderedFinpartition 2 ↦ c.length ≠ 2 ∧ c.length ≠ 1) =
      ∅ := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hc
    have htwo_pos : 0 < 2 := by
      norm_num
    have hpositive : 0 < c.length := c.length_pos htwo_pos
    have hbound : c.length ≤ 2 := c.length_le
    omega
  · intro hc
    exact False.elim (by simpa using hc)

/-- Helper for Infrastructure I.16a: along the fixed graph, differentiating the frozen
first derivative of `R` produces its diagonal second derivative. -/
theorem metricOrderTwoFrozenRDerivative_hasDerivAt
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (u : ℝ) :
    let b := metricOrderOneFixedSlope d zeta h_bunching_one
    HasDerivAt
      (fun v : ℝ ↦
        (fderiv ℝ d.R (v, (zeta : ℝ → X) v)) (1, b.1 u))
      (iteratedFDeriv ℝ 2 d.R (u, (zeta : ℝ → X) u)
        (fun _ : Fin 2 ↦ ((1 : ℝ), b.1 u))) u := by
  dsimp only
  let b := metricOrderOneFixedSlope d zeta h_bunching_one
  let graph : ℝ → ℝ × X := fun v ↦ (v, (zeta : ℝ → X) v)
  let direction : ℝ × X := ((1 : ℝ), b.1 u)
  have hzeta :=
    metricFixedGraph_hasDerivAt_orderOne d zeta hfixed h_bunching_one u
  have hgraph : HasDerivAt graph direction u := by
    exact (hasDerivAt_id u).prodMk hzeta
  have htwo_order : (2 : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast d.hnu
  have hR_two : ContDiffAt ℝ 2 d.R (graph u) :=
    (d.hR_smooth.of_le htwo_order).contDiffAt
  have hderivative_order :
      (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞) := by
    norm_num
  have hR_derivative : ContDiffAt ℝ 1 (fderiv ℝ d.R) (graph u) :=
    hR_two.fderiv_right hderivative_order
  have halong : HasDerivAt (fderiv ℝ d.R ∘ graph)
      ((fderiv ℝ (fderiv ℝ d.R) (graph u)) direction) u := by
    exact (hR_derivative.differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt
      u hgraph
  have hdirection : HasDerivAt (fun _ : ℝ ↦ direction) 0 u :=
    hasDerivAt_const u direction
  have hevaluated := halong.clm_apply hdirection
  have hevaluated' :
      HasDerivAt
        (fun v : ℝ ↦ (fderiv ℝ d.R (graph v)) direction)
        (((fderiv ℝ (fderiv ℝ d.R) (graph u)) direction) direction) u := by
    apply hevaluated.congr_deriv
    simp only [ContinuousLinearMap.map_zero, add_zero]
  have hatomic :
      iteratedFDeriv ℝ 2 d.R (graph u)
          (fun _ : Fin 2 ↦ direction) =
        ((fderiv ℝ (fderiv ℝ d.R) (graph u)) direction) direction := by
    rw [iteratedFDeriv_two_apply]
  rw [← hatomic] at hevaluated'
  simpa only [graph, direction] using hevaluated'

/-- Helper for Infrastructure I.16a: the frozen denominator derivative is the center
coordinate of the diagonal second derivative of `R`. -/
theorem metricOrderTwoFrozenDenominator_hasDerivAt
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (u : ℝ) :
    let b := metricOrderOneFixedSlope d zeta h_bunching_one
    let atomic := iteratedFDeriv ℝ 2 d.R (u, (zeta : ℝ → X) u)
      (fun _ : Fin 2 ↦ ((1 : ℝ), b.1 u))
    HasDerivAt
      (fun v ↦ metricOrderTwoFrozenDenominator d zeta v (b.1 u))
      atomic.1 u := by
  dsimp only
  let b := metricOrderOneFixedSlope d zeta h_bunching_one
  let atomic := iteratedFDeriv ℝ 2 d.R (u, (zeta : ℝ → X) u)
    (fun _ : Fin 2 ↦ ((1 : ℝ), b.1 u))
  have hR := metricOrderTwoFrozenRDerivative_hasDerivAt
    d zeta hfixed h_bunching_one u
  have hcenter : HasDerivAt
      (fun v : ℝ ↦
        ((fderiv ℝ d.R (v, (zeta : ℝ → X) v)) (1, b.1 u)).1)
      atomic.1 u :=
    by
      have hcomponent : HasDerivAt
          (fun v : ℝ ↦
            ((fderiv ℝ d.R (v, (zeta : ℝ → X) v)) (1, b.1 u)).1)
          (((fderiv ℝ (fderiv ℝ d.R) (u, (zeta : ℝ → X) u))
            (1, b.1 u)) (1, b.1 u)).1 u := by
        have hraw := (hR.hasFDerivAt.fst).hasDerivAt
        simpa only [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.toSpanSingleton_apply, one_smul,
          ContinuousLinearMap.coe_fst', b, iteratedFDeriv_two_apply] using hraw
      simpa only [b, atomic, iteratedFDeriv_two_apply] using hcomponent
  have hcenter' : HasDerivAt
      (fun v : ℝ ↦
        ((fderiv ℝ d.R (v, (zeta : ℝ → X) v)) (1, b.1 u)).1)
      atomic.1 u := hcenter
  have hadd :
      (fun _ : ℝ ↦ (1 : ℝ)) +
          (fun v : ℝ ↦
            ((fderiv ℝ d.R (v, (zeta : ℝ → X) v)) (1, b.1 u)).1) =
        (fun v : ℝ ↦
          (1 : ℝ) + ((fderiv ℝ d.R (v, (zeta : ℝ → X) v)) (1, b.1 u)).1) := by
    funext v
    rfl
  have hsum := (hasDerivAt_const u (1 : ℝ)).add hcenter'
  rw [hadd] at hsum
  simpa only [metricOrderTwoFrozenDenominator, b, atomic,
    iteratedFDeriv_two_apply, zero_add, add_zero] using hsum

/-- Helper for Infrastructure I.16a: the frozen numerator derivative is the stable
coordinate of the diagonal second derivative of `R`. -/
theorem metricOrderTwoFrozenNumerator_hasDerivAt
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (u : ℝ) :
    let b := metricOrderOneFixedSlope d zeta h_bunching_one
    let atomic := iteratedFDeriv ℝ 2 d.R (u, (zeta : ℝ → X) u)
      (fun _ : Fin 2 ↦ ((1 : ℝ), b.1 u))
    HasDerivAt
      (fun v ↦ metricOrderTwoFrozenNumerator d zeta v (b.1 u))
      atomic.2 u := by
  dsimp only
  let b := metricOrderOneFixedSlope d zeta h_bunching_one
  let atomic := iteratedFDeriv ℝ 2 d.R (u, (zeta : ℝ → X) u)
    (fun _ : Fin 2 ↦ ((1 : ℝ), b.1 u))
  have hR := metricOrderTwoFrozenRDerivative_hasDerivAt
    d zeta hfixed h_bunching_one u
  have hstable : HasDerivAt
      (fun v : ℝ ↦
        ((fderiv ℝ d.R (v, (zeta : ℝ → X) v)) (1, b.1 u)).2)
      atomic.2 u :=
    by
      have hcomponent : HasDerivAt
          (fun v : ℝ ↦
            ((fderiv ℝ d.R (v, (zeta : ℝ → X) v)) (1, b.1 u)).2)
          (((fderiv ℝ (fderiv ℝ d.R) (u, (zeta : ℝ → X) u))
            (1, b.1 u)) (1, b.1 u)).2 u := by
        have hraw := (hR.hasFDerivAt.snd).hasDerivAt
        simpa only [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.toSpanSingleton_apply, one_smul,
          ContinuousLinearMap.coe_snd', b, iteratedFDeriv_two_apply] using hraw
      simpa only [b, atomic, iteratedFDeriv_two_apply] using hcomponent
  have hstable' : HasDerivAt
      (fun v : ℝ ↦
        ((fderiv ℝ d.R (v, (zeta : ℝ → X) v)) (1, b.1 u)).2)
      atomic.2 u := hstable
  have hadd :
      (fun _ : ℝ ↦ d.L (b.1 u)) +
          (fun v : ℝ ↦
            ((fderiv ℝ d.R (v, (zeta : ℝ → X) v)) (1, b.1 u)).2) =
        (fun v : ℝ ↦
          d.L (b.1 u) +
            ((fderiv ℝ d.R (v, (zeta : ℝ → X) v)) (1, b.1 u)).2) := by
    funext v
    rfl
  have hsum := (hasDerivAt_const u (d.L (b.1 u))).add hstable'
  rw [hadd] at hsum
  simpa only [metricOrderTwoFrozenNumerator, b, atomic,
    iteratedFDeriv_two_apply, zero_add, add_zero] using hsum

/-- Helper for Infrastructure I.16a: at order two the reserved forcing consists exactly of
the diagonal second derivative of `R` with the center feedback subtracted. -/
theorem metricReservedTopForcing_two_eq_frozenAtomic
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (u : ℝ) :
    let b := metricOrderOneFixedSlope d zeta h_bunching_one
    let atomic := iteratedFDeriv ℝ 2 d.R (u, (zeta : ℝ → X) u)
      (fun _ : Fin 2 ↦ ((1 : ℝ), b.1 u))
    metricReservedTopForcing d zeta 2 u =
      (deriv (d.centerMap zeta) u)⁻¹ ^ 2 •
        (atomic.2 - atomic.1 • b.1 (d.centerMap zeta u)) := by
  dsimp only
  let b := metricOrderOneFixedSlope d zeta h_bunching_one
  have hzeta :=
    metricFixedGraph_hasDerivAt_orderOne d zeta hfixed h_bunching_one u
  have hpair : HasDerivAt
      (fun v : ℝ ↦ (v, (zeta : ℝ → X) v)) ((1 : ℝ), b.1 u) u := by
    exact (hasDerivAt_id u).prodMk hzeta
  have hpairDerivative :
      iteratedDeriv 1 (fun v : ℝ ↦ (v, (zeta : ℝ → X) v)) u =
        ((1 : ℝ), b.1 u) := by
    rw [iteratedDeriv_one]
    exact hpair.deriv
  have hgraphDerivative :
      deriv (zeta : ℝ → X) (d.centerMap zeta u) =
        b.1 (d.centerMap zeta u) := by
    rw [metricFixedGraph_deriv_eq_orderOneSlope
      d zeta hfixed h_bunching_one]
  have hnu_two : (2 : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast d.hnu
  have hR_two : ContDiffAt ℝ 2 d.R (u, (zeta : ℝ → X) u) :=
    (d.hR_smooth.of_le hnu_two).contDiffAt
  have hR_fst : ContDiffAt ℝ 2
      (fun z : ℝ × X ↦ (d.R z).1) (u, (zeta : ℝ → X) u) :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.fst ℝ ℝ X)).contDiffAt.comp
      (u, (zeta : ℝ → X) u) hR_two
  have hR_snd : ContDiffAt ℝ 2
      (fun z : ℝ × X ↦ (d.R z).2) (u, (zeta : ℝ → X) u) :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.snd ℝ ℝ X)).contDiffAt.comp
      (u, (zeta : ℝ → X) u) hR_two
  have hR_prod := iteratedFDeriv_prodMk (i := 2) hR_fst hR_snd (by norm_num)
  have hR_fun :
      (fun z : ℝ × X ↦ ((d.R z).1, (d.R z).2)) = d.R := by
    funext z
    rfl
  rw [hR_fun] at hR_prod
  have hR_fst_coeff :
      (iteratedFDeriv ℝ 2 (fun z : ℝ × X ↦ (d.R z).1)
        (u, (zeta : ℝ → X) u))
          (fun _ : Fin 2 ↦ ((1 : ℝ), b.1 u)) =
        (iteratedFDeriv ℝ 2 d.R (u, (zeta : ℝ → X) u)
          (fun _ : Fin 2 ↦ ((1 : ℝ), b.1 u))).1 := by
    simpa only [ContinuousMultilinearMap.prod_apply] using
      (congrArg
        (fun q ↦ (q (fun _ : Fin 2 ↦ ((1 : ℝ), b.1 u))).1) hR_prod).symm
  have hR_snd_coeff :
      (iteratedFDeriv ℝ 2 (fun z : ℝ × X ↦ (d.R z).2)
        (u, (zeta : ℝ → X) u))
          (fun _ : Fin 2 ↦ ((1 : ℝ), b.1 u)) =
        (iteratedFDeriv ℝ 2 d.R (u, (zeta : ℝ → X) u)
          (fun _ : Fin 2 ↦ ((1 : ℝ), b.1 u))).2 := by
    simpa only [ContinuousMultilinearMap.prod_apply] using
      (congrArg
        (fun q ↦ (q (fun _ : Fin 2 ↦ ((1 : ℝ), b.1 u))).2) hR_prod).symm
  rw [metricReservedTopForcing.eq_1, hpairDerivative, hgraphDerivative,
    orderedFinpartition_two_residual_filter_eq_empty, hR_fst_coeff, hR_snd_coeff]
  simp only [Finset.sum_empty, add_zero, sub_zero, b]

/-- Helper for Infrastructure I.16a: the frozen rational value at the fixed slope direction is
the fixed slope at the corresponding output center. -/
theorem metricOrderTwoFrozenSlopeValue_fixed
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (u : ℝ) :
    let b := metricOrderOneFixedSlope d zeta h_bunching_one
    metricOrderTwoFrozenSlopeValue d zeta u (b.1 u) =
      b.1 (d.centerMap zeta u) := by
  dsimp only
  let b := metricOrderOneFixedSlope d zeta h_bunching_one
  have hfixedSlope : metricOrderOneSlopeOperator d zeta b = b :=
    metricOrderOneFixedSlope_fixed d zeta h_bunching_one
  have hvalue := congrArg
    (fun c : MetricSlopeSection d ↦ c.1 (d.centerMap zeta u)) hfixedSlope
  rw [metricOrderOneSlopeOperator_apply_centerMap_eq_frozen] at hvalue
  exact hvalue

/-- Helper for Infrastructure I.16a: the canonical order-two reserved section obtained from the
previous-order fixed graph and the order-two bunching inequality. -/
noncomputable def metricOrderTwoFixedSection
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (h_bunching_two :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ 2 < 1) :
    BoundedContinuousFunction ℝ X :=
  metricReservedTopFixedSection d zeta hfixed (Nat.le_refl 2) d.hnu
    (metricFixedGraph_contDiff_one_of_orderOneBunching
      d zeta hfixed h_bunching_one)
    h_bunching_two

/-- Helper for Infrastructure I.16a: the order-two raw defect compares the translated canonical
fixed slope with the canonical reserved order-two section. -/
noncomputable def metricOrderTwoRawDefect
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (h_bunching_two :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ 2 < 1)
    (y t : ℝ) : X :=
  (metricOrderOneFixedSlope d zeta h_bunching_one).1 (y + t) -
    (metricOrderOneFixedSlope d zeta h_bunching_one).1 y -
      t • metricOrderTwoFixedSection d zeta hfixed h_bunching_one h_bunching_two y

/-- Helper for Infrastructure I.16a: the order-two raw defect vanishes at zero increment. -/
theorem metricOrderTwoRawDefect_zero
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (h_bunching_two :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ 2 < 1)
    (y : ℝ) :
    metricOrderTwoRawDefect d zeta hfixed h_bunching_one h_bunching_two y 0 = 0 := by
  simp only [metricOrderTwoRawDefect, add_zero, sub_self, zero_smul, sub_zero]

/-- Helper for Infrastructure I.16a: the order-two raw defect is uniformly bounded on a fixed
neighborhood of the zero increment. -/
theorem metricOrderTwoRawDefect_locallyUniformlyBounded
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (h_bunching_two :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ 2 < 1) :
    ∃ cutoff > 0, ∃ bound ≥ 0, ∀ y t : ℝ, ‖t‖ < cutoff →
      ‖metricOrderTwoRawDefect d zeta hfixed h_bunching_one h_bunching_two y t‖ ≤
        bound := by
  let b := metricOrderOneFixedSlope d zeta h_bunching_one
  let a := metricOrderTwoFixedSection d zeta hfixed h_bunching_one h_bunching_two
  refine ⟨1, zero_lt_one, 2 * (d.slope : ℝ) + ‖a‖, ?_, ?_⟩
  · positivity
  · intro y t ht
    have ht_abs : |t| < 1 := by
      simpa only [Real.norm_eq_abs] using ht
    have hstable :
        ‖t • a y‖ ≤ ‖a‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |t| * ‖a y‖ ≤ 1 * ‖a y‖ :=
          mul_le_mul_of_nonneg_right ht_abs.le (norm_nonneg _)
        _ = ‖a y‖ := one_mul _
        _ ≤ ‖a‖ := BoundedContinuousFunction.norm_coe_le_norm a y
    calc
      ‖metricOrderTwoRawDefect d zeta hfixed h_bunching_one h_bunching_two y t‖ =
          ‖(b.1 (y + t) - b.1 y) - t • a y‖ := by
        rfl
      _ ≤ ‖b.1 (y + t) - b.1 y‖ + ‖t • a y‖ := norm_sub_le _ _
      _ ≤ (‖b.1 (y + t)‖ + ‖b.1 y‖) + ‖t • a y‖ := by
        exact add_le_add_left
          (norm_sub_le (b.1 (y + t)) (b.1 y)) (‖t • a y‖)
      _ ≤ ((d.slope : ℝ) + (d.slope : ℝ)) + ‖a‖ := by
        exact add_le_add (add_le_add (b.norm_apply_le (y + t))
          (b.norm_apply_le y)) hstable
      _ = 2 * (d.slope : ℝ) + ‖a‖ := by ring

/-- Helper for Infrastructure I.16a: on the canonical fixed slope, the rational denominator is
the derivative of the center change of variables. -/
theorem metricOrderOneDenominator_fixedSlope_eq_centerMap_deriv
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (u : ℝ) :
    metricOrderOneDenominator d zeta
        (metricOrderOneFixedSlope d zeta h_bunching_one) u =
      deriv (d.centerMap zeta) u := by
  let b := metricOrderOneFixedSlope d zeta h_bunching_one
  have hzeta := metricFixedGraph_hasDerivAt_orderOne
    d zeta hfixed h_bunching_one u
  have hpair : HasDerivAt (fun x : ℝ ↦ (x, (zeta : ℝ → X) x))
      ((1 : ℝ), b.1 u) u := by
    exact (hasDerivAt_id u).prodMk hzeta
  have hnu_ne_nat : d.nu ≠ 0 :=
    Nat.ne_of_gt (Nat.zero_lt_two.trans_le d.hnu)
  have hnu_ne : (d.nu : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast hnu_ne_nat
  have hR : DifferentiableAt ℝ d.R (u, (zeta : ℝ → X) u) :=
    (d.hR_smooth.differentiable hnu_ne) (u, (zeta : ℝ → X) u)
  have hcomposition :
      HasDerivAt (fun x : ℝ ↦ d.R (x, (zeta : ℝ → X) x))
        ((fderiv ℝ d.R (u, (zeta : ℝ → X) u)) (1, b.1 u)) u := by
    exact hR.hasFDerivAt.comp_hasDerivAt u hpair
  have hcenterRemainder :
      HasDerivAt (fun x : ℝ ↦ (d.R (x, (zeta : ℝ → X) x)).1)
        (((fderiv ℝ d.R (u, (zeta : ℝ → X) u)) (1, b.1 u)).1) u := by
    exact hcomposition.fst
  have hcenterMap :
      HasDerivAt (d.centerMap zeta)
        (1 + ((fderiv ℝ d.R (u, (zeta : ℝ → X) u)) (1, b.1 u)).1) u := by
    rw [d.centerMap_eq zeta]
    exact (hasDerivAt_id u).add hcenterRemainder
  rw [metricOrderOneDenominator_eq]
  exact hcenterMap.deriv.symm

/-- Helper for Infrastructure I.16a: with the stable direction frozen at the canonical fixed
slope, the rational slope value has derivative equal to the center derivative times the
order-two reserved forcing. -/
theorem metricOrderTwoFrozenSlopeValue_hasDerivAt
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (u : ℝ) :
    let b := metricOrderOneFixedSlope d zeta h_bunching_one
    HasDerivAt
      (fun v ↦ metricOrderTwoFrozenSlopeValue d zeta v (b.1 u))
      (deriv (d.centerMap zeta) u • metricReservedTopForcing d zeta 2 u) u := by
  dsimp only
  let b := metricOrderOneFixedSlope d zeta h_bunching_one
  let atomic := iteratedFDeriv ℝ 2 d.R (u, (zeta : ℝ → X) u)
    (fun _ : Fin 2 ↦ ((1 : ℝ), b.1 u))
  have hdenominator := metricOrderTwoFrozenDenominator_hasDerivAt
    d zeta hfixed h_bunching_one u
  have hnumerator := metricOrderTwoFrozenNumerator_hasDerivAt
    d zeta hfixed h_bunching_one u
  have hdenominatorValue :
      metricOrderTwoFrozenDenominator d zeta u (b.1 u) =
        deriv (d.centerMap zeta) u := by
    rw [metricOrderTwoFrozenDenominator_eq]
    exact metricOrderOneDenominator_fixedSlope_eq_centerMap_deriv
      d zeta hfixed h_bunching_one u
  have hcenter_ne : deriv (d.centerMap zeta) u ≠ 0 := by
    exact centerMap_deriv_ne_zero d zeta
      (metricFixedGraph_contDiff_one_of_orderOneBunching
        d zeta hfixed h_bunching_one) u
  have hdenominator_ne :
      metricOrderTwoFrozenDenominator d zeta u (b.1 u) ≠ 0 := by
    rw [hdenominatorValue]
    exact hcenter_ne
  have hquotient := hasDerivAt_inv_smul_quotient
    hdenominator hnumerator hdenominator_ne
  have hquotient' : HasDerivAt
      (fun v ↦ metricOrderTwoFrozenSlopeValue d zeta v (b.1 u))
      ((metricOrderTwoFrozenDenominator d zeta u (b.1 u))⁻¹ •
        (atomic.2 - atomic.1 •
          ((metricOrderTwoFrozenDenominator d zeta u (b.1 u))⁻¹ •
            metricOrderTwoFrozenNumerator d zeta u (b.1 u)))) u := by
    simpa only [metricOrderTwoFrozenSlopeValue] using hquotient
  have hfrozenValue := metricOrderTwoFrozenSlopeValue_fixed
    d zeta h_bunching_one u
  have hinverseNumerator :
      (metricOrderTwoFrozenDenominator d zeta u (b.1 u))⁻¹ •
          metricOrderTwoFrozenNumerator d zeta u (b.1 u) =
        b.1 (d.centerMap zeta u) := by
    simpa only [metricOrderTwoFrozenSlopeValue] using hfrozenValue
  have hforcing := metricReservedTopForcing_two_eq_frozenAtomic
    d zeta hfixed h_bunching_one u
  have hscalar :
      deriv (d.centerMap zeta) u *
          (deriv (d.centerMap zeta) u)⁻¹ ^ 2 =
        (deriv (d.centerMap zeta) u)⁻¹ := by
    field_simp [hcenter_ne]
  apply hquotient'.congr_deriv
  rw [hinverseNumerator, hdenominatorValue, hforcing, smul_smul, hscalar]

/-- Helper for Infrastructure I.16a: at the canonical fixed direction, the frozen source
partial derivative is the center derivative times the reserved order-two forcing. -/
theorem metricOrderTwoFrozenSourceDerivative_fixed
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (u : ℝ) :
    let b := metricOrderOneFixedSlope d zeta h_bunching_one
    metricOrderTwoFrozenSourceDerivative d zeta u (b.1 u) =
      deriv (d.centerMap zeta) u • metricReservedTopForcing d zeta 2 u := by
  dsimp only
  let b := metricOrderOneFixedSlope d zeta h_bunching_one
  have hzeta_one :=
    metricFixedGraph_contDiff_one_of_orderOneBunching
      d zeta hfixed h_bunching_one
  have hsource :=
    metricOrderTwoFrozenSlopeValue_hasDerivAt_sourceDerivative
      d zeta hzeta_one u (b.norm_apply_le u)
  have hforcing :=
    metricOrderTwoFrozenSlopeValue_hasDerivAt
      d zeta hfixed h_bunching_one u
  exact hsource.unique hforcing

/-- Helper for Infrastructure I.16a: the canonical fixed slope is uniformly continuous on the
whole source line. -/
theorem uniformContinuous_metricOrderOneFixedSlope
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1) :
    UniformContinuous
      (metricOrderOneFixedSlope d zeta h_bunching_one).1 := by
  have hsupport :
      HasCompactSupport
        (metricOrderOneFixedSlope d zeta h_bunching_one).1 := by
    have hderivSupport :=
      (fixedGraph_hasCompactSupport d zeta hfixed).deriv
    rw [metricFixedGraph_deriv_eq_orderOneSlope
      d zeta hfixed h_bunching_one] at hderivSupport
    exact hderivSupport
  exact
    (metricOrderOneFixedSlope d zeta h_bunching_one).1.continuous
      |>.uniformContinuous_of_tendsto_cocompact hsupport.is_zero_at_infty

/-- Helper for Infrastructure I.16a: at the canonical fixed slope, the exact rational difference
coefficient is the center derivative times the reserved order-two coefficient. -/
theorem metricOrderOneDifferenceCoefficient_fixed_eq_centerDeriv_smul_reserved
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (u : ℝ) :
    metricOrderOneDifferenceCoefficient d zeta
        (metricOrderOneFixedSlope d zeta h_bunching_one)
        (metricOrderOneFixedSlope d zeta h_bunching_one) u =
      deriv (d.centerMap zeta) u • metricReservedTopCoefficient d zeta 2 u := by
  let b := metricOrderOneFixedSlope d zeta h_bunching_one
  have hdenominator :=
    metricOrderOneDenominator_fixedSlope_eq_centerMap_deriv
      d zeta hfixed h_bunching_one u
  have hderivGraph :=
    metricFixedGraph_deriv_eq_orderOneSlope d zeta hfixed h_bunching_one
  have hcenter_ne : deriv (d.centerMap zeta) u ≠ 0 := by
    exact centerMap_deriv_ne_zero d zeta
      (metricFixedGraph_contDiff_one_of_orderOneBunching
        d zeta hfixed h_bunching_one) u
  ext w
  rw [metricOrderOneDifferenceCoefficient_apply, hdenominator]
  simp only [smul_apply]
  rw [metricReservedTopCoefficient_apply]
  have hfixedValue : b.1 (d.centerMap zeta u) =
      deriv (zeta : ℝ → X) (d.centerMap zeta u) := by
    rw [hderivGraph]
  rw [hfixedValue, smul_smul]
  have hscalar :
      (deriv (d.centerMap zeta) u) * (deriv (d.centerMap zeta) u)⁻¹ ^ 2 =
        (deriv (d.centerMap zeta) u)⁻¹ := by
    field_simp [hcenter_ne]
  rw [hscalar]

/-- Helper for Infrastructure I.16a: the canonical order-two section satisfies the reserved
affine equation in source coordinates. -/
theorem metricOrderTwoFixedSection_sourceEquation
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (h_bunching_two :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ 2 < 1)
    (u : ℝ) :
    metricOrderTwoFixedSection d zeta hfixed h_bunching_one h_bunching_two
        (d.centerMap zeta u) =
      metricReservedTopCoefficient d zeta 2 u
          (metricOrderTwoFixedSection d zeta hfixed h_bunching_one h_bunching_two u) +
        metricReservedTopForcing d zeta 2 u := by
  exact metricReservedTopFixedSection_sourceEquation d zeta hfixed
    (Nat.le_refl 2) d.hnu
    (metricFixedGraph_contDiff_one_of_orderOneBunching
      d zeta hfixed h_bunching_one)
    h_bunching_two u

/-- Helper for Infrastructure I.16a: after multiplying by the center derivative, the order-two
fixed-section equation uses the rational difference coefficient and the scaled reserved forcing. -/
theorem metricOrderTwoFixedSection_centerDerivativeEquation
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (h_bunching_two :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ 2 < 1)
    (u : ℝ) :
    deriv (d.centerMap zeta) u •
        metricOrderTwoFixedSection d zeta hfixed h_bunching_one h_bunching_two
          (d.centerMap zeta u) =
      metricOrderOneDifferenceCoefficient d zeta
          (metricOrderOneFixedSlope d zeta h_bunching_one)
          (metricOrderOneFixedSlope d zeta h_bunching_one) u
          (metricOrderTwoFixedSection d zeta hfixed h_bunching_one h_bunching_two u) +
        deriv (d.centerMap zeta) u • metricReservedTopForcing d zeta 2 u := by
  have hsource := metricOrderTwoFixedSection_sourceEquation
    d zeta hfixed h_bunching_one h_bunching_two u
  have hcoefficient :=
    metricOrderOneDifferenceCoefficient_fixed_eq_centerDeriv_smul_reserved
      d zeta hfixed h_bunching_one u
  have hcoefficientApply := congrArg
    (fun A : X →L[ℝ] X ↦
      A (metricOrderTwoFixedSection d zeta hfixed h_bunching_one h_bunching_two u))
    hcoefficient
  rw [hsource, smul_add]
  have hpack :
      deriv (d.centerMap zeta) u •
          (metricReservedTopCoefficient d zeta 2 u)
            (metricOrderTwoFixedSection d zeta hfixed h_bunching_one h_bunching_two u) =
        (deriv (d.centerMap zeta) u • metricReservedTopCoefficient d zeta 2 u)
          (metricOrderTwoFixedSection d zeta hfixed h_bunching_one h_bunching_two u) := by
    rfl
  rw [hpack, ← hcoefficientApply]

/-- Helper for Infrastructure I.16a: the base variation compares the fixed-slope value at a
translated source center with the slope transform of the translated candidate at the old center. -/
def metricOrderTwoBaseVariation
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (u s : ℝ) : X :=
  b.1 (d.centerMap zeta (u + s)) -
    (metricOrderOneSlopeOperator d zeta (metricOrderTwoTranslatedSlope d b s)).1
      (d.centerMap zeta u)

/-- Helper for Infrastructure I.16a: for a fixed slope, the base variation is exactly the
source increment of the frozen rational value at the translated stable direction. -/
theorem metricOrderTwoBaseVariation_eq_frozenDifference
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d)
    (hb : metricOrderOneSlopeOperator d zeta b = b) (u s : ℝ) :
    metricOrderTwoBaseVariation d zeta b u s =
      metricOrderTwoFrozenSlopeValue d zeta (u + s) (b.1 (u + s)) -
        metricOrderTwoFrozenSlopeValue d zeta u (b.1 (u + s)) := by
  have hfirst :
      b.1 (d.centerMap zeta (u + s)) =
        metricOrderTwoFrozenSlopeValue d zeta (u + s) (b.1 (u + s)) := by
    rw [← metricOrderOneSlopeOperator_apply_centerMap_eq_frozen]
    rw [hb]
  have hsecond :
      (metricOrderOneSlopeOperator d zeta
          (metricOrderTwoTranslatedSlope d b s)).1
          (d.centerMap zeta u) =
        metricOrderTwoFrozenSlopeValue d zeta u (b.1 (u + s)) := by
    rw [metricOrderOneSlopeOperator_apply_centerMap_eq_frozen,
      metricOrderTwoTranslatedSlope_apply]
  rw [metricOrderTwoBaseVariation, hfirst, hsecond]

/-- Helper for Infrastructure I.16a: the fixed-slope base variation has a source-uniform
first-order expansion given by the scaled reserved order-two forcing. -/
theorem metricOrderTwoBaseVariation_uniform
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1) :
    ∀ e > 0, ∃ delta > 0, ∀ u s : ℝ, |s| < delta →
      ‖metricOrderTwoBaseVariation d zeta
          (metricOrderOneFixedSlope d zeta h_bunching_one) u s -
        s • (deriv (d.centerMap zeta) u •
          metricReservedTopForcing d zeta 2 u)‖ ≤ e * |s| := by
  intro e he
  let b := metricOrderOneFixedSlope d zeta h_bunching_one
  have hbFixed : metricOrderOneSlopeOperator d zeta b = b :=
    metricOrderOneFixedSlope_fixed d zeta h_bunching_one
  have hzeta_one :=
    metricFixedGraph_contDiff_one_of_orderOneBunching
      d zeta hfixed h_bunching_one
  obtain ⟨R, _hR_pos, hR_support⟩ :=
    d.hR_support.isBounded.subset_ball_lt 0 (0 : ℝ × X)
  have hsourceCompact :
      IsCompact (Metric.closedBall (0 : ℝ) (R + 1)) :=
    isCompact_closedBall (0 : ℝ) (R + 1)
  have hstableCompact :
      IsCompact
        (b.1 '' Metric.closedBall (0 : ℝ) (R + 2)) := by
    exact
      (isCompact_closedBall (0 : ℝ) (R + 2)).image b.1.continuous
  have hparameterCompact :
      IsCompact
        (Metric.closedBall (0 : ℝ) (R + 1) ×ˢ
          (b.1 '' Metric.closedBall (0 : ℝ) (R + 2))) :=
    hsourceCompact.prod hstableCompact
  let frozenFamily : (ℝ × X) → ℝ → X :=
    fun p h ↦ metricOrderTwoFrozenSlopeValue d zeta (p.1 + h) p.2
  have hfrozenFamily :
      ∀ p ∈
          Metric.closedBall (0 : ℝ) (R + 1) ×ˢ
            (b.1 '' Metric.closedBall (0 : ℝ) (R + 2)),
        ContDiffAt ℝ 1 (Function.uncurry frozenFamily) (p, 0) := by
    intro p hp
    obtain ⟨v, hv, hv_value⟩ := hp.2
    have hp_bound : ‖p.2‖ ≤ (d.slope : ℝ) := by
      rw [← hv_value]
      exact b.norm_apply_le v
    have hfrozen :=
      metricOrderTwoFrozenSlopeValue_contDiffAt
        d zeta hzeta_one p.1 hp_bound
    have hsourceCoordinate :
        ContDiffAt ℝ 1
          (fun q : (ℝ × X) × ℝ ↦ q.1.1 + q.2) (p, 0) :=
      (contDiffAt_fst.fst).add contDiffAt_snd
    have hstableCoordinate :
        ContDiffAt ℝ 1
          (fun q : (ℝ × X) × ℝ ↦ q.1.2) (p, 0) :=
      contDiffAt_fst.snd
    have hinclusion :
        ContDiffAt ℝ 1
          (fun q : (ℝ × X) × ℝ ↦ (q.1.1 + q.2, q.1.2)) (p, 0) :=
      hsourceCoordinate.prodMk hstableCoordinate
    have hfrozen' :
        ContDiffAt ℝ 1 (fun p : ℝ × X ↦ metricOrderTwoFrozenSlopeValue d zeta p.1 p.2)
          (p.1 + 0, p.2) := by
      simpa only [add_zero] using hfrozen
    have hcomposition := ContDiffAt.comp (p, 0) hfrozen' hinclusion
    have hfun : Function.uncurry frozenFamily =
        (fun q : (ℝ × X) × ℝ ↦
          metricOrderTwoFrozenSlopeValue d zeta (q.1.1 + q.2) q.1.2) := by
      funext q
      rfl
    have hcomposition' :
        ContDiffAt ℝ 1
          (fun q : (ℝ × X) × ℝ ↦
            metricOrderTwoFrozenSlopeValue d zeta (q.1.1 + q.2) q.1.2)
          (p, 0) := by
      simpa only [Function.comp_def] using hcomposition
    rw [hfun]
    exact hcomposition'
  have hfrozenRemainder :=
    FiniteTaylorJet.uniformRemainderOn_of_contDiffAt
      1 frozenFamily 0
      (Metric.closedBall (0 : ℝ) (R + 1) ×ˢ
        (b.1 '' Metric.closedBall (0 : ℝ) (R + 2)))
      hparameterCompact hfrozenFamily (e / 2) (half_pos he)
  obtain ⟨deltaTaylor, hdeltaTaylor, hTaylor⟩ :=
    FiniteTaylorJet.IsUniformRemainderOn.bound hfrozenRemainder
  let derivativeFamily : ℝ × X → X :=
    fun p ↦ metricOrderTwoFrozenSourceDerivative d zeta p.1 (b.1 p.1 + p.2)
  have hderivativeFamily :
      ∀ u ∈ Metric.closedBall (0 : ℝ) (R + 1),
        ContinuousAt derivativeFamily (u, 0) := by
    intro u hu
    have hparameter : Continuous
        (fun p : ℝ × X ↦ (p.1, b.1 p.1 + p.2)) :=
      continuous_fst.prodMk
        ((b.1.continuous.comp continuous_fst).add continuous_snd)
    have hparameterAt :
        ContinuousAt (fun p : ℝ × X ↦ (p.1, b.1 p.1 + p.2)) (u, 0) := by
      simpa only [add_zero] using
        (hparameter.continuousAt :
          ContinuousAt (fun p : ℝ × X ↦ (p.1, b.1 p.1 + p.2)) (u, 0))
    have hpartial :
        ContinuousAt
          (fun q : ℝ × X ↦ metricOrderTwoFrozenSourceDerivative d zeta q.1 q.2)
          (u, b.1 u) :=
      continuousAt_metricOrderTwoFrozenSourceDerivative
        d zeta hzeta_one u (b.norm_apply_le u)
    have hcomposition :=
      ContinuousAt.comp_of_eq (g := fun q : ℝ × X ↦
        metricOrderTwoFrozenSourceDerivative d zeta q.1 q.2)
        (f := fun p : ℝ × X ↦ (p.1, b.1 p.1 + p.2))
        hpartial hparameterAt (by simp)
    simpa only [Function.comp_def, derivativeFamily, add_zero] using hcomposition
  obtain ⟨deltaDerivative, hdeltaDerivative, hDerivative⟩ :=
    FiniteTaylorJet.compactValueOscillation
      hsourceCompact hderivativeFamily (half_pos he)
  obtain ⟨deltaSlope, hdeltaSlope, hSlope⟩ :=
    Metric.uniformContinuous_iff.mp
      (uniformContinuous_metricOrderOneFixedSlope
        d zeta hfixed h_bunching_one)
      deltaDerivative hdeltaDerivative
  let delta := min deltaTaylor (min deltaSlope 1)
  have hdelta : 0 < delta :=
    lt_min hdeltaTaylor (lt_min hdeltaSlope zero_lt_one)
  refine ⟨delta, hdelta, ?_⟩
  intro u s hs
  have hsTaylor : ‖s‖ < deltaTaylor := by
    rw [Real.norm_eq_abs]
    exact hs.trans_le (min_le_left deltaTaylor (min deltaSlope 1))
  have hsSlope : |s| < deltaSlope := by
    exact hs.trans_le
      ((min_le_right deltaTaylor (min deltaSlope 1)).trans
        (min_le_left deltaSlope 1))
  have hsOne : |s| < 1 := by
    exact hs.trans_le
      ((min_le_right deltaTaylor (min deltaSlope 1)).trans
        (min_le_right deltaSlope 1))
  by_cases hu : u ∈ Metric.closedBall (0 : ℝ) (R + 1)
  · have hushift : u + s ∈ Metric.closedBall (0 : ℝ) (R + 2) := by
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hu ⊢
      calc
        |u + s| ≤ |u| + |s| := by
          simpa only [Real.norm_eq_abs] using (norm_add_le u s)
        _ ≤ (R + 1) + 1 := add_le_add hu hsOne.le
        _ = R + 2 := by ring
    have hparameter :
        (u, b.1 (u + s)) ∈
          Metric.closedBall (0 : ℝ) (R + 1) ×ˢ
            (b.1 '' Metric.closedBall (0 : ℝ) (R + 2)) :=
      ⟨hu, ⟨u + s, hushift, rfl⟩⟩
    have hTaylorBound :=
      hTaylor (u, b.1 (u + s)) hparameter s hsTaylor
    rw [metricOrderTwoFrozenSlopeValue_translated_remainder_eq
      d zeta hzeta_one u s (b.norm_apply_le (u + s))] at hTaylorBound
    have hTaylorError :
        ‖metricOrderTwoFrozenSlopeValue d zeta (u + s) (b.1 (u + s)) -
            metricOrderTwoFrozenSlopeValue d zeta u (b.1 (u + s)) -
              s • metricOrderTwoFrozenSourceDerivative d zeta u (b.1 (u + s))‖ ≤
          (e / 2) * |s| := by
      simpa only [frozenFamily, Real.norm_eq_abs, Nat.cast_one, Real.rpow_one] using hTaylorBound
    have hinputDistance : dist (u + s) u < deltaSlope := by
      simpa only [Real.dist_eq, add_sub_cancel_left] using hsSlope
    have hslopeClose := hSlope hinputDistance
    have hslopeDifference :
        ‖b.1 (u + s) - b.1 u‖ < deltaDerivative := by
      simpa only [dist_eq_norm] using hslopeClose
    have hDerivativeBound :=
      hDerivative u hu (b.1 (u + s) - b.1 u) hslopeDifference
    have hslopeSum :
        b.1 u + (b.1 (u + s) - b.1 u) = b.1 (u + s) := by
      abel
    have hDerivativeError :
        ‖metricOrderTwoFrozenSourceDerivative d zeta u (b.1 (u + s)) -
            metricOrderTwoFrozenSourceDerivative d zeta u (b.1 u)‖ ≤
          e / 2 := by
      simpa only [derivativeFamily, zero_add, add_zero, hslopeSum] using
        hDerivativeBound.le
    have hdecomposition :
        metricOrderTwoBaseVariation d zeta b u s -
            s • (deriv (d.centerMap zeta) u •
              metricReservedTopForcing d zeta 2 u) =
          (metricOrderTwoFrozenSlopeValue d zeta (u + s) (b.1 (u + s)) -
              metricOrderTwoFrozenSlopeValue d zeta u (b.1 (u + s)) -
                s • metricOrderTwoFrozenSourceDerivative d zeta u (b.1 (u + s))) +
            s •
              (metricOrderTwoFrozenSourceDerivative d zeta u (b.1 (u + s)) -
                metricOrderTwoFrozenSourceDerivative d zeta u (b.1 u)) := by
      rw [metricOrderTwoBaseVariation_eq_frozenDifference
        d zeta b hbFixed u s,
        ← metricOrderTwoFrozenSourceDerivative_fixed
          d zeta hfixed h_bunching_one u]
      module
    rw [hdecomposition]
    calc
      ‖(metricOrderTwoFrozenSlopeValue d zeta (u + s) (b.1 (u + s)) -
            metricOrderTwoFrozenSlopeValue d zeta u (b.1 (u + s)) -
              s • metricOrderTwoFrozenSourceDerivative d zeta u (b.1 (u + s))) +
          s •
            (metricOrderTwoFrozenSourceDerivative d zeta u (b.1 (u + s)) -
              metricOrderTwoFrozenSourceDerivative d zeta u (b.1 u))‖ ≤
          ‖metricOrderTwoFrozenSlopeValue d zeta (u + s) (b.1 (u + s)) -
            metricOrderTwoFrozenSlopeValue d zeta u (b.1 (u + s)) -
              s • metricOrderTwoFrozenSourceDerivative d zeta u (b.1 (u + s))‖ +
            ‖s •
              (metricOrderTwoFrozenSourceDerivative d zeta u (b.1 (u + s)) -
                metricOrderTwoFrozenSourceDerivative d zeta u (b.1 u))‖ :=
        norm_add_le _ _
      _ ≤ (e / 2) * |s| + |s| * (e / 2) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact add_le_add hTaylorError
          (mul_le_mul_of_nonneg_left hDerivativeError (abs_nonneg s))
      _ = e * |s| := by ring
  · have hu_abs : R + 1 < |u| := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
        not_le] using hu
    have htriangle : |u| ≤ |u + s| + |s| := by
      calc
        |u| = |(u + s) + (-s)| := by ring_nf
        _ ≤ |u + s| + |-s| := by
          simpa only [Real.norm_eq_abs] using (norm_add_le (u + s) (-s))
        _ = |u + s| + |s| := by rw [abs_neg]
    have hushift_abs : R < |u + s| := by
      nlinarith
    have hgraphOutside {v : ℝ} (hv : R < |v|) :
        (v, (zeta : ℝ → X) v) ∉ tsupport d.R := by
      intro hv_support
      have hpoint_lt : ‖(v, (zeta : ℝ → X) v)‖ < R := by
        simpa only [Metric.mem_ball, dist_zero_right] using
          hR_support hv_support
      have hv_le : |v| ≤ ‖(v, (zeta : ℝ → X) v)‖ := by
        simpa only [Real.norm_eq_abs] using
          (norm_fst_le (v, (zeta : ℝ → X) v))
      nlinarith
    have hu_outside_abs : R < |u| := by
      nlinarith
    have hu_graph : (u, (zeta : ℝ → X) u) ∉ tsupport d.R :=
      hgraphOutside hu_outside_abs
    have hushift_graph :
        (u + s, (zeta : ℝ → X) (u + s)) ∉ tsupport d.R :=
      hgraphOutside hushift_abs
    have hbaseZero : metricOrderTwoBaseVariation d zeta b u s = 0 := by
      rw [metricOrderTwoBaseVariation_eq_frozenDifference
        d zeta b hbFixed u s,
        metricOrderTwoFrozenSlopeValue_eq_linear_of_notMem_tsupport
          d zeta hushift_graph,
        metricOrderTwoFrozenSlopeValue_eq_linear_of_notMem_tsupport
          d zeta hu_graph,
        sub_self]
    have hforcingZero :
        deriv (d.centerMap zeta) u •
            metricReservedTopForcing d zeta 2 u = 0 := by
      rw [← metricOrderTwoFrozenSourceDerivative_fixed
        d zeta hfixed h_bunching_one u]
      exact
        metricOrderTwoFrozenSourceDerivative_eq_zero_of_notMem_tsupport
          d zeta hzeta_one (b.norm_apply_le u) hu_graph
    rw [hbaseZero, hforcingZero, smul_zero, sub_zero, norm_zero]
    exact mul_nonneg he.le (abs_nonneg s)

/-- Helper for Infrastructure I.16a: off the graph trace of the remainder support, the metric
center map is the identity. -/
theorem metricCenterMap_eq_self_of_graph_notMem_tsupport
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    {u : ℝ} (hu : (u, (zeta : ℝ → X) u) ∉ tsupport d.R) :
    d.centerMap zeta u = u := by
  have hzero : d.R (u, (zeta : ℝ → X) u) = 0 :=
    image_eq_zero_of_notMem_tsupport hu
  rw [d.centerMap_eq zeta]
  change u + (d.R (u, (zeta : ℝ → X) u)).1 = u
  rw [hzero]
  simp only [Prod.fst_zero, add_zero]

/-- Helper for Infrastructure I.16a: off the graph trace of the remainder support, the metric
center map has derivative one. -/
theorem metricCenterMap_deriv_eq_one_of_graph_notMem_tsupport
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    {u : ℝ} (hu : (u, (zeta : ℝ → X) u) ∉ tsupport d.R) :
    deriv (d.centerMap zeta) u = 1 := by
  rw [← metricOrderOneDenominator_fixedSlope_eq_centerMap_deriv
    d zeta hfixed h_bunching_one u,
    metricOrderOneDenominator_eq,
    fderiv_of_notMem_tsupport ℝ hu]
  simp

/-- Helper for Infrastructure I.16a: the center change of variables has a globally
source-uniform first-order Taylor remainder. -/
theorem metricCenterMapRemainder_uniform
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1) :
    ∀ e > 0, ∃ delta > 0, ∀ u s : ℝ, |s| < delta →
      |d.centerMap zeta (u + s) - d.centerMap zeta u -
        s * deriv (d.centerMap zeta) u| ≤ e * |s| := by
  intro e he
  have hzeta_one :=
    metricFixedGraph_contDiff_one_of_orderOneBunching
      d zeta hfixed h_bunching_one
  have hone_nat : 1 ≤ d.nu :=
    le_trans (by norm_num : 1 ≤ 2) d.hnu
  have hone : (1 : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hone_nat
  have hcenterMap : ContDiff ℝ 1 (d.centerMap zeta) :=
    centerMap_contDiff_of_prev d zeta hone hzeta_one
  obtain ⟨R, _hR_pos, hR_support⟩ :=
    d.hR_support.isBounded.subset_ball_lt 0 (0 : ℝ × X)
  have hsourceCompact :
      IsCompact (Metric.closedBall (0 : ℝ) (R + 1)) :=
    isCompact_closedBall (0 : ℝ) (R + 1)
  obtain ⟨deltaTaylor, hdeltaTaylor, hTaylor⟩ :=
    LocalCutoff.GraphTransform.uniformTranslatedFirstOrderRemainderOn
      hcenterMap hsourceCompact he
  let delta := min deltaTaylor 1
  have hdelta : 0 < delta := lt_min hdeltaTaylor zero_lt_one
  refine ⟨delta, hdelta, ?_⟩
  intro u s hs
  have hsTaylor : ‖s‖ < deltaTaylor := by
    rw [Real.norm_eq_abs]
    exact hs.trans_le (min_le_left deltaTaylor 1)
  have hsOne : |s| < 1 :=
    hs.trans_le (min_le_right deltaTaylor 1)
  by_cases hu : u ∈ Metric.closedBall (0 : ℝ) (R + 1)
  · have hcenterAt :
        HasDerivAt (d.centerMap zeta)
          (deriv (d.centerMap zeta) u) u :=
      (hcenterMap.differentiable one_ne_zero u).hasDerivAt
    have htranslation : HasDerivAt (fun h : ℝ ↦ u + h) 1 0 := by
      have hraw := (hasDerivAt_const 0 u).add (hasDerivAt_id 0)
      have hfun : ((fun _ : ℝ ↦ u) + id) = (fun h : ℝ ↦ u + h) := by
        funext h
        rfl
      rw [hfun] at hraw
      simpa only [zero_add] using hraw
    have hcenterAt' :
        HasDerivAt (d.centerMap zeta) (deriv (d.centerMap zeta) u) (u + 0) := by
      simpa only [add_zero] using hcenterAt
    have htranslated :
        HasDerivAt (fun h : ℝ ↦ d.centerMap zeta (u + h))
          (deriv (d.centerMap zeta) u) 0 := by
      have hcomp := hcenterAt'.hasFDerivAt.comp_hasDerivAt 0 htranslation
      simpa only [Function.comp_def, one_smul, add_zero, mul_one,
        ContinuousLinearMap.toSpanSingleton_apply] using hcomp
    have hTaylorBound := hTaylor u hu s hsTaylor
    rw [finiteTaylorJet_one_remainder_eq
      (fun h : ℝ ↦ d.centerMap zeta (u + h)) 0 s
      htranslated.differentiableAt, htranslated.deriv, zero_add] at hTaylorBound
    simpa only [pow_one, Real.norm_eq_abs, smul_eq_mul, add_zero] using hTaylorBound
  · have hu_abs : R + 1 < |u| := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
        not_le] using hu
    have htriangle : |u| ≤ |u + s| + |s| := by
      calc
        |u| = |(u + s) + (-s)| := by ring_nf
        _ ≤ |u + s| + |-s| := by
          simpa only [Real.norm_eq_abs] using (norm_add_le (u + s) (-s))
        _ = |u + s| + |s| := by rw [abs_neg]
    have hushift_abs : R < |u + s| := by
      nlinarith
    have hgraphOutside {v : ℝ} (hv : R < |v|) :
        (v, (zeta : ℝ → X) v) ∉ tsupport d.R := by
      intro hv_support
      have hpoint_lt : ‖(v, (zeta : ℝ → X) v)‖ < R := by
        simpa only [Metric.mem_ball, dist_zero_right] using
          hR_support hv_support
      have hv_le : |v| ≤ ‖(v, (zeta : ℝ → X) v)‖ := by
        simpa only [Real.norm_eq_abs] using
          (norm_fst_le (v, (zeta : ℝ → X) v))
      nlinarith
    have hu_outside_abs : R < |u| := by
      nlinarith
    have hu_graph : (u, (zeta : ℝ → X) u) ∉ tsupport d.R :=
      hgraphOutside hu_outside_abs
    have hushift_graph :
        (u + s, (zeta : ℝ → X) (u + s)) ∉ tsupport d.R :=
      hgraphOutside hushift_abs
    rw [metricCenterMap_eq_self_of_graph_notMem_tsupport
        d zeta hushift_graph,
      metricCenterMap_eq_self_of_graph_notMem_tsupport d zeta hu_graph,
      metricCenterMap_deriv_eq_one_of_graph_notMem_tsupport
        d zeta hfixed h_bunching_one hu_graph]
    norm_num
    exact mul_nonneg he.le (abs_nonneg s)

/-- Helper for Infrastructure I.16a: the common linear kernel of the exact difference
coefficients has a uniform pointwise operator bound. -/
theorem norm_metricOrderOneDifferenceKernel_apply_le
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d) (u : ℝ) (w : X) :
    ‖d.L w + derivFiber d zeta u w -
        (derivCenterFiber d zeta u w) • b.1 (d.centerMap zeta u)‖ ≤
      ((d.linearRate : ℝ) + (d.epsilon : ℝ) +
        (d.epsilon : ℝ) * (d.slope : ℝ)) * ‖w‖ := by
  have hlinear : ‖d.L w‖ ≤ (d.linearRate : ℝ) * ‖w‖ := by
    exact (d.L.le_opNorm w).trans
      (mul_le_mul_of_nonneg_right d.hL (norm_nonneg w))
  have hfiber : ‖derivFiber d zeta u w‖ ≤ (d.epsilon : ℝ) * ‖w‖ := by
    exact ((derivFiber d zeta u).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right
        (norm_derivFiber_le d zeta u) (norm_nonneg w))
  have hcenter :
      ‖derivCenterFiber d zeta u w‖ ≤ (d.epsilon : ℝ) * ‖w‖ := by
    exact ((derivCenterFiber d zeta u).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right
        (norm_derivCenterFiber_le d zeta u) (norm_nonneg w))
  have hepsilonNorm_nonneg : 0 ≤ (d.epsilon : ℝ) * ‖w‖ := by
    positivity
  have hfeedback :
      ‖(derivCenterFiber d zeta u w) • b.1 (d.centerMap zeta u)‖ ≤
        ((d.epsilon : ℝ) * (d.slope : ℝ)) * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |derivCenterFiber d zeta u w| *
          ‖b.1 (d.centerMap zeta u)‖ ≤
        ((d.epsilon : ℝ) * ‖w‖) * (d.slope : ℝ) := by
          exact mul_le_mul hcenter
            (b.norm_apply_le (d.centerMap zeta u))
            (norm_nonneg _) hepsilonNorm_nonneg
      _ = ((d.epsilon : ℝ) * (d.slope : ℝ)) * ‖w‖ := by ring
  calc
    ‖d.L w + derivFiber d zeta u w -
        (derivCenterFiber d zeta u w) • b.1 (d.centerMap zeta u)‖ ≤
      (‖d.L w‖ + ‖derivFiber d zeta u w‖) +
        ‖(derivCenterFiber d zeta u w) • b.1 (d.centerMap zeta u)‖ := by
          exact (norm_sub_le _ _).trans
            (add_le_add_left (norm_add_le _ _) _)
    _ ≤ ((d.linearRate : ℝ) * ‖w‖ + (d.epsilon : ℝ) * ‖w‖) +
        ((d.epsilon : ℝ) * (d.slope : ℝ)) * ‖w‖ :=
      add_le_add (add_le_add hlinear hfiber) hfeedback
    _ = ((d.linearRate : ℝ) + (d.epsilon : ℝ) +
        (d.epsilon : ℝ) * (d.slope : ℝ)) * ‖w‖ := by ring

/-- Helper for Infrastructure I.16a: changing only the candidate slope in the exact difference
coefficient is controlled by the pointwise slope change. -/
theorem norm_metricOrderOneDifferenceCoefficient_sub_apply_le
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b c : MetricSlopeSection d) (u : ℝ) (w : X) :
    ‖(metricOrderOneDifferenceCoefficient d zeta b c u -
        metricOrderOneDifferenceCoefficient d zeta b b u) w‖ ≤
      ((d.lower : ℝ)⁻¹ ^ 2 * (d.epsilon : ℝ) *
          ((d.linearRate : ℝ) + (d.epsilon : ℝ) +
            (d.epsilon : ℝ) * (d.slope : ℝ))) *
        ‖c.1 u - b.1 u‖ * ‖w‖ := by
  have hinverse :=
    abs_inv_metricOrderOneDenominator_sub_le d zeta c b u
  have hkernel :=
    norm_metricOrderOneDifferenceKernel_apply_le d zeta b u w
  have hinverseBound_nonneg :
      0 ≤ (d.lower : ℝ)⁻¹ ^ 2 * (d.epsilon : ℝ) *
        ‖c.1 u - b.1 u‖ := by
    positivity
  have hidentity :
      (metricOrderOneDifferenceCoefficient d zeta b c u -
          metricOrderOneDifferenceCoefficient d zeta b b u) w =
        ((metricOrderOneDenominator d zeta c u)⁻¹ -
            (metricOrderOneDenominator d zeta b u)⁻¹) •
          (d.L w + derivFiber d zeta u w -
            (derivCenterFiber d zeta u w) •
              b.1 (d.centerMap zeta u)) := by
    rw [sub_apply, metricOrderOneDifferenceCoefficient_apply,
      metricOrderOneDifferenceCoefficient_apply]
    simp only [sub_smul]
  rw [hidentity, norm_smul, Real.norm_eq_abs]
  calc
    |(metricOrderOneDenominator d zeta c u)⁻¹ -
          (metricOrderOneDenominator d zeta b u)⁻¹| *
        ‖d.L w + derivFiber d zeta u w -
          (derivCenterFiber d zeta u w) •
            b.1 (d.centerMap zeta u)‖ ≤
      ((d.lower : ℝ)⁻¹ ^ 2 * (d.epsilon : ℝ) *
          ‖c.1 u - b.1 u‖) *
        (((d.linearRate : ℝ) + (d.epsilon : ℝ) +
          (d.epsilon : ℝ) * (d.slope : ℝ)) * ‖w‖) := by
            exact mul_le_mul hinverse hkernel
              (norm_nonneg _) hinverseBound_nonneg
    _ = ((d.lower : ℝ)⁻¹ ^ 2 * (d.epsilon : ℝ) *
          ((d.linearRate : ℝ) + (d.epsilon : ℝ) +
            (d.epsilon : ℝ) * (d.slope : ℝ))) *
        ‖c.1 u - b.1 u‖ * ‖w‖ := by ring

/-- Helper for Infrastructure I.16a: translating the canonical fixed slope changes the exact
difference coefficient uniformly little in operator norm. -/
theorem metricOrderOneDifferenceCoefficient_translated_uniform
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1) :
    ∀ e > 0, ∃ delta > 0, ∀ u s : ℝ, |s| < delta →
      ‖metricOrderOneDifferenceCoefficient d zeta
          (metricOrderOneFixedSlope d zeta h_bunching_one)
          (metricOrderTwoTranslatedSlope d
            (metricOrderOneFixedSlope d zeta h_bunching_one) s) u -
        metricOrderOneDifferenceCoefficient d zeta
          (metricOrderOneFixedSlope d zeta h_bunching_one)
          (metricOrderOneFixedSlope d zeta h_bunching_one) u‖ ≤ e := by
  intro e he
  let b := metricOrderOneFixedSlope d zeta h_bunching_one
  let coefficientFactor : ℝ :=
    (d.lower : ℝ)⁻¹ ^ 2 * (d.epsilon : ℝ) *
      ((d.linearRate : ℝ) + (d.epsilon : ℝ) +
        (d.epsilon : ℝ) * (d.slope : ℝ))
  have hcoefficientFactor : 0 ≤ coefficientFactor := by
    dsimp only [coefficientFactor]
    positivity
  have hfactor_pos : 0 < coefficientFactor + 1 :=
    add_pos_of_nonneg_of_pos hcoefficientFactor zero_lt_one
  let tolerance := e / (coefficientFactor + 1)
  have htolerance : 0 < tolerance :=
    div_pos he hfactor_pos
  obtain ⟨delta, hdelta, hmodulus⟩ :=
    Metric.uniformContinuous_iff.mp
      (uniformContinuous_metricOrderOneFixedSlope
        d zeta hfixed h_bunching_one)
      tolerance htolerance
  refine ⟨delta, hdelta, ?_⟩
  intro u s hs
  have hinputDistance : dist (u + s) u < delta := by
    simpa only [Real.dist_eq, add_sub_cancel_left] using hs
  have hslopeClose := hmodulus hinputDistance
  have hslopeDifference :
      ‖(metricOrderTwoTranslatedSlope d b s).1 u - b.1 u‖ < tolerance := by
    simpa only [metricOrderTwoTranslatedSlope_apply, dist_eq_norm] using
      hslopeClose
  have hfactorBound :
      coefficientFactor *
          ‖(metricOrderTwoTranslatedSlope d b s).1 u - b.1 u‖ ≤ e := by
    calc
      coefficientFactor *
          ‖(metricOrderTwoTranslatedSlope d b s).1 u - b.1 u‖ ≤
        (coefficientFactor + 1) *
          ‖(metricOrderTwoTranslatedSlope d b s).1 u - b.1 u‖ := by
            exact mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)
      _ ≤ (coefficientFactor + 1) * tolerance :=
        mul_le_mul_of_nonneg_left hslopeDifference.le hfactor_pos.le
      _ = e := by
        dsimp only [tolerance]
        field_simp [ne_of_gt hfactor_pos]
  apply
    (metricOrderOneDifferenceCoefficient d zeta b
        (metricOrderTwoTranslatedSlope d b s) u -
      metricOrderOneDifferenceCoefficient d zeta b b u).opNorm_le_bound he.le
  intro w
  have hpointwise :=
    norm_metricOrderOneDifferenceCoefficient_sub_apply_le d zeta b
      (metricOrderTwoTranslatedSlope d b s) u w
  calc
    ‖(metricOrderOneDifferenceCoefficient d zeta b
          (metricOrderTwoTranslatedSlope d b s) u -
        metricOrderOneDifferenceCoefficient d zeta b b u) w‖ ≤
      coefficientFactor *
        ‖(metricOrderTwoTranslatedSlope d b s).1 u - b.1 u‖ * ‖w‖ := by
          simpa only [coefficientFactor] using hpointwise
    _ ≤ e * ‖w‖ :=
      mul_le_mul_of_nonneg_right hfactorBound (norm_nonneg w)

/-- Helper for Infrastructure I.16a: the fixed-slope increment is the exact rational principal
term plus the named source-coordinate base variation. -/
theorem metricOrderTwoFixedSlope_increment_decomposition
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (b : MetricSlopeSection d)
    (hb : metricOrderOneSlopeOperator d zeta b = b) (u s : ℝ) :
    b.1 (d.centerMap zeta (u + s)) - b.1 (d.centerMap zeta u) =
      metricOrderOneDifferenceCoefficient d zeta b
          (metricOrderTwoTranslatedSlope d b s) u (b.1 (u + s) - b.1 u) +
        metricOrderTwoBaseVariation d zeta b u s := by
  have hprincipal := metricOrderOneSlopeOperator_sub_fixed_apply_centerMap
    d zeta b (metricOrderTwoTranslatedSlope d b s) hb u
  rw [metricOrderTwoTranslatedSlope_apply] at hprincipal
  rw [metricOrderTwoBaseVariation]
  rw [← hprincipal]
  module

/-- Helper for Infrastructure I.16a: the order-two residual collects precisely the translated
base variation and the two first-order compatibility terms left after isolating the source raw
defect. -/
def metricOrderTwoResidual
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (h_bunching_two :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ 2 < 1)
    (y t : ℝ) : X :=
  let b := metricOrderOneFixedSlope d zeta h_bunching_one
  let a := metricOrderTwoFixedSection d zeta hfixed h_bunching_one h_bunching_two
  let u := d.inverseCenter zeta y
  let s := metricOrderOneSourceIncrement d zeta y t
  let translated := metricOrderTwoTranslatedSlope d b s
  metricOrderTwoBaseVariation d zeta b u s +
    s • metricOrderOneDifferenceCoefficient d zeta b translated u (a u) -
      t • a y

/-- Helper for Infrastructure I.16a: the residual is the sum of the frozen-base Taylor error,
the translated-coefficient error, and the center-map Taylor error. -/
theorem metricOrderTwoResidual_error_decomposition
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (h_bunching_two :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ 2 < 1)
    (y t : ℝ) :
    let b := metricOrderOneFixedSlope d zeta h_bunching_one
    let a := metricOrderTwoFixedSection d zeta hfixed h_bunching_one h_bunching_two
    let u := d.inverseCenter zeta y
    let s := metricOrderOneSourceIncrement d zeta y t
    let translated := metricOrderTwoTranslatedSlope d b s
    metricOrderTwoResidual d zeta hfixed h_bunching_one h_bunching_two y t =
      (metricOrderTwoBaseVariation d zeta b u s -
        s • (deriv (d.centerMap zeta) u •
          metricReservedTopForcing d zeta 2 u)) +
      s • ((metricOrderOneDifferenceCoefficient d zeta b translated u -
        metricOrderOneDifferenceCoefficient d zeta b b u) (a u)) +
      (s * deriv (d.centerMap zeta) u - t) • a y := by
  dsimp only
  let b := metricOrderOneFixedSlope d zeta h_bunching_one
  let a := metricOrderTwoFixedSection d zeta hfixed h_bunching_one h_bunching_two
  let u := d.inverseCenter zeta y
  let s := metricOrderOneSourceIncrement d zeta y t
  let translated := metricOrderTwoTranslatedSlope d b s
  have hbase : d.centerMap zeta u = y :=
    centerMap_inverseCenter d zeta y
  have hequation :=
    metricOrderTwoFixedSection_centerDerivativeEquation
      d zeta hfixed h_bunching_one h_bunching_two u
  have hequation_y :
      deriv (d.centerMap zeta) u • a y =
        metricOrderOneDifferenceCoefficient d zeta b b u (a u) +
          deriv (d.centerMap zeta) u •
            metricReservedTopForcing d zeta 2 u := by
    rw [← hbase]
    exact hequation
  have hcancel :
      s • (metricOrderOneDifferenceCoefficient d zeta b b u) (a u) +
          (s * deriv (d.centerMap zeta) u) •
            metricReservedTopForcing d zeta 2 u =
        (s * deriv (d.centerMap zeta) u) • a y := by
    calc
      s • (metricOrderOneDifferenceCoefficient d zeta b b u) (a u) +
            (s * deriv (d.centerMap zeta) u) •
              metricReservedTopForcing d zeta 2 u =
          s • ((metricOrderOneDifferenceCoefficient d zeta b b u) (a u) +
            deriv (d.centerMap zeta) u • metricReservedTopForcing d zeta 2 u) := by
              rw [smul_add, smul_smul]
      _ = s • (deriv (d.centerMap zeta) u • a y) := by rw [← hequation_y]
      _ = (s * deriv (d.centerMap zeta) u) • a y := by rw [smul_smul]
  have hresidual_local :
      metricOrderTwoBaseVariation d zeta b u s +
          s • (metricOrderOneDifferenceCoefficient d zeta b
            (metricOrderTwoTranslatedSlope d b s) u) (a u) - t • a y =
        (metricOrderTwoBaseVariation d zeta b u s -
            (s * deriv (d.centerMap zeta) u) •
              metricReservedTopForcing d zeta 2 u) +
          s • ((metricOrderOneDifferenceCoefficient d zeta b
              (metricOrderTwoTranslatedSlope d b s) u -
            metricOrderOneDifferenceCoefficient d zeta b b u) (a u)) +
          ((s * deriv (d.centerMap zeta) u) • a y - t • a y) := by
    calc
      metricOrderTwoBaseVariation d zeta b u s +
            s • (metricOrderOneDifferenceCoefficient d zeta b
              (metricOrderTwoTranslatedSlope d b s) u) (a u) - t • a y =
          metricOrderTwoBaseVariation d zeta b u s +
            s • (metricOrderOneDifferenceCoefficient d zeta b
              (metricOrderTwoTranslatedSlope d b s) u) (a u) -
              (s • (metricOrderOneDifferenceCoefficient d zeta b b u) (a u) +
                (s * deriv (d.centerMap zeta) u) •
                  metricReservedTopForcing d zeta 2 u) +
              ((s * deriv (d.centerMap zeta) u) • a y - t • a y) := by
                rw [hcancel]
                abel
      _ = (metricOrderTwoBaseVariation d zeta b u s -
            (s * deriv (d.centerMap zeta) u) •
              metricReservedTopForcing d zeta 2 u) +
          s • ((metricOrderOneDifferenceCoefficient d zeta b
              (metricOrderTwoTranslatedSlope d b s) u -
            metricOrderOneDifferenceCoefficient d zeta b b u) (a u)) +
          ((s * deriv (d.centerMap zeta) u) • a y - t • a y) := by
            rw [ContinuousLinearMap.sub_apply, smul_sub]
            abel
  rw [metricOrderTwoResidual]
  simpa only [b, a, u, s, translated, sub_smul, smul_smul] using hresidual_local

/-- Helper for Infrastructure I.16a: the complete order-two residual is uniformly little
compared with the output-center increment. -/
theorem metricOrderTwoResidual_uniform
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (h_bunching_two :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ 2 < 1) :
    ∀ e > 0, ∃ delta > 0, ∀ y t : ℝ, ‖t‖ < delta →
      ‖metricOrderTwoResidual d zeta hfixed
        h_bunching_one h_bunching_two y t‖ ≤ e * ‖t‖ := by
  intro e he
  let b := metricOrderOneFixedSlope d zeta h_bunching_one
  let a := metricOrderTwoFixedSection d zeta hfixed h_bunching_one h_bunching_two
  let transportFactor : ℝ := (d.lower : ℝ)⁻¹
  have hlower_pos : 0 < (d.lower : ℝ) := by
    exact_mod_cast d.hlower_pos
  have htransportFactor : 0 < transportFactor := by
    exact inv_pos.mpr hlower_pos
  have haFactor : 0 < ‖a‖ + 1 :=
    add_pos_of_nonneg_of_pos (norm_nonneg a) zero_lt_one
  let baseTolerance : ℝ := e / (3 * transportFactor)
  let sectionTolerance : ℝ :=
    e / (3 * transportFactor * (‖a‖ + 1))
  have hbaseTolerance : 0 < baseTolerance := by
    dsimp only [baseTolerance]
    positivity
  have hsectionTolerance : 0 < sectionTolerance := by
    dsimp only [sectionTolerance]
    positivity
  obtain ⟨deltaBase, hdeltaBase, hBase⟩ :=
    metricOrderTwoBaseVariation_uniform
      d zeta hfixed h_bunching_one baseTolerance hbaseTolerance
  obtain ⟨deltaCoefficient, hdeltaCoefficient, hCoefficient⟩ :=
    metricOrderOneDifferenceCoefficient_translated_uniform
      d zeta hfixed h_bunching_one sectionTolerance hsectionTolerance
  obtain ⟨deltaCenter, hdeltaCenter, hCenter⟩ :=
    metricCenterMapRemainder_uniform
      d zeta hfixed h_bunching_one sectionTolerance hsectionTolerance
  let sourceDelta := min deltaBase (min deltaCoefficient deltaCenter)
  have hsourceDelta : 0 < sourceDelta :=
    lt_min hdeltaBase (lt_min hdeltaCoefficient hdeltaCenter)
  let delta := sourceDelta / transportFactor
  have hdelta : 0 < delta :=
    div_pos hsourceDelta htransportFactor
  refine ⟨delta, hdelta, ?_⟩
  intro y t ht
  let u := d.inverseCenter zeta y
  let s := metricOrderOneSourceIncrement d zeta y t
  let translated := metricOrderTwoTranslatedSlope d b s
  have hsource_le : |s| ≤ transportFactor * |t| := by
    simpa only [s, transportFactor] using
      abs_metricOrderOneSourceIncrement_le d zeta y t
  have ht_abs : |t| < delta := by
    simpa only [Real.norm_eq_abs] using ht
  have hsource_small : |s| < sourceDelta := by
    calc
      |s| ≤ transportFactor * |t| := hsource_le
      _ < transportFactor * delta :=
        mul_lt_mul_of_pos_left ht_abs htransportFactor
      _ = sourceDelta := by
        dsimp only [delta]
        field_simp [ne_of_gt htransportFactor]
  have hsBase : |s| < deltaBase :=
    hsource_small.trans_le
      (min_le_left deltaBase (min deltaCoefficient deltaCenter))
  have hsCoefficient : |s| < deltaCoefficient :=
    hsource_small.trans_le
      ((min_le_right deltaBase (min deltaCoefficient deltaCenter)).trans
        (min_le_left deltaCoefficient deltaCenter))
  have hsCenter : |s| < deltaCenter :=
    hsource_small.trans_le
      ((min_le_right deltaBase (min deltaCoefficient deltaCenter)).trans
        (min_le_right deltaCoefficient deltaCenter))
  have hbaseError :=
    hBase u s hsBase
  have hcoefficientNorm :=
    hCoefficient u s hsCoefficient
  have hcenterRaw :=
    hCenter u s hsCenter
  have hbaseMap : d.centerMap zeta u = y :=
    centerMap_inverseCenter d zeta y
  have hnextMap : d.centerMap zeta (u + s) = y + t := by
    exact centerMap_add_metricOrderOneSourceIncrement d zeta y t
  have hcenterError :
      |s * deriv (d.centerMap zeta) u - t| ≤
        sectionTolerance * |s| := by
    rw [hnextMap, hbaseMap] at hcenterRaw
    simpa only [add_sub_cancel_left, abs_sub_comm] using hcenterRaw
  have hcoefficientApply :
      ‖(metricOrderOneDifferenceCoefficient d zeta b translated u -
          metricOrderOneDifferenceCoefficient d zeta b b u) (a u)‖ ≤
        sectionTolerance * ‖a‖ := by
    calc
      ‖(metricOrderOneDifferenceCoefficient d zeta b translated u -
          metricOrderOneDifferenceCoefficient d zeta b b u) (a u)‖ ≤
        ‖metricOrderOneDifferenceCoefficient d zeta b translated u -
          metricOrderOneDifferenceCoefficient d zeta b b u‖ * ‖a u‖ :=
            (metricOrderOneDifferenceCoefficient d zeta b translated u -
              metricOrderOneDifferenceCoefficient d zeta b b u).le_opNorm _
      _ ≤ sectionTolerance * ‖a‖ := by
        exact mul_le_mul hcoefficientNorm
          (BoundedContinuousFunction.norm_coe_le_norm a u)
          (norm_nonneg _) hsectionTolerance.le
  have hbaseFactor :
      transportFactor * baseTolerance = e / 3 := by
    dsimp only [baseTolerance]
    field_simp [ne_of_gt htransportFactor]
  have hsectionFactor :
      transportFactor * sectionTolerance * ‖a‖ ≤ e / 3 := by
    calc
      transportFactor * sectionTolerance * ‖a‖ ≤
          transportFactor * sectionTolerance * (‖a‖ + 1) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right zero_le_one)
          (mul_nonneg htransportFactor.le hsectionTolerance.le)
      _ = e / 3 := by
        dsimp only [sectionTolerance]
        field_simp [ne_of_gt htransportFactor, ne_of_gt haFactor]
  have hbaseSmall :
      ‖metricOrderTwoBaseVariation d zeta b u s -
          s • (deriv (d.centerMap zeta) u •
            metricReservedTopForcing d zeta 2 u)‖ ≤
        (e / 3) * |t| := by
    calc
      ‖metricOrderTwoBaseVariation d zeta b u s -
          s • (deriv (d.centerMap zeta) u •
            metricReservedTopForcing d zeta 2 u)‖ ≤
        baseTolerance * |s| := hbaseError
      _ ≤ baseTolerance * (transportFactor * |t|) :=
        mul_le_mul_of_nonneg_left hsource_le hbaseTolerance.le
      _ = (transportFactor * baseTolerance) * |t| := by ring
      _ = (e / 3) * |t| := by rw [hbaseFactor]
  have hcoefficientSmall :
      ‖s • ((metricOrderOneDifferenceCoefficient d zeta b translated u -
        metricOrderOneDifferenceCoefficient d zeta b b u) (a u))‖ ≤
        (e / 3) * |t| := by
    calc
      ‖s • ((metricOrderOneDifferenceCoefficient d zeta b translated u -
          metricOrderOneDifferenceCoefficient d zeta b b u) (a u))‖ =
        |s| *
          ‖(metricOrderOneDifferenceCoefficient d zeta b translated u -
            metricOrderOneDifferenceCoefficient d zeta b b u) (a u)‖ := by
              rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |s| * (sectionTolerance * ‖a‖) :=
        mul_le_mul_of_nonneg_left hcoefficientApply (abs_nonneg s)
      _ ≤ (transportFactor * |t|) * (sectionTolerance * ‖a‖) :=
        mul_le_mul_of_nonneg_right hsource_le
          (mul_nonneg hsectionTolerance.le (norm_nonneg a))
      _ = (transportFactor * sectionTolerance * ‖a‖) * |t| := by ring
      _ ≤ (e / 3) * |t| :=
        mul_le_mul_of_nonneg_right hsectionFactor (abs_nonneg t)
  have hcenterSmall :
      ‖(s * deriv (d.centerMap zeta) u - t) • a y‖ ≤
        (e / 3) * |t| := by
    calc
      ‖(s * deriv (d.centerMap zeta) u - t) • a y‖ =
        |s * deriv (d.centerMap zeta) u - t| * ‖a y‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ (sectionTolerance * |s|) * ‖a‖ := by
        exact mul_le_mul hcenterError
          (BoundedContinuousFunction.norm_coe_le_norm a y)
          (norm_nonneg _) (mul_nonneg hsectionTolerance.le (abs_nonneg s))
      _ ≤ (sectionTolerance * (transportFactor * |t|)) * ‖a‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsource_le hsectionTolerance.le)
          (norm_nonneg a)
      _ = (transportFactor * sectionTolerance * ‖a‖) * |t| := by ring
      _ ≤ (e / 3) * |t| :=
        mul_le_mul_of_nonneg_right hsectionFactor (abs_nonneg t)
  have hdecomposition :
      metricOrderTwoResidual d zeta hfixed h_bunching_one h_bunching_two y t =
        (metricOrderTwoBaseVariation d zeta b u s -
          s • (deriv (d.centerMap zeta) u •
            metricReservedTopForcing d zeta 2 u)) +
        s • ((metricOrderOneDifferenceCoefficient d zeta b translated u -
          metricOrderOneDifferenceCoefficient d zeta b b u) (a u)) +
        (s * deriv (d.centerMap zeta) u - t) • a y := by
    simpa only [b, a, u, s, translated] using
      metricOrderTwoResidual_error_decomposition
        d zeta hfixed h_bunching_one h_bunching_two y t
  rw [hdecomposition]
  calc
    ‖(metricOrderTwoBaseVariation d zeta b u s -
          s • (deriv (d.centerMap zeta) u •
            metricReservedTopForcing d zeta 2 u)) +
        s • ((metricOrderOneDifferenceCoefficient d zeta b translated u -
          metricOrderOneDifferenceCoefficient d zeta b b u) (a u)) +
        (s * deriv (d.centerMap zeta) u - t) • a y‖ ≤
      (‖metricOrderTwoBaseVariation d zeta b u s -
          s • (deriv (d.centerMap zeta) u •
            metricReservedTopForcing d zeta 2 u)‖ +
        ‖s • ((metricOrderOneDifferenceCoefficient d zeta b translated u -
          metricOrderOneDifferenceCoefficient d zeta b b u) (a u))‖) +
        ‖(s * deriv (d.centerMap zeta) u - t) • a y‖ := by
            exact (norm_add_le _ _).trans
              (add_le_add_left (norm_add_le _ _) _)
    _ ≤ ((e / 3) * |t| + (e / 3) * |t|) + (e / 3) * |t| :=
      add_le_add (add_le_add hbaseSmall hcoefficientSmall) hcenterSmall
    _ = e * |t| := by ring
    _ = e * ‖t‖ := by rw [Real.norm_eq_abs]

/-- Helper for Infrastructure I.16a: the output raw defect is the rational coefficient applied
to the inverse-center raw defect, plus the named base-variation residual. -/
theorem metricOrderTwoRawDefect_decomposition
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (h_bunching_two :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ 2 < 1)
    (y t : ℝ) :
    let b := metricOrderOneFixedSlope d zeta h_bunching_one
    let u := d.inverseCenter zeta y
    let s := metricOrderOneSourceIncrement d zeta y t
    let translated := metricOrderTwoTranslatedSlope d b s
    metricOrderTwoRawDefect d zeta hfixed h_bunching_one h_bunching_two y t =
      metricOrderOneDifferenceCoefficient d zeta b translated u
          (metricOrderTwoRawDefect d zeta hfixed h_bunching_one h_bunching_two u s) +
        metricOrderTwoResidual d zeta hfixed h_bunching_one h_bunching_two y t := by
  dsimp only
  let b := metricOrderOneFixedSlope d zeta h_bunching_one
  let a := metricOrderTwoFixedSection d zeta hfixed h_bunching_one h_bunching_two
  let u := d.inverseCenter zeta y
  let s := metricOrderOneSourceIncrement d zeta y t
  let translated := metricOrderTwoTranslatedSlope d b s
  have hbase : d.centerMap zeta u = y := centerMap_inverseCenter d zeta y
  have hnext : d.centerMap zeta (u + s) = y + t := by
    exact centerMap_add_metricOrderOneSourceIncrement d zeta y t
  have hbFixed : metricOrderOneSlopeOperator d zeta b = b :=
    metricOrderOneFixedSlope_fixed d zeta h_bunching_one
  have hincrement := metricOrderTwoFixedSlope_increment_decomposition
    d zeta b hbFixed u s
  rw [hbase, hnext] at hincrement
  rw [metricOrderTwoRawDefect, metricOrderTwoRawDefect,
    metricOrderTwoResidual, hincrement]
  simp only [b, a, u, s, translated]
  simp only [map_sub, map_smul]
  module

/-- Helper for Infrastructure I.16a: the exact rational coefficient gives the principal raw
defect the order-one contraction factor `metricGraphTransformRate * lower⁻¹`. -/
theorem norm_metricOrderTwoRawDefect_le_principal_add_residual
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (h_bunching_two :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ 2 < 1)
    (y t : ℝ) :
    let u := d.inverseCenter zeta y
    let s := metricOrderOneSourceIncrement d zeta y t
    ‖metricOrderTwoRawDefect d zeta hfixed h_bunching_one h_bunching_two y t‖ ≤
      ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
          (d.lower : ℝ)⁻¹) *
        ‖metricOrderTwoRawDefect d zeta hfixed h_bunching_one h_bunching_two u s‖ +
      ‖metricOrderTwoResidual d zeta hfixed h_bunching_one h_bunching_two y t‖ := by
  dsimp only
  let b := metricOrderOneFixedSlope d zeta h_bunching_one
  let u := d.inverseCenter zeta y
  let s := metricOrderOneSourceIncrement d zeta y t
  let translated := metricOrderTwoTranslatedSlope d b s
  have hdecomposition := metricOrderTwoRawDefect_decomposition
    d zeta hfixed h_bunching_one h_bunching_two y t
  have hcoefficient := metricOrderOneDifferenceCoefficient_apply_norm_le
    d zeta b translated (metricOrderOneFixedSlope_fixed d zeta h_bunching_one) u
      (metricOrderTwoRawDefect d zeta hfixed h_bunching_one h_bunching_two u s)
  rw [hdecomposition]
  exact (norm_add_le _ _).trans (add_le_add_left hcoefficient _)

/-- Helper for Infrastructure I.16a: uniform smallness of the order-two residual turns the
raw identity into the inverse-center affine recurrence used by the radius envelope. -/
theorem metricOrderTwoRawDefect_inverseRecurrence
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (h_bunching_two :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ 2 < 1) :
    ∀ e > 0, ∃ delta > 0, ∀ y t : ℝ, t ≠ 0 → ‖t‖ < delta →
      ‖metricOrderTwoRawDefect d zeta hfixed
          h_bunching_one h_bunching_two y t‖ ≤
        ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
          (d.lower : ℝ)⁻¹) *
          ‖metricOrderTwoRawDefect d zeta hfixed
            h_bunching_one h_bunching_two
            (d.inverseCenter zeta y)
            (d.inverseCenter zeta (y + t) - d.inverseCenter zeta y)‖ +
        e * ‖t‖ := by
  intro e he
  obtain ⟨delta, hdelta, hresidual⟩ :=
    metricOrderTwoResidual_uniform
      d zeta hfixed h_bunching_one h_bunching_two e he
  refine ⟨delta, hdelta, ?_⟩
  intro y t ht_ne ht
  have hprincipal :=
    norm_metricOrderTwoRawDefect_le_principal_add_residual
      d zeta hfixed h_bunching_one h_bunching_two y t
  have hresidualBound := hresidual y t ht
  have hcombined :=
    hprincipal.trans (add_le_add_right hresidualBound _)
  have hsource :
      d.inverseCenter zeta (y + t) - d.inverseCenter zeta y =
        metricOrderOneSourceIncrement d zeta y t := by
    have hadd := inverseCenter_add_metricOrderOneSourceIncrement d zeta y t
    linarith
  rw [← hsource] at hcombined
  exact hcombined

/-- Helper for Infrastructure I.16a: the raw defect of the canonical fixed slope relative to
the reserved order-two section is little-o of its increment at every base point. -/
theorem metricOrderTwoRawDefect_isLittleO
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (h_bunching_two :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ 2 < 1) :
    ∀ y : ℝ,
      (fun t : ℝ ↦ metricOrderTwoRawDefect d zeta hfixed
        h_bunching_one h_bunching_two y t) =o[𝓝 0]
        (fun t : ℝ ↦ t) := by
  have hlower_pos : 0 < (d.lower : ℝ) := by
    exact_mod_cast d.hlower_pos
  have hproduct :
      ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
          (d.lower : ℝ)⁻¹) * (d.lower : ℝ)⁻¹ =
        (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
          (d.lower : ℝ)⁻¹ ^ 2 := by
    ring
  apply LocalCutoff.GraphTransform.rawDefect_isLittleO_of_inverseRecurrence
    (metricOrderTwoRawDefect d zeta hfixed h_bunching_one h_bunching_two)
    (d.inverseCenter zeta)
    ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
      (d.lower : ℝ)⁻¹)
    (d.lower : ℝ)⁻¹
  · exact metricOrderTwoRawDefect_zero
      d zeta hfixed h_bunching_one h_bunching_two
  · exact metricOrderTwoRawDefect_locallyUniformlyBounded
      d zeta hfixed h_bunching_one h_bunching_two
  · exact norm_metricOrderOneInverseCenterIncrement_le d zeta
  · positivity
  · exact h_bunching_one
  · exact inv_pos.mpr hlower_pos
  · rw [hproduct]
    exact h_bunching_two
  · exact metricOrderTwoRawDefect_inverseRecurrence
      d zeta hfixed h_bunching_one h_bunching_two

/-- Helper for Infrastructure I.16a: the canonical reserved order-two section is the derivative
of the canonical fixed slope at every source center. -/
theorem metricOrderOneFixedSlope_hasDerivAt_orderTwo
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (h_bunching_two :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ 2 < 1) :
    ∀ y : ℝ,
      HasDerivAt
        (metricOrderOneFixedSlope d zeta h_bunching_one).1
        (metricOrderTwoFixedSection d zeta hfixed
          h_bunching_one h_bunching_two y) y := by
  apply LocalCutoff.GraphTransform.predecessorHasDerivAt_of_rawDefectLittleO
    (metricOrderOneFixedSlope d zeta h_bunching_one).1
    (metricOrderTwoFixedSection d zeta hfixed h_bunching_one h_bunching_two)
  intro y
  simpa only [metricOrderTwoRawDefect] using
    metricOrderTwoRawDefect_isLittleO
      d zeta hfixed h_bunching_one h_bunching_two y

/-- Infrastructure I.16a: under the order-one and order-two bunching inequalities, the first
derivative of the metric fixed graph has the continuous canonical reserved order-two derivative
section. -/
theorem metricFixedGraph_orderTwoDerivativeSection
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (_hprev : ContDiff ℝ 1 (zeta : ℝ → X))
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (h_bunching_two :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ 2 < 1) :
    ∃ v : ℝ → X, Continuous v ∧
      ∀ u, HasDerivAt (iteratedDeriv 1 (zeta : ℝ → X)) (v u) u := by
  let v :=
    metricOrderTwoFixedSection d zeta hfixed h_bunching_one h_bunching_two
  refine ⟨v, v.continuous, ?_⟩
  have hderiv :
      deriv (zeta : ℝ → X) =
        (metricOrderOneFixedSlope d zeta h_bunching_one).1 :=
    metricFixedGraph_deriv_eq_orderOneSlope
      d zeta hfixed h_bunching_one
  intro u
  rw [iteratedDeriv_one, hderiv]
  exact metricOrderOneFixedSlope_hasDerivAt_orderTwo
    d zeta hfixed h_bunching_one h_bunching_two u

/-- Helper for Infrastructure I.16a: the order-two derivative section upgrades the metric fixed
graph from `C¹` to `C²`. -/
theorem metricFixedGraph_contDiff_two_of_orderTwoBunching
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta)
    (hprev : ContDiff ℝ 1 (zeta : ℝ → X))
    (h_bunching_one :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ < 1)
    (h_bunching_two :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ 2 < 1) :
    ContDiff ℝ 2 (zeta : ℝ → X) := by
  obtain ⟨v, hv_continuous, hv⟩ :=
    metricFixedGraph_orderTwoDerivativeSection
      d zeta hfixed hprev h_bunching_one h_bunching_two
  have hiterated : ContDiff ℝ 1 (iteratedDeriv 1 (zeta : ℝ → X)) := by
    rw [contDiff_one_iff_deriv]
    constructor
    · intro u
      exact (hv u).differentiableAt
    · have hderiv :
          deriv (iteratedDeriv 1 (zeta : ℝ → X)) = v := by
        funext u
        exact (hv u).deriv
      rw [hderiv]
      exact hv_continuous
  exact
    contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mpr
      ⟨hprev, hiterated⟩

end LocalInvariantGraph
