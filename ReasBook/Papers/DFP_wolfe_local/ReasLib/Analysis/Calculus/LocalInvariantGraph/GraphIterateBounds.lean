/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricFiberLengthOneExtraction
public import ReasLib.Analysis.Calculus.ContDiff.SupportBounds
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.OrderedPartitionBounds
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ArzelaAscoliRegularity
public import Mathlib.Analysis.Calculus.ContDiff.Operations

public section

noncomputable section

open Filter Set
open scoped Topology NNReal BigOperators

universe u

namespace LocalInvariantGraph.GraphIterateBounds

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Helper for cm-center-proposition: the exact zero-start iterates of the
canonical truncated graph transform, before any regularity of its fixed point. -/
def graphIterate (d : MetricGraphTransformData X) (n : ℕ) :
    SmallLipschitzGraph X d.radius d.slope :=
  d.transform^[n] (SmallLipschitzGraph.zero X d.radius d.slope)

/-- Helper for cm-center-proposition: the source iteration starts at the zero graph. -/
theorem graphIterate_zero (d : MetricGraphTransformData X) :
    graphIterate d 0 = SmallLipschitzGraph.zero X d.radius d.slope := by
  rfl

/-- Helper for cm-center-proposition: the complete function underlying the
initial graph iterate is the zero function. -/
theorem graphIterate_zero_coe (d : MetricGraphTransformData X) :
    (graphIterate d 0 : ℝ → X) = 0 := by
  funext u
  rw [graphIterate_zero]
  exact congrFun (congrArg DFunLike.coe (SmallLipschitzGraph.coe_zero d.radius d.slope)) u

/-- Helper for cm-center-proposition: every source successor is the same transform
applied to the preceding graph. -/
theorem graphIterate_succ (d : MetricGraphTransformData X) (n : ℕ) :
    graphIterate d (n + 1) = d.transform (graphIterate d n) := by
  exact Function.iterate_succ_apply' _ _ _

/-- Helper for cm-center-proposition: the selected scalar inverse cancels the
center coordinate of every graph in the original Lipschitz cone. -/
theorem inverseCenter_centerMap (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) (u : ℝ) :
    d.inverseCenter ξ (d.centerMap ξ u) = u := by
  rw [d.inverseCenter_eq]
  exact Function.leftInverse_invFun (d.centerMap_bijective ξ).1 u

/-- Helper for cm-center-proposition: the center coordinate cancels its selected
scalar inverse everywhere. -/
theorem centerMap_inverseCenter (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) (v : ℝ) :
    d.centerMap ξ (d.inverseCenter ξ v) = v := by
  rw [d.inverseCenter_eq]
  exact Function.rightInverse_invFun (d.centerMap_bijective ξ).2 v

/-- Helper for cm-center-proposition: the center projection of any graph in the
cone is continuous, without a graph smoothness assumption. -/
theorem centerMap_continuous (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) : Continuous (d.centerMap ξ) := by
  rw [d.centerMap_eq]
  exact continuous_id.add
    (continuous_fst.comp (d.hR_lipschitz.continuous.comp
      (continuous_id.prodMk (SmallLipschitzGraph.lipschitzWith ξ).continuous)))

/-- Helper for cm-center-proposition: only the scalar center projection is
inverted in the graph transform. This is its canonical global homeomorphism. -/
def centerHomeomorph (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) : ℝ ≃ₜ ℝ where
  toFun := d.centerMap ξ
  invFun := d.inverseCenter ξ
  left_inv := inverseCenter_centerMap d ξ
  right_inv := centerMap_inverseCenter d ξ
  continuous_toFun := centerMap_continuous d ξ
  continuous_invFun := (d.inverseCenter_lipschitzWith ξ).continuous

/-- Helper for cm-center-proposition: the center homeomorphism is exactly the
original center coordinate. -/
theorem centerHomeomorph_coe (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) :
    (centerHomeomorph d ξ : ℝ → ℝ) = d.centerMap ξ := by
  rfl

/-- Helper for cm-center-proposition: its inverse is exactly the selected inverse
used by the original metric transform. -/
theorem centerHomeomorph_symm_coe (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) :
    ((centerHomeomorph d ξ).symm : ℝ → ℝ) = d.inverseCenter ξ := by
  rfl

/-- Helper for cm-center-proposition: a finite-smooth graph has a scalar inverse
center coordinate of the same smoothness. No inverse of the full map is used. -/
theorem inverseCenter_contDiff (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) {k : ℕ}
    (hk : 1 ≤ k) (hkν : k ≤ d.nu) (hξ : ContDiff ℝ k (ξ : ℝ → X)) :
    ContDiff ℝ k (d.inverseCenter ξ) := by
  have hkTop : (k : WithTop ℕ∞) ≤ d.nu := by exact_mod_cast hkν
  have hone : (1 : WithTop ℕ∞) ≤ k := by exact_mod_cast hk
  have hξone : ContDiff ℝ 1 (ξ : ℝ → X) := hξ.of_le hone
  have hcenter := centerMap_contDiff_of_prev d ξ hkTop hξ
  have hne : ∀ u, deriv (d.centerMap ξ) u ≠ 0 :=
    centerMap_deriv_ne_zero d ξ hξone
  have hderiv : ∀ u, HasDerivAt (d.centerMap ξ) (deriv (d.centerMap ξ) u) u := by
    intro u
    exact ((hcenter.of_le hone).differentiable_one u).hasDerivAt
  have hsmooth := (centerHomeomorph d ξ).contDiff_symm_deriv hne hderiv hcenter
  simpa only [centerHomeomorph_symm_coe] using hsmooth

/-- Helper for cm-center-proposition: the original transform preserves every
positive finite smoothness order available for the truncated remainder. -/
theorem transform_contDiff (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) {k : ℕ}
    (hk : 1 ≤ k) (hkν : k ≤ d.nu) (hξ : ContDiff ℝ k (ξ : ℝ → X)) :
    ContDiff ℝ k (d.transform ξ : ℝ → X) := by
  have hfun : (d.transform ξ : ℝ → X) =
      (fun u ↦ d.L (ξ u) + (d.R (u, ξ u)).2) ∘ d.inverseCenter ξ := by
    funext v
    rw [d.transform_apply, d.rawTransform_eq]
    rfl
  have hkTop : (k : WithTop ℕ∞) ≤ d.nu := by exact_mod_cast hkν
  have hright : ContDiff ℝ k (fun u ↦ d.L (ξ u) + (d.R (u, ξ u)).2) :=
    (d.L.contDiff.comp hξ).add
      (contDiff_snd.comp ((d.hR_smooth.of_le hkTop).comp (contDiff_id.prodMk hξ)))
  rw [hfun]
  exact hright.comp (inverseCenter_contDiff d ξ hk hkν hξ)

/-- Helper for cm-center-proposition: every exact zero-start graph-transform
iterate has all finite derivatives available for the truncated map. -/
theorem graphIterate_contDiff (d : MetricGraphTransformData X) (n : ℕ) :
    ContDiff ℝ d.nu (graphIterate d n : ℝ → X) := by
  induction n with
  | zero =>
      have hzero : (graphIterate d 0 : ℝ → X) = fun _ ↦ 0 := by
        funext u
        rw [graphIterate_zero]
        exact congrFun (congrArg DFunLike.coe (SmallLipschitzGraph.coe_zero d.radius d.slope)) u
      rw [hzero]
      exact contDiff_const
  | succ n ih =>
      rw [graphIterate_succ]
      exact transform_contDiff d _ (one_le_two.trans d.hnu) le_rfl ih

/-- Helper for cm-center-proposition: the defining graph-transform equation holds
for arbitrary input graphs, rather than only at a fixed point. -/
theorem transform_equation (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) (u : ℝ) :
    d.transform ξ (d.centerMap ξ u) = d.L (ξ u) + (d.R (u, ξ u)).2 := by
  simp only [d.transform_apply, d.rawTransform_eq, inverseCenter_centerMap]

/-- Helper for cm-center-proposition: the source equation relating consecutive
iterates uses the preceding graph's scalar center projection. -/
theorem graphIterate_equation (d : MetricGraphTransformData X) (n : ℕ) (u : ℝ) :
    graphIterate d (n + 1) (d.centerMap (graphIterate d n) u) =
      d.L (graphIterate d n u) + (d.R (u, graphIterate d n u)).2 := by
  rw [graphIterate_succ]
  exact transform_equation d _ u

/-- Helper for cm-center-proposition: the cone supplies a common zeroth-order
bound for all exact graph-transform iterates. -/
theorem norm_graphIterate_le (d : MetricGraphTransformData X) (n : ℕ) (u : ℝ) :
    ‖graphIterate d n u‖ ≤ (d.radius : ℝ) := by
  exact (BoundedContinuousFunction.norm_coe_le_norm
    (graphIterate d n : BoundedContinuousFunction ℝ X) u).trans
      (SmallLipschitzGraph.norm_le _)

/-- Helper for cm-center-proposition: the source Lipschitz cone gives the first
derivative bound uniformly in both the iteration index and center coordinate. -/
theorem norm_deriv_graphIterate_le (d : MetricGraphTransformData X) (n : ℕ) (u : ℝ) :
    ‖deriv (graphIterate d n : ℝ → X) u‖ ≤ (d.slope : ℝ) := by
  exact norm_deriv_le_of_lipschitz (SmallLipschitzGraph.lipschitzWith _)

/-- Helper for cm-center-proposition: compact support of the truncated remainder
gives a single exterior interval where it vanishes for every stable coordinate. -/
theorem remainder_zero_outside_interval (d : MetricGraphTransformData X) :
    ∃ a > 0, ∀ u : ℝ, a ≤ |u| → ∀ z : X, d.R (u, z) = 0 := by
  obtain ⟨a, ha, hball⟩ := d.hR_support.isBounded.subset_ball_lt 0 (0 : ℝ × X)
  refine ⟨a, ha, ?_⟩
  intro u hu z
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hnorm : ‖(u, z)‖ < a := by
    simpa only [Metric.mem_ball, dist_zero_right] using hball hmem
  have hfirst : |u| ≤ ‖(u, z)‖ := by
    simpa only [Real.norm_eq_abs] using norm_fst_le (u, z)
  exact (not_lt_of_ge hu) (hfirst.trans_lt hnorm)

/-- Helper for cm-center-proposition: outside a common truncation interval,
the transform is just the stable linear map applied to the original graph. -/
theorem transform_eq_linear_outside (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) (u : ℝ)
    (hzero : d.R (u, ξ u) = 0) : d.transform ξ u = d.L (ξ u) := by
  have hcenter : d.centerMap ξ u = u := by
    simp only [d.centerMap_eq, hzero, Prod.fst_zero, add_zero]
  have h := transform_equation d ξ u
  simpa only [hcenter, hzero, Prod.snd_zero, add_zero] using h

/-- Helper for cm-center-proposition: every exact zero-start graph iterate
vanishes outside one interval fixed before the iteration index. -/
theorem graphIterate_commonExterior (d : MetricGraphTransformData X) :
    ∃ a > 0, ∀ n : ℕ, ∀ u : ℝ, a ≤ |u| → graphIterate d n u = 0 := by
  obtain ⟨a, ha, hzero⟩ := remainder_zero_outside_interval d
  refine ⟨a, ha, ?_⟩
  intro n
  induction n with
  | zero =>
      intro u _
      rw [graphIterate_zero]
      exact congrFun (congrArg DFunLike.coe (SmallLipschitzGraph.coe_zero d.radius d.slope)) u
  | succ n ih =>
      intro u hu
      rw [graphIterate_succ, transform_eq_linear_outside d _ u (hzero u hu _), ih u hu,
        map_zero]

/-- Helper for cm-center-proposition: the smooth graph-transform iterates
all have a common compact support set in the scalar center coordinate. -/
theorem graphIterate_commonCompactSupport (d : MetricGraphTransformData X) :
    ∃ s : Set ℝ, IsCompact s ∧
      ∀ n : ℕ, ∀ u : ℝ, u ∉ s → graphIterate d n u = 0 := by
  obtain ⟨a, _, hzero⟩ := graphIterate_commonExterior d
  refine ⟨Metric.closedBall 0 a, isCompact_closedBall 0 a, ?_⟩
  intro n u hu
  have habs : a < |u| := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] using hu
  exact hzero n u habs.le

/-- Helper for cm-center-proposition: each exact iterate is compactly supported,
as a consequence of the common source truncation interval. -/
theorem graphIterate_hasCompactSupport (d : MetricGraphTransformData X) (n : ℕ) :
    HasCompactSupport (graphIterate d n : ℝ → X) := by
  obtain ⟨s, hs, hzero⟩ := graphIterate_commonCompactSupport d
  exact HasCompactSupport.intro hs (hzero n)

/-- Helper for cm-center-proposition: every individual derivative of an iterate
has a global bound. Uniformity in the iteration index is a separate obligation. -/
theorem graphIterate_derivativeBound (d : MetricGraphTransformData X)
    (n r : ℕ) (hr : r ≤ d.nu) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u, ‖iteratedDeriv r (graphIterate d n : ℝ → X) u‖ ≤ B := by
  have hrTop : (r : WithTop ℕ∞) ≤ d.nu := by exact_mod_cast hr
  obtain ⟨B, hB, hbound⟩ := (graphIterate_hasCompactSupport d n).exists_norm_iteratedFDeriv_le
    ((graphIterate_contDiff d n).of_le hrTop)
  refine ⟨B, hB, ?_⟩
  intro u
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hbound u

/-- Helper for cm-center-proposition: the C⁰ limit of the exact source iterates
is the canonical fixed graph of the same metric transform. -/
def graphLimit [CompleteSpace X] (d : MetricGraphTransformData X) :
    SmallLipschitzGraph X d.radius d.slope :=
  ContractingWith.fixedPoint d.transform d.transform_contracting

/-- Helper for cm-center-proposition: the metric limit satisfies the original
graph-transform equation without any finite-smooth fixed-point theorem. -/
theorem graphLimit_fixed [CompleteSpace X] (d : MetricGraphTransformData X) :
    d.transform (graphLimit d) = graphLimit d := by
  exact d.transform_contracting.fixedPoint_isFixedPt

/-- Helper for cm-center-proposition: the zero-start exact iterates converge
to that fixed graph in the original uniform graph metric. -/
theorem graphIterate_tendsto [CompleteSpace X] (d : MetricGraphTransformData X) :
    Tendsto (graphIterate d) atTop (𝓝 (graphLimit d)) := by
  exact d.transform_contracting.tendsto_iterate_fixedPoint _

/-- Helper for cm-center-proposition: metric convergence of the actual graph
iterates is uniform convergence of their functions on the whole center axis. -/
theorem graphIterate_tendstoUniformly [CompleteSpace X] (d : MetricGraphTransformData X) :
    TendstoUniformly (fun n ↦ (graphIterate d n : ℝ → X)) (graphLimit d : ℝ → X) atTop := by
  have hbounded : Tendsto
      (fun n ↦ (graphIterate d n : BoundedContinuousFunction ℝ X)) atTop
      (𝓝 (graphLimit d : BoundedContinuousFunction ℝ X)) :=
    (continuous_subtype_val.tendsto _).comp (graphIterate_tendsto d)
  exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hbounded

/-- Helper for cm-center-proposition: the compact truncated map has a single
global envelope for all its derivative tensors up to any fixed available order. -/
theorem remainderJetBound (d : MetricGraphTransformData X) (r : ℕ) :
    r ≤ d.nu → ∃ D : ℝ, 1 ≤ D ∧
      ∀ k : ℕ, k ≤ r → ∀ p, ‖iteratedFDeriv ℝ k d.R p‖ ≤ D := by
  induction r with
  | zero =>
      intro _
      have hzero : (0 : WithTop ℕ∞) ≤ d.nu := bot_le
      obtain ⟨B, _, hbound⟩ := d.hR_support.exists_norm_iteratedFDeriv_le
        (d.hR_smooth.of_le hzero)
      refine ⟨max 1 B, le_max_left _ _, ?_⟩
      intro k hk p
      have hkzero : k = 0 := Nat.eq_zero_of_le_zero hk
      rw [hkzero]
      exact (hbound p).trans (le_max_right _ _)
  | succ r ih =>
      intro hr
      obtain ⟨D, hD, hbound⟩ := ih ((Nat.le_succ r).trans hr)
      have hrTop : ((r + 1 : ℕ) : WithTop ℕ∞) ≤ d.nu := by exact_mod_cast hr
      obtain ⟨B, _, hnew⟩ := d.hR_support.exists_norm_iteratedFDeriv_le
        (d.hR_smooth.of_le hrTop)
      refine ⟨max D B, hD.trans (le_max_left _ _), ?_⟩
      intro k hk p
      by_cases hkr : k ≤ r
      · exact (hbound k hkr p).trans (le_max_left _ _)
      · have hksucc : k = r + 1 := by omega
        rw [hksucc]
        exact (hnew p).trans (le_max_right _ _)

/-- Helper for cm-center-proposition: the numerator of the source highest-order
coefficient is `D_zF_s - ψ'(Θ_ξ) D_zF_c`, for the actual output `ψ=Tξ`. -/
def topNumerator (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) (u : ℝ) : X →L[ℝ] X :=
  d.L + derivFiber d ξ u - (derivCenterFiber d ξ u).smulRight
    (deriv (d.transform ξ : ℝ → X) (d.centerMap ξ u))

/-- Helper for cm-center-proposition: applying the numerator gives exactly the
stable derivative minus the output slope times the center-fiber derivative. -/
theorem topNumerator_apply (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) (u : ℝ) (w : X) :
    topNumerator d ξ u w = d.L w + derivFiber d ξ u w -
      derivCenterFiber d ξ u w • deriv (d.transform ξ : ℝ → X) (d.centerMap ξ u) := by
  simp only [topNumerator, sub_apply, add_apply,
    ContinuousLinearMap.smulRight_apply]

/-- Helper for cm-center-proposition: the source highest-order numerator has
the uniform bound `linearRate + epsilon*(1+slope)` for every input graph. -/
theorem norm_topNumerator_le (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) (u : ℝ) :
    ‖topNumerator d ξ u‖ ≤ (d.linearRate : ℝ) + (d.epsilon : ℝ) * (1 + (d.slope : ℝ)) := by
  have hslope : ‖deriv (d.transform ξ : ℝ → X) (d.centerMap ξ u)‖ ≤ (d.slope : ℝ) :=
    norm_deriv_le_of_lipschitz (SmallLipschitzGraph.lipschitzWith _)
  have htensor : ‖(derivCenterFiber d ξ u).smulRight
      (deriv (d.transform ξ : ℝ → X) (d.centerMap ξ u))‖ ≤
      (d.epsilon : ℝ) * (d.slope : ℝ) := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul (norm_derivCenterFiber_le d ξ u) hslope (norm_nonneg _)
      d.epsilon.coe_nonneg
  calc
    ‖topNumerator d ξ u‖ ≤ ‖d.L + derivFiber d ξ u‖ +
        ‖(derivCenterFiber d ξ u).smulRight
          (deriv (d.transform ξ : ℝ → X) (d.centerMap ξ u))‖ :=
      norm_sub_le _ _
    _ ≤ ‖d.L‖ + ‖derivFiber d ξ u‖ + (d.epsilon : ℝ) * (d.slope : ℝ) :=
      add_le_add (norm_add_le _ _) htensor
    _ ≤ (d.linearRate : ℝ) + (d.epsilon : ℝ) * (1 + (d.slope : ℝ)) := by
      nlinarith [d.hL, norm_derivFiber_le d ξ u]

/-- Helper for cm-center-proposition: the exact source linear coefficient
after division by the rth power of the scalar center derivative. -/
def topCoefficient (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) (r : ℕ) (u : ℝ) : X →L[ℝ] X :=
  (deriv (d.centerMap ξ) u)⁻¹ ^ r • topNumerator d ξ u

/-- Helper for cm-center-proposition: the coefficient's action retains the
source numerator and the inverse rth power of the scalar center derivative. -/
theorem topCoefficient_apply (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) (r : ℕ) (u : ℝ) (w : X) :
    topCoefficient d ξ r u w = (deriv (d.centerMap ξ) u)⁻¹ ^ r •
      (d.L w + derivFiber d ξ u w -
        derivCenterFiber d ξ u w • deriv (d.transform ξ : ℝ → X) (d.centerMap ξ u)) := by
  rw [topCoefficient, smul_apply, topNumerator_apply]

/-- Helper for cm-center-proposition: the highest-order coefficient is bounded
by the manuscript's bunching expression, uniformly over all smooth input graphs. -/
theorem norm_topCoefficient_le (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope)
    (hξ : ContDiff ℝ 1 (ξ : ℝ → X)) (r : ℕ) (u : ℝ) :
    ‖topCoefficient d ξ r u‖ ≤
      ((d.linearRate : ℝ) + (d.epsilon : ℝ) * (1 + (d.slope : ℝ))) * (d.lower : ℝ)⁻¹ ^ r := by
  have hden := centerMap_deriv_lower_bound d ξ hξ u
  have hpositive := centerMap_deriv_pos d ξ hξ u
  have hlower : 0 < (d.lower : ℝ) := by exact_mod_cast d.hlower_pos
  have hinv : (deriv (d.centerMap ξ) u)⁻¹ ≤ (d.lower : ℝ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hlower hden
  have hpower := pow_le_pow_left₀ (inv_nonneg.mpr hpositive.le) hinv r
  have hscalar : ‖(deriv (d.centerMap ξ) u)⁻¹ ^ r‖ = (deriv (d.centerMap ξ) u)⁻¹ ^ r :=
    Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hpositive.le) r)
  rw [topCoefficient, norm_smul, hscalar]
  calc
    _ ≤ (d.lower : ℝ)⁻¹ ^ r *
        ((d.linearRate : ℝ) + (d.epsilon : ℝ) * (1 + (d.slope : ℝ))) :=
      mul_le_mul hpower (norm_topNumerator_le d ξ u) (norm_nonneg _)
        (pow_nonneg (inv_nonneg.mpr hlower.le) r)
    _ = _ := mul_comm _ _

/-- Helper for cm-center-proposition: the source scalar recurrence gives one
uniform bound despite arbitrary reparametrization of the preceding center point. -/
theorem uniformBound_of_affineRecurrence {Y : Type*} [NormedAddCommGroup Y]
    (f : ℕ → ℝ → Y) (σ : ℕ → ℝ → ℝ) (q C : ℝ)
    (hq : 0 ≤ q) (hqone : q < 1) (hC : 0 ≤ C)
    (hzero : ∀ u, f 0 u = 0)
    (hstep : ∀ n u, ‖f (n + 1) u‖ ≤ q * ‖f n (σ n u)‖ + C) :
    ∀ n u, ‖f n u‖ ≤ C / (1 - q) := by
  have hden : 0 < 1 - q := sub_pos.mpr hqone
  have hbound : 0 ≤ C / (1 - q) := div_nonneg hC hden.le
  have hfixed : q * (C / (1 - q)) + C = C / (1 - q) := by
    field_simp [hden.ne']
    ring
  intro n
  induction n with
  | zero =>
      intro u
      simpa only [hzero u, norm_zero] using hbound
  | succ n ih =>
      intro u
      calc
        ‖f (n + 1) u‖ ≤ q * ‖f n (σ n u)‖ + C := hstep n u
        _ ≤ q * (C / (1 - q)) + C :=
          add_le_add (mul_le_mul_of_nonneg_left (ih (σ n u)) hq) le_rfl
        _ = _ := hfixed

/-- Helper for cm-center-proposition: the nonlinear composition remainder is the
finite Faà di Bruno sum with the single highest input-derivative branch removed. -/
def nonlinearJetRemainder (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) (r : ℕ) (u : ℝ) : ℝ × X :=
  ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition r ↦ c.length ≠ 1)),
    iteratedFDeriv ℝ c.length d.R (u, ξ u)
      (fun j ↦ iteratedDeriv (c.partSize j) (fun v : ℝ ↦ (v, ξ v)) u)

/-- Helper for cm-center-proposition: the public finite-sum formula for the
nonlinear remainder contains only parts of size strictly below r. -/
theorem nonlinearJetRemainder_def (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) (r : ℕ) (u : ℝ) :
    nonlinearJetRemainder d ξ r u =
      ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition r ↦ c.length ≠ 1)),
        iteratedFDeriv ℝ c.length d.R (u, ξ u)
          (fun j ↦ iteratedDeriv (c.partSize j) (fun v : ℝ ↦ (v, ξ v)) u) := by
  rfl

/-- Helper for cm-center-proposition: the unique single-block branch of the
full nonlinear map carries precisely its fiber derivative on the top graph jet. -/
theorem nonlinear_singleBlock_summand (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) {r : ℕ} (hr : 2 ≤ r)
    (hξ : ContDiff ℝ r (ξ : ℝ → X)) (u : ℝ) :
    iteratedFDeriv ℝ (singleBlock r (Nat.zero_lt_two.trans_le hr)).length d.R (u, ξ u)
        (fun j ↦ iteratedDeriv ((singleBlock r (Nat.zero_lt_two.trans_le hr)).partSize j)
          (fun v : ℝ ↦ (v, ξ v)) u) =
      fderiv ℝ d.R (u, ξ u) (0, iteratedDeriv r (ξ : ℝ → X) u) := by
  change iteratedFDeriv ℝ 1 d.R (u, ξ u)
    (fun _ : Fin 1 ↦ iteratedDeriv r (fun v : ℝ ↦ (v, ξ v)) u) = _
  rw [iteratedFDeriv_one_apply, iteratedDeriv_pair_eq_of_two_le d ξ hr u hξ.contDiffAt]

/-- Helper for cm-center-proposition: differentiating the nonlinear map along
an arbitrary smooth graph isolates its top graph derivative exactly. -/
theorem nonlinearJet_split (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) {r : ℕ}
    (hr : 2 ≤ r) (hrν : r ≤ d.nu) (hξ : ContDiff ℝ r (ξ : ℝ → X)) (u : ℝ) :
    iteratedDeriv r (fun v : ℝ ↦ d.R (v, ξ v)) u =
      fderiv ℝ d.R (u, ξ u) (0, iteratedDeriv r (ξ : ℝ → X) u) +
        nonlinearJetRemainder d ξ r u := by
  have hrTop : (r : WithTop ℕ∞) ≤ d.nu := by exact_mod_cast hrν
  have hR := d.hR_smooth.of_le hrTop
  have hpair : ContDiff ℝ r (fun v : ℝ ↦ (v, ξ v)) := contDiff_id.prodMk hξ
  have hcomposition : (fun v : ℝ ↦ d.R (v, ξ v)) =
      d.R ∘ (fun v : ℝ ↦ (v, ξ v)) := rfl
  rw [hcomposition, iteratedDeriv_vcomp_eq_sum_orderedFinpartition
    hR.contDiffAt hpair.contDiffAt le_rfl]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (singleBlock r (Nat.zero_lt_two.trans_le hr))),
    nonlinear_singleBlock_summand d ξ hr hξ u, nonlinearJetRemainder_def]
  congr 1
  apply Finset.sum_congr
  · ext c
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    exact not_congr (orderedFinpartition_length_eq_one_iff_singleBlock
      (Nat.zero_lt_two.trans_le hr) c).symm
  · intro _ _
    rfl

/-- Helper for cm-center-proposition: finite partition sums turn a fixed-map
derivative envelope and lower input jets into a uniform nonlinear forcing bound. -/
theorem norm_nonlinearJetRemainder_le (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) (r : ℕ) (u D B : ℝ)
    (hD : 0 ≤ D) (hB : 1 ≤ B)
    (hR : ∀ k : ℕ, k ≤ r → ∀ p, ‖iteratedFDeriv ℝ k d.R p‖ ≤ D)
    (hpair : ∀ k : ℕ, 1 ≤ k → k < r →
      ‖iteratedDeriv k (fun v : ℝ ↦ (v, ξ v)) u‖ ≤ B) :
    ‖nonlinearJetRemainder d ξ r u‖ ≤
      (Fintype.card (OrderedFinpartition r) : ℝ) * D * B ^ r := by
  have hterm : ∀ c : OrderedFinpartition r, c.length ≠ 1 →
      ‖iteratedFDeriv ℝ c.length d.R (u, ξ u)
        (fun j ↦ iteratedDeriv (c.partSize j) (fun v : ℝ ↦ (v, ξ v)) u)‖ ≤ D * B ^ r := by
    intro c hc
    have hproduct := ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le
      (hR c.length c.length_le (u, ξ u))
      (fun j ↦ hpair (c.partSize j) (c.partSize_pos j)
        (orderedFinpartition_partSize_lt_of_length_ne_one c hc j))
    have hpower : B ^ c.length ≤ B ^ r := pow_le_pow_right₀ hB c.length_le
    have hcomparison : D * (∏ _j : Fin c.length, B) ≤ D * B ^ r := by
      simpa using mul_le_mul_of_nonneg_left hpower hD
    exact hproduct.trans hcomparison
  rw [nonlinearJetRemainder_def]
  calc
    _ ≤ ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition r ↦ c.length ≠ 1)),
        ‖iteratedFDeriv ℝ c.length d.R (u, ξ u)
          (fun j ↦ iteratedDeriv (c.partSize j) (fun v : ℝ ↦ (v, ξ v)) u)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _c ∈ (Finset.univ.filter (fun c : OrderedFinpartition r ↦ c.length ≠ 1)),
        D * B ^ r := by
      apply Finset.sum_le_sum
      intro c hc
      exact hterm c (Finset.mem_filter.mp hc).2
    _ ≤ ∑ _c : OrderedFinpartition r, D * B ^ r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro _ _ _
      exact mul_nonneg hD (pow_nonneg (zero_le_one.trans hB) r)
    _ = _ := by simp [mul_assoc]

/-- Helper for cm-center-proposition: an ordered partition has as many parts as
points exactly when it is the partition into singletons. -/
theorem orderedPartition_length_eq_iff_atomic {r : ℕ} (c : OrderedFinpartition r) :
    c.length = r ↔ c = OrderedFinpartition.atomic r := by
  constructor
  · intro hlength
    have hsum : ∑ j, c.partSize j = r := by
      have h := c.sum_sigma_eq_sum (fun _ ↦ (1 : ℕ))
      simpa using h
    have hparts : ∀ j, c.partSize j = 1 := by
      intro j
      have hle : ∀ k, 1 ≤ c.partSize k := fun k ↦ c.partSize_pos k
      by_contra hne
      have hlt : 1 < c.partSize j := lt_of_le_of_ne (hle j) (Ne.symm hne)
      have hgt : ∑ k, c.partSize k > ∑ _k : Fin c.length, (1 : ℕ) :=
        Finset.sum_lt_sum (fun k _ ↦ hle k) ⟨j, Finset.mem_univ j, hlt⟩
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        mul_one, hlength, hsum] at hgt
      exact (lt_irrefl r) hgt
    rcases c with ⟨length, partSize, hpos, emb, hmono, hpmono, hdisj, hcover⟩
    dsimp only at hlength hparts
    subst length
    obtain rfl : partSize = fun _ ↦ 1 := funext hparts
    have horder : StrictMono (fun j : Fin r ↦
        emb j ⟨1 - 1, Nat.sub_one_lt_of_lt (hpos j)⟩) := hpmono
    have hidentity : ∀ j : Fin r,
        emb j ⟨1 - 1, Nat.sub_one_lt_of_lt (hpos j)⟩ = j := by
      have hfun := le_antisymm horder.le_id horder.id_le
      exact congrFun hfun
    have hemb : ∀ (j : Fin r) (k : Fin 1), emb j k = j := by
      intro j k
      have hk : k = ⟨1 - 1, Nat.sub_one_lt_of_lt (hpos j)⟩ := Subsingleton.elim _ _
      rw [hk]
      exact hidentity j
    simpa [OrderedFinpartition.ext_iff, OrderedFinpartition.atomic, funext_iff,
      Fin.forall_fin_one] using hemb
  · intro h
    subst h
    rfl

/-- Helper for cm-center-proposition: the middle scalar-composition branches
involve only strictly lower derivatives of both the outer and inner curves. -/
def scalarJetRemainder (ψ : ℝ → X) (Θ : ℝ → ℝ) (r : ℕ) (u : ℝ) : X :=
  ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
    (∏ j, iteratedDeriv (c.partSize j) Θ u) • iteratedDeriv c.length ψ (Θ u)

/-- Helper for cm-center-proposition: the scalar-composition remainder has its
exact finite sum over the non-atomic, non-single-block branches. -/
theorem scalarJetRemainder_def (ψ : ℝ → X) (Θ : ℝ → ℝ) (r : ℕ) (u : ℝ) :
    scalarJetRemainder ψ Θ r u =
      ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
        (∏ j, iteratedDeriv (c.partSize j) Θ u) • iteratedDeriv c.length ψ (Θ u) := by
  rfl

/-- Helper for cm-center-proposition: Faà di Bruno separates the highest outer
jet, the highest inner jet and the strictly lower middle terms for two curves. -/
theorem scalarComposition_split (ψ : ℝ → X) (Θ : ℝ → ℝ) {r : ℕ}
    (hr : 2 ≤ r) (hψ : ContDiff ℝ r ψ) (hΘ : ContDiff ℝ r Θ) (u : ℝ) :
    iteratedDeriv r (ψ ∘ Θ) u =
      deriv Θ u ^ r • iteratedDeriv r ψ (Θ u) +
        iteratedDeriv r Θ u • deriv ψ (Θ u) + scalarJetRemainder ψ Θ r u := by
  have hrzero : 0 < r := Nat.zero_lt_two.trans_le hr
  have hsingle : singleBlock r hrzero ∈
      (Finset.univ : Finset (OrderedFinpartition r)).erase (OrderedFinpartition.atomic r) := by
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h
    have hlength := congrArg OrderedFinpartition.length h
    simp only [singleBlock_length, OrderedFinpartition.atomic_length] at hlength
    omega
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition
    hψ.contDiffAt hΘ.contDiffAt le_rfl]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (OrderedFinpartition.atomic r)),
    ← Finset.add_sum_erase _ _ hsingle]
  have hatomic :
      (∏ j, iteratedDeriv ((OrderedFinpartition.atomic r).partSize j) Θ u) •
        iteratedDeriv (OrderedFinpartition.atomic r).length ψ (Θ u) =
      deriv Θ u ^ r • iteratedDeriv r ψ (Θ u) := by
    change (∏ _j : Fin r, iteratedDeriv 1 Θ u) • iteratedDeriv r ψ (Θ u) = _
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, iteratedDeriv_one]
  have hblock :
      (∏ j, iteratedDeriv ((singleBlock r hrzero).partSize j) Θ u) •
        iteratedDeriv (singleBlock r hrzero).length ψ (Θ u) =
      iteratedDeriv r Θ u • deriv ψ (Θ u) := by
    change (∏ _j : Fin 1, iteratedDeriv r Θ u) • iteratedDeriv 1 ψ (Θ u) = _
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, iteratedDeriv_one]
  rw [hatomic, hblock, scalarJetRemainder_def]
  simp only [add_assoc]
  congr 1
  congr 1
  apply Finset.sum_congr
  · ext c
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    have hatom := not_congr (orderedPartition_length_eq_iff_atomic c)
    have hblock := not_congr (orderedFinpartition_length_eq_one_iff_singleBlock hrzero c)
    constructor
    · rintro ⟨hb, ha⟩
      exact ⟨hatom.mpr ha, hblock.mpr hb⟩
    · rintro ⟨ha, hb⟩
      exact ⟨hblock.mp hb, hatom.mp ha⟩
  · intro _ _
    rfl

/-- Helper for cm-center-proposition: a continuous linear map commutes with
every available scalar iterated derivative of an arbitrary smooth curve. -/
theorem iteratedDeriv_linear {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (f : ℝ → E) {r : ℕ} {u : ℝ} (hf : ContDiffAt ℝ r f u) :
    iteratedDeriv r (L ∘ f) u = L (iteratedDeriv r f u) := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    ContinuousLinearMap.iteratedFDeriv_comp_left L hf le_rfl]
  rfl

/-- Helper for cm-center-proposition: the first jet of the graph pairing has
norm at most one, uniformly on the original Lipschitz cone. -/
theorem norm_graphPair_deriv_le_one (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) (u : ℝ) :
    ‖deriv (fun v : ℝ ↦ (v, ξ v)) u‖ ≤ 1 := by
  have hpair : LipschitzWith 1 (fun v : ℝ ↦ (v, ξ v)) := by
    simpa only [Function.comp_def, id_eq, max_eq_left d.hslope_one] using
      LipschitzWith.id.prodMk (SmallLipschitzGraph.lipschitzWith ξ)
  exact norm_deriv_le_of_lipschitz hpair

/-- Helper for cm-center-proposition: lower graph-jet bounds give lower paired
jet bounds without requiring the unbounded scalar coordinate itself to be bounded. -/
theorem graphPair_lowerJetBound (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) (r : ℕ)
    (hξ : ContDiff ℝ r (ξ : ℝ → X)) (B : ℝ) (hB : 1 ≤ B)
    (hjets : ∀ k : ℕ, 1 ≤ k → k < r → ∀ u, ‖iteratedDeriv k (ξ : ℝ → X) u‖ ≤ B) :
    ∀ k : ℕ, 1 ≤ k → k < r → ∀ u,
      ‖iteratedDeriv k (fun v : ℝ ↦ (v, ξ v)) u‖ ≤ B := by
  intro k hk hkr u
  by_cases hone : k = 1
  · subst k
    simpa only [iteratedDeriv_one] using (norm_graphPair_deriv_le_one d ξ u).trans hB
  · have htwo : 2 ≤ k := by omega
    have hkTop : (k : WithTop ℕ∞) ≤ r := by exact_mod_cast hkr.le
    rw [iteratedDeriv_pair_eq_of_two_le d ξ htwo u (hξ.of_le hkTop).contDiffAt,
      Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]
    exact hjets k hk hkr u

/-- Helper for cm-center-proposition: the top center-map jet consists of its
center-fiber derivative on the input top jet plus the lower nonlinear remainder. -/
theorem centerMap_topJet (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) {r : ℕ}
    (hr : 2 ≤ r) (hrν : r ≤ d.nu) (hξ : ContDiff ℝ r (ξ : ℝ → X)) (u : ℝ) :
    iteratedDeriv r (d.centerMap ξ) u =
      derivCenterFiber d ξ u (iteratedDeriv r (ξ : ℝ → X) u) +
        (nonlinearJetRemainder d ξ r u).1 := by
  have hrTop : (r : WithTop ℕ∞) ≤ d.nu := by exact_mod_cast hrν
  have hpair : ContDiff ℝ r (fun v : ℝ ↦ (v, ξ v)) := contDiff_id.prodMk hξ
  have hR : ContDiff ℝ r (fun v : ℝ ↦ d.R (v, ξ v)) :=
    (d.hR_smooth.of_le hrTop).comp hpair
  have hfun : d.centerMap ξ = (id : ℝ → ℝ) +
      (ContinuousLinearMap.fst ℝ ℝ X) ∘ (fun v : ℝ ↦ d.R (v, ξ v)) := by
    funext v
    rw [d.centerMap_eq]
    rfl
  have hzero : r ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_two.trans_le hr)
  have hone : r ≠ 1 := by omega
  rw [hfun, iteratedDeriv_add contDiff_id.contDiffAt
    ((ContinuousLinearMap.fst ℝ ℝ X).contDiff.comp hR).contDiffAt,
    iteratedDeriv_id, if_neg hzero, if_neg hone, zero_add,
    iteratedDeriv_linear _ _ hR.contDiffAt, nonlinearJet_split d ξ hr hrν hξ u]
  simp only [ContinuousLinearMap.coe_fst', Prod.fst_add, ← derivCenterFiber_apply]

/-- Helper for cm-center-proposition: the differentiated actual transform
equation has the stable linear/fiber top term and the lower nonlinear remainder. -/
theorem stableComposition_topJet (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) {r : ℕ}
    (hr : 2 ≤ r) (hrν : r ≤ d.nu) (hξ : ContDiff ℝ r (ξ : ℝ → X)) (u : ℝ) :
    iteratedDeriv r ((d.transform ξ : ℝ → X) ∘ d.centerMap ξ) u =
      d.L (iteratedDeriv r (ξ : ℝ → X) u) +
        derivFiber d ξ u (iteratedDeriv r (ξ : ℝ → X) u) +
          (nonlinearJetRemainder d ξ r u).2 := by
  have hrTop : (r : WithTop ℕ∞) ≤ d.nu := by exact_mod_cast hrν
  have hpair : ContDiff ℝ r (fun v : ℝ ↦ (v, ξ v)) := contDiff_id.prodMk hξ
  have hR : ContDiff ℝ r (fun v : ℝ ↦ d.R (v, ξ v)) :=
    (d.hR_smooth.of_le hrTop).comp hpair
  have hfun : (d.transform ξ : ℝ → X) ∘ d.centerMap ξ =
      d.L ∘ (ξ : ℝ → X) + (ContinuousLinearMap.snd ℝ ℝ X) ∘
        (fun v : ℝ ↦ d.R (v, ξ v)) := by
    funext v
    exact transform_equation d ξ v
  rw [hfun, iteratedDeriv_add (d.L.contDiff.comp hξ).contDiffAt
    ((ContinuousLinearMap.snd ℝ ℝ X).contDiff.comp hR).contDiffAt,
    iteratedDeriv_linear _ _ hξ.contDiffAt, iteratedDeriv_linear _ _ hR.contDiffAt,
    nonlinearJet_split d ξ hr hrν hξ u]
  simp only [ContinuousLinearMap.coe_snd', Prod.snd_add, ← derivFiber_apply, add_assoc]

/-- Helper for cm-center-proposition: the actual highest-order forcing uses
only the nonlinear lower-input-jet sum and the lower scalar-composition sum. -/
def topForcing (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) (r : ℕ) (u : ℝ) : X :=
  (deriv (d.centerMap ξ) u)⁻¹ ^ r •
    ((nonlinearJetRemainder d ξ r u).2 - (nonlinearJetRemainder d ξ r u).1 •
      deriv (d.transform ξ : ℝ → X) (d.centerMap ξ u) -
        scalarJetRemainder (d.transform ξ : ℝ → X) (d.centerMap ξ) r u)

/-- Helper for cm-center-proposition: the finite lower-jet formula for the
source forcing after division by the scalar center derivative. -/
theorem topForcing_def (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) (r : ℕ) (u : ℝ) :
    topForcing d ξ r u = (deriv (d.centerMap ξ) u)⁻¹ ^ r •
      ((nonlinearJetRemainder d ξ r u).2 - (nonlinearJetRemainder d ξ r u).1 •
        deriv (d.transform ξ : ℝ → X) (d.centerMap ξ u) -
          scalarJetRemainder (d.transform ξ : ℝ → X) (d.centerMap ξ) r u) := by
  rfl

/-- Helper for cm-center-proposition: the actual coupled transform identity
isolates exactly the manuscript's highest-derivative numerator before division. -/
theorem transform_topJet_scaled (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) {r : ℕ}
    (hr : 2 ≤ r) (hrν : r ≤ d.nu) (hξ : ContDiff ℝ r (ξ : ℝ → X)) (u : ℝ) :
    deriv (d.centerMap ξ) u ^ r •
      iteratedDeriv r (d.transform ξ : ℝ → X) (d.centerMap ξ u) =
      topNumerator d ξ u (iteratedDeriv r (ξ : ℝ → X) u) +
        (nonlinearJetRemainder d ξ r u).2 - (nonlinearJetRemainder d ξ r u).1 •
          deriv (d.transform ξ : ℝ → X) (d.centerMap ξ u) -
            scalarJetRemainder (d.transform ξ : ℝ → X) (d.centerMap ξ) r u := by
  have hrTop : (r : WithTop ℕ∞) ≤ d.nu := by exact_mod_cast hrν
  have hψ := transform_contDiff d ξ (one_le_two.trans hr) hrν hξ
  have hΘ := centerMap_contDiff_of_prev d ξ hrTop hξ
  have h := stableComposition_topJet d ξ hr hrν hξ u
  rw [scalarComposition_split _ _ hr hψ hΘ u] at h
  calc
    _ = (deriv (d.centerMap ξ) u ^ r •
          iteratedDeriv r (d.transform ξ : ℝ → X) (d.centerMap ξ u) +
        iteratedDeriv r (d.centerMap ξ) u •
          deriv (d.transform ξ : ℝ → X) (d.centerMap ξ u) +
        scalarJetRemainder (d.transform ξ : ℝ → X) (d.centerMap ξ) r u) -
          iteratedDeriv r (d.centerMap ξ) u •
            deriv (d.transform ξ : ℝ → X) (d.centerMap ξ u) -
          scalarJetRemainder (d.transform ξ : ℝ → X) (d.centerMap ξ) r u := by abel
    _ = (d.L (iteratedDeriv r (ξ : ℝ → X) u) +
        derivFiber d ξ u (iteratedDeriv r (ξ : ℝ → X) u) +
        (nonlinearJetRemainder d ξ r u).2) -
          iteratedDeriv r (d.centerMap ξ) u •
            deriv (d.transform ξ : ℝ → X) (d.centerMap ξ u) -
          scalarJetRemainder (d.transform ξ : ℝ → X) (d.centerMap ξ) r u := by rw [h]
    _ = _ := by
      rw [centerMap_topJet d ξ hr hrν hξ u, topNumerator_apply, add_smul]
      abel

/-- Helper for cm-center-proposition: the exact graph-transform highest-jet
recurrence has the original contracting coefficient and an explicit lower-jet forcing. -/
theorem transform_topJet (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope) {r : ℕ}
    (hr : 2 ≤ r) (hrν : r ≤ d.nu) (hξ : ContDiff ℝ r (ξ : ℝ → X)) (u : ℝ) :
    iteratedDeriv r (d.transform ξ : ℝ → X) (d.centerMap ξ u) =
      topCoefficient d ξ r u (iteratedDeriv r (ξ : ℝ → X) u) + topForcing d ξ r u := by
  have hone : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast one_le_two.trans hr
  have hne := centerMap_deriv_ne_zero d ξ (hξ.of_le hone) u
  have hcancel : (deriv (d.centerMap ξ) u)⁻¹ ^ r * deriv (d.centerMap ξ) u ^ r = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hne, one_pow]
  have h := congrArg (fun z : X ↦ (deriv (d.centerMap ξ) u)⁻¹ ^ r • z)
    (transform_topJet_scaled d ξ hr hrν hξ u)
  simp only [smul_smul, hcancel, one_smul] at h
  rw [h]
  simp only [topCoefficient, smul_apply, topForcing_def, topNumerator_apply]
  module

/-- Helper for cm-center-proposition: the scalar middle sum is exactly the
multilinear evaluation sum controlled by the finite ordered-partition interface. -/
theorem scalarJetRemainder_tensor (ψ : ℝ → X) (Θ : ℝ → ℝ) (r : ℕ) (u : ℝ) :
    scalarJetRemainder ψ Θ r u =
      ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
        iteratedFDeriv ℝ c.length ψ (Θ u)
          (fun j ↦ iteratedDeriv (c.partSize j) Θ u) := by
  simp only [scalarJetRemainder_def, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]

/-- Helper for cm-center-proposition: common lower outer and inner jet bounds
control the scalar middle forcing uniformly, without either top derivative. -/
theorem norm_scalarJetRemainder_le (ψ : ℝ → X) (Θ : ℝ → ℝ)
    (r : ℕ) (u A B : ℝ) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (houter : ∀ k : ℕ, k < r → ‖iteratedDeriv k ψ (Θ u)‖ ≤ A)
    (hinner : ∀ k : ℕ, 0 < k → k < r → ‖iteratedDeriv k Θ u‖ ≤ B) :
    ‖scalarJetRemainder ψ Θ r u‖ ≤
      (Fintype.card (OrderedFinpartition r) : ℝ) * A * B ^ r := by
  let Ann : ℝ≥0 := ⟨A, hA⟩
  have hBzero : 0 ≤ B := zero_le_one.trans hB
  let Bnn : ℝ≥0 := ⟨B, hBzero⟩
  have hjet : ∀ k, k < r → ‖iteratedFDeriv ℝ k ψ (Θ u)‖ ≤ Ann := by
    intro k hk
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact houter k hk
  have hslots : ∀ k : ℕ, 0 < k → k < r → ‖iteratedDeriv k Θ u‖ ≤ Bnn := hinner
  have hbound := norm_mixedPartitionSum_le r
    (fun k ↦ iteratedFDeriv ℝ k ψ (Θ u)) (fun k ↦ iteratedDeriv k Θ u)
      Ann Bnn hjet hslots
  simp only [Ann, Bnn] at hbound
  rw [scalarJetRemainder_tensor]
  calc
    _ ≤ ∑ c ∈ (Finset.univ.filter
        (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)), A * B ^ c.length :=
      hbound
    _ ≤ ∑ _c ∈ (Finset.univ.filter
        (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)), A * B ^ r := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB c.length_le) hA
    _ ≤ ∑ _c : OrderedFinpartition r, A * B ^ r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro _ _ _
      exact mul_nonneg hA (pow_nonneg hBzero r)
    _ = _ := by simp [mul_assoc]

/-- Helper for cm-center-proposition: the scalar inverse derivative contributes
at most the prescribed reciprocal lower rate at every finite order. -/
theorem norm_inverse_centerDerivative_pow_le (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope)
    (hξ : ContDiff ℝ 1 (ξ : ℝ → X)) (r : ℕ) (u : ℝ) :
    ‖(deriv (d.centerMap ξ) u)⁻¹ ^ r‖ ≤ (d.lower : ℝ)⁻¹ ^ r := by
  have hden := centerMap_deriv_lower_bound d ξ hξ u
  have hpositive := centerMap_deriv_pos d ξ hξ u
  have hlower : 0 < (d.lower : ℝ) := by exact_mod_cast d.hlower_pos
  have hinv : (deriv (d.centerMap ξ) u)⁻¹ ≤ (d.lower : ℝ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hlower hden
  rw [Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hpositive.le) r)]
  exact pow_le_pow_left₀ (inv_nonneg.mpr hpositive.le) hinv r

/-- Helper for cm-center-proposition: the explicit source forcing is bounded by
its two lower-jet remainders and the fixed reciprocal center rate. -/
theorem norm_topForcing_of_remainderBounds (d : MetricGraphTransformData X)
    (ξ : SmallLipschitzGraph X d.radius d.slope)
    (hξ : ContDiff ℝ 1 (ξ : ℝ → X)) (r : ℕ) (u A B : ℝ)
    (hA : 0 ≤ A)
    (hR : ‖nonlinearJetRemainder d ξ r u‖ ≤ A)
    (hS : ‖scalarJetRemainder (d.transform ξ : ℝ → X) (d.centerMap ξ) r u‖ ≤ B) :
    ‖topForcing d ξ r u‖ ≤
      (d.lower : ℝ)⁻¹ ^ r * (A * (1 + (d.slope : ℝ)) + B) := by
  have hstable := (norm_snd_le (nonlinearJetRemainder d ξ r u)).trans hR
  have hcenter := (norm_fst_le (nonlinearJetRemainder d ξ r u)).trans hR
  have hslope : ‖deriv (d.transform ξ : ℝ → X) (d.centerMap ξ u)‖ ≤ (d.slope : ℝ) :=
    norm_deriv_le_of_lipschitz (SmallLipschitzGraph.lipschitzWith _)
  have hproduct : ‖(nonlinearJetRemainder d ξ r u).1 •
      deriv (d.transform ξ : ℝ → X) (d.centerMap ξ u)‖ ≤ A * (d.slope : ℝ) := by
    rw [norm_smul]
    exact mul_le_mul hcenter hslope (norm_nonneg _) hA
  have hinside : ‖(nonlinearJetRemainder d ξ r u).2 -
      (nonlinearJetRemainder d ξ r u).1 •
        deriv (d.transform ξ : ℝ → X) (d.centerMap ξ u) -
      scalarJetRemainder (d.transform ξ : ℝ → X) (d.centerMap ξ) r u‖ ≤
        A * (1 + (d.slope : ℝ)) + B := by
    calc
      _ ≤ ‖(nonlinearJetRemainder d ξ r u).2 -
          (nonlinearJetRemainder d ξ r u).1 •
            deriv (d.transform ξ : ℝ → X) (d.centerMap ξ u)‖ +
          ‖scalarJetRemainder (d.transform ξ : ℝ → X) (d.centerMap ξ) r u‖ := norm_sub_le _ _
      _ ≤ ‖(nonlinearJetRemainder d ξ r u).2‖ +
          ‖(nonlinearJetRemainder d ξ r u).1 •
            deriv (d.transform ξ : ℝ → X) (d.centerMap ξ u)‖ + B :=
        add_le_add (norm_sub_le _ _) hS
      _ ≤ _ := by nlinarith
  rw [topForcing_def, norm_smul]
  exact mul_le_mul (norm_inverse_centerDerivative_pow_le d ξ hξ r u) hinside
    (norm_nonneg _) (pow_nonneg (inv_nonneg.mpr d.lower.coe_nonneg) r)

/-- Helper for cm-center-proposition: common lower input jets give one common
bound on the lower center-map jets for every smooth graph in the cone. -/
theorem centerMap_lowerJetBound (d : MetricGraphTransformData X) (r : ℕ)
    (hr : 2 ≤ r) (hrν : r ≤ d.nu) (B : ℝ) (hB : 1 ≤ B) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ ξ : SmallLipschitzGraph X d.radius d.slope,
      ContDiff ℝ r (ξ : ℝ → X) →
      (∀ k : ℕ, k < r → ∀ u, ‖iteratedDeriv k (ξ : ℝ → X) u‖ ≤ B) →
      ∀ k : ℕ, 0 < k → k < r → ∀ u, ‖iteratedDeriv k (d.centerMap ξ) u‖ ≤ H := by
  obtain ⟨D, hDone, hR⟩ := remainderJetBound d r hrν
  have hD : 0 ≤ D := zero_le_one.trans hDone
  have hBzero : 0 ≤ B := zero_le_one.trans hB
  let S : ℝ := ∑ k : Fin r, (Fintype.card (OrderedFinpartition (k : ℕ)) : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
  have hcard : ∀ k : ℕ, k < r → (Fintype.card (OrderedFinpartition k) : ℝ) ≤ S := by
    intro k hk
    exact Finset.single_le_sum
      (f := fun j : Fin r ↦ (Fintype.card (OrderedFinpartition (j : ℕ)) : ℝ))
      (fun _ _ ↦ Nat.cast_nonneg _) (Finset.mem_univ (⟨k, hk⟩ : Fin r))
  have hlarge : 0 ≤ S * D * B ^ r :=
    mul_nonneg (mul_nonneg hS hD) (pow_nonneg hBzero r)
  let H := 1 + (d.epsilon : ℝ) * B + S * D * B ^ r
  have hεB : 0 ≤ (d.epsilon : ℝ) * B := mul_nonneg d.epsilon.coe_nonneg hBzero
  have hH : 1 ≤ H := by
    dsimp only [H]
    linarith
  refine ⟨H, hH, ?_⟩
  intro ξ hξ hjets k hk hkr u
  have honeTop : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast one_le_two.trans hr
  have hξone : ContDiff ℝ 1 (ξ : ℝ → X) := hξ.of_le honeTop
  by_cases hone : k = 1
  · subst k
    have hfirst : ‖deriv (d.centerMap ξ) u‖ ≤ 1 + (d.epsilon : ℝ) := by
      rw [(centerMap_hasDerivAt d ξ hξone u).deriv]
      calc
        _ ≤ ‖(1 : ℝ)‖ + ‖deriv (fun v : ℝ ↦ (d.R (v, ξ v)).1) u‖ := norm_add_le _ _
        _ ≤ 1 + (d.epsilon : ℝ) := by
          simpa only [norm_one] using
            add_le_add (le_refl (1 : ℝ)) (centerRemainder_norm_deriv_le d ξ u)
    have hε := mul_le_mul_of_nonneg_left hB d.epsilon.coe_nonneg
    simp only [mul_one] at hε
    have hlast : 1 + (d.epsilon : ℝ) ≤ H := by
      dsimp only [H]
      linarith
    simpa only [iteratedDeriv_one] using hfirst.trans hlast
  · have htwo : 2 ≤ k := by omega
    have hkTop : (k : WithTop ℕ∞) ≤ r := by exact_mod_cast hkr.le
    have hpair := graphPair_lowerJetBound d ξ r hξ B hB (fun j _ hj ↦ hjets j hj)
    have hrem := norm_nonlinearJetRemainder_le d ξ k u D B hD hB
      (fun j hj p ↦ hR j (hj.trans hkr.le) p)
      (fun j hj hjk ↦ hpair j hj (hjk.trans hkr) u)
    have hlinear : ‖derivCenterFiber d ξ u (iteratedDeriv k (ξ : ℝ → X) u)‖ ≤
        (d.epsilon : ℝ) * B :=
      ((derivCenterFiber d ξ u).le_opNorm _).trans
        (mul_le_mul (norm_derivCenterFiber_le d ξ u) (hjets k hkr u)
          (norm_nonneg _) d.epsilon.coe_nonneg)
    have hremUniform : (Fintype.card (OrderedFinpartition k) : ℝ) * D * B ^ k ≤
        S * D * B ^ r :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hcard k hkr) hD)
        (pow_le_pow_right₀ hB hkr.le) (pow_nonneg hBzero k) (mul_nonneg hS hD)
    have hpart := (norm_fst_le (nonlinearJetRemainder d ξ k u)).trans (hrem.trans hremUniform)
    rw [centerMap_topJet d ξ htwo (hkr.le.trans hrν) (hξ.of_le hkTop) u]
    apply (norm_add_le _ _).trans
    have hbound := add_le_add hlinear hpart
    dsimp only [H]
    linarith

/-- Helper for cm-center-proposition: fixed compact-map derivatives and common
lower jets of an input and its actual output give a common source forcing bound. -/
theorem topForcing_uniformBound (d : MetricGraphTransformData X) (r : ℕ)
    (hr : 2 ≤ r) (hrν : r ≤ d.nu) (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : SmallLipschitzGraph X d.radius d.slope,
      ContDiff ℝ r (ξ : ℝ → X) →
      (∀ k : ℕ, k < r → ∀ u, ‖iteratedDeriv k (ξ : ℝ → X) u‖ ≤ B) →
      (∀ k : ℕ, k < r → ∀ u, ‖iteratedDeriv k (d.transform ξ : ℝ → X) u‖ ≤ B) →
      ∀ u, ‖topForcing d ξ r u‖ ≤ C := by
  obtain ⟨D, hDone, hR⟩ := remainderJetBound d r hrν
  obtain ⟨H, hH, hcenter⟩ := centerMap_lowerJetBound d r hr hrν B hB
  have hD : 0 ≤ D := zero_le_one.trans hDone
  have hBzero : 0 ≤ B := zero_le_one.trans hB
  have hHzero : 0 ≤ H := zero_le_one.trans hH
  let A := (Fintype.card (OrderedFinpartition r) : ℝ) * D * B ^ r
  let T := (Fintype.card (OrderedFinpartition r) : ℝ) * B * H ^ r
  have hA : 0 ≤ A := by positivity
  have hT : 0 ≤ T := by positivity
  let C := (d.lower : ℝ)⁻¹ ^ r * (A * (1 + (d.slope : ℝ)) + T)
  have hC : 0 ≤ C := by positivity
  refine ⟨C, hC, ?_⟩
  intro ξ hξ hinput houtput u
  have hpair := graphPair_lowerJetBound d ξ r hξ B hB (fun k _ hk ↦ hinput k hk)
  have hnonlinear : ‖nonlinearJetRemainder d ξ r u‖ ≤ A :=
    norm_nonlinearJetRemainder_le d ξ r u D B hD hB (fun k hk p ↦ hR k hk p)
      (fun k hk hkr ↦ hpair k hk hkr u)
  have hscalar : ‖scalarJetRemainder (d.transform ξ : ℝ → X) (d.centerMap ξ) r u‖ ≤ T :=
    norm_scalarJetRemainder_le _ _ r u B H hBzero hH
      (fun k hk ↦ houtput k hk (d.centerMap ξ u))
      (fun k hk hkr ↦ hcenter ξ hξ hinput k hk hkr u)
  have honeTop : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast one_le_two.trans hr
  exact norm_topForcing_of_remainderBounds d ξ (hξ.of_le honeTop) r u A T hA
    hnonlinear hscalar

/-- Helper for cm-center-proposition: the exact zero-start graph-transform
iterates have one common bound for every derivative through m. The hypotheses
are only the finite source bunching inequalities on the truncated map, and the
uniform forcing estimates are derived from compact support and lower-order jets. -/
theorem graphIterate_uniformDerivativeBounds (d : MetricGraphTransformData X) (m : ℕ) :
    m ≤ d.nu →
    (∀ r : ℕ, 2 ≤ r → r ≤ m →
      ((d.linearRate : ℝ) + (d.epsilon : ℝ) * (1 + (d.slope : ℝ))) *
        (d.lower : ℝ)⁻¹ ^ r < 1) →
    ∃ B : ℝ, 1 ≤ B ∧ ∀ n r : ℕ, r ≤ m → ∀ u : ℝ,
      ‖iteratedDeriv r (graphIterate d n : ℝ → X) u‖ ≤ B := by
  induction m with
  | zero =>
      intro _ _
      refine ⟨max 1 (d.radius : ℝ), le_max_left _ _, ?_⟩
      intro n r hr u
      have hrzero : r = 0 := Nat.eq_zero_of_le_zero hr
      subst r
      simpa only [iteratedDeriv_zero] using
        (norm_graphIterate_le d n u).trans (le_max_right 1 (d.radius : ℝ))
  | succ m ih =>
      intro hmν hbunching
      obtain ⟨B, hB, hbound⟩ := ih ((Nat.le_succ m).trans hmν)
        (fun r hr hrm ↦ hbunching r hr (hrm.trans (Nat.le_succ m)))
      by_cases htwo : 2 ≤ m + 1
      · obtain ⟨C, hC, hforcing⟩ := topForcing_uniformBound d (m + 1) htwo hmν B hB
        let q := ((d.linearRate : ℝ) + (d.epsilon : ℝ) * (1 + (d.slope : ℝ))) *
          (d.lower : ℝ)⁻¹ ^ (m + 1)
        have hq : 0 ≤ q := by positivity
        have hqone : q < 1 := hbunching (m + 1) htwo le_rfl
        let f : ℕ → ℝ → X := fun n ↦ iteratedDeriv (m + 1) (graphIterate d n : ℝ → X)
        let σ : ℕ → ℝ → ℝ := fun n ↦ d.inverseCenter (graphIterate d n)
        have hzero : ∀ u, f 0 u = 0 := by
          intro u
          dsimp only [f]
          rw [graphIterate_zero_coe]
          exact iteratedDeriv_const_zero
        have hstep : ∀ n v, ‖f (n + 1) v‖ ≤ q * ‖f n (σ n v)‖ + C := by
          intro n v
          let ξ := graphIterate d n
          let u := d.inverseCenter ξ v
          have hrTop : ((m + 1 : ℕ) : WithTop ℕ∞) ≤ d.nu := by exact_mod_cast hmν
          have hξ : ContDiff ℝ (m + 1 : ℕ) (ξ : ℝ → X) :=
            (graphIterate_contDiff d n).of_le hrTop
          have hinput : ∀ k : ℕ, k < m + 1 → ∀ u, ‖iteratedDeriv k (ξ : ℝ → X) u‖ ≤ B := by
            intro k hk u
            exact hbound n k (Nat.le_of_lt_succ hk) u
          have houtput : ∀ k : ℕ, k < m + 1 → ∀ u,
              ‖iteratedDeriv k (d.transform ξ : ℝ → X) u‖ ≤ B := by
            intro k hk u
            simpa only [graphIterate_succ, ξ] using
              hbound (n + 1) k (Nat.le_of_lt_succ hk) u
          have hforce := hforcing ξ hξ hinput houtput u
          have honeTop : (1 : WithTop ℕ∞) ≤ (m + 1 : ℕ) := by
            exact_mod_cast one_le_two.trans htwo
          have hcoef := norm_topCoefficient_le d ξ (hξ.of_le honeTop) (m + 1) u
          have hpoint : ‖iteratedDeriv (m + 1) (d.transform ξ : ℝ → X) (d.centerMap ξ u)‖ ≤
              q * ‖iteratedDeriv (m + 1) (ξ : ℝ → X) u‖ + C := by
            rw [transform_topJet d ξ htwo hmν hξ u]
            apply (norm_add_le _ _).trans
            exact add_le_add
              (((topCoefficient d ξ (m + 1) u).le_opNorm _).trans
                (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _))) hforce
          simpa only [f, σ, ξ, u, centerMap_inverseCenter, graphIterate_succ] using hpoint
        have htop := uniformBound_of_affineRecurrence f σ q C hq hqone hC hzero hstep
        refine ⟨max B (C / (1 - q)), hB.trans (le_max_left _ _), ?_⟩
        intro n r hr u
        by_cases hrm : r ≤ m
        · exact (hbound n r hrm u).trans (le_max_left _ _)
        · have hrnext : r = m + 1 := by omega
          subst r
          exact (htop n u).trans (le_max_right _ _)
      · refine ⟨B, hB, ?_⟩
        intro n r hr u
        by_cases hrm : r ≤ m
        · exact hbound n r hrm u
        · have hrone : r = 1 := by omega
          subst r
          have hslope : (d.slope : ℝ) ≤ 1 := by exact_mod_cast d.hslope_one
          simpa only [iteratedDeriv_one] using
            (norm_deriv_graphIterate_le d n u).trans (hslope.trans hB)

/-- Helper for cm-center-proposition: the source bunching inequalities through
eight give C⁸ exact graph-transform iterates with one common derivative bound.
Neither uniform derivative bounds nor a smooth invariant graph are inputs. -/
theorem graphIterate_uniformC8 (d : MetricGraphTransformData X) (hν : 8 ≤ d.nu)
    (hbunching : ∀ r : ℕ, 2 ≤ r → r ≤ 8 →
      ((d.linearRate : ℝ) + (d.epsilon : ℝ) * (1 + (d.slope : ℝ))) *
        (d.lower : ℝ)⁻¹ ^ r < 1) :
    ∃ B : ℝ≥0, 1 ≤ B ∧
      (∀ n : ℕ, ContDiff ℝ 8 (graphIterate d n : ℝ → X)) ∧
      ∀ n r : ℕ, r ≤ 8 → ∀ u : ℝ,
        ‖iteratedDeriv r (graphIterate d n : ℝ → X) u‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := graphIterate_uniformDerivativeBounds d 8 hν hbunching
  have hBzero : 0 ≤ B := zero_le_one.trans hB
  let Bnn : ℝ≥0 := ⟨B, hBzero⟩
  have hBnn : (1 : ℝ≥0) ≤ Bnn := by exact_mod_cast hB
  have hνTop : (8 : WithTop ℕ∞) ≤ d.nu := by exact_mod_cast hν
  exact ⟨Bnn, hBnn, fun n ↦ (graphIterate_contDiff d n).of_le hνTop, hbound⟩

/-- Helper for cm-center-proposition: uniform C⁸ iterates and the SAME transform's
C⁰ limit give C⁷ regularity by finite-jet Arzelà–Ascoli, as in the manuscript. -/
theorem graphLimit_contDiff_seven [ProperSpace X]
    (d : MetricGraphTransformData X) (hν : 8 ≤ d.nu)
    (hbunching : ∀ r : ℕ, 2 ≤ r → r ≤ 8 →
      ((d.linearRate : ℝ) + (d.epsilon : ℝ) * (1 + (d.slope : ℝ))) *
        (d.lower : ℝ)⁻¹ ^ r < 1) :
    ContDiff ℝ 7 (graphLimit d : ℝ → X) := by
  obtain ⟨B, _, hsmooth, hbound⟩ := graphIterate_uniformC8 d hν hbunching
  apply contDiff_iff_contDiffAt.mpr
  intro u
  have hlocal := contDiffOn_of_uniformDerivativeBounds 7 (u - 1) (u + 1)
    (fun n ↦ (graphIterate d n : ℝ → X)) (graphLimit d : ℝ → X) B hsmooth
    (fun n r hr x _ ↦ hbound n r hr x)
    (fun x _ ↦ (graphIterate_tendstoUniformly d).tendsto_at x)
  have hleft : u - 1 < u := by linarith
  have hright : u < u + 1 := by linarith
  exact hlocal.contDiffAt (Ioo_mem_nhds hleft hright)

/-- Helper for cm-center-proposition: the canonical metric limit satisfies the
exact source graph equation, independently of its subsequent AA regularity. -/
theorem graphLimit_equation [CompleteSpace X] (d : MetricGraphTransformData X) (u : ℝ) :
    graphLimit d (d.centerMap (graphLimit d) u) =
      d.L (graphLimit d u) + (d.R (u, graphLimit d u)).2 := by
  simpa only [graphLimit_fixed] using transform_equation d (graphLimit d) u

/-- Helper for cm-center-proposition: after the source AA regularity step, a
zero-derivative nonlinear germ forces the resulting graph to be tangent to zero. -/
theorem graphLimit_tangent_zero [ProperSpace X]
    (d : MetricGraphTransformData X) (hν : 8 ≤ d.nu)
    (hbunching : ∀ r : ℕ, 2 ≤ r → r ≤ 8 →
      ((d.linearRate : ℝ) + (d.epsilon : ℝ) * (1 + (d.slope : ℝ))) *
        (d.lower : ℝ)⁻¹ ^ r < 1)
    (hR : HasFDerivAt d.R (0 : (ℝ × X) →L[ℝ] (ℝ × X)) (0, 0)) :
    HasFDerivAt (graphLimit d : ℝ → X) (0 : ℝ →L[ℝ] X) 0 := by
  have hone : (1 : WithTop ℕ∞) ≤ 7 := by norm_num
  have hC1 := (graphLimit_contDiff_seven d hν hbunching).of_le hone
  have hderiv := (hC1.differentiable_one 0).hasFDerivAt
  have hzero := SmallLipschitzGraph.zero_apply (graphLimit d)
  have hrate : (d.linearRate : ℝ) < 1 := by exact_mod_cast d.hlinearRate
  have hL : ‖d.L‖ < 1 := d.hL.trans_lt hrate
  have hinvariant : (fun u ↦ (metricCenterStableMap d (u, graphLimit d u)).2) =ᶠ[𝓝 0]
      fun u ↦ graphLimit d (metricCenterStableMap d (u, graphLimit d u)).1 := by
    filter_upwards [] with u
    simpa only [metricCenterStableMap_apply, MetricGraphTransformData.centerMap_eq] using
      (graphLimit_equation d u).symm
  exact tangent_zero_of_centerStable_invariant (graphLimit d : ℝ → X)
    (fderiv ℝ (graphLimit d : ℝ → X) 0) (metricCenterStableMap d) d.L hzero hderiv
    (metricCenterStableMap_zero d) (metricCenterStableMap_hasFDerivAt_of_zeroDerivative d hR)
    hinvariant hL

end LocalInvariantGraph.GraphIterateBounds
