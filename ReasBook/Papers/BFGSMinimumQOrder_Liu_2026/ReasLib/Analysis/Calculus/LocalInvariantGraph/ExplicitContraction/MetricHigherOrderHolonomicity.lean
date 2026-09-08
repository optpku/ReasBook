module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricReservedTopOperator
import all ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricReservedTopOperator
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricRawDefectEnvelope
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.ProofSupport.AffineCocycle

public section

noncomputable section

open Filter Set
open scoped NNReal Topology

universe u v

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Helper for Infrastructure I.16a: finite natural orders are unchanged by the
successor-then-predecessor operation in the `WithTop ℕ∞` regularity index. -/
theorem withTopNatCast_add_sub_one (m : ℕ) :
    (m : WithTop ℕ∞) + 1 - 1 = (m : WithTop ℕ∞) := by
  have hENat : (m : ℕ∞) + 1 - 1 = (m : ℕ∞) := by
    rw [← ENat.coe_one]
    rw [← ENat.coe_add]
    rw [← ENat.coe_sub]
    rw [Nat.add_sub_cancel]
  calc
    (m : WithTop ℕ∞) + 1 - 1 =
        ((((m : ℕ∞) + 1 - 1 : ℕ∞)) : WithTop ℕ∞) := by
      rw [← WithTop.coe_natCast m]
      rw [← WithTop.coe_one]
      rw [← WithTop.coe_add]
      rw [← WithTop.coe_sub]
    _ = (m : WithTop ℕ∞) := by
      exact congrArg (fun n : ℕ∞ => (n : WithTop ℕ∞)) hENat

/-- Helper for Infrastructure I.16a: the reserved-top coefficient at every order at least two is
`C¹` once the graph is `C^m`. -/
theorem metricReservedTopCoefficient_contDiff_one_of_previousOrder
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {m : ℕ} (hm : 2 ≤ m)
    (hprev : ContDiff ℝ m (ζ : ℝ → X)) :
    ContDiff ℝ 1 (metricReservedTopCoefficient d ζ m) := by
  have hone_nat : 1 ≤ m := by
    omega
  have hone : (1 : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast hone_nat
  have htwo : (2 : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast hm
  have htwo_nu : (2 : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast d.hnu
  have hone_two : (1 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞) := by
    norm_num
  have hderivative_order :
      (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞) := by
    norm_num
  have hζ_one : ContDiff ℝ 1 (ζ : ℝ → X) := hprev.of_le hone
  have hζ_two : ContDiff ℝ 2 (ζ : ℝ → X) := hprev.of_le htwo
  have hcenter_two : ContDiff ℝ 2 (d.centerMap ζ) :=
    centerMap_contDiff_of_prev d ζ htwo_nu hζ_two
  have hcenter_one : ContDiff ℝ 1 (d.centerMap ζ) :=
    hcenter_two.of_le hone_two
  have hcenter_deriv : ContDiff ℝ 1 (deriv (d.centerMap ζ)) := by
    have hiterated :=
      (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp hcenter_two).2
    simpa only [iteratedDeriv_one] using hiterated
  have hcenter_deriv_ne : ∀ x, deriv (d.centerMap ζ) x ≠ 0 :=
    fun x ↦ centerMap_deriv_ne_zero d ζ hζ_one x
  have hcenter_deriv_inv :
      ContDiff ℝ 1 (fun x ↦ (deriv (d.centerMap ζ) x)⁻¹) :=
    hcenter_deriv.inv hcenter_deriv_ne
  have hscale :
      ContDiff ℝ 1 (fun x ↦ (deriv (d.centerMap ζ) x)⁻¹ ^ m) :=
    hcenter_deriv_inv.pow m
  have hζ_deriv : ContDiff ℝ 1 (deriv (ζ : ℝ → X)) := by
    have hiterated :=
      (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp hζ_two).2
    simpa only [iteratedDeriv_one] using hiterated
  have hζ_deriv_center :
      ContDiff ℝ 1 (fun x ↦ deriv (ζ : ℝ → X) (d.centerMap ζ x)) :=
    hζ_deriv.comp hcenter_one
  have hR_two : ContDiff ℝ 2 d.R := d.hR_smooth.of_le htwo_nu
  have hR_fderiv : ContDiff ℝ 1 (fderiv ℝ d.R) :=
    hR_two.fderiv_right hderivative_order
  have hgraph : ContDiff ℝ 1 (fun x : ℝ ↦ (x, (ζ : ℝ → X) x)) :=
    contDiff_id.prodMk hζ_one
  have hfderiv_graph :
      ContDiff ℝ 1 (fun x ↦ fderiv ℝ d.R (x, (ζ : ℝ → X) x)) :=
    hR_fderiv.comp hgraph
  have hinr : ContDiff ℝ 1
      (fun _ : ℝ ↦ ContinuousLinearMap.inr ℝ ℝ X) := contDiff_const
  have hinner : ContDiff ℝ 1 (fun x ↦
      (fderiv ℝ d.R (x, (ζ : ℝ → X) x)).comp
        (ContinuousLinearMap.inr ℝ ℝ X)) :=
    hfderiv_graph.clm_comp hinr
  have hsnd : ContDiff ℝ 1
      (fun _ : ℝ ↦ ContinuousLinearMap.snd ℝ ℝ X) := contDiff_const
  have hfst : ContDiff ℝ 1
      (fun _ : ℝ ↦ ContinuousLinearMap.fst ℝ ℝ X) := contDiff_const
  have hderivFiber : ContDiff ℝ 1 (fun x ↦ derivFiber d ζ x) := by
    have hcomposed := hsnd.clm_comp hinner
    have heq : (fun x ↦ derivFiber d ζ x) =
        (fun x ↦ ContinuousLinearMap.snd ℝ ℝ X ∘SL
          (fderiv ℝ d.R (x, (ζ : ℝ → X) x)) ∘SL
            ContinuousLinearMap.inr ℝ ℝ X) := by
      funext x
      apply ContinuousLinearMap.ext
      intro w
      exact derivFiber_apply d ζ x w
    rw [heq]
    exact hcomposed
  have hderivCenterFiber :
      ContDiff ℝ 1 (fun x ↦ derivCenterFiber d ζ x) := by
    have hcomposed := hfst.clm_comp hinner
    have heq : (fun x ↦ derivCenterFiber d ζ x) =
        (fun x ↦ ContinuousLinearMap.fst ℝ ℝ X ∘SL
          (fderiv ℝ d.R (x, (ζ : ℝ → X) x)) ∘SL
            ContinuousLinearMap.inr ℝ ℝ X) := by
      funext x
      apply ContinuousLinearMap.ext
      intro w
      exact derivCenterFiber_apply d ζ x w
    rw [heq]
    exact hcomposed
  have hcurried : ContDiff ℝ 1 (fun x ↦
      ContinuousLinearMap.smulRightL ℝ X X (derivCenterFiber d ζ x)) :=
    (ContinuousLinearMap.smulRightL ℝ X X).contDiff.comp hderivCenterFiber
  have hfeedback : ContDiff ℝ 1 (fun x ↦
      (derivCenterFiber d ζ x).smulRight
        (deriv (ζ : ℝ → X) (d.centerMap ζ x))) :=
    hcurried.clm_apply hζ_deriv_center
  have hcocycle : ContDiff ℝ 1 (fun x ↦ d.L + derivFiber d ζ x) :=
    contDiff_const.add hderivFiber
  have hbracket : ContDiff ℝ 1 (fun x ↦
      d.L + derivFiber d ζ x -
        (derivCenterFiber d ζ x).smulRight
          (deriv (ζ : ℝ → X) (d.centerMap ζ x))) :=
    hcocycle.sub hfeedback
  unfold metricReservedTopCoefficient
  exact hscale.smul hbracket

/-- Helper for Infrastructure I.16a: on a fixed graph, the reserved-top coefficient differs
from its exterior constant value `d.L` only on a compact set. -/
theorem metricReservedTopCoefficient_sub_linear_hasCompactSupport
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m)
    (hprev : ContDiff ℝ m (ζ : ℝ → X)) :
    HasCompactSupport (fun x ↦ metricReservedTopCoefficient d ζ m x - d.L) := by
  let KR : Set ℝ := Prod.fst '' tsupport d.R
  let Kζ : Set ℝ := d.inverseCenter ζ '' tsupport (ζ : ℝ → X)
  have hKR : IsCompact KR :=
    d.hR_support.image continuous_fst
  have hKζ : IsCompact Kζ := by
    have hinverse : Continuous (d.inverseCenter ζ) :=
      (d.inverseCenter_lipschitzWith ζ).continuous
    exact (fixedGraph_hasCompactSupport d ζ hfixed).image hinverse
  have hone_nat : 1 ≤ m := by
    omega
  have hone : (1 : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast hone_nat
  have hζ_one : ContDiff ℝ 1 (ζ : ℝ → X) :=
    hprev.of_le hone
  apply HasCompactSupport.intro (hKR.union hKζ)
  intro x hx
  have hxKR : x ∉ KR :=
    fun hxmem ↦ hx (Or.inl hxmem)
  have hxKζ : x ∉ Kζ :=
    fun hxmem ↦ hx (Or.inr hxmem)
  have hgraph : (x, (ζ : ℝ → X) x) ∉ tsupport d.R := by
    intro hmem
    apply hxKR
    exact ⟨(x, (ζ : ℝ → X) x), hmem, rfl⟩
  have hcenter : d.centerMap ζ x ∉ tsupport (ζ : ℝ → X) := by
    intro hmem
    apply hxKζ
    refine ⟨d.centerMap ζ x, hmem, ?_⟩
    rw [d.inverseCenter_eq ζ]
    exact Function.leftInverse_invFun (d.centerMap_bijective ζ).1 x
  have hgraph_continuous :
      Continuous (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) :=
    continuous_id.prodMk hζ_one.continuous
  have hR_graph :
      (fun y : ℝ ↦ d.R (y, (ζ : ℝ → X) y)) =ᶠ[nhds x]
        (fun _ : ℝ ↦ (0 : ℝ × X)) := by
    have hopen : IsOpen (tsupport d.R)ᶜ :=
      (isClosed_tsupport d.R).isOpen_compl
    have hgraph_compl :
        (x, (ζ : ℝ → X) x) ∈ (tsupport d.R)ᶜ :=
      hgraph
    have hnear :
        ∀ᶠ y in nhds x, (y, (ζ : ℝ → X) y) ∈ (tsupport d.R)ᶜ :=
      hgraph_continuous.continuousAt (hopen.mem_nhds hgraph_compl)
    filter_upwards [hnear] with y hy
    have hy_not : (y, (ζ : ℝ → X) y) ∉ tsupport d.R := by
      simpa only [mem_compl_iff] using hy
    exact image_eq_zero_of_notMem_tsupport hy_not
  have hcenter_local :
      d.centerMap ζ =ᶠ[nhds x] (fun y : ℝ ↦ y) := by
    filter_upwards [hR_graph] with y hy
    have hcenter_eq : d.centerMap ζ y = y := by
      rw [d.centerMap_eq ζ]
      simp only [hy, Prod.fst_zero, add_zero]
    exact hcenter_eq
  have hcenter_deriv : deriv (d.centerMap ζ) x = 1 := by
    exact ((hcenter_local.hasDerivAt_iff).mpr (hasDerivAt_id x)).deriv
  have hζ_local :
      (ζ : ℝ → X) =ᶠ[nhds (d.centerMap ζ x)] (fun _ : ℝ ↦ (0 : X)) :=
    fixedGraph_eventuallyEq_zero_of_notMem_tsupport ζ hcenter
  have hζ_deriv :
      deriv (ζ : ℝ → X) (d.centerMap ζ x) = 0 := by
    exact ((hζ_local.hasDerivAt_iff).mpr
      (hasDerivAt_const (d.centerMap ζ x) (0 : X))).deriv
  have hR_fderiv :
      fderiv ℝ d.R (x, (ζ : ℝ → X) x) = 0 :=
    fderiv_of_notMem_tsupport ℝ hgraph
  have hderivFiber_zero : derivFiber d ζ x = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    rw [derivFiber_apply, hR_fderiv]
    simp only [ContinuousLinearMap.zero_apply, Prod.fst_zero, Prod.snd_zero]
  have hderivCenterFiber_zero : derivCenterFiber d ζ x = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    rw [derivCenterFiber_apply, hR_fderiv]
    simp only [ContinuousLinearMap.zero_apply, Prod.fst_zero, Prod.snd_zero]
  rw [metricReservedTopCoefficient.eq_1, hcenter_deriv,
    hderivFiber_zero, hderivCenterFiber_zero, hζ_deriv]
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.zero_apply, inv_one, one_pow, one_smul, zero_smul,
    smul_zero, add_zero, sub_zero, sub_self]

/-- Helper for Infrastructure I.16a: the derivative of the reserved-top coefficient has compact
support because subtracting its exterior constant value does not change its derivative. -/
theorem metricReservedTopCoefficient_deriv_hasCompactSupport
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m)
    (hprev : ContDiff ℝ m (ζ : ℝ → X)) :
    HasCompactSupport (deriv (metricReservedTopCoefficient d ζ m)) := by
  have hsupport :=
    (metricReservedTopCoefficient_sub_linear_hasCompactSupport
      d ζ hfixed hm hprev).deriv
  simpa only [deriv_sub_const_fun] using hsupport

/-- Helper for Infrastructure I.16a: the derivative of the reserved-top coefficient is uniformly
continuous on the whole source line. -/
theorem uniformContinuous_metricReservedTopCoefficient_deriv
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m)
    (hprev : ContDiff ℝ m (ζ : ℝ → X)) :
    UniformContinuous (deriv (metricReservedTopCoefficient d ζ m)) := by
  have hcoefficient :
      ContDiff ℝ 1 (metricReservedTopCoefficient d ζ m) :=
    metricReservedTopCoefficient_contDiff_one_of_previousOrder d ζ hm hprev
  have hcontinuous :
      Continuous (deriv (metricReservedTopCoefficient d ζ m)) := by
    have hiterated := hcoefficient.continuous_iteratedDeriv 1 le_rfl
    simpa only [iteratedDeriv_one] using hiterated
  have hsupport :
      HasCompactSupport (deriv (metricReservedTopCoefficient d ζ m)) :=
    metricReservedTopCoefficient_deriv_hasCompactSupport
      d ζ hfixed hm hprev
  exact hcontinuous.uniformContinuous_of_tendsto_cocompact
    hsupport.is_zero_at_infty

/-- Helper for Infrastructure I.16a: on a fixed graph, the derivative of the lower-order
reserved-top forcing has compact support. -/
theorem metricReservedTopForcing_deriv_hasCompactSupport
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    (r : ℕ) :
    HasCompactSupport (deriv (metricReservedTopForcing d ζ r)) := by
  exact (metricReservedTopForcing_hasCompactSupport d ζ hfixed r).deriv

/-- Helper for Infrastructure I.16a: at every nontrivial predecessor order, the derivative of
the lower-order reserved-top forcing is uniformly continuous on the whole source line. -/
theorem uniformContinuous_metricReservedTopForcing_deriv
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {r : ℕ} (hr : 2 ≤ r) (hrν : r + 1 ≤ d.nu)
    (hprev : ContDiff ℝ r (ζ : ℝ → X)) :
    UniformContinuous (deriv (metricReservedTopForcing d ζ r)) := by
  have hforcing : ContDiff ℝ 1 (metricReservedTopForcing d ζ r) :=
    metricReservedTopForcing_contDiff_one d ζ hr hrν hprev
  have hcontinuous :
      Continuous (deriv (metricReservedTopForcing d ζ r)) := by
    have hiterated := hforcing.continuous_iteratedDeriv 1 le_rfl
    simpa only [iteratedDeriv_one] using hiterated
  have hsupport :
      HasCompactSupport (deriv (metricReservedTopForcing d ζ r)) :=
    metricReservedTopForcing_deriv_hasCompactSupport d ζ hfixed r
  exact hcontinuous.uniformContinuous_of_tendsto_cocompact
    hsupport.is_zero_at_infty

/-- Helper for Infrastructure I.16a: multiplying the predecessor coefficient by the inverse
center derivative gives exactly the successor reserved-top coefficient. -/
theorem inverseCenterDerivative_smul_metricReservedTopCoefficient
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (m : ℕ) (x : ℝ) :
    (deriv (d.centerMap ζ) x)⁻¹ •
        metricReservedTopCoefficient d ζ m x =
      metricReservedTopCoefficient d ζ (m + 1) x := by
  simp only [metricReservedTopCoefficient, pow_succ, smul_smul, mul_comm]

/-- Helper for Infrastructure I.16a: the inhomogeneous term obtained by differentiating the
order-`m` affine source equation and dividing by the center derivative. -/
def metricReservedTopDerivativeForcing
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (m : ℕ) (x : ℝ) : X :=
  (deriv (d.centerMap ζ) x)⁻¹ •
    (deriv (metricReservedTopCoefficient d ζ m) x
        (iteratedDeriv m (ζ : ℝ → X) x) +
      deriv (metricReservedTopForcing d ζ m) x)

/-- Helper for Infrastructure I.16a: the differentiated lower-order affine forcing is continuous
when the graph has the full predecessor regularity. -/
theorem metricReservedTopDerivativeForcing_continuous
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X)) :
    Continuous (metricReservedTopDerivativeForcing d ζ m) := by
  have hone_nat : 1 ≤ m := by
    omega
  have hone : (1 : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast hone_nat
  have hζ_one : ContDiff ℝ 1 (ζ : ℝ → X) :=
    hprev.of_le hone
  have hscale_pow :
      Continuous (fun x ↦ (deriv (d.centerMap ζ) x)⁻¹ ^ 1) :=
    centerMap_deriv_inv_pow_continuous d ζ hζ_one 1
  have hscale :
      Continuous (fun x ↦ (deriv (d.centerMap ζ) x)⁻¹) := by
    simpa only [pow_one] using hscale_pow
  have hcoefficient_deriv :
      Continuous (deriv (metricReservedTopCoefficient d ζ m)) := by
    exact (metricReservedTopCoefficient_contDiff_one_of_previousOrder
      d ζ hm hprev).continuous_deriv le_rfl
  have hpredecessor :
      Continuous (iteratedDeriv m (ζ : ℝ → X)) :=
    hprev.continuous_iteratedDeriv m le_rfl
  have hcoefficient_term : Continuous (fun x ↦
      deriv (metricReservedTopCoefficient d ζ m) x
        (iteratedDeriv m (ζ : ℝ → X) x)) :=
    hcoefficient_deriv.clm_apply hpredecessor
  have hforcing_deriv :
      Continuous (deriv (metricReservedTopForcing d ζ m)) := by
    exact (metricReservedTopForcing_contDiff_one
      d ζ hm hmν hprev).continuous_deriv le_rfl
  unfold metricReservedTopDerivativeForcing
  exact hscale.smul (hcoefficient_term.add hforcing_deriv)

/-- Helper for Infrastructure I.16a: the differentiated affine forcing has compact support on a
fixed graph. -/
theorem metricReservedTopDerivativeForcing_hasCompactSupport
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m)
    (hprev : ContDiff ℝ m (ζ : ℝ → X)) :
    HasCompactSupport (metricReservedTopDerivativeForcing d ζ m) := by
  have hcoefficient_deriv :
      HasCompactSupport (deriv (metricReservedTopCoefficient d ζ m)) :=
    metricReservedTopCoefficient_deriv_hasCompactSupport
      d ζ hfixed hm hprev
  have hcoefficient_term : HasCompactSupport (fun x ↦
      deriv (metricReservedTopCoefficient d ζ m) x
        (iteratedDeriv m (ζ : ℝ → X) x)) := by
    apply HasCompactSupport.intro hcoefficient_deriv
    intro x hx
    have hzero :
        deriv (metricReservedTopCoefficient d ζ m) x = 0 :=
      image_eq_zero_of_notMem_tsupport hx
    rw [hzero]
    exact zero_apply _
  have hforcing_deriv :
      HasCompactSupport (deriv (metricReservedTopForcing d ζ m)) :=
    metricReservedTopForcing_deriv_hasCompactSupport d ζ hfixed m
  have hsum : HasCompactSupport (fun x ↦
      deriv (metricReservedTopCoefficient d ζ m) x
          (iteratedDeriv m (ζ : ℝ → X) x) +
        deriv (metricReservedTopForcing d ζ m) x) :=
    hcoefficient_term.add hforcing_deriv
  unfold metricReservedTopDerivativeForcing
  exact hsum.smul_left

/-- Helper for Infrastructure I.16a: compact support and continuity give a nonnegative uniform
bound for the differentiated affine forcing. -/
theorem exists_metricReservedTopDerivativeForcing_norm_bound
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, ‖metricReservedTopDerivativeForcing d ζ m x‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (metricReservedTopDerivativeForcing_continuous
      d ζ hfixed hm hmν hprev).bounded_above_of_compact_support
        (metricReservedTopDerivativeForcing_hasCompactSupport
          d ζ hfixed hm hprev)
  have hC_nonneg : 0 ≤ C :=
    (norm_nonneg (metricReservedTopDerivativeForcing d ζ m 0)).trans
      (hC 0)
  exact ⟨C, hC_nonneg, hC⟩

/-- Helper for Infrastructure I.16a: a selected nonnegative uniform bound for the differentiated
affine forcing. -/
noncomputable def metricReservedTopDerivativeForcingBound
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X)) : ℝ :=
  Classical.choose
    (exists_metricReservedTopDerivativeForcing_norm_bound
      d ζ hfixed hm hmν hprev)

/-- Helper for Infrastructure I.16a: the selected derivative-forcing bound is nonnegative. -/
theorem metricReservedTopDerivativeForcingBound_nonneg
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X)) :
    0 ≤ metricReservedTopDerivativeForcingBound
      d ζ hfixed hm hmν hprev := by
  exact (Classical.choose_spec
    (exists_metricReservedTopDerivativeForcing_norm_bound
      d ζ hfixed hm hmν hprev)).1

/-- Helper for Infrastructure I.16a: the selected derivative-forcing bound controls every source
value. -/
theorem norm_metricReservedTopDerivativeForcing_le_bound
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X)) (x : ℝ) :
    ‖metricReservedTopDerivativeForcing d ζ m x‖ ≤
      metricReservedTopDerivativeForcingBound
        d ζ hfixed hm hmν hprev := by
  exact (Classical.choose_spec
    (exists_metricReservedTopDerivativeForcing_norm_bound
      d ζ hfixed hm hmν hprev)).2 x

/-- Helper for Infrastructure I.16a: the differentiated affine forcing bundled as a bounded
continuous source-coordinate section. -/
def metricReservedTopDerivativeForcingSection
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X)) :
    BoundedContinuousFunction ℝ X :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (metricReservedTopDerivativeForcing d ζ m)
    (metricReservedTopDerivativeForcing_continuous
      d ζ hfixed hm hmν hprev)
    (metricReservedTopDerivativeForcingBound
      d ζ hfixed hm hmν hprev)
    (norm_metricReservedTopDerivativeForcing_le_bound
      d ζ hfixed hm hmν hprev)

/-- Helper for Infrastructure I.16a: evaluating the bundled differentiated forcing recovers its
source-coordinate formula. -/
theorem metricReservedTopDerivativeForcingSection_apply
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X)) (x : ℝ) :
    metricReservedTopDerivativeForcingSection
        d ζ hfixed hm hmν hprev x =
      metricReservedTopDerivativeForcing d ζ m x := by
  rfl

/-- Helper for Infrastructure I.16a: the inverse center map cancels the center map in source
coordinates. -/
theorem metricInverseCenter_centerMap
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (x : ℝ) :
    d.inverseCenter ζ (d.centerMap ζ x) = x := by
  rw [d.inverseCenter_eq ζ]
  exact Function.leftInverse_invFun (d.centerMap_bijective ζ).1 x

/-- Helper for Infrastructure I.16a: the output-coordinate value of the differentiated
predecessor affine operator. -/
def metricReservedTopDerivativeOperatorValue
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (m : ℕ) (b : BoundedContinuousFunction ℝ X) (y : ℝ) : X :=
  metricReservedTopCoefficient d ζ (m + 1) (d.inverseCenter ζ y)
      (b (d.inverseCenter ζ y)) +
    metricReservedTopDerivativeForcing d ζ m (d.inverseCenter ζ y)

/-- Helper for Infrastructure I.16a: the differentiated predecessor affine operator has a
continuous output-coordinate value. -/
theorem metricReservedTopDerivativeOperatorValue_continuous
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (b : BoundedContinuousFunction ℝ X) :
    Continuous (metricReservedTopDerivativeOperatorValue d ζ m b) := by
  have hsuccessor : 2 ≤ m + 1 := by
    exact le_trans hm (Nat.le_succ m)
  have hprev_successor :
      ContDiff ℝ (m + 1 - 1) (ζ : ℝ → X) := by
    have horder : (m : WithTop ℕ∞) + 1 - 1 = (m : WithTop ℕ∞) :=
      withTopNatCast_add_sub_one m
    rw [horder]
    exact hprev
  have hinverse : Continuous (d.inverseCenter ζ) :=
    (d.inverseCenter_lipschitzWith ζ).continuous
  have hcoefficient : Continuous (fun y ↦
      metricReservedTopCoefficient d ζ (m + 1)
        (d.inverseCenter ζ y)) :=
    (metricReservedTopCoefficient_continuous
      d ζ hsuccessor hprev_successor).comp hinverse
  have hsection : Continuous (fun y ↦ b (d.inverseCenter ζ y)) :=
    b.continuous.comp hinverse
  have hlinear : Continuous (fun y ↦
      metricReservedTopCoefficient d ζ (m + 1)
          (d.inverseCenter ζ y) (b (d.inverseCenter ζ y))) :=
    hcoefficient.clm_apply hsection
  have hforcing : Continuous (fun y ↦
      metricReservedTopDerivativeForcing d ζ m
        (d.inverseCenter ζ y)) :=
    (metricReservedTopDerivativeForcing_continuous
      d ζ hfixed hm hmν hprev).comp hinverse
  exact hlinear.add hforcing

/-- Helper for Infrastructure I.16a: the differentiated affine operator value is bounded by the
successor contraction factor and the bundled differentiated forcing. -/
theorem norm_metricReservedTopDerivativeOperatorValue_le
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (b : BoundedContinuousFunction ℝ X) (y : ℝ) :
    ‖metricReservedTopDerivativeOperatorValue d ζ m b y‖ ≤
      (metricReservedTopFactor d (m + 1) : ℝ) * ‖b‖ +
        ‖metricReservedTopDerivativeForcingSection
          d ζ hfixed hm hmν hprev‖ := by
  let x := d.inverseCenter ζ y
  have hsuccessor : 2 ≤ m + 1 := by
    exact le_trans hm (Nat.le_succ m)
  have hprev_successor :
      ContDiff ℝ (m + 1 - 1) (ζ : ℝ → X) := by
    have horder : (m : WithTop ℕ∞) + 1 - 1 = (m : WithTop ℕ∞) :=
      withTopNatCast_add_sub_one m
    rw [horder]
    exact hprev
  have hcoefficient :
      ‖metricReservedTopCoefficient d ζ (m + 1) x‖ ≤
        (metricReservedTopFactor d (m + 1) : ℝ) :=
    norm_metricReservedTopCoefficient_le_factor
      d ζ hfixed hsuccessor hprev_successor x
  have hb : ‖b x‖ ≤ ‖b‖ :=
    BoundedContinuousFunction.norm_coe_le_norm b x
  have hfactor_nonneg :
      0 ≤ (metricReservedTopFactor d (m + 1) : ℝ) :=
    metricReservedTopFactor_nonneg d (m + 1)
  have hlinear :
      ‖metricReservedTopCoefficient d ζ (m + 1) x (b x)‖ ≤
        (metricReservedTopFactor d (m + 1) : ℝ) * ‖b‖ := by
    calc
      ‖metricReservedTopCoefficient d ζ (m + 1) x (b x)‖ ≤
          ‖metricReservedTopCoefficient d ζ (m + 1) x‖ * ‖b x‖ :=
        (metricReservedTopCoefficient d ζ (m + 1) x).le_opNorm _
      _ ≤ (metricReservedTopFactor d (m + 1) : ℝ) * ‖b x‖ :=
        mul_le_mul_of_nonneg_right hcoefficient (norm_nonneg _)
      _ ≤ (metricReservedTopFactor d (m + 1) : ℝ) * ‖b‖ :=
        mul_le_mul_of_nonneg_left hb hfactor_nonneg
  have hforcing :
      ‖metricReservedTopDerivativeForcing d ζ m x‖ ≤
        ‖metricReservedTopDerivativeForcingSection
          d ζ hfixed hm hmν hprev‖ := by
    exact BoundedContinuousFunction.norm_coe_le_norm
      (metricReservedTopDerivativeForcingSection
        d ζ hfixed hm hmν hprev) x
  unfold metricReservedTopDerivativeOperatorValue
  exact (norm_add_le _ _).trans (add_le_add hlinear hforcing)

/-- Helper for Infrastructure I.16a: the uniform bound used to bundle the differentiated affine
operator is nonnegative. -/
theorem metricReservedTopDerivativeOperatorValue_bound_nonneg
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (b : BoundedContinuousFunction ℝ X) :
    0 ≤ (metricReservedTopFactor d (m + 1) : ℝ) * ‖b‖ +
      ‖metricReservedTopDerivativeForcingSection
        d ζ hfixed hm hmν hprev‖ := by
  positivity

/-- Helper for Infrastructure I.16a: the differentiated predecessor affine operator on bounded
continuous sections, evaluated in output coordinates through `d.inverseCenter ζ`. -/
def metricReservedTopDerivativeOperator
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (b : BoundedContinuousFunction ℝ X) :
    BoundedContinuousFunction ℝ X :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (metricReservedTopDerivativeOperatorValue d ζ m b)
    (metricReservedTopDerivativeOperatorValue_continuous
      d ζ hfixed hm hmν hprev b)
    ((metricReservedTopFactor d (m + 1) : ℝ) * ‖b‖ +
      ‖metricReservedTopDerivativeForcingSection
        d ζ hfixed hm hmν hprev‖)
    (norm_metricReservedTopDerivativeOperatorValue_le
      d ζ hfixed hm hmν hprev b)

/-- Helper for Infrastructure I.16a: evaluation of the bundled differentiated affine operator
exposes its output-coordinate formula. -/
theorem metricReservedTopDerivativeOperator_apply
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (b : BoundedContinuousFunction ℝ X) (y : ℝ) :
    metricReservedTopDerivativeOperator
        d ζ hfixed hm hmν hprev b y =
      metricReservedTopCoefficient d ζ (m + 1)
          (d.inverseCenter ζ y) (b (d.inverseCenter ζ y)) +
        metricReservedTopDerivativeForcing d ζ m
          (d.inverseCenter ζ y) := by
  rfl

/-- Helper for Infrastructure I.16a: in source coordinates, the differentiated affine operator
has its untranslated coefficient-plus-forcing formula. -/
theorem metricReservedTopDerivativeOperator_apply_centerMap
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (b : BoundedContinuousFunction ℝ X) (x : ℝ) :
    metricReservedTopDerivativeOperator
        d ζ hfixed hm hmν hprev b (d.centerMap ζ x) =
      metricReservedTopCoefficient d ζ (m + 1) x (b x) +
        metricReservedTopDerivativeForcing d ζ m x := by
  rw [metricReservedTopDerivativeOperator_apply,
    metricInverseCenter_centerMap]

/-- Helper for Infrastructure I.16a: the differentiated affine operator has the successor
reserved-top contraction factor pointwise. -/
theorem metricReservedTopDerivativeOperator_dist_apply_le
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (b c : BoundedContinuousFunction ℝ X) (y : ℝ) :
    dist
        (metricReservedTopDerivativeOperator
          d ζ hfixed hm hmν hprev b y)
        (metricReservedTopDerivativeOperator
          d ζ hfixed hm hmν hprev c y) ≤
      (metricReservedTopFactor d (m + 1) : ℝ) * dist b c := by
  let x := d.inverseCenter ζ y
  have hsuccessor : 2 ≤ m + 1 := by
    exact le_trans hm (Nat.le_succ m)
  have hprev_successor :
      ContDiff ℝ (m + 1 - 1) (ζ : ℝ → X) := by
    have horder : (m : WithTop ℕ∞) + 1 - 1 = (m : WithTop ℕ∞) :=
      withTopNatCast_add_sub_one m
    rw [horder]
    exact hprev
  have hcoefficient :
      ‖metricReservedTopCoefficient d ζ (m + 1) x‖ ≤
        (metricReservedTopFactor d (m + 1) : ℝ) :=
    norm_metricReservedTopCoefficient_le_factor
      d ζ hfixed hsuccessor hprev_successor x
  have heval : dist (b x) (c x) ≤ dist b c :=
    BoundedContinuousFunction.dist_coe_le_dist (f := b) (g := c) x
  have hfactor_nonneg :
      0 ≤ (metricReservedTopFactor d (m + 1) : ℝ) :=
    metricReservedTopFactor_nonneg d (m + 1)
  rw [metricReservedTopDerivativeOperator_apply,
    metricReservedTopDerivativeOperator_apply, dist_eq_norm]
  have hdifference :
      metricReservedTopCoefficient d ζ (m + 1) x (b x) +
          metricReservedTopDerivativeForcing d ζ m x -
        (metricReservedTopCoefficient d ζ (m + 1) x (c x) +
          metricReservedTopDerivativeForcing d ζ m x) =
        metricReservedTopCoefficient d ζ (m + 1) x (b x - c x) := by
    rw [map_sub]
    module
  rw [hdifference]
  calc
    ‖metricReservedTopCoefficient d ζ (m + 1) x (b x - c x)‖ ≤
        ‖metricReservedTopCoefficient d ζ (m + 1) x‖ *
          ‖b x - c x‖ :=
      (metricReservedTopCoefficient d ζ (m + 1) x).le_opNorm _
    _ ≤ (metricReservedTopFactor d (m + 1) : ℝ) * ‖b x - c x‖ :=
      mul_le_mul_of_nonneg_right hcoefficient (norm_nonneg _)
    _ ≤ (metricReservedTopFactor d (m + 1) : ℝ) * dist b c := by
      rw [← dist_eq_norm]
      exact mul_le_mul_of_nonneg_left heval hfactor_nonneg

/-- Helper for Infrastructure I.16a: successor bunching makes the differentiated predecessor
affine operator a contraction. -/
theorem metricReservedTopDerivativeOperator_contractingWith
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ (m + 1) < 1) :
    ContractingWith (metricReservedTopFactor d (m + 1))
      (metricReservedTopDerivativeOperator
        d ζ hfixed hm hmν hprev) := by
  have hfactor_lt_one_real :
      (metricReservedTopFactor d (m + 1) : ℝ) < 1 := by
    rw [metricReservedTopFactor_coe]
    exact h_bunching
  have hfactor_lt_one :
      metricReservedTopFactor d (m + 1) < 1 := by
    exact_mod_cast hfactor_lt_one_real
  refine ⟨hfactor_lt_one, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro b c
  apply BoundedContinuousFunction.dist_le_iff_of_nonempty.mpr
  intro y
  exact metricReservedTopDerivativeOperator_dist_apply_le
    d ζ hfixed hm hmν hprev b c y

/-- Helper for Infrastructure I.16a: the canonical differentiated predecessor section is the
fixed point of its inverse-center affine operator. -/
noncomputable def metricReservedTopDerivativeFixedSection
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ (m + 1) < 1) :
    BoundedContinuousFunction ℝ X :=
  ContractingWith.fixedPoint
    (metricReservedTopDerivativeOperator
      d ζ hfixed hm hmν hprev)
    (metricReservedTopDerivativeOperator_contractingWith
      d ζ hfixed hm hmν hprev h_bunching)

/-- Helper for Infrastructure I.16a: the canonical differentiated predecessor section satisfies
its affine fixed-point equation. -/
theorem metricReservedTopDerivativeFixedSection_is_fixed
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ (m + 1) < 1) :
    metricReservedTopDerivativeOperator d ζ hfixed hm hmν hprev
        (metricReservedTopDerivativeFixedSection
          d ζ hfixed hm hmν hprev h_bunching) =
      metricReservedTopDerivativeFixedSection
        d ζ hfixed hm hmν hprev h_bunching := by
  exact (metricReservedTopDerivativeOperator_contractingWith
    d ζ hfixed hm hmν hprev h_bunching).fixedPoint_isFixedPt

/-- Helper for Infrastructure I.16a: every bounded fixed section of the differentiated affine
operator is its canonical fixed section. -/
theorem metricReservedTopDerivativeFixedSection_unique
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ (m + 1) < 1)
    (b : BoundedContinuousFunction ℝ X)
    (hb : metricReservedTopDerivativeOperator
      d ζ hfixed hm hmν hprev b = b) :
    b = metricReservedTopDerivativeFixedSection
      d ζ hfixed hm hmν hprev h_bunching := by
  exact (metricReservedTopDerivativeOperator_contractingWith
    d ζ hfixed hm hmν hprev h_bunching).fixedPoint_unique hb

/-- Helper for Infrastructure I.16a: in source coordinates, the canonical differentiated section
obeys the differentiated predecessor affine equation. -/
theorem metricReservedTopDerivativeFixedSection_sourceEquation
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ (m + 1) < 1)
    (x : ℝ) :
    metricReservedTopDerivativeFixedSection
        d ζ hfixed hm hmν hprev h_bunching (d.centerMap ζ x) =
      metricReservedTopCoefficient d ζ (m + 1) x
          (metricReservedTopDerivativeFixedSection
            d ζ hfixed hm hmν hprev h_bunching x) +
        metricReservedTopDerivativeForcing d ζ m x := by
  have hfixedSection :=
    metricReservedTopDerivativeFixedSection_is_fixed
      d ζ hfixed hm hmν hprev h_bunching
  have hpoint := congrArg
    (fun b : BoundedContinuousFunction ℝ X ↦
      b (d.centerMap ζ x)) hfixedSection
  rw [metricReservedTopDerivativeOperator_apply_centerMap] at hpoint
  exact hpoint.symm

/-- Helper for Infrastructure I.16a: the canonical differentiated predecessor section satisfies
the pointwise derivative equation obtained from the order-`m` affine source equation. -/
theorem metricReservedTopDerivativeFixedSection_derivativeEquation
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ (m + 1) < 1)
    (x : ℝ) :
    deriv (d.centerMap ζ) x •
        metricReservedTopDerivativeFixedSection
          d ζ hfixed hm hmν hprev h_bunching (d.centerMap ζ x) =
      deriv (metricReservedTopCoefficient d ζ m) x
          (iteratedDeriv m (ζ : ℝ → X) x) +
        metricReservedTopCoefficient d ζ m x
          (metricReservedTopDerivativeFixedSection
            d ζ hfixed hm hmν hprev h_bunching x) +
        deriv (metricReservedTopForcing d ζ m) x := by
  have hone_nat : 1 ≤ m := by
    omega
  have hone : (1 : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast hone_nat
  have hζ_one : ContDiff ℝ 1 (ζ : ℝ → X) :=
    hprev.of_le hone
  have hcenter_ne :
      deriv (d.centerMap ζ) x ≠ 0 :=
    centerMap_deriv_ne_zero d ζ hζ_one x
  have hsource :=
    metricReservedTopDerivativeFixedSection_sourceEquation
      d ζ hfixed hm hmν hprev h_bunching x
  rw [← inverseCenterDerivative_smul_metricReservedTopCoefficient
    d ζ m x] at hsource
  unfold metricReservedTopDerivativeForcing at hsource
  have hscaled := congrArg
    (fun z : X ↦ deriv (d.centerMap ζ) x • z) hsource
  simp only [ContinuousLinearMap.smul_apply, smul_add, smul_smul,
    mul_inv_cancel₀ hcenter_ne, one_smul] at hscaled
  have hreorder :
      metricReservedTopCoefficient d ζ m x
            (metricReservedTopDerivativeFixedSection
              d ζ hfixed hm hmν hprev h_bunching x) +
          (deriv (metricReservedTopCoefficient d ζ m) x
              (iteratedDeriv m (ζ : ℝ → X) x) +
            deriv (metricReservedTopForcing d ζ m) x) =
        deriv (metricReservedTopCoefficient d ζ m) x
              (iteratedDeriv m (ζ : ℝ → X) x) +
          metricReservedTopCoefficient d ζ m x
            (metricReservedTopDerivativeFixedSection
              d ζ hfixed hm hmν hprev h_bunching x) +
          deriv (metricReservedTopForcing d ζ m) x := by
    abel
  exact hscaled.trans hreorder

/-- Helper for Infrastructure I.16a: the raw first-order defect of the predecessor iterated
derivative relative to a proposed derivative section. -/
def metricReservedTopRawDefect
    (ζ : ℝ → X) (m : ℕ) (sectionFn : ℝ → X)
    (y t : ℝ) : X :=
  iteratedDeriv m ζ (y + t) - iteratedDeriv m ζ y -
    t • sectionFn y

/-- Helper for Infrastructure I.16a: every predecessor raw defect vanishes at zero increment. -/
theorem metricReservedTopRawDefect_zero
    (ζ : ℝ → X) (m : ℕ) (sectionFn : ℝ → X) (y : ℝ) :
    metricReservedTopRawDefect ζ m sectionFn y 0 = 0 := by
  simp only [metricReservedTopRawDefect, add_zero, sub_self, zero_smul, sub_zero]

/-- Helper for Infrastructure I.16a: the remainder block in the affine-cocycle decomposition of
the higher-order raw defect. -/
def metricReservedTopAffineRemainder
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (m : ℕ) (sectionFn : ℝ → X)
    (u delta s : ℝ) : X :=
  ((metricReservedTopCoefficient d ζ m (u + delta) -
        metricReservedTopCoefficient d ζ m u)
      (iteratedDeriv m (ζ : ℝ → X) u) -
    delta • deriv (metricReservedTopCoefficient d ζ m) u
      (iteratedDeriv m (ζ : ℝ → X) u)) +
  (metricReservedTopCoefficient d ζ m (u + delta) -
      metricReservedTopCoefficient d ζ m u)
    (delta • sectionFn u) +
  (metricReservedTopForcing d ζ m (u + delta) -
    metricReservedTopForcing d ζ m u -
    delta • deriv (metricReservedTopForcing d ζ m) u) +
  (deriv (d.centerMap ζ) u * delta - s) •
    sectionFn (d.centerMap ζ u)

/-- Helper for Infrastructure I.16a: separate bounds on the four Taylor components control the
whole reserved-top affine remainder. -/
theorem norm_metricReservedTopAffineRemainder_le_four_mul
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (m : ℕ) (sectionFn : ℝ → X)
    (u delta s q : ℝ)
    (hcoefficientTaylor :
      ‖(metricReservedTopCoefficient d ζ m (u + delta) -
            metricReservedTopCoefficient d ζ m u)
          (iteratedDeriv m (ζ : ℝ → X) u) -
        delta • deriv (metricReservedTopCoefficient d ζ m) u
          (iteratedDeriv m (ζ : ℝ → X) u)‖ ≤ q)
    (hcoefficientIncrement :
      ‖(metricReservedTopCoefficient d ζ m (u + delta) -
          metricReservedTopCoefficient d ζ m u)
        (delta • sectionFn u)‖ ≤ q)
    (hforcingTaylor :
      ‖metricReservedTopForcing d ζ m (u + delta) -
          metricReservedTopForcing d ζ m u -
          delta • deriv (metricReservedTopForcing d ζ m) u‖ ≤ q)
    (hcenterTaylor :
      ‖(deriv (d.centerMap ζ) u * delta - s) •
          sectionFn (d.centerMap ζ u)‖ ≤ q) :
    ‖metricReservedTopAffineRemainder
      d ζ m sectionFn u delta s‖ ≤ 4 * q := by
  let A : X :=
    (metricReservedTopCoefficient d ζ m (u + delta) -
        metricReservedTopCoefficient d ζ m u)
      (iteratedDeriv m (ζ : ℝ → X) u) -
      delta • deriv (metricReservedTopCoefficient d ζ m) u
        (iteratedDeriv m (ζ : ℝ → X) u)
  let B : X :=
    (metricReservedTopCoefficient d ζ m (u + delta) -
        metricReservedTopCoefficient d ζ m u) (delta • sectionFn u)
  let C : X :=
    metricReservedTopForcing d ζ m (u + delta) -
      metricReservedTopForcing d ζ m u -
      delta • deriv (metricReservedTopForcing d ζ m) u
  let D : X :=
    (deriv (d.centerMap ζ) u * delta - s) • sectionFn (d.centerMap ζ u)
  have hA : ‖A‖ ≤ q := by
    exact hcoefficientTaylor
  have hB : ‖B‖ ≤ q := by
    exact hcoefficientIncrement
  have hC : ‖C‖ ≤ q := by
    exact hforcingTaylor
  have hD : ‖D‖ ≤ q := by
    exact hcenterTaylor
  change ‖A + B + C + D‖ ≤ 4 * q
  calc
    ‖A + B + C + D‖ ≤ ‖A + B + C‖ + ‖D‖ := norm_add_le _ _
    _ ≤ (‖A + B‖ + ‖C‖) + ‖D‖ := by
      exact add_le_add_left (norm_add_le _ _) _
    _ ≤ ((‖A‖ + ‖B‖) + ‖C‖) + ‖D‖ := by
      exact add_le_add_left (add_le_add_left (norm_add_le _ _) _) _
    _ ≤ 4 * q := by
      linarith

/-- Helper for Infrastructure I.16a: the center map cancels the inverse center map in output
coordinates. -/
theorem metricCenterMap_inverseCenter
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (y : ℝ) :
    d.centerMap ζ (d.inverseCenter ζ y) = y := by
  rw [d.inverseCenter_eq ζ]
  exact Function.rightInverse_invFun (d.centerMap_bijective ζ).2 y

/-- Helper for Infrastructure I.16a: any section satisfying the differentiated affine equation
gives the exact affine-cocycle decomposition of the predecessor raw defect. -/
theorem metricReservedTopRawDefect_decomposition_of_sourceEquation
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (m : ℕ) (sectionFn : ℝ → X)
    (hsource : ∀ x,
      iteratedDeriv m (ζ : ℝ → X) (d.centerMap ζ x) =
        metricReservedTopCoefficient d ζ m x
            (iteratedDeriv m (ζ : ℝ → X) x) +
          metricReservedTopForcing d ζ m x)
    (hderivative : ∀ x,
      deriv (d.centerMap ζ) x • sectionFn (d.centerMap ζ x) =
        deriv (metricReservedTopCoefficient d ζ m) x
            (iteratedDeriv m (ζ : ℝ → X) x) +
          metricReservedTopCoefficient d ζ m x (sectionFn x) +
          deriv (metricReservedTopForcing d ζ m) x)
    (u s : ℝ) :
    let delta :=
      d.inverseCenter ζ (d.centerMap ζ u + s) - u
    metricReservedTopRawDefect (ζ : ℝ → X) m sectionFn
        (d.centerMap ζ u) s =
      metricReservedTopCoefficient d ζ m (u + delta)
          (metricReservedTopRawDefect (ζ : ℝ → X) m sectionFn u delta) +
        metricReservedTopAffineRemainder d ζ m sectionFn u delta s := by
  dsimp only
  let delta :=
    d.inverseCenter ζ (d.centerMap ζ u + s) - u
  have hdelta :
      u + delta =
        d.inverseCenter ζ (d.centerMap ζ u + s) := by
    dsimp only [delta]
    ring
  have hcenter :
      d.centerMap ζ (u + delta) = d.centerMap ζ u + s := by
    rw [hdelta]
    exact metricCenterMap_inverseCenter d ζ
      (d.centerMap ζ u + s)
  have hsource_target :
      iteratedDeriv m (ζ : ℝ → X) (d.centerMap ζ u + s) =
        metricReservedTopCoefficient d ζ m (u + delta)
            (iteratedDeriv m (ζ : ℝ → X) (u + delta)) +
          metricReservedTopForcing d ζ m (u + delta) := by
    rw [← hcenter]
    exact hsource (u + delta)
  unfold metricReservedTopRawDefect
  rw [hsource_target, hsource u]
  unfold metricReservedTopAffineRemainder
  exact LocalCutoff.GraphTransform.affineCocycle_defect_decomposition
    (metricReservedTopCoefficient d ζ m u)
    (metricReservedTopCoefficient d ζ m (u + delta))
    (deriv (metricReservedTopCoefficient d ζ m) u)
    (metricReservedTopForcing d ζ m u)
    (metricReservedTopForcing d ζ m (u + delta))
    (deriv (metricReservedTopForcing d ζ m) u)
    (iteratedDeriv m (ζ : ℝ → X) u)
    (iteratedDeriv m (ζ : ℝ → X) (u + delta))
    (sectionFn u) (sectionFn (d.centerMap ζ u))
    (deriv (d.centerMap ζ) u) delta s
    (hderivative u)

/-- Helper for Infrastructure I.16a: the canonical differentiated fixed section gives the exact
raw-defect decomposition for every predecessor order at least two. -/
theorem metricReservedTopDerivativeFixedSection_rawDefect_decomposition
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ (m + 1) < 1)
    (u s : ℝ) :
    let sectionFn :=
      metricReservedTopDerivativeFixedSection
        d ζ hfixed hm hmν hprev h_bunching
    let delta :=
      d.inverseCenter ζ (d.centerMap ζ u + s) - u
    metricReservedTopRawDefect (ζ : ℝ → X) m sectionFn
        (d.centerMap ζ u) s =
      metricReservedTopCoefficient d ζ m (u + delta)
          (metricReservedTopRawDefect
            (ζ : ℝ → X) m sectionFn u delta) +
        metricReservedTopAffineRemainder
          d ζ m sectionFn u delta s := by
  let sectionFn :=
    metricReservedTopDerivativeFixedSection
      d ζ hfixed hm hmν hprev h_bunching
  have hm_leν : m ≤ d.nu :=
    (Nat.le_succ m).trans hmν
  have hsource : ∀ x,
      iteratedDeriv m (ζ : ℝ → X) (d.centerMap ζ x) =
        metricReservedTopCoefficient d ζ m x
            (iteratedDeriv m (ζ : ℝ → X) x) +
          metricReservedTopForcing d ζ m x :=
    iteratedDeriv_fixedGraph_reservedTop_affine_split
      d ζ hfixed hm hm_leν hprev
  have hderivative : ∀ x,
      deriv (d.centerMap ζ) x • sectionFn (d.centerMap ζ x) =
        deriv (metricReservedTopCoefficient d ζ m) x
            (iteratedDeriv m (ζ : ℝ → X) x) +
          metricReservedTopCoefficient d ζ m x (sectionFn x) +
          deriv (metricReservedTopForcing d ζ m) x := by
    intro x
    exact metricReservedTopDerivativeFixedSection_derivativeEquation
      d ζ hfixed hm hmν hprev h_bunching x
  exact metricReservedTopRawDefect_decomposition_of_sourceEquation
    d ζ m sectionFn hsource hderivative u s

/-- Helper for Infrastructure I.16a: a bound on the named affine remainder yields the raw-defect
recurrence with the predecessor reserved-top contraction factor. -/
theorem norm_metricReservedTopDerivativeFixedSection_rawDefect_le
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ (m + 1) < 1)
    (u s eta : ℝ)
    (hremainder :
      let sectionFn :=
        metricReservedTopDerivativeFixedSection
          d ζ hfixed hm hmν hprev h_bunching
      let delta :=
        d.inverseCenter ζ (d.centerMap ζ u + s) - u
      ‖metricReservedTopAffineRemainder
        d ζ m sectionFn u delta s‖ ≤ eta * |s|) :
    let sectionFn :=
      metricReservedTopDerivativeFixedSection
        d ζ hfixed hm hmν hprev h_bunching
    let delta :=
      d.inverseCenter ζ (d.centerMap ζ u + s) - u
    ‖metricReservedTopRawDefect (ζ : ℝ → X) m sectionFn
        (d.centerMap ζ u) s‖ ≤
      (metricReservedTopFactor d m : ℝ) *
          ‖metricReservedTopRawDefect
            (ζ : ℝ → X) m sectionFn u delta‖ +
        eta * |s| := by
  dsimp only
  let sectionFn :=
    metricReservedTopDerivativeFixedSection
      d ζ hfixed hm hmν hprev h_bunching
  let delta :=
    d.inverseCenter ζ (d.centerMap ζ u + s) - u
  have hdecomposition :=
    metricReservedTopDerivativeFixedSection_rawDefect_decomposition
      d ζ hfixed hm hmν hprev h_bunching u s
  dsimp only [sectionFn, delta] at hdecomposition
  have hprevious_nat : m - 1 ≤ m :=
    Nat.sub_le m 1
  have hprevious :
      ((m - 1 : ℕ) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast hprevious_nat
  have hprev_lower :
      ContDiff ℝ (m - 1) (ζ : ℝ → X) :=
    hprev.of_le hprevious
  have hcoefficient :
      ‖metricReservedTopCoefficient d ζ m (u + delta)‖ ≤
        (metricReservedTopFactor d m : ℝ) :=
    norm_metricReservedTopCoefficient_le_factor
      d ζ hfixed hm hprev_lower (u + delta)
  rw [hdecomposition]
  calc
    ‖metricReservedTopCoefficient d ζ m (u + delta)
          (metricReservedTopRawDefect
            (ζ : ℝ → X) m sectionFn u delta) +
        metricReservedTopAffineRemainder
          d ζ m sectionFn u delta s‖ ≤
        ‖metricReservedTopCoefficient d ζ m (u + delta)
          (metricReservedTopRawDefect
            (ζ : ℝ → X) m sectionFn u delta)‖ +
        ‖metricReservedTopAffineRemainder
          d ζ m sectionFn u delta s‖ :=
      norm_add_le _ _
    _ ≤ ‖metricReservedTopCoefficient d ζ m (u + delta)‖ *
          ‖metricReservedTopRawDefect
            (ζ : ℝ → X) m sectionFn u delta‖ +
        eta * |s| :=
      add_le_add
        ((metricReservedTopCoefficient d ζ m
          (u + delta)).le_opNorm _) hremainder
    _ ≤ (metricReservedTopFactor d m : ℝ) *
          ‖metricReservedTopRawDefect
            (ζ : ℝ → X) m sectionFn u delta‖ +
        eta * |s| :=
      add_le_add
        (mul_le_mul_of_nonneg_right hcoefficient (norm_nonneg _))
        le_rfl

/-- Helper for Infrastructure I.16a: a differentiable function with uniformly continuous
derivative has a first-order Taylor remainder uniformly controlled over all translation centers. -/
theorem uniformFirstOrderRemainder_of_uniformContinuous_deriv
    {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : ℝ → Y}
    (hf : Differentiable ℝ f)
    (hderiv : UniformContinuous (deriv f))
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ delta > 0, ∀ u h : ℝ, |h| < delta →
      ‖f (u + h) - f u - h • deriv f u‖ ≤ kappa * |h| := by
  obtain ⟨delta, hdelta, hmodulus⟩ :=
    Metric.uniformContinuous_iff.mp hderiv kappa hkappa
  refine ⟨delta, hdelta, ?_⟩
  intro u h hh
  let p : ℝ := u
  let q : ℝ := u + h
  let A : ℝ →L[ℝ] Y := fderiv ℝ f p
  let g : ℝ → Y := fun z ↦ f z - A z
  have hpq : q - p = h := by
    simp only [q, p, add_sub_cancel_left]
  have hpq_norm : ‖q - p‖ = |h| := by
    rw [hpq, Real.norm_eq_abs]
  have hpq_dist : dist p q < delta := by
    rw [dist_comm, dist_eq_norm, hpq_norm]
    exact hh
  have hderivative_bound : ∀ z ∈ segment ℝ p q,
      ‖fderiv ℝ f z - A‖ ≤ kappa := by
    intro z hz
    have hzp_norm : ‖z - p‖ ≤ ‖q - p‖ :=
      norm_sub_le_of_mem_segment hz
    have hpq_norm_lt : ‖q - p‖ < delta := by
      simpa only [dist_comm p q, dist_eq_norm] using hpq_dist
    have hzp_dist : dist z p < delta := by
      rw [dist_eq_norm]
      exact hzp_norm.trans_lt hpq_norm_lt
    have hclose := hmodulus hzp_dist
    have hnorm_fderiv :
        ‖fderiv ℝ f z - fderiv ℝ f p‖ =
          ‖deriv f z - deriv f p‖ := by
      rw [← toSpanSingleton_deriv, ← toSpanSingleton_deriv]
      have hspan :
          ContinuousLinearMap.toSpanSingleton ℝ (deriv f z) -
              ContinuousLinearMap.toSpanSingleton ℝ (deriv f p) =
            ContinuousLinearMap.toSpanSingleton ℝ (deriv f z - deriv f p) := by
        ext v
        simp only [ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.toSpanSingleton_apply]
        rw [one_smul, one_smul, one_smul]
      rw [hspan, ContinuousLinearMap.norm_toSpanSingleton]
    rw [hnorm_fderiv]
    simpa only [A, p, dist_eq_norm] using hclose.le
  have hg_derivative : ∀ z ∈ segment ℝ p q,
      HasFDerivWithinAt g (fderiv ℝ f z - A)
        (segment ℝ p q) z := by
    intro z hz
    exact ((hf z).hasFDerivAt.sub A.hasFDerivAt).hasFDerivWithinAt
  have hmean :=
    (convex_segment p q).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hg_derivative hderivative_bound
      (left_mem_segment ℝ p q) (right_mem_segment ℝ p q)
  have hA_difference :
      A q - A p = h • deriv f u := by
    rw [← map_sub, hpq]
    simp only [A, p, fderiv_eq_smul_deriv]
  have hg_algebra :
      g q - g p = f q - f p - (A q - A p) := by
    unfold g
    abel
  rw [hg_algebra, hA_difference] at hmean
  dsimp only [q, p] at hmean
  rw [hpq_norm] at hmean
  exact hmean

/-- Helper for Infrastructure I.16a: every iterated derivative of a compactly supported scalar
curve remains compactly supported. -/
theorem iteratedDeriv_hasCompactSupport
    {f : ℝ → X} (hf : HasCompactSupport f) (m : ℕ) :
    HasCompactSupport (iteratedDeriv m f) := by
  induction m with
  | zero =>
      simpa only [iteratedDeriv_zero] using hf
  | succ m ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

/-- Helper for Infrastructure I.16a: the predecessor iterated derivative on a fixed graph has a
global norm bound. -/
theorem exists_metricIteratedDeriv_norm_bound
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    (m : ℕ)
    (hprev : ContDiff ℝ m (ζ : ℝ → X)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, ‖iteratedDeriv m (ζ : ℝ → X) x‖ ≤ C := by
  have hcontinuous :
      Continuous (iteratedDeriv m (ζ : ℝ → X)) :=
    hprev.continuous_iteratedDeriv m le_rfl
  have hsupport :
      HasCompactSupport (iteratedDeriv m (ζ : ℝ → X)) :=
    iteratedDeriv_hasCompactSupport
      (fixedGraph_hasCompactSupport d ζ hfixed) m
  obtain ⟨C, hC⟩ :=
    hcontinuous.bounded_above_of_compact_support hsupport
  have hC_nonneg : 0 ≤ C :=
    (norm_nonneg (iteratedDeriv m (ζ : ℝ → X) 0)).trans
      (hC 0)
  exact ⟨C, hC_nonneg, hC⟩

/-- Helper for Infrastructure I.16a: the reserved-top coefficient itself is uniformly continuous
because its difference from the exterior constant coefficient has compact support. -/
theorem uniformContinuous_metricReservedTopCoefficient
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m)
    (hprev : ContDiff ℝ m (ζ : ℝ → X)) :
    UniformContinuous (metricReservedTopCoefficient d ζ m) := by
  have hcoefficient :
      Continuous (metricReservedTopCoefficient d ζ m) :=
    (metricReservedTopCoefficient_contDiff_one_of_previousOrder
      d ζ hm hprev).continuous
  have hperturbation : Continuous (fun x ↦
      metricReservedTopCoefficient d ζ m x - d.L) :=
    hcoefficient.sub continuous_const
  have hsupport : HasCompactSupport (fun x ↦
      metricReservedTopCoefficient d ζ m x - d.L) :=
    metricReservedTopCoefficient_sub_linear_hasCompactSupport
      d ζ hfixed hm hprev
  have hperturbation_uniform : UniformContinuous (fun x ↦
      metricReservedTopCoefficient d ζ m x - d.L) :=
    hperturbation.uniformContinuous_of_tendsto_cocompact
      hsupport.is_zero_at_infty
  have hsum := hperturbation_uniform.add
    (uniformContinuous_const : UniformContinuous (fun _ : ℝ ↦ d.L))
  simpa only [sub_add_cancel] using hsum

/-- Helper for Infrastructure I.16a: sufficiently short source increments change the reserved-top
coefficient by an arbitrarily small operator norm, uniformly in the source point. -/
theorem metricReservedTopCoefficient_increment_uniform
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ delta > 0, ∀ u h : ℝ, |h| < delta →
      ‖metricReservedTopCoefficient d ζ m (u + h) -
        metricReservedTopCoefficient d ζ m u‖ ≤ kappa := by
  obtain ⟨delta, hdelta, hcontrol⟩ :=
    (Metric.uniformContinuous_iff.mp
      (uniformContinuous_metricReservedTopCoefficient
        d ζ hfixed hm hprev)) kappa hkappa
  refine ⟨delta, hdelta, ?_⟩
  intro u h hh
  have hsource : dist (u + h) u < delta := by
    simpa only [Real.dist_eq, add_sub_cancel_left] using hh
  have htarget := hcontrol hsource
  simpa only [dist_eq_norm] using htarget.le

/-- Helper for Infrastructure I.16a: the reserved-top coefficient has a globally uniform
first-order Taylor remainder. -/
theorem metricReservedTopCoefficient_taylor_uniform
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ delta > 0, ∀ u h : ℝ, |h| < delta →
      ‖metricReservedTopCoefficient d ζ m (u + h) -
          metricReservedTopCoefficient d ζ m u -
          h • deriv (metricReservedTopCoefficient d ζ m) u‖ ≤
        kappa * |h| := by
  have hcoefficient :
      ContDiff ℝ 1 (metricReservedTopCoefficient d ζ m) :=
    metricReservedTopCoefficient_contDiff_one_of_previousOrder
      d ζ hm hprev
  exact uniformFirstOrderRemainder_of_uniformContinuous_deriv
    (hcoefficient.differentiable one_ne_zero)
    (uniformContinuous_metricReservedTopCoefficient_deriv
      d ζ hfixed hm hprev) hkappa

/-- Helper for Infrastructure I.16a: the lower-order reserved-top forcing has a globally uniform
first-order Taylor remainder. -/
theorem metricReservedTopForcing_taylor_uniform
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ delta > 0, ∀ u h : ℝ, |h| < delta →
      ‖metricReservedTopForcing d ζ m (u + h) -
          metricReservedTopForcing d ζ m u -
          h • deriv (metricReservedTopForcing d ζ m) u‖ ≤
        kappa * |h| := by
  have hforcing : ContDiff ℝ 1 (metricReservedTopForcing d ζ m) :=
    metricReservedTopForcing_contDiff_one d ζ hm hmν hprev
  exact uniformFirstOrderRemainder_of_uniformContinuous_deriv
    (hforcing.differentiable one_ne_zero)
    (uniformContinuous_metricReservedTopForcing_deriv
      d ζ hfixed hm hmν hprev) hkappa

/-- Helper for Infrastructure I.16a: the center derivative differs from one only on a compact
set controlled by the base projection of `tsupport d.R`. -/
theorem centerMapDeriv_sub_one_hasCompactSupport
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) :
    HasCompactSupport (fun x ↦ deriv (d.centerMap ζ) x - 1) := by
  let KR : Set ℝ := Prod.fst '' tsupport d.R
  have hKR : IsCompact KR :=
    d.hR_support.image continuous_fst
  apply HasCompactSupport.intro hKR
  intro x hx
  have hgraph : (x, (ζ : ℝ → X) x) ∉ tsupport d.R := by
    intro hmem
    apply hx
    exact ⟨(x, (ζ : ℝ → X) x), hmem, rfl⟩
  have hgraph_continuous :
      Continuous (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) :=
    continuous_id.prodMk ζ.1.continuous
  have hR_graph :
      (fun y : ℝ ↦ d.R (y, (ζ : ℝ → X) y)) =ᶠ[nhds x]
        (fun _ : ℝ ↦ (0 : ℝ × X)) := by
    have hopen : IsOpen (tsupport d.R)ᶜ :=
      (isClosed_tsupport d.R).isOpen_compl
    have hgraph_compl :
        (x, (ζ : ℝ → X) x) ∈ (tsupport d.R)ᶜ :=
      hgraph
    have hnear :
        ∀ᶠ y in nhds x, (y, (ζ : ℝ → X) y) ∈ (tsupport d.R)ᶜ :=
      hgraph_continuous.continuousAt
        (hopen.mem_nhds hgraph_compl)
    filter_upwards [hnear] with y hy
    have hy_not : (y, (ζ : ℝ → X) y) ∉ tsupport d.R := by
      simpa only [mem_compl_iff] using hy
    exact image_eq_zero_of_notMem_tsupport hy_not
  have hcenter_local :
      d.centerMap ζ =ᶠ[nhds x] (fun y : ℝ ↦ y) := by
    filter_upwards [hR_graph] with y hy
    have hcenter_eq : d.centerMap ζ y = y := by
      rw [d.centerMap_eq ζ]
      simp only [hy, Prod.fst_zero, add_zero]
    exact hcenter_eq
  have hcenter_deriv :
      deriv (d.centerMap ζ) x = 1 :=
    ((hcenter_local.hasDerivAt_iff).mpr (hasDerivAt_id x)).deriv
  exact sub_eq_zero.mpr hcenter_deriv

/-- Helper for Infrastructure I.16a: the center-map derivative is uniformly continuous on the
whole source line. -/
theorem uniformContinuous_centerMap_deriv
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hζ_one : ContDiff ℝ 1 (ζ : ℝ → X)) :
    UniformContinuous (deriv (d.centerMap ζ)) := by
  have honeν : (1 : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast le_trans one_le_two d.hnu
  have hcenter : ContDiff ℝ 1 (d.centerMap ζ) :=
    centerMap_contDiff_of_prev d ζ honeν hζ_one
  have hderiv : Continuous (deriv (d.centerMap ζ)) :=
    hcenter.continuous_deriv le_rfl
  have hperturbation :
      Continuous (fun x ↦ deriv (d.centerMap ζ) x - 1) :=
    hderiv.sub continuous_const
  have hperturbation_uniform :
      UniformContinuous (fun x ↦ deriv (d.centerMap ζ) x - 1) :=
    hperturbation.uniformContinuous_of_tendsto_cocompact
      (centerMapDeriv_sub_one_hasCompactSupport d ζ).is_zero_at_infty
  have hsum := hperturbation_uniform.add
    (uniformContinuous_const :
      UniformContinuous (fun _ : ℝ ↦ (1 : ℝ)))
  simpa only [sub_add_cancel] using hsum

/-- Helper for Infrastructure I.16a: the center map has a globally uniform first-order Taylor
remainder. -/
theorem centerMap_taylor_uniform
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hζ_one : ContDiff ℝ 1 (ζ : ℝ → X))
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ delta > 0, ∀ u h : ℝ, |h| < delta →
      |d.centerMap ζ (u + h) - d.centerMap ζ u -
          h * deriv (d.centerMap ζ) u| ≤
        kappa * |h| := by
  have honeν : (1 : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast le_trans one_le_two d.hnu
  have hcenter : ContDiff ℝ 1 (d.centerMap ζ) :=
    centerMap_contDiff_of_prev d ζ honeν hζ_one
  have hremainder :=
    uniformFirstOrderRemainder_of_uniformContinuous_deriv
      (hcenter.differentiable one_ne_zero)
      (uniformContinuous_centerMap_deriv d ζ hζ_one)
      hkappa
  simpa only [Real.norm_eq_abs, smul_eq_mul] using hremainder

/-- Helper for Infrastructure I.16a: inverse-center transport contracts scalar increments by at
most `lower⁻¹`. -/
theorem abs_metricInverseCenterIncrement_le
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (u s : ℝ) :
    |d.inverseCenter ζ (d.centerMap ζ u + s) - u| ≤
      (d.lower : ℝ)⁻¹ * |s| := by
  have hbound :=
    (d.inverseCenter_lipschitzWith ζ).dist_le_mul
      (d.centerMap ζ u + s) (d.centerMap ζ u)
  rw [metricInverseCenter_centerMap] at hbound
  simpa only [dist_eq_norm, Real.norm_eq_abs, add_sub_cancel_left,
    NNReal.coe_inv] using hbound

/-- Helper for Infrastructure I.16a: the inverse-center increment transports the perturbed
output coordinate exactly back to the corresponding source coordinate. -/
theorem metricCenterMap_add_inverseCenterIncrement
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (u s : ℝ) :
    d.centerMap ζ
        (u + (d.inverseCenter ζ (d.centerMap ζ u + s) - u)) =
      d.centerMap ζ u + s := by
  have hsum :
      u + (d.inverseCenter ζ (d.centerMap ζ u + s) - u) =
        d.inverseCenter ζ (d.centerMap ζ u + s) := by
    ring
  rw [hsum]
  exact metricCenterMap_inverseCenter d ζ (d.centerMap ζ u + s)

/-- Helper for Infrastructure I.16a: the affine remainder in the differentiated reserved-top
cocycle is uniformly little compared with the output increment. -/
theorem metricReservedTopAffineRemainder_uniform
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ (m + 1) < 1) :
    ∀ eta > 0, ∃ rho > 0, ∀ u s : ℝ, |s| < rho →
      let sectionFn :=
        metricReservedTopDerivativeFixedSection
          d ζ hfixed hm hmν hprev h_bunching
      let delta :=
        d.inverseCenter ζ (d.centerMap ζ u + s) - u
      ‖metricReservedTopAffineRemainder
        d ζ m sectionFn u delta s‖ ≤ eta * |s| := by
  let sectionFn :=
    metricReservedTopDerivativeFixedSection
      d ζ hfixed hm hmν hprev h_bunching
  obtain ⟨W, hW_nonneg, hW⟩ :=
    exists_metricIteratedDeriv_norm_bound d ζ hfixed m hprev
  let B : ℝ := ‖sectionFn‖
  let ell : ℝ := d.lower
  let c : ℝ := ell⁻¹
  have hell_pos : 0 < ell := by
    dsimp only [ell]
    exact_mod_cast d.hlower_pos
  have hc_pos : 0 < c := inv_pos.mpr hell_pos
  have hB_nonneg : 0 ≤ B := by
    exact norm_nonneg sectionFn
  let M : ℝ := c * W + 2 * (c * B) + c + 1
  have hcW_nonneg : 0 ≤ c * W :=
    mul_nonneg hc_pos.le hW_nonneg
  have hcB_nonneg : 0 ≤ c * B :=
    mul_nonneg hc_pos.le hB_nonneg
  have hM_pos : 0 < M := by
    dsimp only [M]
    linarith
  have hM_ne : M ≠ 0 := ne_of_gt hM_pos
  have hcW_le_M : c * W ≤ M := by
    dsimp only [M]
    linarith
  have hcB_le_M : c * B ≤ M := by
    dsimp only [M]
    linarith
  have hc_le_M : c ≤ M := by
    dsimp only [M]
    linarith
  intro eta heta
  let kappa : ℝ := eta / (4 * M)
  have hfour_pos : 0 < (4 : ℝ) := by
    norm_num
  have hdenominator_pos : 0 < 4 * M :=
    mul_pos hfour_pos hM_pos
  have hkappa_pos : 0 < kappa := by
    exact div_pos heta hdenominator_pos
  have hkappa_nonneg : 0 ≤ kappa := hkappa_pos.le
  have hkappa_M : 4 * kappa * M = eta := by
    dsimp only [kappa]
    field_simp [hM_ne]
  obtain ⟨rCoefficientTaylor, hrCoefficientTaylor,
      hCoefficientTaylor⟩ :=
    metricReservedTopCoefficient_taylor_uniform
      d ζ hfixed hm hprev hkappa_pos
  obtain ⟨rCoefficientIncrement, hrCoefficientIncrement,
      hCoefficientIncrement⟩ :=
    metricReservedTopCoefficient_increment_uniform
      d ζ hfixed hm hprev hkappa_pos
  obtain ⟨rForcing, hrForcing, hForcing⟩ :=
    metricReservedTopForcing_taylor_uniform
      d ζ hfixed hm hmν hprev hkappa_pos
  have hone_nat : 1 ≤ m := by
    omega
  have hone : (1 : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast hone_nat
  have hζ_one : ContDiff ℝ 1 (ζ : ℝ → X) :=
    hprev.of_le hone
  obtain ⟨rCenter, hrCenter, hCenter⟩ :=
    centerMap_taylor_uniform d ζ hζ_one hkappa_pos
  let rmin : ℝ :=
    min rCoefficientTaylor
      (min rCoefficientIncrement (min rForcing rCenter))
  have hrmin_pos : 0 < rmin := by
    dsimp only [rmin]
    exact lt_min hrCoefficientTaylor
      (lt_min hrCoefficientIncrement (lt_min hrForcing hrCenter))
  let rho : ℝ := rmin * ell / 2
  have hrho_pos : 0 < rho := by
    dsimp only [rho]
    positivity
  refine ⟨rho, hrho_pos, ?_⟩
  intro u s hs
  let delta : ℝ :=
    d.inverseCenter ζ (d.centerMap ζ u + s) - u
  have hdelta_le : |delta| ≤ c * |s| := by
    dsimp only [delta, c, ell]
    exact abs_metricInverseCenterIncrement_le d ζ u s
  have htransport_radius : c * rho = rmin / 2 := by
    dsimp only [c, rho]
    field_simp [ne_of_gt hell_pos]
  have hdelta_lt_rmin : |delta| < rmin := by
    have hscaled : c * |s| < c * rho :=
      mul_lt_mul_of_pos_left hs hc_pos
    have hscaled_rmin : c * |s| < rmin := by
      rw [htransport_radius] at hscaled
      linarith
    exact hdelta_le.trans_lt hscaled_rmin
  have hdelta_coefficientTaylor : |delta| < rCoefficientTaylor :=
    hdelta_lt_rmin.trans_le (min_le_left _ _)
  have hdelta_coefficientIncrement : |delta| < rCoefficientIncrement :=
    hdelta_lt_rmin.trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hdelta_forcing : |delta| < rForcing :=
    hdelta_lt_rmin.trans_le
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hdelta_center : |delta| < rCenter :=
    hdelta_lt_rmin.trans_le
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  have hcoefficientTaylor :=
    hCoefficientTaylor u delta hdelta_coefficientTaylor
  have hcoefficientIncrement :=
    hCoefficientIncrement u delta hdelta_coefficientIncrement
  have hforcingTaylor :=
    hForcing u delta hdelta_forcing
  have hcenterTaylor :=
    hCenter u delta hdelta_center
  have hsection : ∀ x, ‖sectionFn x‖ ≤ B := by
    intro x
    exact BoundedContinuousFunction.norm_coe_le_norm sectionFn x
  have hfirstApplication :
      ‖(metricReservedTopCoefficient d ζ m (u + delta) -
            metricReservedTopCoefficient d ζ m u)
          (iteratedDeriv m (ζ : ℝ → X) u) -
        delta • deriv (metricReservedTopCoefficient d ζ m) u
          (iteratedDeriv m (ζ : ℝ → X) u)‖ ≤
        ‖metricReservedTopCoefficient d ζ m (u + delta) -
            metricReservedTopCoefficient d ζ m u -
            delta • deriv (metricReservedTopCoefficient d ζ m) u‖ *
          ‖iteratedDeriv m (ζ : ℝ → X) u‖ := by
    exact (metricReservedTopCoefficient d ζ m (u + delta) -
      metricReservedTopCoefficient d ζ m u -
      delta • deriv (metricReservedTopCoefficient d ζ m) u).le_opNorm _
  have hfirst :
      ‖(metricReservedTopCoefficient d ζ m (u + delta) -
            metricReservedTopCoefficient d ζ m u)
          (iteratedDeriv m (ζ : ℝ → X) u) -
        delta • deriv (metricReservedTopCoefficient d ζ m) u
          (iteratedDeriv m (ζ : ℝ → X) u)‖ ≤
        (kappa * M) * |s| := by
    calc
      _ ≤ ‖metricReservedTopCoefficient d ζ m (u + delta) -
              metricReservedTopCoefficient d ζ m u -
              delta • deriv (metricReservedTopCoefficient d ζ m) u‖ *
            ‖iteratedDeriv m (ζ : ℝ → X) u‖ := hfirstApplication
      _ ≤ (kappa * |delta|) * W :=
        mul_le_mul hcoefficientTaylor (hW u) (norm_nonneg _)
          (mul_nonneg hkappa_nonneg (abs_nonneg delta))
      _ ≤ (kappa * (c * |s|)) * W := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hdelta_le hkappa_nonneg
        · exact hW_nonneg
      _ = (kappa * (c * W)) * |s| := by ring
      _ ≤ (kappa * M) * |s| := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hcW_le_M hkappa_nonneg
        · exact abs_nonneg s
  have hsecondApplication :
      ‖(metricReservedTopCoefficient d ζ m (u + delta) -
          metricReservedTopCoefficient d ζ m u)
        (delta • sectionFn u)‖ ≤
        ‖metricReservedTopCoefficient d ζ m (u + delta) -
          metricReservedTopCoefficient d ζ m u‖ *
        ‖delta • sectionFn u‖ := by
    exact (metricReservedTopCoefficient d ζ m (u + delta) -
      metricReservedTopCoefficient d ζ m u).le_opNorm _
  have hsecond :
      ‖(metricReservedTopCoefficient d ζ m (u + delta) -
          metricReservedTopCoefficient d ζ m u)
        (delta • sectionFn u)‖ ≤
        (kappa * M) * |s| := by
    calc
      _ ≤ ‖metricReservedTopCoefficient d ζ m (u + delta) -
              metricReservedTopCoefficient d ζ m u‖ *
            ‖delta • sectionFn u‖ := hsecondApplication
      _ ≤ kappa * (|delta| * B) := by
        rw [norm_smul, Real.norm_eq_abs]
        have hsection_scaled :
            |delta| * ‖sectionFn u‖ ≤ |delta| * B :=
          mul_le_mul_of_nonneg_left (hsection u) (abs_nonneg delta)
        have hsection_scaled_nonneg :
            0 ≤ |delta| * ‖sectionFn u‖ :=
          mul_nonneg (abs_nonneg delta) (norm_nonneg _)
        exact mul_le_mul hcoefficientIncrement hsection_scaled
          hsection_scaled_nonneg hkappa_nonneg
      _ ≤ kappa * ((c * |s|) * B) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_right hdelta_le hB_nonneg
        · exact hkappa_nonneg
      _ = (kappa * (c * B)) * |s| := by ring
      _ ≤ (kappa * M) * |s| := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hcB_le_M hkappa_nonneg
        · exact abs_nonneg s
  have hthird :
      ‖metricReservedTopForcing d ζ m (u + delta) -
          metricReservedTopForcing d ζ m u -
          delta • deriv (metricReservedTopForcing d ζ m) u‖ ≤
        (kappa * M) * |s| := by
    calc
      _ ≤ kappa * |delta| := hforcingTaylor
      _ ≤ kappa * (c * |s|) :=
        mul_le_mul_of_nonneg_left hdelta_le hkappa_nonneg
      _ = (kappa * c) * |s| := by ring
      _ ≤ (kappa * M) * |s| := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hc_le_M hkappa_nonneg
        · exact abs_nonneg s
  have hcenter_exact :
      d.centerMap ζ (u + delta) = d.centerMap ζ u + s := by
    dsimp only [delta]
    exact metricCenterMap_add_inverseCenterIncrement d ζ u s
  have hcenter_residual :
      |deriv (d.centerMap ζ) u * delta - s| =
        |d.centerMap ζ (u + delta) - d.centerMap ζ u -
          delta * deriv (d.centerMap ζ) u| := by
    calc
      |deriv (d.centerMap ζ) u * delta - s| =
          |-(deriv (d.centerMap ζ) u * delta - s)| :=
        (abs_neg _).symm
      _ = |(d.centerMap ζ u + s) - d.centerMap ζ u -
          delta * deriv (d.centerMap ζ) u| := by
        congr 1
        ring
      _ = |d.centerMap ζ (u + delta) - d.centerMap ζ u -
          delta * deriv (d.centerMap ζ) u| := by
        rw [hcenter_exact]
  have hfour :
      ‖(deriv (d.centerMap ζ) u * delta - s) •
          sectionFn (d.centerMap ζ u)‖ ≤
        (kappa * M) * |s| := by
    calc
      _ = |deriv (d.centerMap ζ) u * delta - s| *
          ‖sectionFn (d.centerMap ζ u)‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ = |d.centerMap ζ (u + delta) - d.centerMap ζ u -
          delta * deriv (d.centerMap ζ) u| *
          ‖sectionFn (d.centerMap ζ u)‖ := by
        rw [hcenter_residual]
      _ ≤ (kappa * |delta|) * B :=
        mul_le_mul hcenterTaylor (hsection (d.centerMap ζ u))
          (norm_nonneg _) (mul_nonneg hkappa_nonneg (abs_nonneg delta))
      _ ≤ (kappa * (c * |s|)) * B := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hdelta_le hkappa_nonneg
        · exact hB_nonneg
      _ = (kappa * (c * B)) * |s| := by ring
      _ ≤ (kappa * M) * |s| := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hcB_le_M hkappa_nonneg
        · exact abs_nonneg s
  have hremainder :=
    norm_metricReservedTopAffineRemainder_le_four_mul
      d ζ m sectionFn u delta s ((kappa * M) * |s|)
      hfirst hsecond hthird hfour
  calc
    ‖metricReservedTopAffineRemainder
        d ζ m sectionFn u delta s‖ ≤ 4 * (kappa * M) * |s| := by
      have hscale : 4 * ((kappa * M) * |s|) =
          4 * (kappa * M) * |s| := by ring
      exact hremainder.trans_eq hscale
    _ = eta * |s| := by
      rw [← mul_assoc, hkappa_M]

/-- Helper for Infrastructure I.16a: the predecessor raw defect relative to the canonical
differentiated section is uniformly bounded on a fixed neighborhood of zero increment. -/
theorem metricReservedTopDerivativeFixedSection_rawDefect_locallyUniformlyBounded
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ (m + 1) < 1) :
    let sectionFn :=
      metricReservedTopDerivativeFixedSection
        d ζ hfixed hm hmν hprev h_bunching
    ∃ cutoff > 0, ∃ bound ≥ 0, ∀ y t : ℝ, ‖t‖ < cutoff →
      ‖metricReservedTopRawDefect
        (ζ : ℝ → X) m sectionFn y t‖ ≤ bound := by
  let sectionFn :=
    metricReservedTopDerivativeFixedSection
      d ζ hfixed hm hmν hprev h_bunching
  obtain ⟨W, hW_nonneg, hW⟩ :=
    exists_metricIteratedDeriv_norm_bound d ζ hfixed m hprev
  refine ⟨1, zero_lt_one, 2 * W + ‖sectionFn‖, ?_, ?_⟩
  · positivity
  · intro y t ht
    have ht_abs : |t| < 1 := by
      simpa only [Real.norm_eq_abs] using ht
    have hsection : ‖sectionFn y‖ ≤ ‖sectionFn‖ :=
      BoundedContinuousFunction.norm_coe_le_norm sectionFn y
    have hscaled : ‖t • sectionFn y‖ ≤ ‖sectionFn‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |t| * ‖sectionFn y‖ ≤ 1 * ‖sectionFn y‖ :=
          mul_le_mul_of_nonneg_right ht_abs.le (norm_nonneg _)
        _ = ‖sectionFn y‖ := one_mul _
        _ ≤ ‖sectionFn‖ := hsection
    unfold metricReservedTopRawDefect
    have hnorm :
        ‖iteratedDeriv m (ζ : ℝ → X) (y + t) -
            iteratedDeriv m (ζ : ℝ → X) y‖ ≤
          ‖iteratedDeriv m (ζ : ℝ → X) (y + t)‖ +
            ‖iteratedDeriv m (ζ : ℝ → X) y‖ :=
      norm_sub_le _ _
    calc
      ‖iteratedDeriv m (ζ : ℝ → X) (y + t) -
          iteratedDeriv m (ζ : ℝ → X) y - t • sectionFn y‖ ≤
          ‖iteratedDeriv m (ζ : ℝ → X) (y + t) -
            iteratedDeriv m (ζ : ℝ → X) y‖ +
          ‖t • sectionFn y‖ := norm_sub_le _ _
      _ ≤ (‖iteratedDeriv m (ζ : ℝ → X) (y + t)‖ +
            ‖iteratedDeriv m (ζ : ℝ → X) y‖) +
          ‖t • sectionFn y‖ :=
        add_le_add_left hnorm (‖t • sectionFn y‖)
      _ ≤ (W + W) + ‖sectionFn‖ :=
        add_le_add (add_le_add (hW (y + t)) (hW y)) hscaled
      _ = 2 * W + ‖sectionFn‖ := by ring

/-- Helper for Infrastructure I.16a: uniform affine-remainder smallness gives the inverse-center
raw-defect recurrence at predecessor order `m`. -/
theorem metricReservedTopDerivativeFixedSection_rawDefect_inverseRecurrence
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ (m + 1) < 1) :
    let sectionFn :=
      metricReservedTopDerivativeFixedSection
        d ζ hfixed hm hmν hprev h_bunching
    ∀ eta > 0, ∃ rho > 0, ∀ y t : ℝ, t ≠ 0 → ‖t‖ < rho →
      ‖metricReservedTopRawDefect
        (ζ : ℝ → X) m sectionFn y t‖ ≤
        (metricReservedTopFactor d m : ℝ) *
          ‖metricReservedTopRawDefect (ζ : ℝ → X) m sectionFn
            (d.inverseCenter ζ y)
            (d.inverseCenter ζ (y + t) - d.inverseCenter ζ y)‖ +
        eta * ‖t‖ := by
  dsimp only
  let sectionFn :=
    metricReservedTopDerivativeFixedSection
      d ζ hfixed hm hmν hprev h_bunching
  intro eta heta
  obtain ⟨rho, hrho, hremainder⟩ :=
    metricReservedTopAffineRemainder_uniform
      d ζ hfixed hm hmν hprev h_bunching eta heta
  refine ⟨rho, hrho, ?_⟩
  intro y t _ht_ne ht
  let u := d.inverseCenter ζ y
  have hcenter : d.centerMap ζ u = y := by
    dsimp only [u]
    exact metricCenterMap_inverseCenter d ζ y
  have ht_abs : |t| < rho := by
    simpa only [Real.norm_eq_abs] using ht
  have hsmall := hremainder u t ht_abs
  have hrecurrence :=
    norm_metricReservedTopDerivativeFixedSection_rawDefect_le
      d ζ hfixed hm hmν hprev h_bunching u t eta hsmall
  simpa only [hcenter, u, Real.norm_eq_abs] using hrecurrence

/-- Helper for Infrastructure I.16a: the predecessor raw defect relative to the differentiated
reserved-top fixed section is little-o of its increment at every source point. -/
theorem metricReservedTopDerivativeFixedSection_rawDefect_isLittleO
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ (m + 1) < 1) :
    let sectionFn :=
      metricReservedTopDerivativeFixedSection
        d ζ hfixed hm hmν hprev h_bunching
    ∀ y : ℝ,
      (fun t : ℝ ↦ metricReservedTopRawDefect
        (ζ : ℝ → X) m sectionFn y t) =o[𝓝 0]
        (fun t : ℝ ↦ t) := by
  let sectionFn :=
    metricReservedTopDerivativeFixedSection
      d ζ hfixed hm hmν hprev h_bunching
  let p : ℝ := metricReservedTopFactor d m
  let c : ℝ := (d.lower : ℝ)⁻¹
  have hlower_pos : 0 < (d.lower : ℝ) := by
    exact_mod_cast d.hlower_pos
  have hepsilon_nonneg : 0 ≤ (d.epsilon : ℝ) :=
    NNReal.coe_nonneg d.epsilon
  have hlower_add :
      (d.lower : ℝ) + (d.epsilon : ℝ) = 1 := by
    exact_mod_cast d.hlower_add
  have hlower_le_one : (d.lower : ℝ) ≤ 1 := by
    linarith
  have hc_pos : 0 < c := by
    dsimp only [c]
    exact inv_pos.mpr hlower_pos
  have hc_ge_one : 1 ≤ c := by
    dsimp only [c]
    have hlower_ne : (d.lower : ℝ) ≠ 0 := ne_of_gt hlower_pos
    have hinverse_nonneg : 0 ≤ (d.lower : ℝ)⁻¹ :=
      inv_nonneg.mpr hlower_pos.le
    calc
      1 = (d.lower : ℝ) * (d.lower : ℝ)⁻¹ :=
        (mul_inv_cancel₀ hlower_ne).symm
      _ ≤ 1 * (d.lower : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hlower_le_one hinverse_nonneg
      _ = (d.lower : ℝ)⁻¹ := one_mul _
  have hp_nonneg : 0 ≤ p := by
    dsimp only [p]
    exact metricReservedTopFactor_nonneg d m
  have hproduct :
      p * c =
        (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
          (d.lower : ℝ)⁻¹ ^ (m + 1) := by
    dsimp only [p, c]
    rw [metricReservedTopFactor_coe, pow_succ]
    ring
  have hp_lt_one : p < 1 := by
    calc
      p = p * 1 := (mul_one p).symm
      _ ≤ p * c := mul_le_mul_of_nonneg_left hc_ge_one hp_nonneg
      _ < 1 := by
        rw [hproduct]
        exact h_bunching
  have hpc_lt_one : p * c < 1 := by
    rw [hproduct]
    exact h_bunching
  apply LocalCutoff.GraphTransform.rawDefect_isLittleO_of_inverseRecurrence
    (metricReservedTopRawDefect (ζ : ℝ → X) m sectionFn)
    (d.inverseCenter ζ) p c
  · exact metricReservedTopRawDefect_zero (ζ : ℝ → X) m sectionFn
  · exact metricReservedTopDerivativeFixedSection_rawDefect_locallyUniformlyBounded
      d ζ hfixed hm hmν hprev h_bunching
  · intro y t
    dsimp only [c]
    have hbound := (d.inverseCenter_lipschitzWith ζ).dist_le_mul (y + t) y
    simpa only [dist_eq_norm, Real.norm_eq_abs, add_sub_cancel_left,
      NNReal.coe_inv] using hbound
  · exact hp_nonneg
  · exact hp_lt_one
  · exact hc_pos
  · exact hpc_lt_one
  · exact metricReservedTopDerivativeFixedSection_rawDefect_inverseRecurrence
      d ζ hfixed hm hmν hprev h_bunching

/-- Helper for Infrastructure I.16a: the canonical differentiated reserved-top fixed section is
the pointwise derivative of the predecessor iterated derivative. -/
theorem metricIteratedDeriv_hasDerivAt_higherOrder
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ (m + 1) < 1) :
    ∀ y : ℝ,
      HasDerivAt (iteratedDeriv m (ζ : ℝ → X))
        (metricReservedTopDerivativeFixedSection
          d ζ hfixed hm hmν hprev h_bunching y) y := by
  apply LocalCutoff.GraphTransform.predecessorHasDerivAt_of_rawDefectLittleO
    (iteratedDeriv m (ζ : ℝ → X))
    (metricReservedTopDerivativeFixedSection
      d ζ hfixed hm hmν hprev h_bunching)
  intro y
  simpa only [metricReservedTopRawDefect] using
    metricReservedTopDerivativeFixedSection_rawDefect_isLittleO
      d ζ hfixed hm hmν hprev h_bunching y

/-- Infrastructure I.16a: at every predecessor order `m ≥ 2`, successor bunching produces a
continuous derivative section for `iteratedDeriv m` of the metric fixed graph. -/
theorem metricFixedGraph_higherOrderDerivativeSection
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m + 1 ≤ d.nu)
    (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ (m + 1) < 1) :
    ∃ v : ℝ → X, Continuous v ∧
      ∀ u, HasDerivAt (iteratedDeriv m (ζ : ℝ → X)) (v u) u := by
  let v :=
    metricReservedTopDerivativeFixedSection
      d ζ hfixed hm hmν hprev h_bunching
  refine ⟨v, v.continuous, ?_⟩
  exact metricIteratedDeriv_hasDerivAt_higherOrder
    d ζ hfixed hm hmν hprev h_bunching


end LocalInvariantGraph
