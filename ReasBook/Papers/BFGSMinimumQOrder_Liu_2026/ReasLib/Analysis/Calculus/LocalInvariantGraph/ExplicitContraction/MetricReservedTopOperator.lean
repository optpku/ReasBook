module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionCoreAssembly
import all ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionCoreAssembly

public section

noncomputable section

open scoped NNReal Topology
open Filter Set

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-!
# The reserved-top affine operator

For `r ≥ 2`, the differentiated fixed-graph equation is affine in the reserved value
`iteratedDeriv r ζ`.  This file packages that affine equation on bounded continuous sections.
The operator is written in output coordinates: if `Φ = d.centerMap ζ` and
`Ψ = d.inverseCenter ζ`, then

`(T b)(y) = C(Ψ y) (b (Ψ y)) + F(Ψ y)`.

The continuity proofs below deliberately assume only `ContDiff ℝ (r - 1) ζ`.  In every
double-filtered Faà-di-Bruno term the outer length is smaller than `r`, and exclusion of the
length-one block makes every inner part size smaller than `r`.  Thus the operator is available
before the order-`r` derivative has been constructed.
-/

/-- Helper for Infrastructure I.16a: an order-`r` multilinear jet evaluated on a continuously
varying diagonal first jet is continuous. -/
private theorem iteratedFDeriv_diagonalFirstJet_continuous
    {Z Y : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (g : Z → Y) (f : ℝ → Z) {r : ℕ}
    (hg : ContDiff ℝ r g) (hf : ContDiff ℝ 1 f) :
    Continuous (fun x ↦
      iteratedFDeriv ℝ r g (f x) (fun _ : Fin r ↦ iteratedDeriv 1 f x)) := by
  have hr_order : (r : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := le_rfl
  have hone_order : (1 : WithTop ℕ∞) ≤ (1 : WithTop ℕ∞) := le_rfl
  have hjet : Continuous (fun x ↦ iteratedFDeriv ℝ r g (f x)) :=
    (hg.continuous_iteratedFDeriv hr_order).comp hf.continuous
  have hfirst : Continuous (iteratedDeriv 1 f) :=
    hf.continuous_iteratedDeriv 1 hone_order
  have hvec : Continuous (fun x ↦ fun _ : Fin r ↦ iteratedDeriv 1 f x) := by
    apply continuous_pi
    intro j
    exact hfirst
  exact hjet.eval hvec

/-- Helper for Infrastructure I.16a: after excluding both the atomic and length-one
Faà-di-Bruno blocks, every retained evaluation is continuous using only the previous order. -/
private theorem orderedFinpartition_evaluation_continuous_of_previousOrder
    {Z Y : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (g : Z → Y) (f : ℝ → Z) {r : ℕ}
    (hg : ContDiff ℝ (r - 1) g) (hf : ContDiff ℝ (r - 1) f)
    (c : OrderedFinpartition r) (hlenr : c.length ≠ r) (hlen1 : c.length ≠ 1) :
    Continuous (fun x ↦ iteratedFDeriv ℝ c.length g (f x)
      (fun j ↦ iteratedDeriv (c.partSize j) f x)) := by
  have hlength_lt : c.length < r := lt_of_le_of_ne c.length_le hlenr
  have hlength_previous : c.length ≤ r - 1 := by
    omega
  have hlength_order :
      (c.length : WithTop ℕ∞) ≤ ((r - 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast hlength_previous
  have hjet : Continuous (fun x ↦ iteratedFDeriv ℝ c.length g (f x)) :=
    (hg.continuous_iteratedFDeriv hlength_order).comp hf.continuous
  have hvec : Continuous
      (fun x ↦ fun j ↦ iteratedDeriv (c.partSize j) f x) := by
    apply continuous_pi
    intro j
    have hpart_lt : c.partSize j < r :=
      orderedFinpartition_partSize_lt_of_length_ne_one c hlen1 j
    have hpart_previous : c.partSize j ≤ r - 1 := by
      omega
    have hpart_order :
        (c.partSize j : WithTop ℕ∞) ≤ ((r - 1 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast hpart_previous
    exact hf.continuous_iteratedDeriv (c.partSize j) hpart_order
  exact hjet.eval hvec

/-- Helper for Infrastructure I.16a: the order-`r` stable-coordinate atomic evaluation is
continuous under the non-circular assumptions `r ≤ d.nu` and `ζ ∈ C^(r-1)`. -/
theorem metricStableAtomicEvaluation_continuous_of_previousOrder
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X)) :
    Continuous (fun x ↦
      iteratedFDeriv ℝ r (fun z : ℝ × X ↦ (d.R z).2)
        (x, (ζ : ℝ → X) x)
        (fun _ : Fin r ↦
          iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) x)) := by
  have hr_order : (r : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hrν
  have hone_previous_nat : 1 ≤ r - 1 := by
    omega
  have hone_previous :
      (1 : WithTop ℕ∞) ≤ ((r - 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast hone_previous_nat
  have hR : ContDiff ℝ r d.R := d.hR_smooth.of_le hr_order
  have hg : ContDiff ℝ r (fun z : ℝ × X ↦ (d.R z).2) :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.snd ℝ ℝ X)).comp hR
  have hpair : ContDiff ℝ 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) :=
    contDiff_id.prodMk (hprev.of_le hone_previous)
  exact iteratedFDeriv_diagonalFirstJet_continuous
    (fun z : ℝ × X ↦ (d.R z).2) (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) hg hpair

/-- Helper for Infrastructure I.16a: the order-`r` center-coordinate atomic evaluation is
continuous under the non-circular assumptions `r ≤ d.nu` and `ζ ∈ C^(r-1)`. -/
theorem metricCenterAtomicEvaluation_continuous_of_previousOrder
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X)) :
    Continuous (fun x ↦
      iteratedFDeriv ℝ r (fun z : ℝ × X ↦ (d.R z).1)
        (x, (ζ : ℝ → X) x)
        (fun _ : Fin r ↦
          iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) x)) := by
  have hr_order : (r : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hrν
  have hone_previous_nat : 1 ≤ r - 1 := by
    omega
  have hone_previous :
      (1 : WithTop ℕ∞) ≤ ((r - 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast hone_previous_nat
  have hR : ContDiff ℝ r d.R := d.hR_smooth.of_le hr_order
  have hg : ContDiff ℝ r (fun z : ℝ × X ↦ (d.R z).1) :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.fst ℝ ℝ X)).comp hR
  have hpair : ContDiff ℝ 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) :=
    contDiff_id.prodMk (hprev.of_le hone_previous)
  exact iteratedFDeriv_diagonalFirstJet_continuous
    (fun z : ℝ × X ↦ (d.R z).1) (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) hg hpair

/-- Helper for Infrastructure I.16a: the stable-coordinate doubled-filter residual is
continuous using only the previous-order regularity of the graph. -/
theorem iteratedDeriv_fiber_remainder_length_one_residual_continuous_of_previousOrder
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X)) :
    Continuous (fun x ↦ ∑ c ∈ (Finset.univ.filter
        (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
      iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).2)
        (x, (ζ : ℝ → X) x)
        (fun j ↦ iteratedDeriv (c.partSize j)
          (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) x)) := by
  have hr_order : (r : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hrν
  have hprevious_order :
      ((r - 1 : ℕ) : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by
    exact_mod_cast Nat.sub_le r 1
  have hR : ContDiff ℝ r d.R := d.hR_smooth.of_le hr_order
  have hg_r : ContDiff ℝ r (fun z : ℝ × X ↦ (d.R z).2) :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.snd ℝ ℝ X)).comp hR
  have hg : ContDiff ℝ (r - 1) (fun z : ℝ × X ↦ (d.R z).2) :=
    hg_r.of_le hprevious_order
  have hpair : ContDiff ℝ (r - 1) (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) :=
    contDiff_id.prodMk hprev
  apply continuous_finsetSum
  intro c hc
  rw [Finset.mem_filter] at hc
  exact orderedFinpartition_evaluation_continuous_of_previousOrder
    (fun z : ℝ × X ↦ (d.R z).2) (fun y : ℝ ↦ (y, (ζ : ℝ → X) y))
    hg hpair c hc.2.1 hc.2.2

/-- Helper for Infrastructure I.16a: the center-coordinate doubled-filter residual is
continuous using only the previous-order regularity of the graph. -/
theorem iteratedDeriv_center_remainder_length_one_residual_continuous_of_previousOrder
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X)) :
    Continuous (fun x ↦ ∑ c ∈ (Finset.univ.filter
        (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
      iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).1)
        (x, (ζ : ℝ → X) x)
        (fun j ↦ iteratedDeriv (c.partSize j)
          (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) x)) := by
  have hr_order : (r : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hrν
  have hprevious_order :
      ((r - 1 : ℕ) : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by
    exact_mod_cast Nat.sub_le r 1
  have hR : ContDiff ℝ r d.R := d.hR_smooth.of_le hr_order
  have hg_r : ContDiff ℝ r (fun z : ℝ × X ↦ (d.R z).1) :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.fst ℝ ℝ X)).comp hR
  have hg : ContDiff ℝ (r - 1) (fun z : ℝ × X ↦ (d.R z).1) :=
    hg_r.of_le hprevious_order
  have hpair : ContDiff ℝ (r - 1) (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) :=
    contDiff_id.prodMk hprev
  apply continuous_finsetSum
  intro c hc
  rw [Finset.mem_filter] at hc
  exact orderedFinpartition_evaluation_continuous_of_previousOrder
    (fun z : ℝ × X ↦ (d.R z).1) (fun y : ℝ ↦ (y, (ζ : ℝ → X) y))
    hg hpair c hc.2.1 hc.2.2

/-- Helper for Infrastructure I.16a: the graph-composition doubled-filter residual is
continuous using only the previous-order regularity of the graph. -/
theorem iteratedDeriv_zeta_comp_centerMap_length_one_residual_continuous_of_previousOrder
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X)) :
    Continuous (fun x ↦ ∑ c ∈ (Finset.univ.filter
        (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
      iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ x)
        (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) x)) := by
  have hpreviousν_nat : r - 1 ≤ d.nu := (Nat.sub_le r 1).trans hrν
  have hpreviousν : ((r - 1 : ℕ) : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hpreviousν_nat
  have hcenter : ContDiff ℝ (r - 1) (d.centerMap ζ) :=
    centerMap_contDiff_of_prev d ζ hpreviousν hprev
  apply continuous_finsetSum
  intro c hc
  rw [Finset.mem_filter] at hc
  exact orderedFinpartition_evaluation_continuous_of_previousOrder
    (ζ : ℝ → X) (d.centerMap ζ) hprev hcenter c hc.2.1 hc.2.2

/-- Helper for Infrastructure I.16a: previous-order regularity at every order at least two
contains first-order regularity. -/
private theorem contDiff_one_of_previousOrder
    {f : ℝ → X} {r : ℕ} (hr : 2 ≤ r)
    (hprev : ContDiff ℝ (r - 1) f) :
    ContDiff ℝ 1 f := by
  have hone_previous_nat : 1 ≤ r - 1 := by
    omega
  have hone_previous :
      (1 : WithTop ℕ∞) ≤ ((r - 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast hone_previous_nat
  exact hprev.of_le hone_previous

/-- Helper for Infrastructure I.16a: the complete reserved-top coefficient is continuous under
the previous-order regularity needed to form its center-feedback term. -/
theorem metricReservedTopCoefficient_continuous
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {r : ℕ} (hr : 2 ≤ r)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X)) :
    Continuous (metricReservedTopCoefficient d ζ r) := by
  have hone_previous_nat : 1 ≤ r - 1 := by
    omega
  have hone_previous :
      (1 : WithTop ℕ∞) ≤ ((r - 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast hone_previous_nat
  have hζ_one : ContDiff ℝ 1 (ζ : ℝ → X) := hprev.of_le hone_previous
  have hscale : Continuous (fun x ↦ (deriv (d.centerMap ζ) x)⁻¹ ^ r) :=
    centerMap_deriv_inv_pow_continuous d ζ hζ_one r
  have hζ_deriv : Continuous (deriv (ζ : ℝ → X)) := by
    have hiterated := hζ_one.continuous_iteratedDeriv 1 le_rfl
    simpa only [iteratedDeriv_one] using hiterated
  have hζ_deriv_center :
      Continuous (fun x ↦ deriv (ζ : ℝ → X) (d.centerMap ζ x)) :=
    hζ_deriv.comp (centerMap_continuous d ζ)
  have hfeedback : Continuous (fun x ↦
      (derivCenterFiber d ζ x).smulRight
        (deriv (ζ : ℝ → X) (d.centerMap ζ x))) :=
    (ContinuousLinearMap.smulRightL ℝ X X).continuous₂.comp
      ((continuous_derivCenterFiber d ζ).prodMk hζ_deriv_center)
  have hcocycle : Continuous (fun x ↦ d.L + derivFiber d ζ x) :=
    continuous_const.add (continuous_derivFiber d ζ)
  have hbracket : Continuous (fun x ↦
      d.L + derivFiber d ζ x -
        (derivCenterFiber d ζ x).smulRight
          (deriv (ζ : ℝ → X) (d.centerMap ζ x))) :=
    hcocycle.sub hfeedback
  apply Continuous.congr (hscale.smul hbracket)
  intro x
  exact (metricReservedTopCoefficient.eq_1 d ζ r x).symm

/-- Helper for Infrastructure I.16a: the complete lower-order reserved-top forcing is
continuous from exactly `ζ ∈ C^(r-1)`; no order-`r` graph derivative is used. -/
theorem metricReservedTopForcing_continuous_of_previousOrder
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X)) :
    Continuous (metricReservedTopForcing d ζ r) := by
  have hone_previous_nat : 1 ≤ r - 1 := by
    omega
  have hone_previous :
      (1 : WithTop ℕ∞) ≤ ((r - 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast hone_previous_nat
  have hζ_one : ContDiff ℝ 1 (ζ : ℝ → X) := hprev.of_le hone_previous
  have hscale : Continuous (fun x ↦ (deriv (d.centerMap ζ) x)⁻¹ ^ r) :=
    centerMap_deriv_inv_pow_continuous d ζ hζ_one r
  have hstable_atomic :=
    metricStableAtomicEvaluation_continuous_of_previousOrder d ζ hr hrν hprev
  have hstable_residual :=
    iteratedDeriv_fiber_remainder_length_one_residual_continuous_of_previousOrder
      d ζ hr hrν hprev
  have hcenter_atomic :=
    metricCenterAtomicEvaluation_continuous_of_previousOrder d ζ hr hrν hprev
  have hcenter_residual :=
    iteratedDeriv_center_remainder_length_one_residual_continuous_of_previousOrder
      d ζ hr hrν hprev
  have hpreviousν_nat : r - 1 ≤ d.nu := (Nat.sub_le r 1).trans hrν
  have hpreviousν : ((r - 1 : ℕ) : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hpreviousν_nat
  have hcenter : ContDiff ℝ (r - 1) (d.centerMap ζ) :=
    centerMap_contDiff_of_prev d ζ hpreviousν hprev
  have hζ_deriv : Continuous (deriv (ζ : ℝ → X)) := by
    have hiterated := hζ_one.continuous_iteratedDeriv 1 le_rfl
    simpa only [iteratedDeriv_one] using hiterated
  have hζ_deriv_center :
      Continuous (fun x ↦ deriv (ζ : ℝ → X) (d.centerMap ζ x)) :=
    hζ_deriv.comp hcenter.continuous
  have hζ_residual :=
    iteratedDeriv_zeta_comp_centerMap_length_one_residual_continuous_of_previousOrder
      d ζ hr hrν hprev
  have hstable_block := hstable_atomic.add hstable_residual
  have hcenter_block := hcenter_atomic.add hcenter_residual
  have hfeedback := hcenter_block.smul hζ_deriv_center
  have hbracket := (hstable_block.sub hfeedback).sub hζ_residual
  apply Continuous.congr (hscale.smul hbracket)
  intro x
  exact (metricReservedTopForcing.eq_1 d ζ r x).symm

/-- Helper for Infrastructure I.16a: outside the support of `R`, every stable-coordinate
iterated jet of `R` vanishes. -/
private theorem iteratedFDeriv_stableR_eq_zero_of_notMem_tsupport
    (d : MetricGraphTransformData X) (n : ℕ) {z : ℝ × X}
    (hz : z ∉ tsupport d.R) :
    iteratedFDeriv ℝ n (fun w : ℝ × X ↦ (d.R w).2) z = 0 := by
  have hsupport :
      tsupport (fun w : ℝ × X ↦ (d.R w).2) ⊆ tsupport d.R := by
    have hcomp : (fun w : ℝ × X ↦ (d.R w).2) =
        (ContinuousLinearMap.snd ℝ ℝ X) ∘ d.R := by
      funext w
      rfl
    rw [hcomp]
    exact tsupport_comp_subset (map_zero _) d.R
  exact iteratedFDeriv_eq_zero_of_notMem_tsupport
    (fun w : ℝ × X ↦ (d.R w).2) n (fun hw ↦ hz (hsupport hw))

/-- Helper for Infrastructure I.16a: outside the support of `R`, every center-coordinate
iterated jet of `R` vanishes. -/
private theorem iteratedFDeriv_centerR_eq_zero_of_notMem_tsupport
    (d : MetricGraphTransformData X) (n : ℕ) {z : ℝ × X}
    (hz : z ∉ tsupport d.R) :
    iteratedFDeriv ℝ n (fun w : ℝ × X ↦ (d.R w).1) z = 0 := by
  have hsupport :
      tsupport (fun w : ℝ × X ↦ (d.R w).1) ⊆ tsupport d.R := by
    have hcomp : (fun w : ℝ × X ↦ (d.R w).1) =
        (ContinuousLinearMap.fst ℝ ℝ X) ∘ d.R := by
      funext w
      rfl
    rw [hcomp]
    exact tsupport_comp_subset (map_zero _) d.R
  exact iteratedFDeriv_eq_zero_of_notMem_tsupport
    (fun w : ℝ × X ↦ (d.R w).1) n (fun hw ↦ hz (hsupport hw))

/-- Helper for Infrastructure I.16a: the inverse center map cancels the center map at every
source coordinate. -/
private theorem inverseCenter_centerMap
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) (x : ℝ) :
    d.inverseCenter ζ (d.centerMap ζ x) = x := by
  rw [d.inverseCenter_eq ζ]
  exact Function.leftInverse_invFun (d.centerMap_bijective ζ).1 x

/-- Helper for Infrastructure I.16a: on a fixed graph, the previous-order reserved-top forcing
has compact support. Its support is controlled by the center projection of `tsupport d.R`
together with the inverse-center image of `tsupport ζ`. -/
theorem metricReservedTopForcing_hasCompactSupport
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) (r : ℕ) :
    HasCompactSupport (metricReservedTopForcing d ζ r) := by
  let KR : Set ℝ := Prod.fst '' tsupport d.R
  let Kζ : Set ℝ := d.inverseCenter ζ '' tsupport (ζ : ℝ → X)
  have hKR : IsCompact KR := by
    exact d.hR_support.image continuous_fst
  have hKζ : IsCompact Kζ := by
    have hinverse : Continuous (d.inverseCenter ζ) :=
      (d.inverseCenter_lipschitzWith ζ).continuous
    exact (fixedGraph_hasCompactSupport d ζ hfixed).image hinverse
  apply HasCompactSupport.intro (hKR.union hKζ)
  intro x hx
  have hxKR : x ∉ KR := fun hxmem ↦ hx (Or.inl hxmem)
  have hxKζ : x ∉ Kζ := fun hxmem ↦ hx (Or.inr hxmem)
  have hgraph : (x, (ζ : ℝ → X) x) ∉ tsupport d.R := by
    intro hmem
    apply hxKR
    exact ⟨(x, (ζ : ℝ → X) x), hmem, rfl⟩
  have hcenter : d.centerMap ζ x ∉ tsupport (ζ : ℝ → X) := by
    intro hmem
    apply hxKζ
    refine ⟨d.centerMap ζ x, hmem, ?_⟩
    exact inverseCenter_centerMap d ζ x
  have hstable_atomic :
      iteratedFDeriv ℝ r (fun z : ℝ × X ↦ (d.R z).2)
        (x, (ζ : ℝ → X) x)
        (fun _ : Fin r ↦
          iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) x) = 0 := by
    rw [iteratedFDeriv_stableR_eq_zero_of_notMem_tsupport d r hgraph]
    exact zero_apply _
  have hcenter_atomic :
      iteratedFDeriv ℝ r (fun z : ℝ × X ↦ (d.R z).1)
        (x, (ζ : ℝ → X) x)
        (fun _ : Fin r ↦
          iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) x) = 0 := by
    rw [iteratedFDeriv_centerR_eq_zero_of_notMem_tsupport d r hgraph]
    exact zero_apply _
  have hstable_residual :
      ∑ c ∈ (Finset.univ.filter
          (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
        iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).2)
          (x, (ζ : ℝ → X) x)
          (fun j ↦ iteratedDeriv (c.partSize j)
            (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) x) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    rw [iteratedFDeriv_stableR_eq_zero_of_notMem_tsupport d c.length hgraph]
    exact zero_apply _
  have hcenter_residual :
      ∑ c ∈ (Finset.univ.filter
          (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
        iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).1)
          (x, (ζ : ℝ → X) x)
          (fun j ↦ iteratedDeriv (c.partSize j)
            (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) x) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    rw [iteratedFDeriv_centerR_eq_zero_of_notMem_tsupport d c.length hgraph]
    exact zero_apply _
  have hζ_residual :
      ∑ c ∈ (Finset.univ.filter
          (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
        iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ x)
          (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) x) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    rw [iteratedFDeriv_eq_zero_of_notMem_tsupport
      (ζ : ℝ → X) c.length hcenter]
    exact zero_apply _
  rw [metricReservedTopForcing.eq_1]
  rw [hstable_atomic, hstable_residual, hcenter_atomic, hcenter_residual, hζ_residual]
  simp only [zero_add, zero_smul, smul_zero, sub_zero]

/-- Helper for Infrastructure I.16a: the reserved-top contraction factor as a nonnegative real
number. -/
def metricReservedTopFactor
    (d : MetricGraphTransformData X) (r : ℕ) : ℝ≥0 :=
  metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope * d.lower⁻¹ ^ r

/-- Helper for Infrastructure I.16a: the real coercion of `metricReservedTopFactor` is the
sharp coefficient appearing in the bunching inequality. -/
theorem metricReservedTopFactor_coe
    (d : MetricGraphTransformData X) (r : ℕ) :
    (metricReservedTopFactor d r : ℝ) =
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r := by
  simp only [metricReservedTopFactor, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv]

/-- Helper for Infrastructure I.16a: the reserved-top contraction factor is nonnegative. -/
theorem metricReservedTopFactor_nonneg
    (d : MetricGraphTransformData X) (r : ℕ) :
    (0 : ℝ) ≤ (metricReservedTopFactor d r : ℝ) := by
  exact NNReal.coe_nonneg (metricReservedTopFactor d r)

/-- Helper for Infrastructure I.16a: the complete reserved-top coefficient is bounded by the
bundled nonnegative contraction factor. -/
theorem norm_metricReservedTopCoefficient_le_factor
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X)) (x : ℝ) :
    ‖metricReservedTopCoefficient d ζ r x‖ ≤
      (metricReservedTopFactor d r : ℝ) := by
  have hζ_one := contDiff_one_of_previousOrder hr hprev
  rw [metricReservedTopFactor_coe]
  exact norm_metricReservedTopCoefficient_le d ζ hζ_one hfixed r x

/-- Helper for Infrastructure I.16a: the complete reserved-top coefficient bundled as a bounded
continuous operator-valued section. -/
def metricReservedTopCoefficientSection
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X)) :
    BoundedContinuousFunction ℝ (X →L[ℝ] X) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (metricReservedTopCoefficient d ζ r)
    (metricReservedTopCoefficient_continuous d ζ hr hprev)
    (metricReservedTopFactor d r)
    (norm_metricReservedTopCoefficient_le_factor d ζ hfixed hr hprev)

/-- Helper for Infrastructure I.16a: evaluation of the bundled coefficient is the original
reserved-top coefficient. -/
theorem metricReservedTopCoefficientSection_apply
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X)) (x : ℝ) :
    metricReservedTopCoefficientSection d ζ hfixed hr hprev x =
      metricReservedTopCoefficient d ζ r x := by
  rfl

/-- Helper for Infrastructure I.16a: compact support and continuity give a nonnegative uniform
bound for the reserved-top forcing. -/
theorem exists_metricReservedTopForcing_norm_bound
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖metricReservedTopForcing d ζ r x‖ ≤ C := by
  have hcontinuous :=
    metricReservedTopForcing_continuous_of_previousOrder d ζ hr hrν hprev
  obtain ⟨C, hC⟩ :=
    hcontinuous.bounded_above_of_compact_support
      (metricReservedTopForcing_hasCompactSupport d ζ hfixed r)
  have hC_nonneg : 0 ≤ C :=
    (norm_nonneg (metricReservedTopForcing d ζ r 0)).trans (hC 0)
  exact ⟨C, hC_nonneg, hC⟩

/-- Helper for Infrastructure I.16a: a selected nonnegative uniform norm bound for the
reserved-top forcing. -/
noncomputable def metricReservedTopForcingBound
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X)) : ℝ :=
  Classical.choose
    (exists_metricReservedTopForcing_norm_bound d ζ hfixed hr hrν hprev)

/-- Helper for Infrastructure I.16a: the selected forcing bound is nonnegative. -/
theorem metricReservedTopForcingBound_nonneg
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X)) :
    0 ≤ metricReservedTopForcingBound d ζ hfixed hr hrν hprev := by
  exact (Classical.choose_spec
    (exists_metricReservedTopForcing_norm_bound d ζ hfixed hr hrν hprev)).1

/-- Helper for Infrastructure I.16a: the selected forcing bound controls every source value. -/
theorem norm_metricReservedTopForcing_le_bound
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X)) (x : ℝ) :
    ‖metricReservedTopForcing d ζ r x‖ ≤
      metricReservedTopForcingBound d ζ hfixed hr hrν hprev := by
  exact (Classical.choose_spec
    (exists_metricReservedTopForcing_norm_bound d ζ hfixed hr hrν hprev)).2 x

/-- Helper for Infrastructure I.16a: the lower-order forcing bundled as a bounded continuous
section on source coordinates. -/
def metricReservedTopForcingSection
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X)) :
    BoundedContinuousFunction ℝ X :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (metricReservedTopForcing d ζ r)
    (metricReservedTopForcing_continuous_of_previousOrder d ζ hr hrν hprev)
    (metricReservedTopForcingBound d ζ hfixed hr hrν hprev)
    (norm_metricReservedTopForcing_le_bound d ζ hfixed hr hrν hprev)

/-- Helper for Infrastructure I.16a: evaluation of the bundled forcing is the original
reserved-top forcing. -/
theorem metricReservedTopForcingSection_apply
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X)) (x : ℝ) :
    metricReservedTopForcingSection d ζ hfixed hr hrν hprev x =
      metricReservedTopForcing d ζ r x := by
  rfl

/-- Helper for Infrastructure I.16a: the output-coordinate value of the reserved-top affine
operator. -/
def metricReservedTopOperatorValue
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) (r : ℕ)
    (b : BoundedContinuousFunction ℝ X) (y : ℝ) : X :=
  metricReservedTopCoefficient d ζ r (d.inverseCenter ζ y)
      (b (d.inverseCenter ζ y)) +
    metricReservedTopForcing d ζ r (d.inverseCenter ζ y)

/-- Helper for Infrastructure I.16a: the output-coordinate affine operator value is continuous. -/
theorem metricReservedTopOperatorValue_continuous
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X))
    (b : BoundedContinuousFunction ℝ X) :
    Continuous (metricReservedTopOperatorValue d ζ r b) := by
  have hinverse : Continuous (d.inverseCenter ζ) :=
    (d.inverseCenter_lipschitzWith ζ).continuous
  have hcoefficient : Continuous (fun y ↦
      metricReservedTopCoefficient d ζ r (d.inverseCenter ζ y)) :=
    (metricReservedTopCoefficient_continuous d ζ hr hprev).comp hinverse
  have hsection : Continuous (fun y ↦ b (d.inverseCenter ζ y)) :=
    b.continuous.comp hinverse
  have hlinear : Continuous (fun y ↦
      metricReservedTopCoefficient d ζ r (d.inverseCenter ζ y)
        (b (d.inverseCenter ζ y))) :=
    hcoefficient.clm_apply hsection
  have hforcing : Continuous (fun y ↦
      metricReservedTopForcing d ζ r (d.inverseCenter ζ y)) :=
    (metricReservedTopForcing_continuous_of_previousOrder d ζ hr hrν hprev).comp hinverse
  exact hlinear.add hforcing

/-- Helper for Infrastructure I.16a: the affine operator value has a uniform bound obtained from
the sharp coefficient factor and the bundled forcing norm. -/
theorem norm_metricReservedTopOperatorValue_le
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X))
    (b : BoundedContinuousFunction ℝ X) (y : ℝ) :
    ‖metricReservedTopOperatorValue d ζ r b y‖ ≤
      (metricReservedTopFactor d r : ℝ) * ‖b‖ +
        ‖metricReservedTopForcingSection d ζ hfixed hr hrν hprev‖ := by
  let x := d.inverseCenter ζ y
  have hone_previous_nat : 1 ≤ r - 1 := by
    omega
  have hone_previous :
      (1 : WithTop ℕ∞) ≤ ((r - 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast hone_previous_nat
  have hζ_one : ContDiff ℝ 1 (ζ : ℝ → X) := hprev.of_le hone_previous
  have hcoefficient :=
    metricReservedTopCoefficient_apply_norm_le d ζ hζ_one hfixed r x (b x)
  have hb : ‖b x‖ ≤ ‖b‖ := BoundedContinuousFunction.norm_coe_le_norm b x
  have hfactor_nonneg : 0 ≤ (metricReservedTopFactor d r : ℝ) :=
    metricReservedTopFactor_nonneg d r
  have hlinear :
      ‖metricReservedTopCoefficient d ζ r x (b x)‖ ≤
        (metricReservedTopFactor d r : ℝ) * ‖b‖ := by
    rw [metricReservedTopFactor_coe]
    exact hcoefficient.trans
      (mul_le_mul_of_nonneg_left hb hfactor_nonneg)
  have hforcing :
      ‖metricReservedTopForcing d ζ r x‖ ≤
        ‖metricReservedTopForcingSection d ζ hfixed hr hrν hprev‖ := by
    exact BoundedContinuousFunction.norm_coe_le_norm
      (metricReservedTopForcingSection d ζ hfixed hr hrν hprev) x
  unfold metricReservedTopOperatorValue
  exact (norm_add_le _ _).trans (add_le_add hlinear hforcing)

/-- Helper for Infrastructure I.16a: the uniform bound used to bundle the affine operator is
nonnegative. -/
theorem metricReservedTopOperatorValue_bound_nonneg
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X))
    (b : BoundedContinuousFunction ℝ X) :
    0 ≤ (metricReservedTopFactor d r : ℝ) * ‖b‖ +
      ‖metricReservedTopForcingSection d ζ hfixed hr hrν hprev‖ := by
  positivity

/-- Helper for Infrastructure I.16a: the paper-faithful reserved-top affine operator on bounded
continuous sections, evaluated in output coordinates through `d.inverseCenter ζ`. -/
def metricReservedTopOperator
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X))
    (b : BoundedContinuousFunction ℝ X) : BoundedContinuousFunction ℝ X :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (metricReservedTopOperatorValue d ζ r b)
    (metricReservedTopOperatorValue_continuous d ζ hr hrν hprev b)
    ((metricReservedTopFactor d r : ℝ) * ‖b‖ +
      ‖metricReservedTopForcingSection d ζ hfixed hr hrν hprev‖)
    (norm_metricReservedTopOperatorValue_le d ζ hfixed hr hrν hprev b)

/-- Helper for Infrastructure I.16a: evaluation of the bundled affine operator exposes its
output-coordinate formula. -/
theorem metricReservedTopOperator_apply
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X))
    (b : BoundedContinuousFunction ℝ X) (y : ℝ) :
    metricReservedTopOperator d ζ hfixed hr hrν hprev b y =
      metricReservedTopCoefficient d ζ r (d.inverseCenter ζ y)
          (b (d.inverseCenter ζ y)) +
        metricReservedTopForcing d ζ r (d.inverseCenter ζ y) := by
  rfl

/-- Helper for Infrastructure I.16a: at a source center coordinate, the affine operator has the
untranslated source formula `C x (b x) + F x`. -/
theorem metricReservedTopOperator_apply_centerMap
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X))
    (b : BoundedContinuousFunction ℝ X) (x : ℝ) :
    metricReservedTopOperator d ζ hfixed hr hrν hprev b (d.centerMap ζ x) =
      metricReservedTopCoefficient d ζ r x (b x) +
        metricReservedTopForcing d ζ r x := by
  rw [metricReservedTopOperator_apply, inverseCenter_centerMap]

/-- Helper for Infrastructure I.16a: the reserved-top affine operator has the sharp pointwise
contraction factor `metricGraphTransformRate * lower⁻ʳ`. -/
theorem metricReservedTopOperator_dist_apply_le
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X))
    (b c : BoundedContinuousFunction ℝ X) (y : ℝ) :
    dist (metricReservedTopOperator d ζ hfixed hr hrν hprev b y)
        (metricReservedTopOperator d ζ hfixed hr hrν hprev c y) ≤
      (metricReservedTopFactor d r : ℝ) * dist b c := by
  let x := d.inverseCenter ζ y
  have hone_previous_nat : 1 ≤ r - 1 := by
    omega
  have hone_previous :
      (1 : WithTop ℕ∞) ≤ ((r - 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast hone_previous_nat
  have hζ_one : ContDiff ℝ 1 (ζ : ℝ → X) := hprev.of_le hone_previous
  have hcoefficient := metricReservedTopCoefficient_apply_norm_le d ζ hζ_one hfixed r x
    (b x - c x)
  have heval : dist (b x) (c x) ≤ dist b c :=
    BoundedContinuousFunction.dist_coe_le_dist (f := b) (g := c) x
  have hfactor_nonneg : 0 ≤ (metricReservedTopFactor d r : ℝ) :=
    metricReservedTopFactor_nonneg d r
  rw [metricReservedTopOperator_apply, metricReservedTopOperator_apply, dist_eq_norm]
  have hdifference :
      metricReservedTopCoefficient d ζ r x (b x) + metricReservedTopForcing d ζ r x -
          (metricReservedTopCoefficient d ζ r x (c x) +
            metricReservedTopForcing d ζ r x) =
        metricReservedTopCoefficient d ζ r x (b x - c x) := by
    rw [map_sub]
    module
  dsimp only [x] at hcoefficient hdifference ⊢
  have hcoefficient_factor :
      ‖metricReservedTopCoefficient d ζ r (d.inverseCenter ζ y)
          (b (d.inverseCenter ζ y) - c (d.inverseCenter ζ y))‖ ≤
        (metricReservedTopFactor d r : ℝ) *
          dist (b (d.inverseCenter ζ y)) (c (d.inverseCenter ζ y)) := by
    rw [metricReservedTopFactor_coe]
    simpa only [dist_eq_norm] using hcoefficient
  have hnorm_difference :
      ‖metricReservedTopCoefficient d ζ r (d.inverseCenter ζ y) (b (d.inverseCenter ζ y)) +
          metricReservedTopForcing d ζ r (d.inverseCenter ζ y) -
        (metricReservedTopCoefficient d ζ r (d.inverseCenter ζ y) (c (d.inverseCenter ζ y)) +
          metricReservedTopForcing d ζ r (d.inverseCenter ζ y))‖ =
      ‖metricReservedTopCoefficient d ζ r (d.inverseCenter ζ y)
          (b (d.inverseCenter ζ y) - c (d.inverseCenter ζ y))‖ := by
    exact congrArg (fun z : X ↦ ‖z‖) hdifference
  calc
    ‖metricReservedTopCoefficient d ζ r (d.inverseCenter ζ y) (b (d.inverseCenter ζ y)) +
          metricReservedTopForcing d ζ r (d.inverseCenter ζ y) -
        (metricReservedTopCoefficient d ζ r (d.inverseCenter ζ y) (c (d.inverseCenter ζ y)) +
          metricReservedTopForcing d ζ r (d.inverseCenter ζ y))‖ =
        ‖metricReservedTopCoefficient d ζ r (d.inverseCenter ζ y)
            (b (d.inverseCenter ζ y) - c (d.inverseCenter ζ y))‖ := hnorm_difference
    _ ≤ (metricReservedTopFactor d r : ℝ) *
          dist (b (d.inverseCenter ζ y)) (c (d.inverseCenter ζ y)) := hcoefficient_factor
    _ ≤ (metricReservedTopFactor d r : ℝ) * dist b c :=
      mul_le_mul_of_nonneg_left heval hfactor_nonneg

/-- Infrastructure I.16a: the order-`r` bunching inequality makes the reserved-top affine
operator a `ContractingWith` map. -/
theorem metricReservedTopOperator_contractingWith
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1) :
    ContractingWith (metricReservedTopFactor d r)
      (metricReservedTopOperator d ζ hfixed hr hrν hprev) := by
  have hfactor_lt_one_real :
      (metricReservedTopFactor d r : ℝ) < 1 := by
    rw [metricReservedTopFactor_coe]
    exact h_bunching
  have hfactor_lt_one : metricReservedTopFactor d r < 1 := by
    exact_mod_cast hfactor_lt_one_real
  refine ⟨hfactor_lt_one, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro b c
  apply BoundedContinuousFunction.dist_le_iff_of_nonempty.mpr
  intro y
  exact metricReservedTopOperator_dist_apply_le
    d ζ hfixed hr hrν hprev b c y

/-- Helper for Infrastructure I.16a: the canonical reserved-top bounded continuous section is
the fixed point of the inverse-center affine operator. -/
noncomputable def metricReservedTopFixedSection
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1) : BoundedContinuousFunction ℝ X :=
  ContractingWith.fixedPoint
    (metricReservedTopOperator d ζ hfixed hr hrν hprev)
    (metricReservedTopOperator_contractingWith
      d ζ hfixed hr hrν hprev h_bunching)

/-- Helper for Infrastructure I.16a: the canonical reserved-top section satisfies the affine
fixed-section equation. -/
theorem metricReservedTopFixedSection_is_fixed
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1) :
    metricReservedTopOperator d ζ hfixed hr hrν hprev
        (metricReservedTopFixedSection d ζ hfixed hr hrν hprev h_bunching) =
      metricReservedTopFixedSection d ζ hfixed hr hrν hprev h_bunching := by
  exact (metricReservedTopOperator_contractingWith
    d ζ hfixed hr hrν hprev h_bunching).fixedPoint_isFixedPt

/-- Helper for Infrastructure I.16a: every fixed bounded section of the reserved-top affine
operator is the canonical fixed section. -/
theorem metricReservedTopFixedSection_unique
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1)
    (b : BoundedContinuousFunction ℝ X)
    (hb : metricReservedTopOperator d ζ hfixed hr hrν hprev b = b) :
    b = metricReservedTopFixedSection d ζ hfixed hr hrν hprev h_bunching := by
  exact (metricReservedTopOperator_contractingWith
    d ζ hfixed hr hrν hprev h_bunching).fixedPoint_unique hb

/-- Helper for Infrastructure I.16a: in source coordinates, the canonical fixed section obeys
exactly the paper's affine reserved-top equation. -/
theorem metricReservedTopFixedSection_sourceEquation
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X))
    (h_bunching :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1) (x : ℝ) :
    metricReservedTopFixedSection d ζ hfixed hr hrν hprev h_bunching
        (d.centerMap ζ x) =
      metricReservedTopCoefficient d ζ r x
          (metricReservedTopFixedSection d ζ hfixed hr hrν hprev h_bunching x) +
        metricReservedTopForcing d ζ r x := by
  have hfixedSection :=
    metricReservedTopFixedSection_is_fixed d ζ hfixed hr hrν hprev h_bunching
  have hpoint := congrArg
    (fun b : BoundedContinuousFunction ℝ X ↦ b (d.centerMap ζ x)) hfixedSection
  rw [metricReservedTopOperator_apply_centerMap] at hpoint
  exact hpoint.symm

end LocalInvariantGraph
