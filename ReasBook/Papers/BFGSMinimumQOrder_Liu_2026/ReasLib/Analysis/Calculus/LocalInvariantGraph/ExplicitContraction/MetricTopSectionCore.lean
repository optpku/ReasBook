module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricFiberDerivative
import all ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricFiberDerivative
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Prod

public section

noncomputable section

open scoped NNReal Topology
open Filter Set

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## The metric top-section core: `C^{m+1}` regularity of the fixed graph from bunching.

This file closes the last Claim-1 gap at `MetricFiniteSmooth.lean:163`: producing the holonomic
top-section witness for the metric fixed graph `ζ` at every order `1 ≤ r ≤ d.nu`.

The analytic content is the **fiber-contraction cocycle**.  The fixed-graph equation
`ζ ∘ φ = L ∘ ζ + g` (with `φ = centerMap ζ`, `g u = (R (u, ζ u)).2`) is differentiated `m` times
via the Faà-di-Bruno formula.  The atomic term carries the full chain-rule derivative of the fiber
`G = snd ∘ R` along the diagonal jet of `pair = (id, ζ)`; the **bivariate linear-isolation lemma**
`fiber_atomic_isolate` splits that into the first-slot part `∂₁R` and the second-slot (fiber) part
`derivFiber d ζ u (iteratedDeriv m ζ u)`.  The second-slot part feeds the contraction cocycle
`𝒯V(w) = (φ′u)⁻¹ (L + ∂₂R) V(φu)`; the non-atomic Faà-di-Bruno sum is strictly lower order in `ζ`.

The recurrence `‖D(w,t)‖ ≤ p ‖D(u,σ)‖ + o(t)` (with `p = rate·lower⁻¹^m`, change-of-variables
`c = lower⁻¹`, so `p·c = h_bunching (m+1)`) is fed to `radiusEnvelope_sublinear_of_recurrence`
and discharged by `hasDerivAt_of_secant_bounds` (both in the assembly leaf).  The derivative-value
section `v` is the continuous fixed point of the cocycle on bounded sections.

STATUS: scaffold — lemmas added incrementally against `lake build`. -/

/-- **Bivariate linear isolation, order `m = 1`.** At a point where the graph is differentiable,
the atomic fiber term splits into the stable-coordinate first-slot part
`(∂₁R(u,ζu) • 1).2` and the fiber (second-slot) part
`derivFiber d ζ u (iteratedDeriv 1 ζ u)`. This is the chain rule for `G ∘ pair`
(`G = snd ∘ R`, `pair y = (y, ζ y)`), made explicit. The differentiability hypothesis is
necessary because `fderiv` is defined to be zero at a nondifferentiability point. -/
theorem fiber_atomic_isolate_one
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) (u : ℝ)
    (hζ : DifferentiableAt ℝ (ζ : ℝ → X) u) :
    iteratedFDeriv ℝ 1 (fun z : ℝ × X ↦ (d.R z).2) (u, (ζ : ℝ → X) u)
        (fun _ : Fin 1 ↦ iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u) =
      (fderiv ℝ (fun z : ℝ × X ↦ (d.R z).2) (u, (ζ : ℝ → X) u)) (1, 0) +
        derivFiber d ζ u (iteratedDeriv 1 (ζ : ℝ → X) u) := by
  rw [iteratedFDeriv_one_apply]
  simp only [iteratedDeriv_one]
  have hpair : HasFDerivAt (fun y : ℝ => (y, (ζ : ℝ → X) y))
      ((1 : ℝ →L[ℝ] ℝ).prod (fderiv ℝ (ζ : ℝ → X) u)) u := by
    exact (hasFDerivAt_id u).prodMk hζ.hasFDerivAt
  rw [hpair.hasDerivAt.deriv]
  have hzero_lt_two : 0 < (2 : ℕ) := by norm_num
  have hnu_pos : 0 < d.nu := lt_of_lt_of_le hzero_lt_two d.hnu
  have hnu_ne_nat : d.nu ≠ 0 := Nat.ne_of_gt hnu_pos
  have hnu_ne : (d.nu : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast hnu_ne_nat
  have hRdiff : DifferentiableAt ℝ d.R (u, (ζ : ℝ → X) u) :=
    d.hR_smooth.contDiffAt.differentiableAt hnu_ne
  have hGderiv : fderiv ℝ (fun z : ℝ × X ↦ (d.R z).2) (u, (ζ : ℝ → X) u) =
      (ContinuousLinearMap.snd ℝ ℝ X).comp
        (fderiv ℝ d.R (u, (ζ : ℝ → X) u)) := by
    have h := fderiv_comp (x := (u, (ζ : ℝ → X) u))
      (f := d.R) (g := (Prod.snd : (ℝ × X) → X))
      (ContinuousLinearMap.snd ℝ ℝ X).differentiableAt hRdiff
    simpa only [Function.comp_def, fderiv_snd] using h
  rw [hGderiv]
  simp only [derivFiber, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.inr_apply]
  have hdecomp :
      ((1 : ℝ →L[ℝ] ℝ) 1, (fderiv ℝ (ζ : ℝ → X) u) 1) =
        ((1 : ℝ), (0 : X)) + ((0 : ℝ), deriv (ζ : ℝ → X) u) := by
    apply Prod.ext
    · change 1 = 1 + 0
      exact (add_zero 1).symm
    · change (fderiv ℝ (ζ : ℝ → X) u) 1 = 0 + (fderiv ℝ (ζ : ℝ → X) u) 1
      exact (zero_add _).symm
  rw [hdecomp, map_add]
  exact (ContinuousLinearMap.snd ℝ ℝ X).map_add _ _

/-- Helper for Infrastructure I.16a: at the base point, the center-stable derivative
annihilates the stable-coordinate contribution to the order-one fiber atom. -/
theorem fiber_atomic_isolate_one_at_origin
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hζ : DifferentiableAt ℝ (ζ : ℝ → X) 0)
    (hR_deriv : HasFDerivAt d.R (LocalCutoff.centerStable d.L) (0, 0)) :
    iteratedFDeriv ℝ 1 (fun z : ℝ × X ↦ (d.R z).2) (0, (ζ : ℝ → X) 0)
        (fun _ : Fin 1 ↦
          iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) 0) =
      derivFiber d ζ 0 (iteratedDeriv 1 (ζ : ℝ → X) 0) := by
  have hsplit := fiber_atomic_isolate_one d ζ 0 hζ
  have hζ0 : (ζ : ℝ → X) 0 = 0 := SmallLipschitzGraph.zero_apply ζ
  have hRdiff : DifferentiableAt ℝ d.R (0, (ζ : ℝ → X) 0) := by
    rw [hζ0]
    exact hR_deriv.differentiableAt
  have hGderiv :
      fderiv ℝ (fun z : ℝ × X ↦ (d.R z).2) (0, (ζ : ℝ → X) 0) =
        (ContinuousLinearMap.snd ℝ ℝ X).comp
          (fderiv ℝ d.R (0, (ζ : ℝ → X) 0)) := by
    have h := fderiv_comp (x := (0, (ζ : ℝ → X) 0))
      (f := d.R) (g := (Prod.snd : (ℝ × X) → X))
      (ContinuousLinearMap.snd ℝ ℝ X).differentiableAt hRdiff
    simpa only [Function.comp_def, fderiv_snd] using h
  have hstable :
      (fderiv ℝ (fun z : ℝ × X ↦ (d.R z).2) (0, (ζ : ℝ → X) 0)) (1, 0) = 0 := by
    rw [hGderiv, hζ0, hR_deriv.fderiv]
    simp only [ContinuousLinearMap.comp_apply, LocalCutoff.centerStable_apply,
      ContinuousLinearMap.coe_snd', map_zero]
  rw [hsplit, hstable, zero_add]

/-! ## Compact support of the fixed graph — the localization lever.

The metric fixed graph `ζ` vanishes outside a fixed ball `closedBall 0 R` (with `R` from
`d.hR_support`): outside the remainder's support the center map is the identity and the
fixed-point equation degenerates to `ζ u = L (ζ u)`, which the strict contraction `‖L‖ < 1`
forces to `0`.  This is proved as `metricFixedGraph_hasCompactSupport` in `MetricFiniteSmooth`,
but that file is downstream of this leaf; the proof uses only fields of
`MetricGraphTransformData` (`fixedGraph_equation`, `centerMap_bijective`, `hR_support`, `hL`,
`hlinearRate`), so it is reproduced here for use by the top-section core.

The payoff: the top-section obligation `∀ u, HasDerivAt (iteratedDeriv m ζ) (v u) u` need only
be verified on the compact set `closedBall 0 R`; outside it `ζ` — and hence every iterated
derivative — is locally constant `0`, so the derivative is trivially `0`.  This upgrades a
pointwise `o(t)` control to the compact-uniform control the recurrence envelope requires. -/

/-- The metric fixed graph has compact support (reproduced from `MetricFiniteSmooth` so the
top-section core can localize its obligations to a compact set).  Uses only fields of
`MetricGraphTransformData`. -/
theorem fixedGraph_hasCompactSupport
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) :
    HasCompactSupport (ζ : ℝ → X) := by
  have hinverse_def : d.inverseCenter ζ = Function.invFun (d.centerMap ζ) :=
    d.inverseCenter_eq ζ
  have hcenter_def : d.centerMap ζ = fun u ↦ u + (d.R (u, ζ u)).1 := d.centerMap_eq ζ
  obtain ⟨Rr, hRr_nonneg, hRr⟩ := d.hR_support.isBounded.subset_ball_lt 0 (0 : ℝ × X)
  let R : ℝ := Rr
  have hR_nonneg : 0 ≤ R := hRr_nonneg.le
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R)
  intro u hu
  have hR_le : R ≤ |u| := by
    have hR_lt : R < |u| := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] using hu
    exact hR_lt.le
  have hR_point : R ≤ ‖(u, ζ u)‖ := by
    calc
      R ≤ |u| := hR_le
      _ = ‖u‖ := (Real.norm_eq_abs u).symm
      _ ≤ ‖(u, ζ u)‖ := by
        simpa only [Prod.fst] using (norm_fst_le (u, ζ u))
  have hR_zero_at_u : d.R (u, ζ u) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hpoint_lt : ‖(u, ζ u)‖ < Rr := by
      simpa only [Metric.mem_ball, dist_zero_right] using hRr hmem
    exact (not_lt_of_ge hR_point) (by simpa only [R] using hpoint_lt)
  have hnorm : ‖ζ u‖ ≤ (d.linearRate : ℝ) * ‖ζ u‖ := by
    have hfixed_u := d.fixedGraph_equation ζ hfixed u
    have hcenter_id : d.centerMap ζ u = u := by
      rw [hcenter_def]; dsimp only; rw [hR_zero_at_u]; simp only [Prod.fst_zero, add_zero]
    calc
      ‖ζ u‖ = ‖ζ (d.centerMap ζ u)‖ := by rw [hcenter_id]
      _ = ‖d.L (ζ u) + (d.R (u, ζ u)).2‖ := by rw [hfixed_u]
      _ = ‖d.L (ζ u)‖ := by rw [hR_zero_at_u, Prod.snd_zero, add_zero]
      _ ≤ ‖d.L‖ * ‖ζ u‖ := d.L.le_opNorm _
      _ ≤ (d.linearRate : ℝ) * ‖ζ u‖ := mul_le_mul_of_nonneg_right d.hL (norm_nonneg _)
  have hlinearRate_real : (d.linearRate : ℝ) < 1 := by exact_mod_cast d.hlinearRate
  have hnorm_zero : ‖ζ u‖ = 0 := by nlinarith [hlinearRate_real, norm_nonneg (ζ u)]
  exact norm_eq_zero.mp hnorm_zero

/-! ## Exterior triviality of the iterated derivative.

`ζ` has compact support (`fixedGraph_hasCompactSupport`), so outside the (closed) support `ζ`
agrees with the zero function on a whole neighbourhood.  Consequently every iterated derivative
`iteratedDeriv m ζ` agrees with `0` on that neighbourhood and therefore has derivative `0` there.
This is the localization lever: the top-section obligation `∀ u, HasDerivAt (iteratedDeriv m ζ) …`
is automatic off the compact support, so only the compact set `tsupport ζ` carries analytic
content. -/

/-- Off the (compact) support of `ζ`, the graph agrees with the zero function on a neighbourhood.
This is a purely topological consequence of `tsupport` being closed; no fixed-point data needed. -/
theorem fixedGraph_eventuallyEq_zero_of_notMem_tsupport
    {d : MetricGraphTransformData X}
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {u : ℝ} (hu : u ∉ tsupport (ζ : ℝ → X)) :
    (ζ : ℝ → X) =ᶠ[nhds u] (fun _ : ℝ ↦ (0 : X)) := by
  have hclosed : IsClosed (tsupport (ζ : ℝ → X)) := isClosed_tsupport _
  have hopen : IsOpen (tsupport (ζ : ℝ → X))ᶜ := hclosed.isOpen_compl
  have hmem : u ∈ (tsupport (ζ : ℝ → X))ᶜ := hu
  filter_upwards [hopen.mem_nhds hmem] with y hy
  exact image_eq_zero_of_notMem_tsupport (by simpa using hy)

/-- Off the support of `ζ`, every iterated derivative has derivative `0`.  This discharges the
top-section obligation on the complement of the compact support without any analytic work. -/
theorem hasDerivAt_iteratedDeriv_of_notMem_tsupport
    {d : MetricGraphTransformData X}
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (m : ℕ) {u : ℝ} (hu : u ∉ tsupport (ζ : ℝ → X)) :
    HasDerivAt (iteratedDeriv m (ζ : ℝ → X)) 0 u := by
  have hzero : (ζ : ℝ → X) =ᶠ[nhds u] (fun _ : ℝ ↦ (0 : X)) :=
    fixedGraph_eventuallyEq_zero_of_notMem_tsupport ζ hu
  have hiter : iteratedDeriv m (ζ : ℝ → X) =ᶠ[nhds u]
      iteratedDeriv m (fun _ : ℝ ↦ (0 : X)) := hzero.iteratedDeriv m
  have hconst : iteratedDeriv m (fun _ : ℝ ↦ (0 : X)) =ᶠ[nhds u] (fun _ : ℝ ↦ (0 : X)) := by
    filter_upwards with y
    simp only [iteratedDeriv_fun_const_zero]
  have heq : iteratedDeriv m (ζ : ℝ → X) =ᶠ[nhds u] (fun _ : ℝ ↦ (0 : X)) := hiter.trans hconst
  exact (heq.hasDerivAt_iff).mpr (hasDerivAt_const u (0 : X))

end LocalInvariantGraph
