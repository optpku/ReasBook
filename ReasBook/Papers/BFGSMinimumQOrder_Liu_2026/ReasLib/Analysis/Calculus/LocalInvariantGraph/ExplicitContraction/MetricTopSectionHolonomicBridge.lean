module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricPicardCertificate
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricInvariantGraph
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionHolonomicAssembly
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionDerivativeBridge
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.FaaDiBrunoAdapter
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Continuity
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.RadiusEnvelope
public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

public section

noncomputable section

open scoped NNReal Topology
open Filter Set

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Step 1–2: smoothness and antilipschitz control of the metric center coordinate.

The metric fixed graph `ζ` is only continuous by construction; its finite smoothness is
supplied order-by-order by the induction hypothesis.  The center coordinate `centerMap ζ`
inherits one order less than the ambient remainder `R`, and it is antilipschitz with constant
`d.lower` because its inverse is `lower⁻¹`-Lipschitz. -/

/-- Step 1: the metric center coordinate is as smooth as the current graph iterate.  From
`ContDiff ℝ k ζ` (the induction hypothesis) and the ambient remainder smoothness, the center
map `u ↦ u + (R (u, ζ u)).1` is `ContDiff ℝ k`. -/
theorem centerMap_contDiff_of_prev
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {k : ℕ} (hk : (k : WithTop ℕ∞) ≤ d.nu)
    (hprev : ContDiff ℝ k (ζ : ℝ → X)) :
    ContDiff ℝ k (d.centerMap ζ) := by
  rw [d.centerMap_eq ζ]
  -- `u ↦ (u, ζ u)` is `ContDiff ℝ k`.
  have hpair : ContDiff ℝ k (fun u : ℝ ↦ (u, ζ u)) :=
    contDiff_id.prodMk hprev
  -- `R` is `ContDiff ℝ d.nu`, hence `ContDiff ℝ k` after `of_le`.
  have hR : ContDiff ℝ k d.R := d.hR_smooth.of_le hk
  -- Compose and take the first coordinate, then add the identity.
  have hcomp : ContDiff ℝ k (fun u : ℝ ↦ d.R (u, ζ u)) := hR.comp hpair
  have hfst : ContDiff ℝ k (fun u : ℝ ↦ (d.R (u, ζ u)).1) :=
    contDiff_fst.comp hcomp
  exact contDiff_id.add hfst

/-- Step 2: the metric center coordinate is antilipschitz with the reciprocal lower rate.
Its global inverse is `lower⁻¹`-Lipschitz, so `dist u v ≤ lower⁻¹ · dist (centerMap u) (centerMap v)`,
which is exactly the antilipschitz bound with constant `d.lower⁻¹`. -/
theorem centerMap_antilipschitz
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) :
    AntilipschitzWith d.lower⁻¹ (d.centerMap ζ) := by
  rw [antilipschitzWith_iff_le_mul_dist]
  intro u v
  -- The inverse is `lower⁻¹`-Lipschitz; apply it to the center images and cancel.
  have hlip := (d.inverseCenter_lipschitzWith ζ).dist_le_mul
    (d.centerMap ζ u) (d.centerMap ζ v)
  have hleft : d.inverseCenter ζ (d.centerMap ζ u) = u := by
    rw [d.inverseCenter_eq ζ]
    exact Function.leftInverse_invFun (d.centerMap_bijective ζ).1 u
  have hright : d.inverseCenter ζ (d.centerMap ζ v) = v := by
    rw [d.inverseCenter_eq ζ]
    exact Function.leftInverse_invFun (d.centerMap_bijective ζ).1 v
  rw [hleft, hright] at hlip
  -- `hlip : dist u v ≤ lower⁻¹ * dist (centerMap u) (centerMap v)`.
  simpa only [NNReal.coe_inv] using hlip

/-! ## Step 3 scaffolding: definitional bridges.

The order-`r` obligation is `HasFDerivAt (fun y ↦ (ftaylorSeries ℝ ζ y) (r-1)) ((a u).curryLeft) u`.
By definition `ftaylorSeries ℝ ζ y m = iteratedFDeriv ℝ m ζ y`, and the scalar iterated
derivative is the all-ones evaluation of the multilinear one.  We record these as `rfl`
lemmas so the later steps may work on the scalar-valued `iteratedDeriv (r-1) ζ : ℝ → X`
and transfer through `ContinuousMultilinearMap.piFieldEquiv`. -/

/-- Definitional: the holonomic obligation's Taylor coefficient is the multilinear iterated
derivative. -/
theorem ftaylorSeries_eq_iteratedFDeriv (ζ : ℝ → X) (m : ℕ) (y : ℝ) :
    (ftaylorSeries ℝ ζ y) m = iteratedFDeriv ℝ m ζ y := rfl

/-- Definitional: the scalar iterated derivative is the all-ones evaluation of the
multilinear iterated derivative. -/
theorem iteratedDeriv_eq_iteratedFDeriv_ones (ζ : ℝ → X) (m : ℕ) (y : ℝ) :
    iteratedDeriv m ζ y = (iteratedFDeriv ℝ m ζ y) (fun _ : Fin m => (1 : ℝ)) := rfl

/-! ## Center-map derivative control (self-contained port).

The proven cocycle infrastructure (`MetricTopSectionSecantKernel`, `MetricTopSectionMasterIdentity`,
`MetricTopSectionCocycleRecurrence`) is downstream of this leaf, so its center-map derivative
estimates cannot be imported here.  We re-derive the small set we need directly from
`MetricPicardCertificate`: the center coordinate `Φ = centerMap ζ` is `id + c` with `c` the
`epsilon`-Lipschitz remainder coordinate, hence `Φ' u = 1 + c' u ≥ 1 - epsilon = lower > 0`. -/

/-- The center remainder coordinate `u ↦ (R (u, ζ u)).1` is `epsilon`-Lipschitz. -/
theorem centerRemainder_lipschitz
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) :
    LipschitzWith d.epsilon (fun u : ℝ ↦ (d.R (u, (ζ : ℝ → X) u)).1) := by
  have hgraph : LipschitzWith 1 (fun u : ℝ ↦ (u, (ζ : ℝ → X) u)) := by
    simpa only [Function.comp_def, id_eq, max_eq_left d.hslope_one] using
      LipschitzWith.id.prodMk (SmallLipschitzGraph.lipschitzWith ζ)
  simpa only [one_mul, mul_one, Function.comp_def] using
    LipschitzWith.prod_fst.comp (d.hR_lipschitz.comp hgraph)

/-- The center remainder coordinate `c u = (R (u, ζ u)).1` is `ContDiff ℝ m` for `m ≤ d.nu`. -/
theorem centerRemainder_contDiff
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {m : ℕ} (hmν : (m : WithTop ℕ∞) ≤ d.nu) (hζ : ContDiff ℝ m (ζ : ℝ → X)) :
    ContDiff ℝ m (fun u : ℝ ↦ (d.R (u, (ζ : ℝ → X) u)).1) := by
  have hgraph : ContDiff ℝ m (fun u : ℝ ↦ (u, (ζ : ℝ → X) u)) :=
    contDiff_id.prodMk hζ
  have hR : ContDiff ℝ m d.R := d.hR_smooth.of_le hmν
  exact contDiff_fst.comp (hR.comp hgraph)

/-- The center remainder coordinate is differentiable at every point, given `ζ` is `C¹`. -/
theorem centerRemainder_differentiableAt
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hζ : ContDiff ℝ 1 (ζ : ℝ → X)) (u : ℝ) :
    DifferentiableAt ℝ (fun u : ℝ ↦ (d.R (u, (ζ : ℝ → X) u)).1) u := by
  have hm : (1 : ℕ) ≤ d.nu := le_trans one_le_two d.hnu
  have hm_top : (1 : WithTop ℕ∞) ≤ d.nu := by exact_mod_cast hm
  exact (centerRemainder_contDiff d ζ hm_top hζ).differentiable_one.differentiableAt

/-- The scalar derivative of the center remainder coordinate has norm `≤ epsilon`. -/
theorem centerRemainder_norm_deriv_le
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) (u : ℝ) :
    ‖deriv (fun u : ℝ ↦ (d.R (u, (ζ : ℝ → X) u)).1) u‖ ≤ (d.epsilon : ℝ) :=
  norm_deriv_le_of_lipschitz (centerRemainder_lipschitz d ζ)

/-- The center map has derivative `1 + c' u` at every point (given `ζ` is `C¹`). -/
theorem centerMap_hasDerivAt
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hζ : ContDiff ℝ 1 (ζ : ℝ → X)) (u : ℝ) :
    HasDerivAt (d.centerMap ζ)
      (1 + deriv (fun u : ℝ ↦ (d.R (u, (ζ : ℝ → X) u)).1) u) u := by
  have hc : HasDerivAt (fun u : ℝ ↦ (d.R (u, (ζ : ℝ → X) u)).1)
      (deriv (fun u : ℝ ↦ (d.R (u, (ζ : ℝ → X) u)).1) u) u :=
    (centerRemainder_differentiableAt d ζ hζ u).hasDerivAt
  have hsum := (hasDerivAt_id u).add hc
  rw [d.centerMap_eq ζ]
  exact hsum

/-- The center-map derivative is bounded below by `lower > 0`. -/
theorem centerMap_deriv_lower_bound
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hζ : ContDiff ℝ 1 (ζ : ℝ → X)) (u : ℝ) :
    (d.lower : ℝ) ≤ deriv (d.centerMap ζ) u := by
  have hval : deriv (d.centerMap ζ) u
      = 1 + deriv (fun u : ℝ ↦ (d.R (u, (ζ : ℝ → X) u)).1) u :=
    (centerMap_hasDerivAt d ζ hζ u).deriv
  set c' := deriv (fun u : ℝ ↦ (d.R (u, (ζ : ℝ → X) u)).1) u with hc'
  have habs : |c'| ≤ (d.epsilon : ℝ) := by
    simpa only [Real.norm_eq_abs] using centerRemainder_norm_deriv_le d ζ u
  have hge : -(d.epsilon : ℝ) ≤ c' := (abs_le.mp habs).1
  have hadd : (d.lower : ℝ) + (d.epsilon : ℝ) = 1 := by exact_mod_cast d.hlower_add
  rw [hval]; linarith

/-- The center-map derivative is strictly positive (it is `≥ lower > 0`). -/
theorem centerMap_deriv_pos
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hζ : ContDiff ℝ 1 (ζ : ℝ → X)) (u : ℝ) :
    (0 : ℝ) < deriv (d.centerMap ζ) u := by
  have hpos : (0 : ℝ) < (d.lower : ℝ) := by exact_mod_cast d.hlower_pos
  exact lt_of_lt_of_le hpos (centerMap_deriv_lower_bound d ζ hζ u)

/-- The center-map derivative is nonzero. -/
theorem centerMap_deriv_ne_zero
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hζ : ContDiff ℝ 1 (ζ : ℝ → X)) (u : ℝ) :
    deriv (d.centerMap ζ) u ≠ 0 :=
  ne_of_gt (centerMap_deriv_pos d ζ hζ u)

/-! ## Local bunching arithmetic (re-derived, cycle-safe).

`MetricTopSectionCoreAssembly` supplies these but imports this leaf; re-derive locally. -/

/-- `p·c = (rate · lower⁻ᵐ) · lower⁻¹ = rate · lower⁻⁽ᵐ⁺¹⁾ < 1`, from `h_bunching (m + 1)`. -/
theorem bunching_transport_factor_lt_one
    (d : MetricGraphTransformData X)
    (h_bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1)
    {m : ℕ} (hm : m < d.nu) :
    ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ m) * (d.lower : ℝ)⁻¹ < 1 := by
  have hb := h_bunching (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hm
  calc
    ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ m) * (d.lower : ℝ)⁻¹
        = (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
            (d.lower : ℝ)⁻¹ ^ (m + 1) := by rw [pow_succ]; ring
    _ < 1 := hb

/-- `p = rate · lower⁻ᵐ < 1`. -/
theorem bunching_linear_factor_lt_one
    (d : MetricGraphTransformData X)
    (h_bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1)
    {m : ℕ} (hm : m < d.nu) :
    (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ m < 1 := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0; simpa only [pow_zero, mul_one] using (by exact_mod_cast d.hrate : _)
  · exact h_bunching m hmpos hm.le

/-- `0 ≤ rate · lower⁻ᵐ`. -/
theorem bunching_linear_factor_nonneg
    (d : MetricGraphTransformData X) (m : ℕ) :
    (0 : ℝ) ≤ (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ m :=
  mul_nonneg (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope).coe_nonneg
    (by positivity)

/-- `0 < lower⁻¹`. -/
theorem bunching_change_of_variables_pos
    (d : MetricGraphTransformData X) :
    (0 : ℝ) < (d.lower : ℝ)⁻¹ :=
  inv_pos.mpr (by exact_mod_cast d.hlower_pos)

/-! ## Packaging: from the scalar top-section core to the holonomic export.

Given a continuous derivative-value field `v` with `∀ u, HasDerivAt (iteratedDeriv m ζ) (v u) u`
(the *metric top-section core* at order `m`), the multilinear curry-packaging of
`MetricTopSectionHolonomicAssembly` produces the exact holonomic obligation at order `r = m + 1`.
This step is unconditional and does not depend on how the core `v` is constructed. -/

/-- Package a scalar top-section core into the holonomic top-section witness at order `m + 1`.
`a u := (topSectionValue m (v u)).curryLeft`-style witness with the continuity and the curried
Fréchet derivative equation for `y ↦ (ftaylorSeries ℝ ζ y) m`. -/
theorem topSection_of_scalar_core
    (ζ : ℝ → X) (m : ℕ) (v : ℝ → X)
    (hv : Continuous v)
    (hderiv : ∀ u, HasDerivAt (iteratedDeriv m ζ) (v u) u) :
    ∃ a : ℝ → (ℝ [×(m + 1)]→L[ℝ] X),
      Continuous a ∧
        ∀ u, HasFDerivAt (fun y ↦ (ftaylorSeries ℝ ζ y) m) ((a u).curryLeft) u := by
  refine ⟨fun u ↦ topSectionValue m (v u), continuous_topSectionValue m v hv, ?_⟩
  intro u
  exact hasFDerivAt_iteratedFDeriv_of_hasDerivAt m ζ v u (hderiv u)

/-! ## Conditional export: the holonomic top section from the metric top-section core.

`MetricTopSectionDerivativeBridge` supplies the entire orderwise reduction — the per-order
finite-smoothness induction (`contDiff_le_of_core`) and the single-order curry packaging
(`topSectionWitness_at_of_core`) — from the *metric top-section core*
`MetricTopSectionCore d ζ` (a continuous derivative-value field witnessing the pointwise
`HasDerivAt` of every scalar top iterated derivative at orders `< d.nu`).  Consequently the
frozen `topSection` obligation follows unconditionally *from the core*.

The core itself — constructing that continuous derivative-value field from bunching and the
fixed-point equation alone — is the sole remaining analytic content of Claim 1 and is isolated
as the hypothesis `hcore` below. -/

/-- **Conditional export.**  Given the metric top-section core, the frozen holonomic
`topSection` obligation holds at every order `1 ≤ r ≤ d.nu`.  This wires the core through the
cycle-safe `MetricTopSectionDerivativeBridge` reduction; the only outstanding obligation of
Claim 1 is the construction of `hcore`. -/
theorem metricFixedGraph_topSection_of_core
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hcore : MetricTopSectionCore d ζ) :
    ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      ∃ a : ℝ → (ℝ [×(r - 1 + 1)]→L[ℝ] X),
        Continuous a ∧
          ∀ u, HasFDerivAt (fun y ↦ (ftaylorSeries ℝ (ζ : ℝ → X) y) (r - 1))
            ((a u).curryLeft) u := by
  intro r hr hrν
  exact topSectionWitness_at_of_core d ζ hcore hr hrν

end LocalInvariantGraph
