module

-- Assembly of the metric top-section core.  Builds on the solved cocycle recurrence
-- `iteratedDeriv_fixedGraph_cocycle_solved` and the secant/envelope toolkit to produce, for every
-- order `m < d.nu` with `ζ ∈ Cᵐ`, a continuous derivative-value field `v` witnessing
-- `HasDerivAt (iteratedDeriv m ζ) (v u) u` — i.e. `MetricTopSectionCore d ζ`.
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionCocycleRecurrence
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionMasterIdentity
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionSecantKernel
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricFiberFaaDiBruno
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricFiberLengthOneExtraction
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionCore
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionHolonomicBridge
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionHolonomicAssembly
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionDerivativeBridge

public section

noncomputable section

open scoped NNReal Topology
open Filter Set

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## The bunching arithmetic.

The bunching arithmetic (`bunching_transport_factor_lt_one` giving `p · c = rate · lower⁻⁽ᵐ⁺¹⁾ < 1`,
`bunching_linear_factor_lt_one`, `bunching_linear_factor_nonneg`, `bunching_change_of_variables_pos`)
is provided by the Stage-A `MetricTopSectionHolonomicBridge` leaf, imported above; the names resolve
from there.  (They were duplicated here originally; the leaf is the canonical cycle-safe home.) -/

/-! ## The fixed-section operator contraction factor.

The candidate derivative field `v` is the fixed point of the affine operator
`𝒯(b)(u) := (Φ′u)⁻ᵐ • L(b(Φu)) + F₀(u)` on bounded continuous fields, where `F₀` is a continuous
(not necessarily `C¹`) forcing term.  The linear part `b ↦ ((Φ′·)⁻ᵐ • L(b(Φ·)))` contracts by
`p = rate · lower⁻ᵐ`: its pointwise Lipschitz constant is `‖(Φ′u)⁻ᵐ‖ · ‖L‖ ≤ lower⁻ᵐ · rate`
(using `(Φ′u)⁻¹ ≤ lower⁻¹` from `centerMap_deriv_lower_bound` and `‖L‖ ≤ rate` from `d.hL`
composed with `d.hlinearRate`).  This factor is `< 1` by `bunching_linear_factor_lt_one`, so
`BoundedSectionContractionCertificate.existsUnique_fixedSection` produces `v`.  The pointwise
operator Lipschitz bound `‖(Φ′u)⁻ᵐ • L w‖ ≤ (rate · lower⁻ᵐ) · ‖w‖` is recorded next. -/

/-- The pointwise linear-part Lipschitz bound for the fixed-section operator, stated with the exact
linear coefficient `linearRate` (which bounds `‖L‖` via `d.hL`):
`‖(Φ′u)⁻ᵐ • L w‖ ≤ (linearRate · lower⁻ᵐ) · ‖w‖`.  Combines `‖L w‖ ≤ linearRate · ‖w‖` (from `d.hL`)
with `|(Φ′u)⁻ᵐ| ≤ lower⁻ᵐ` (from `centerMap_deriv_lower_bound`).  Since
`linearRate ≤ metricGraphTransformRate …` (monotonicity of the rate, all summands nonnegative), this
also bounds the operator by `rate · lower⁻ᵐ`, the factor `bunching_linear_factor_lt_one` proves
`< 1`. -/
theorem operator_linear_part_norm_le
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hζ1 : ContDiff ℝ 1 (ζ : ℝ → X)) (m : ℕ) (u : ℝ) (w : X) :
    ‖(deriv (d.centerMap ζ) u)⁻¹ ^ m • d.L w‖ ≤
      ((d.linearRate : ℝ) * (d.lower : ℝ)⁻¹ ^ m) * ‖w‖ := by
  have hlower_pos : (0 : ℝ) < (d.lower : ℝ) := by exact_mod_cast d.hlower_pos
  have hφ_lb : (d.lower : ℝ) ≤ deriv (d.centerMap ζ) u :=
    centerMap_deriv_lower_bound d ζ hζ1 u
  have hφ_pos : (0 : ℝ) < deriv (d.centerMap ζ) u := lt_of_lt_of_le hlower_pos hφ_lb
  -- `|(Φ′u)⁻¹| ≤ lower⁻¹`, hence `|(Φ′u)⁻ᵐ| ≤ lower⁻ᵐ`.
  have hinv_le : (deriv (d.centerMap ζ) u)⁻¹ ≤ (d.lower : ℝ)⁻¹ :=
    inv_anti₀ hlower_pos hφ_lb
  have hinv_nonneg : (0 : ℝ) ≤ (deriv (d.centerMap ζ) u)⁻¹ := le_of_lt (inv_pos.mpr hφ_pos)
  have hpow_le : (deriv (d.centerMap ζ) u)⁻¹ ^ m ≤ (d.lower : ℝ)⁻¹ ^ m :=
    pow_le_pow_left₀ hinv_nonneg hinv_le m
  have hpow_nonneg : (0 : ℝ) ≤ (deriv (d.centerMap ζ) u)⁻¹ ^ m := pow_nonneg hinv_nonneg m
  have hlower_inv_pow_nonneg : (0 : ℝ) ≤ (d.lower : ℝ)⁻¹ ^ m := by
    positivity
  -- Norm of the scalar smul.
  have hLw : ‖d.L w‖ ≤ (d.linearRate : ℝ) * ‖w‖ := by
    calc
      ‖d.L w‖ ≤ ‖d.L‖ * ‖w‖ := d.L.le_opNorm w
      _ ≤ (d.linearRate : ℝ) * ‖w‖ := mul_le_mul_of_nonneg_right d.hL (norm_nonneg _)
  calc
    ‖(deriv (d.centerMap ζ) u)⁻¹ ^ m • d.L w‖
        = (deriv (d.centerMap ζ) u)⁻¹ ^ m * ‖d.L w‖ := by
          rw [norm_smul, Real.norm_of_nonneg hpow_nonneg]
    _ ≤ (d.lower : ℝ)⁻¹ ^ m * ((d.linearRate : ℝ) * ‖w‖) := by
          exact mul_le_mul hpow_le hLw (norm_nonneg _) hlower_inv_pow_nonneg
    _ = ((d.linearRate : ℝ) * (d.lower : ℝ)⁻¹ ^ m) * ‖w‖ := by ring

/-! ## Continuity of the center map and its reciprocal-power coefficient.

The bounded-section operator `𝒯` composes its argument with `Φ = centerMap ζ` and scales by the
coefficient `a u := (Φ′u)⁻ᵐ`.  For `𝒯` to land in `ℝ →ᵇ X` we need `Φ` continuous (always, since
`ζ` is continuous and `Φ = id + c` with `c` continuous) and `a` continuous and bounded.  We record
these here. -/

/-- The center map `Φ = centerMap ζ` is continuous (it is `id + c` with `c` the continuous center
remainder coordinate; `ζ` is continuous). -/
theorem centerMap_continuous
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) :
    Continuous (d.centerMap ζ) := by
  rw [centerMap_eq_add_remainder]
  have hc : Continuous (fun u : ℝ ↦ (d.R (u, (ζ : ℝ → X) u)).1) :=
    (centerRemainder_lipschitz d ζ).continuous
  exact continuous_id.add hc

/-- The reciprocal-power coefficient `a u := (deriv Φ u)⁻ᵐ` is bounded by `lower⁻ᵐ` in absolute
value.  Uses the lower bound `lower ≤ Φ′u` (`centerMap_deriv_lower_bound`, needs `ζ ∈ C¹`). -/
theorem centerMap_deriv_inv_pow_abs_le
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hζ1 : ContDiff ℝ 1 (ζ : ℝ → X)) (m : ℕ) (u : ℝ) :
    |(deriv (d.centerMap ζ) u)⁻¹ ^ m| ≤ (d.lower : ℝ)⁻¹ ^ m := by
  have hlower_pos : (0 : ℝ) < (d.lower : ℝ) := by exact_mod_cast d.hlower_pos
  have hφ_lb : (d.lower : ℝ) ≤ deriv (d.centerMap ζ) u :=
    centerMap_deriv_lower_bound d ζ hζ1 u
  have hφ_pos : (0 : ℝ) < deriv (d.centerMap ζ) u := lt_of_lt_of_le hlower_pos hφ_lb
  have hinv_nonneg : (0 : ℝ) ≤ (deriv (d.centerMap ζ) u)⁻¹ := le_of_lt (inv_pos.mpr hφ_pos)
  have hinv_le : (deriv (d.centerMap ζ) u)⁻¹ ≤ (d.lower : ℝ)⁻¹ :=
    inv_anti₀ hlower_pos hφ_lb
  have hpow_nonneg : (0 : ℝ) ≤ (deriv (d.centerMap ζ) u)⁻¹ ^ m := pow_nonneg hinv_nonneg m
  rw [abs_of_nonneg hpow_nonneg]
  exact pow_le_pow_left₀ hinv_nonneg hinv_le m

/-- The reciprocal-power coefficient `a u := (deriv Φ u)⁻ᵐ` is continuous.  For `m ≥ 1` this uses
that `Φ = centerMap ζ` is `C¹` (hence `deriv Φ` is continuous) whenever `ζ` is `C¹`; the coefficient
is `(deriv Φ ·)⁻¹ ^ m`, a continuous function of the (nonvanishing) continuous `deriv Φ`. -/
theorem centerMap_deriv_inv_pow_continuous
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hζ1 : ContDiff ℝ 1 (ζ : ℝ → X)) (m : ℕ) :
    Continuous (fun u ↦ (deriv (d.centerMap ζ) u)⁻¹ ^ m) := by
  have h1ν : (1 : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast le_trans one_le_two d.hnu
  have hΦ : ContDiff ℝ 1 (d.centerMap ζ) := centerMap_contDiff_of_prev d ζ h1ν hζ1
  have hderiv_cont : Continuous (deriv (d.centerMap ζ)) := hΦ.continuous_deriv (le_refl _)
  have hne : ∀ u, deriv (d.centerMap ζ) u ≠ 0 := fun u => centerMap_deriv_ne_zero d ζ hζ1 u
  exact (hderiv_cont.inv₀ hne).pow m

/-! ## The combined fiber-cocycle operator norm bound.

The reserved-top-order operator keeps the fiber term `∂₂R = derivFiber` inside the contracted
linear part, so the operator's linear coefficient is `M(u) := L + derivFiber u`.  Its pointwise
Lipschitz constant is `‖(Φ′u)⁻ᵐ • M(u) w‖ ≤ ((linearRate + epsilon) · lower⁻ᵐ) · ‖w‖`, combining
`operator_linear_part_norm_le` (the `L`-part, coefficient `linearRate`) with `norm_derivFiber_le`
(`‖derivFiber‖ ≤ epsilon`) and `|(Φ′u)⁻ᵐ| ≤ lower⁻ᵐ`.  Chaining through
`linearRate_add_epsilon_le_metricGraphTransformRate_real` upgrades the coefficient to the metric
transform rate, which `bunching_linear_factor_lt_one` certifies `< 1`. -/

/-- The pointwise Lipschitz bound for the **combined** fiber-cocycle operator
`M(u) := L + derivFiber u`:  `‖(Φ′u)⁻ᵐ • (L + derivFiber u) w‖ ≤ ((linearRate + epsilon)·lower⁻ᵐ)·‖w‖`.
The `L`-part reuses `operator_linear_part_norm_le`; the `derivFiber`-part uses `‖derivFiber‖ ≤ ε`
(`norm_derivFiber_le`) and `|(Φ′u)⁻ᵐ| ≤ lower⁻ᵐ` (`centerMap_deriv_inv_pow_abs_le`). -/
theorem operator_fiber_cocycle_norm_le
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hζ1 : ContDiff ℝ 1 (ζ : ℝ → X)) (m : ℕ) (u : ℝ) (w : X) :
    ‖(deriv (d.centerMap ζ) u)⁻¹ ^ m • (d.L w + derivFiber d ζ u w)‖ ≤
      (((d.linearRate : ℝ) + (d.epsilon : ℝ)) * (d.lower : ℝ)⁻¹ ^ m) * ‖w‖ := by
  -- `|(Φ′u)⁻ᵐ| ≤ lower⁻ᵐ`, and it is nonnegative.
  have hpow_abs_le : |(deriv (d.centerMap ζ) u)⁻¹ ^ m| ≤ (d.lower : ℝ)⁻¹ ^ m :=
    centerMap_deriv_inv_pow_abs_le d ζ hζ1 m u
  have hpow_nonneg : (0 : ℝ) ≤ (deriv (d.centerMap ζ) u)⁻¹ ^ m := by
    have hlower_pos : (0 : ℝ) < (d.lower : ℝ) := by exact_mod_cast d.hlower_pos
    have hφ_lb : (d.lower : ℝ) ≤ deriv (d.centerMap ζ) u :=
      centerMap_deriv_lower_bound d ζ hζ1 u
    exact pow_nonneg (le_of_lt (inv_pos.mpr (lt_of_lt_of_le hlower_pos hφ_lb))) m
  -- Bound the two summands of the fiber cocycle: `‖L w‖ ≤ linearRate·‖w‖`, `‖derivFiber w‖ ≤ ε·‖w‖`.
  have hLw : ‖d.L w‖ ≤ (d.linearRate : ℝ) * ‖w‖ := by
    calc
      ‖d.L w‖ ≤ ‖d.L‖ * ‖w‖ := d.L.le_opNorm w
      _ ≤ (d.linearRate : ℝ) * ‖w‖ := mul_le_mul_of_nonneg_right d.hL (norm_nonneg _)
  have hFw : ‖derivFiber d ζ u w‖ ≤ (d.epsilon : ℝ) * ‖w‖ := by
    calc
      ‖derivFiber d ζ u w‖ ≤ ‖derivFiber d ζ u‖ * ‖w‖ := (derivFiber d ζ u).le_opNorm w
      _ ≤ (d.epsilon : ℝ) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (norm_derivFiber_le d ζ u) (norm_nonneg _)
  -- `‖L w + derivFiber w‖ ≤ (linearRate + epsilon)·‖w‖`.
  have hsum : ‖d.L w + derivFiber d ζ u w‖ ≤ ((d.linearRate : ℝ) + (d.epsilon : ℝ)) * ‖w‖ := by
    calc
      ‖d.L w + derivFiber d ζ u w‖ ≤ ‖d.L w‖ + ‖derivFiber d ζ u w‖ := norm_add_le _ _
      _ ≤ (d.linearRate : ℝ) * ‖w‖ + (d.epsilon : ℝ) * ‖w‖ := add_le_add hLw hFw
      _ = ((d.linearRate : ℝ) + (d.epsilon : ℝ)) * ‖w‖ := by ring
  have hsum_nonneg : (0 : ℝ) ≤ ‖d.L w + derivFiber d ζ u w‖ := norm_nonneg _
  calc
    ‖(deriv (d.centerMap ζ) u)⁻¹ ^ m • (d.L w + derivFiber d ζ u w)‖
        = |(deriv (d.centerMap ζ) u)⁻¹ ^ m| * ‖d.L w + derivFiber d ζ u w‖ := by
          rw [norm_smul, Real.norm_eq_abs]
    _ ≤ (d.lower : ℝ)⁻¹ ^ m * (((d.linearRate : ℝ) + (d.epsilon : ℝ)) * ‖w‖) := by
          apply mul_le_mul hpow_abs_le hsum hsum_nonneg
          positivity
    _ = (((d.linearRate : ℝ) + (d.epsilon : ℝ)) * (d.lower : ℝ)⁻¹ ^ m) * ‖w‖ := by ring

/-- The combined fiber-cocycle operator is bounded by the **metric transform rate**:
`‖(Φ′u)⁻ᵐ • (L + derivFiber u) w‖ ≤ (rate · lower⁻ᵐ) · ‖w‖`, where
`rate = metricGraphTransformRate …`.  Chains `operator_fiber_cocycle_norm_le` through
`linearRate_add_epsilon_le_metricGraphTransformRate_real`.  The coefficient `rate · lower⁻ᵐ` is
`< 1` by `bunching_linear_factor_lt_one`. -/
theorem operator_fiber_cocycle_norm_le_rate
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hζ1 : ContDiff ℝ 1 (ζ : ℝ → X)) (m : ℕ) (u : ℝ) (w : X) :
    ‖(deriv (d.centerMap ζ) u)⁻¹ ^ m • (d.L w + derivFiber d ζ u w)‖ ≤
      ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ m) * ‖w‖ := by
  have hbase := operator_fiber_cocycle_norm_le d ζ hζ1 m u w
  have hrate_le :
      (d.linearRate : ℝ) + (d.epsilon : ℝ) ≤
        (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) :=
    linearRate_add_epsilon_le_metricGraphTransformRate_real d.lower d.linearRate d.epsilon d.slope
  have hpow_nonneg : (0 : ℝ) ≤ (d.lower : ℝ)⁻¹ ^ m := by positivity
  have hcoeff_le :
      ((d.linearRate : ℝ) + (d.epsilon : ℝ)) * (d.lower : ℝ)⁻¹ ^ m ≤
        (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
          (d.lower : ℝ)⁻¹ ^ m :=
    mul_le_mul_of_nonneg_right hrate_le hpow_nonneg
  refine hbase.trans ?_
  exact mul_le_mul_of_nonneg_right hcoeff_le (norm_nonneg _)

/-! ## The reserved-top-order coefficient with center feedback.

Differentiating the fixed-graph equation also differentiates the center change of variables.
Consequently the actual coefficient of the reserved top derivative is not merely
`L + derivFiber`, but has the rank-one center-feedback term
`derivCenterFiber w • deriv ζ (centerMap ζ u)` subtracted.  The following definition and
application lemma isolate this construction, while the norm theorem records that the trailing
summand in `metricGraphTransformRate` pays for the feedback exactly. -/

/-- Helper for Infrastructure I.16a: the complete reserved-top-order coefficient, including the
rank-one feedback from the center component of the fiber derivative. -/
def metricReservedTopCoefficient
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) (m : ℕ) (u : ℝ) : X →L[ℝ] X :=
  (deriv (d.centerMap ζ) u)⁻¹ ^ m •
    (d.L + derivFiber d ζ u -
      (derivCenterFiber d ζ u).smulRight
        (deriv (ζ : ℝ → X) (d.centerMap ζ u)))

/-- Helper for Infrastructure I.16a: application of `metricReservedTopCoefficient` exposes the
fiber cocycle and the complete center-feedback term. -/
theorem metricReservedTopCoefficient_apply
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) (m : ℕ) (u : ℝ) (w : X) :
    metricReservedTopCoefficient d ζ m u w =
      (deriv (d.centerMap ζ) u)⁻¹ ^ m •
        (d.L w + derivFiber d ζ u w -
          (derivCenterFiber d ζ u w) •
            deriv (ζ : ℝ → X) (d.centerMap ζ u)) := by
  rfl

/-- Helper for Infrastructure I.16a: the lower-order forcing in the affine reserved-top
derivative equation.  The two `R`-component sums and the nonlinear graph-composition sum omit
both the reserved length-`r` block and the isolated length-one block. -/
def metricReservedTopForcing
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) (r : ℕ) (u : ℝ) : X :=
  (deriv (d.centerMap ζ) u)⁻¹ ^ r •
    (iteratedFDeriv ℝ r (fun z : ℝ × X ↦ (d.R z).2)
        (u, (ζ : ℝ → X) u)
        (fun _ : Fin r ↦
          iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u)
      + ∑ c ∈ (Finset.univ.filter
          (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
          iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).2)
            (u, (ζ : ℝ → X) u)
            (fun j ↦ iteratedDeriv (c.partSize j)
              (fun y ↦ (y, (ζ : ℝ → X) y)) u)
      - (iteratedFDeriv ℝ r (fun z : ℝ × X ↦ (d.R z).1)
            (u, (ζ : ℝ → X) u)
            (fun _ : Fin r ↦
              iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u)
          + ∑ c ∈ (Finset.univ.filter
              (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
              iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).1)
                (u, (ζ : ℝ → X) u)
                (fun j ↦ iteratedDeriv (c.partSize j)
                  (fun y ↦ (y, (ζ : ℝ → X) y)) u))
          • deriv (ζ : ℝ → X) (d.centerMap ζ u)
      - ∑ c ∈ (Finset.univ.filter
          (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
          iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ u)
            (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) u))

/-- Helper for Infrastructure I.16a: if `g` is `C^(r + 1)` and `f` is `C^r` for
`r ≥ 2`, then evaluating `iteratedFDeriv ℝ r g` on the diagonal first jet of `f` is `C¹`. -/
private theorem iteratedFDeriv_diagonalFirstJet_contDiff_one
    {Z Y : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (g : Z → Y) (f : ℝ → Z) {r : ℕ} (hr : 2 ≤ r)
    (hg : ContDiff ℝ (r + 1 : ℕ) g) (hf : ContDiff ℝ r f) :
    ContDiff ℝ 1 (fun u ↦
      iteratedFDeriv ℝ r g (f u) (fun _ : Fin r ↦ iteratedDeriv 1 f u)) := by
  have houter_order_nat : 1 + r ≤ r + 1 := by
    omega
  have houter_order :
      (1 : WithTop ℕ∞) + (r : WithTop ℕ∞) ≤ ((r + 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast houter_order_nat
  have houter : ContDiff ℝ 1 (iteratedFDeriv ℝ r g) :=
    hg.iteratedFDeriv_right houter_order
  have hone_nat : 1 ≤ r := by
    omega
  have hone : (1 : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by
    exact_mod_cast hone_nat
  have hf_one : ContDiff ℝ 1 f := hf.of_le hone
  have hjet : ContDiff ℝ 1 (fun u ↦ iteratedFDeriv ℝ r g (f u)) :=
    houter.comp hf_one
  have htwo : (2 : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by
    exact_mod_cast hr
  have hf_two : ContDiff ℝ 2 f := hf.of_le htwo
  have hfirst : ContDiff ℝ 1 (iteratedDeriv 1 f) :=
    (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp hf_two).2
  have hvec : ContDiff ℝ 1
      (fun u ↦ (fun _ : Fin r ↦ iteratedDeriv 1 f u)) := by
    rw [contDiff_pi]
    intro j
    exact hfirst
  have hevaluation : ContDiff ℝ 1
      (fun p : (Z [×r]→L[ℝ] Y) × (Fin r → Z) ↦ p.1 p.2) := by
    have heval : AnalyticOnNhd ℝ
        (fun p : (Z [×r]→L[ℝ] Y) × (Fin r → Z) ↦ p.1 p.2)
        (Set.univ : Set ((Z [×r]→L[ℝ] Y) × (Fin r → Z))) :=
      ContinuousLinearMap.analyticOnNhd_uncurry_of_multilinear
        (ContinuousLinearMap.id ℝ (Z [×r]→L[ℝ] Y))
        (s := Set.univ)
    exact heval.contDiff
  simpa only [Function.comp_def] using hevaluation.comp (hjet.prodMk hvec)

/-- Helper for Infrastructure I.16a: the stable-coordinate order-`r` atomic evaluation in
`metricReservedTopForcing` is `C¹` when `r ≥ 2`, `r + 1 ≤ d.nu`, and `ζ` is `C^r`. -/
theorem metricStableAtomicEvaluation_contDiff_one
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {r : ℕ} (hr : 2 ≤ r) (hrν : r + 1 ≤ d.nu)
    (hprev : ContDiff ℝ r (ζ : ℝ → X)) :
    ContDiff ℝ 1 (fun u ↦
      iteratedFDeriv ℝ r (fun z : ℝ × X ↦ (d.R z).2)
        (u, (ζ : ℝ → X) u)
        (fun _ : Fin r ↦
          iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u)) := by
  have hrν_with_top : ((r + 1 : ℕ) : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hrν
  have hR : ContDiff ℝ (r + 1 : ℕ) d.R := d.hR_smooth.of_le hrν_with_top
  have hg : ContDiff ℝ (r + 1 : ℕ) (fun z : ℝ × X ↦ (d.R z).2) :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.snd ℝ ℝ X)).comp hR
  have hpair : ContDiff ℝ r (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) :=
    contDiff_id.prodMk hprev
  exact iteratedFDeriv_diagonalFirstJet_contDiff_one
    (fun z : ℝ × X ↦ (d.R z).2) (fun y : ℝ ↦ (y, (ζ : ℝ → X) y))
    hr hg hpair

/-- Helper for Infrastructure I.16a: the center-coordinate order-`r` atomic evaluation in
`metricReservedTopForcing` is `C¹` when `r ≥ 2`, `r + 1 ≤ d.nu`, and `ζ` is `C^r`. -/
theorem metricCenterAtomicEvaluation_contDiff_one
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {r : ℕ} (hr : 2 ≤ r) (hrν : r + 1 ≤ d.nu)
    (hprev : ContDiff ℝ r (ζ : ℝ → X)) :
    ContDiff ℝ 1 (fun u ↦
      iteratedFDeriv ℝ r (fun z : ℝ × X ↦ (d.R z).1)
        (u, (ζ : ℝ → X) u)
        (fun _ : Fin r ↦
          iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u)) := by
  have hrν_with_top : ((r + 1 : ℕ) : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hrν
  have hR : ContDiff ℝ (r + 1 : ℕ) d.R := d.hR_smooth.of_le hrν_with_top
  have hg : ContDiff ℝ (r + 1 : ℕ) (fun z : ℝ × X ↦ (d.R z).1) :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.fst ℝ ℝ X)).comp hR
  have hpair : ContDiff ℝ r (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) :=
    contDiff_id.prodMk hprev
  exact iteratedFDeriv_diagonalFirstJet_contDiff_one
    (fun z : ℝ × X ↦ (d.R z).1) (fun y : ℝ ↦ (y, (ζ : ℝ → X) y))
    hr hg hpair

/-- Infrastructure I.16a: if `r ≥ 2`, `r + 1 ≤ d.nu`, and `ζ` is `C^r`, then the
complete lower-order affine forcing `metricReservedTopForcing d ζ r` is `C¹`. -/
theorem metricReservedTopForcing_contDiff_one
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {r : ℕ} (hr : 2 ≤ r) (hrν : r + 1 ≤ d.nu)
    (hprev : ContDiff ℝ r (ζ : ℝ → X)) :
    ContDiff ℝ 1 (metricReservedTopForcing d ζ r) := by
  have hrν_nat : r ≤ d.nu := by
    omega
  have hrν_with_top : (r : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hrν_nat
  have hone_nat : 1 ≤ r := by
    omega
  have hone : (1 : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by
    exact_mod_cast hone_nat
  have htwo : (2 : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by
    exact_mod_cast hr
  have hζ_one : ContDiff ℝ 1 (ζ : ℝ → X) := hprev.of_le hone
  have hζ_two : ContDiff ℝ 2 (ζ : ℝ → X) := hprev.of_le htwo
  have hcenterMap : ContDiff ℝ r (d.centerMap ζ) :=
    centerMap_contDiff_of_prev d ζ hrν_with_top hprev
  have hcenterMap_one : ContDiff ℝ 1 (d.centerMap ζ) :=
    hcenterMap.of_le hone
  have hcenterMap_two : ContDiff ℝ 2 (d.centerMap ζ) :=
    hcenterMap.of_le htwo
  have hcenterMap_deriv : ContDiff ℝ 1 (deriv (d.centerMap ζ)) := by
    have hiterated :=
      (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp hcenterMap_two).2
    simpa only [iteratedDeriv_one] using hiterated
  have hcenterMap_deriv_ne : ∀ u, deriv (d.centerMap ζ) u ≠ 0 :=
    fun u ↦ centerMap_deriv_ne_zero d ζ hζ_one u
  have hcenterMap_deriv_inv :
      ContDiff ℝ 1 (fun u ↦ (deriv (d.centerMap ζ) u)⁻¹) :=
    hcenterMap_deriv.inv hcenterMap_deriv_ne
  have hscale :
      ContDiff ℝ 1 (fun u ↦ (deriv (d.centerMap ζ) u)⁻¹ ^ r) :=
    hcenterMap_deriv_inv.pow r
  have hζ_deriv : ContDiff ℝ 1 (deriv (ζ : ℝ → X)) := by
    have hiterated :=
      (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp hζ_two).2
    simpa only [iteratedDeriv_one] using hiterated
  have hζ_deriv_center : ContDiff ℝ 1
      (fun u ↦ deriv (ζ : ℝ → X) (d.centerMap ζ u)) :=
    hζ_deriv.comp hcenterMap_one
  have hstable_atomic :=
    metricStableAtomicEvaluation_contDiff_one d ζ hr hrν hprev
  have hstable_residual :=
    iteratedDeriv_fiber_remainder_length_one_residual_contDiff
      d ζ hr hrν_nat hprev
  have hcenter_atomic :=
    metricCenterAtomicEvaluation_contDiff_one d ζ hr hrν hprev
  have hcenter_residual :=
    iteratedDeriv_center_remainder_length_one_residual_contDiff
      d ζ hr hrν_nat hprev
  have hζ_residual :=
    iteratedDeriv_zeta_comp_centerMap_length_one_residual_contDiff
      d ζ hr hrν_nat hprev
  have hstable_block := hstable_atomic.add hstable_residual
  have hcenter_block := hcenter_atomic.add hcenter_residual
  have hfeedback := hcenter_block.smul hζ_deriv_center
  have hbracket := (hstable_block.sub hfeedback).sub hζ_residual
  unfold metricReservedTopForcing
  exact hscale.smul hbracket

/-- Helper for Infrastructure I.16a: for orders at least two, the differentiated fixed-graph
equation is affine in the reserved top derivative.  Its linear part is the complete fiber
coefficient with negative center feedback, while `metricReservedTopForcing` contains only
lower-order graph jets. -/
theorem iteratedDeriv_fixedGraph_reservedTop_affine_split
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ r (ζ : ℝ → X)) (u : ℝ) :
    iteratedDeriv r (ζ : ℝ → X) (d.centerMap ζ u) =
      metricReservedTopCoefficient d ζ r u
        (iteratedDeriv r (ζ : ℝ → X) u)
      + metricReservedTopForcing d ζ r u := by
  have hr0 : 0 < r := by
    omega
  have h1r_nat : 1 ≤ r := by
    omega
  have h1r : (1 : WithTop ℕ∞) ≤ r := by
    exact_mod_cast h1r_nat
  have hζ1 : ContDiff ℝ 1 (ζ : ℝ → X) := hprev.of_le h1r
  have hrν_top : (r : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hrν
  have hpair : ContDiff ℝ r (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) :=
    contDiff_id.prodMk hprev
  have hR : ContDiff ℝ r d.R := d.hR_smooth.of_le hrν_top
  have hcenterSmooth :
      ContDiff ℝ r (fun y : ℝ ↦ (d.R (y, (ζ : ℝ → X) y)).1) :=
    contDiff_fst.comp (hR.comp hpair)
  have hstable :
      iteratedDeriv r (fun y : ℝ ↦ (d.R (y, (ζ : ℝ → X) y)).2) u =
        iteratedFDeriv ℝ r (fun z : ℝ × X ↦ (d.R z).2)
            (u, (ζ : ℝ → X) u)
            (fun _ : Fin r ↦
              iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u)
          + derivFiber d ζ u (iteratedDeriv r (ζ : ℝ → X) u)
          + ∑ c ∈ (Finset.univ.filter
              (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
              iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).2)
                (u, (ζ : ℝ → X) u)
                (fun j ↦ iteratedDeriv (c.partSize j)
                  (fun y ↦ (y, (ζ : ℝ → X) y)) u) := by
    simpa only [Function.comp_def] using
      iteratedDeriv_fiber_remainder_length_one_split_of_contDiff
        d ζ hr hrν hprev u
  have hcenter :
      iteratedDeriv r (fun y : ℝ ↦ (d.R (y, (ζ : ℝ → X) y)).1) u =
        iteratedFDeriv ℝ r (fun z : ℝ × X ↦ (d.R z).1)
            (u, (ζ : ℝ → X) u)
            (fun _ : Fin r ↦
              iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u)
          + derivCenterFiber d ζ u (iteratedDeriv r (ζ : ℝ → X) u)
          + ∑ c ∈ (Finset.univ.filter
              (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
              iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).1)
                (u, (ζ : ℝ → X) u)
                (fun j ↦ iteratedDeriv (c.partSize j)
                  (fun y ↦ (y, (ζ : ℝ → X) y)) u) := by
    simpa only [Function.comp_def] using
      iteratedDeriv_center_remainder_length_one_split_of_contDiff
        d ζ hr hrν hprev u
  have hcenterFunction :
      d.centerMap ζ =
        (fun y : ℝ ↦ y) + (fun y : ℝ ↦ (d.R (y, (ζ : ℝ → X) y)).1) := by
    funext y
    rw [d.centerMap_eq ζ]
    rfl
  have hcenterAdd := iteratedDeriv_add
    (f := fun y : ℝ ↦ y)
    (g := fun y : ℝ ↦ (d.R (y, (ζ : ℝ → X) y)).1)
    (n := r) (x := u) contDiff_id.contDiffAt hcenterSmooth.contDiffAt
  have hr_ne_zero : r ≠ 0 := by
    omega
  have hr_ne_one : r ≠ 1 := by
    omega
  have hidzero : iteratedDeriv r (fun y : ℝ ↦ y) u = 0 := by
    change iteratedDeriv r (id : ℝ → ℝ) u = 0
    rw [iteratedDeriv_id]
    simp [hr_ne_zero, hr_ne_one]
  have hcenterMapTop :
      iteratedDeriv r (d.centerMap ζ) u =
        iteratedFDeriv ℝ r (fun z : ℝ × X ↦ (d.R z).1)
            (u, (ζ : ℝ → X) u)
            (fun _ : Fin r ↦
              iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u)
          + derivCenterFiber d ζ u (iteratedDeriv r (ζ : ℝ → X) u)
          + ∑ c ∈ (Finset.univ.filter
              (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
              iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).1)
                (u, (ζ : ℝ → X) u)
                (fun j ↦ iteratedDeriv (c.partSize j)
                  (fun y ↦ (y, (ζ : ℝ → X) y)) u) := by
    calc
      iteratedDeriv r (d.centerMap ζ) u =
          iteratedDeriv r
            ((fun y : ℝ ↦ y) + (fun y : ℝ ↦ (d.R (y, (ζ : ℝ → X) y)).1)) u := by
        rw [hcenterFunction]
      _ = iteratedDeriv r (fun y : ℝ ↦ y) u
          + iteratedDeriv r (fun y : ℝ ↦ (d.R (y, (ζ : ℝ → X) y)).1) u :=
        hcenterAdd
      _ = iteratedDeriv r (fun y : ℝ ↦ (d.R (y, (ζ : ℝ → X) y)).1) u := by
        rw [hidzero, zero_add]
      _ = _ := hcenter
  have hzetaSingle :
      iteratedFDeriv ℝ (singleBlock r hr0).length (ζ : ℝ → X)
          (d.centerMap ζ u)
          (fun j ↦ iteratedDeriv ((singleBlock r hr0).partSize j)
            (d.centerMap ζ) u) =
        iteratedDeriv r (d.centerMap ζ) u •
          deriv (ζ : ℝ → X) (d.centerMap ζ u) := by
    show iteratedFDeriv ℝ 1 (ζ : ℝ → X) (d.centerMap ζ u)
          (fun _ : Fin 1 ↦ iteratedDeriv r (d.centerMap ζ) u) =
        iteratedDeriv r (d.centerMap ζ) u •
          deriv (ζ : ℝ → X) (d.centerMap ζ u)
    rw [iteratedFDeriv_one_apply, fderiv_eq_smul_deriv]
  have hzetaMem :
      singleBlock r hr0 ∈
        (Finset.univ.filter (fun c : OrderedFinpartition r ↦ c.length ≠ r)) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [singleBlock_length]
    omega
  have hzetaErase :
      (Finset.univ.filter
          (fun c : OrderedFinpartition r ↦ c.length ≠ r)).erase (singleBlock r hr0) =
        Finset.univ.filter
          (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1) := by
    ext c
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, and_true, true_and]
    constructor
    · rintro ⟨hne, hlen⟩
      refine ⟨hlen, ?_⟩
      intro hone
      exact hne ((orderedFinpartition_length_eq_one_iff_singleBlock hr0 c).mp hone)
    · rintro ⟨hlenr, hlen1⟩
      refine ⟨?_, hlenr⟩
      intro heq
      subst heq
      rw [singleBlock_length] at hlen1
      exact hlen1 rfl
  have hzetaRemainder :
      (∑ c ∈ (Finset.univ.filter
          (fun c : OrderedFinpartition r ↦ c.length ≠ r)),
          iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ u)
            (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) u)) =
        iteratedDeriv r (d.centerMap ζ) u •
            deriv (ζ : ℝ → X) (d.centerMap ζ u)
          + ∑ c ∈ (Finset.univ.filter
              (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
              iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ u)
                (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) u) := by
    rw [← Finset.add_sum_erase _ _ hzetaMem, hzetaSingle, hzetaErase]
  have hsolved :=
    iteratedDeriv_fixedGraph_cocycle_solved d ζ hfixed r hrν hprev hζ1 u
  rw [hstable, hzetaRemainder, hcenterMapTop] at hsolved
  rw [hsolved, metricReservedTopCoefficient_apply]
  unfold metricReservedTopForcing
  simp only [smul_add, smul_sub, add_smul]
  abel

/-- Helper for Infrastructure I.16a: on a fixed graph, the complete reserved-top-order
coefficient is bounded by the full metric transform rate; its trailing rate term absorbs the
center feedback using the sharp fixed-graph Lipschitz constant. -/
theorem metricReservedTopCoefficient_apply_norm_le [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hζ1 : ContDiff ℝ 1 (ζ : ℝ → X)) (hfixed : d.transform ζ = ζ)
    (m : ℕ) (u : ℝ) (w : X) :
    ‖metricReservedTopCoefficient d ζ m u w‖ ≤
      ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ m) * ‖w‖ := by
  have hpow_abs_le : |(deriv (d.centerMap ζ) u)⁻¹ ^ m| ≤ (d.lower : ℝ)⁻¹ ^ m :=
    centerMap_deriv_inv_pow_abs_le d ζ hζ1 m u
  have hLw : ‖d.L w‖ ≤ (d.linearRate : ℝ) * ‖w‖ := by
    calc
      ‖d.L w‖ ≤ ‖d.L‖ * ‖w‖ := d.L.le_opNorm w
      _ ≤ (d.linearRate : ℝ) * ‖w‖ :=
        mul_le_mul_of_nonneg_right d.hL (norm_nonneg _)
  have hfiber : ‖derivFiber d ζ u w‖ ≤ (d.epsilon : ℝ) * ‖w‖ := by
    calc
      ‖derivFiber d ζ u w‖ ≤ ‖derivFiber d ζ u‖ * ‖w‖ :=
        (derivFiber d ζ u).le_opNorm w
      _ ≤ (d.epsilon : ℝ) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (norm_derivFiber_le d ζ u) (norm_nonneg _)
  have hcenter : ‖derivCenterFiber d ζ u w‖ ≤ (d.epsilon : ℝ) * ‖w‖ := by
    calc
      ‖derivCenterFiber d ζ u w‖ ≤ ‖derivCenterFiber d ζ u‖ * ‖w‖ :=
        (derivCenterFiber d ζ u).le_opNorm w
      _ ≤ (d.epsilon : ℝ) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (norm_derivCenterFiber_le d ζ u) (norm_nonneg _)
  have hζ_deriv :
      ‖deriv (ζ : ℝ → X) (d.centerMap ζ u)‖ ≤
        ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
          (d.lower : ℝ)⁻¹ := by
    exact d.norm_deriv_fixedGraph_le_sharp ζ hfixed (d.centerMap ζ u)
  have hcenter_bound_nonneg : (0 : ℝ) ≤ (d.epsilon : ℝ) * ‖w‖ := by
    positivity
  have hfeedback :
      ‖(derivCenterFiber d ζ u w) • deriv (ζ : ℝ → X) (d.centerMap ζ u)‖ ≤
        (((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
          (d.lower : ℝ)⁻¹ * (d.epsilon : ℝ)) * ‖w‖ := by
    calc
      ‖(derivCenterFiber d ζ u w) •
          deriv (ζ : ℝ → X) (d.centerMap ζ u)‖ =
          ‖derivCenterFiber d ζ u w‖ *
            ‖deriv (ζ : ℝ → X) (d.centerMap ζ u)‖ := norm_smul _ _
      _ ≤ ((d.epsilon : ℝ) * ‖w‖) *
          (((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
            (d.lower : ℝ)⁻¹) := by
        exact mul_le_mul hcenter hζ_deriv (norm_nonneg _) hcenter_bound_nonneg
      _ = (((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
          (d.lower : ℝ)⁻¹ * (d.epsilon : ℝ)) * ‖w‖ := by ring
  have hfiber_cocycle :
      ‖d.L w + derivFiber d ζ u w‖ ≤
        ((d.linearRate : ℝ) + (d.epsilon : ℝ)) * ‖w‖ := by
    calc
      ‖d.L w + derivFiber d ζ u w‖ ≤ ‖d.L w‖ + ‖derivFiber d ζ u w‖ :=
        norm_add_le _ _
      _ ≤ (d.linearRate : ℝ) * ‖w‖ + (d.epsilon : ℝ) * ‖w‖ :=
        add_le_add hLw hfiber
      _ = ((d.linearRate : ℝ) + (d.epsilon : ℝ)) * ‖w‖ := by ring
  have hcoefficient :
      ‖d.L w + derivFiber d ζ u w -
          (derivCenterFiber d ζ u w) •
            deriv (ζ : ℝ → X) (d.centerMap ζ u)‖ ≤
        ((d.linearRate : ℝ) + (d.epsilon : ℝ) +
          ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
            (d.lower : ℝ)⁻¹ * (d.epsilon : ℝ)) * ‖w‖ := by
    calc
      ‖d.L w + derivFiber d ζ u w -
          (derivCenterFiber d ζ u w) •
            deriv (ζ : ℝ → X) (d.centerMap ζ u)‖ ≤
          ‖d.L w + derivFiber d ζ u w‖ +
            ‖(derivCenterFiber d ζ u w) •
              deriv (ζ : ℝ → X) (d.centerMap ζ u)‖ := norm_sub_le _ _
      _ ≤ ((d.linearRate : ℝ) + (d.epsilon : ℝ)) * ‖w‖ +
          (((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
            (d.lower : ℝ)⁻¹ * (d.epsilon : ℝ)) * ‖w‖ :=
        add_le_add hfiber_cocycle hfeedback
      _ = ((d.linearRate : ℝ) + (d.epsilon : ℝ) +
          ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
            (d.lower : ℝ)⁻¹ * (d.epsilon : ℝ)) * ‖w‖ := by ring
  have hrate_real :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) =
        (d.linearRate : ℝ) + (d.epsilon : ℝ) +
          ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
            (d.lower : ℝ)⁻¹ * (d.epsilon : ℝ) := by
    exact metricGraphTransformRate_coe d.lower d.linearRate d.epsilon d.slope
  have hlower_inv_pow_nonneg : (0 : ℝ) ≤ (d.lower : ℝ)⁻¹ ^ m := by
    positivity
  rw [metricReservedTopCoefficient_apply, norm_smul, Real.norm_eq_abs]
  calc
    |(deriv (d.centerMap ζ) u)⁻¹ ^ m| *
        ‖d.L w + derivFiber d ζ u w -
          (derivCenterFiber d ζ u w) •
            deriv (ζ : ℝ → X) (d.centerMap ζ u)‖ ≤
        (d.lower : ℝ)⁻¹ ^ m *
          ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) * ‖w‖) := by
      rw [hrate_real]
      exact mul_le_mul hpow_abs_le hcoefficient (norm_nonneg _) hlower_inv_pow_nonneg
    _ = ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ m) * ‖w‖ := by ring
/-- Helper for Infrastructure I.16a: the operator norm of the complete reserved-top-order
coefficient is bounded by the contraction coefficient supplied by the metric transform rate. -/
theorem norm_metricReservedTopCoefficient_le [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hζ1 : ContDiff ℝ 1 (ζ : ℝ → X)) (hfixed : d.transform ζ = ζ)
    (m : ℕ) (u : ℝ) :
    ‖metricReservedTopCoefficient d ζ m u‖ ≤
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ m := by
  have hrate_coefficient_nonneg :
      (0 : ℝ) ≤
        (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
          (d.lower : ℝ)⁻¹ ^ m := by
    positivity
  apply (metricReservedTopCoefficient d ζ m u).opNorm_le_bound hrate_coefficient_nonneg
  intro w
  exact metricReservedTopCoefficient_apply_norm_le d ζ hζ1 hfixed m u w



/-! ## Compact-support localization of the derivative obligation.

The fixed graph `ζ` has compact support (`fixedGraph_hasCompactSupport`), so off the closed set
`tsupport ζ` every iterated derivative is locally `0` and therefore has derivative `0`
(`hasDerivAt_iteratedDeriv_of_notMem_tsupport`).  Consequently the pointwise obligation
`∀ u, HasDerivAt (iteratedDeriv m ζ) (v u) u` splits: off `tsupport ζ` it is automatic once the
candidate field `v` vanishes there; the analytic content is confined to the (compact) support.
This combinator packages that split with `v` still an opaque field, so it is available before the
closed form of `v` is fixed. -/

/-- **Localization combinator.**  A candidate derivative field `v` that (a) witnesses the
`HasDerivAt` on `tsupport ζ` and (b) vanishes off `tsupport ζ` witnesses it everywhere.  The
off-support branch is discharged by `hasDerivAt_iteratedDeriv_of_notMem_tsupport` (derivative `0`)
together with `v u = 0`. -/
theorem hasDerivAt_iteratedDeriv_of_onSupport
    {d : MetricGraphTransformData X}
    (ζ : SmallLipschitzGraph X d.radius d.slope) (m : ℕ) (v : ℝ → X)
    (hon : ∀ u ∈ tsupport (ζ : ℝ → X), HasDerivAt (iteratedDeriv m (ζ : ℝ → X)) (v u) u)
    (hoff : ∀ u ∉ tsupport (ζ : ℝ → X), v u = 0) :
    ∀ u, HasDerivAt (iteratedDeriv m (ζ : ℝ → X)) (v u) u := by
  intro u
  by_cases hu : u ∈ tsupport (ζ : ℝ → X)
  · exact hon u hu
  · rw [hoff u hu]
    exact hasDerivAt_iteratedDeriv_of_notMem_tsupport ζ m hu

/-! ## The radius-envelope factor tuple.

The self-similar secant-defect recurrence contracts by the linear factor `p = rate · lower⁻ᵐ`
after the inverse-center change of variables of scale `c = lower⁻¹`.  The envelope hypotheses
`0 ≤ p`, `p < 1`, `0 < c`, `p · c < 1` are exactly the bunching arithmetic of the Stage-A leaf; we
collect them into one lemma (independent of the closed form of `v`) so the call to
`radiusEnvelope_sublinear_of_recurrence` is a single application. -/

/-- The radius-envelope factor hypotheses for the metric secant recurrence, packaged together:
`p = rate · lower⁻ᵐ` is nonnegative and `< 1`, `c = lower⁻¹ > 0`, and `p · c < 1`. -/
theorem radiusEnvelope_factors
    (d : MetricGraphTransformData X)
    (h_bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1)
    {m : ℕ} (hm : m < d.nu) :
    (0 : ℝ) ≤ (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ m ∧
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ m < 1 ∧
      (0 : ℝ) < (d.lower : ℝ)⁻¹ ∧
      ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ m) * (d.lower : ℝ)⁻¹ < 1 :=
  ⟨bunching_linear_factor_nonneg d m,
    bunching_linear_factor_lt_one d h_bunching hm,
    bunching_change_of_variables_pos d,
    bunching_transport_factor_lt_one d h_bunching hm⟩

/-! ## (A) The inverse-center change-of-variables secant identity (keystone).

Write `W := iteratedDeriv m ζ`, `Φ := d.centerMap ζ`, `Ψ := d.inverseCenter ζ` (a global inverse of
`Φ`, `lower⁻¹`-Lipschitz).  The solved value cocycle
`iteratedDeriv_fixedGraph_cocycle_solved` reads, at any base point `w`,
`W (Φ w) = (Φ′w)⁻ᵐ • L (W w) + Rem w`, where `Rem w` collects the fiber-remainder derivative and the
strictly-lower-order Faà-di-Bruno `ζ`-remainder (the `(C)` bucket).  Evaluating at `w = Ψ y` and
`w = Ψ y'` and using `Φ (Ψ y) = y` re-expresses the **translation secant of `W` between `y` and
`y'`** as the difference of the `(Φ′)⁻ᵐ • L`-self-references at the `Ψ`-preimages plus the difference
of remainders.  Because `Ψ` is `lower⁻¹`-Lipschitz, the self-reference is `W` sampled at points whose
separation is `≤ lower⁻¹ · dist y y'` — this is the `c = lower⁻¹` self-similarity that the radius
envelope recurrence consumes.

The `(C)` bucket is kept as an EXPLICIT hypothesis `hcocycle` (the cocycle written in `Rem`-form with
`Rem` an opaque field) — no unresolved proof placeholder or discharge of the lower-order estimate here. -/

/-- **(A.1) Change-of-variables scale bound.**  The inverse center map `Ψ = d.inverseCenter ζ`
contracts distances by the factor `c = lower⁻¹`: `dist (Ψ y) (Ψ y') ≤ lower⁻¹ · dist y y'`.  This is
the geometric source of the `c·x` self-similarity in the radius-envelope recurrence. -/
theorem inverseCenter_dist_scale_le
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) (y y' : ℝ) :
    dist (d.inverseCenter ζ y) (d.inverseCenter ζ y') ≤
      (d.lower : ℝ)⁻¹ * dist y y' := by
  have hlip := (d.inverseCenter_lipschitzWith ζ).dist_le_mul y y'
  simpa only [NNReal.coe_inv] using hlip

/-- **(A.2) Subtracted-cocycle change-of-variables secant identity (keystone).**  Given the value
cocycle in `Rem`-form — `∀ w, W (Φ w) = (Φ′w)⁻ᵐ • L (W w) + Rem w`, with `W := iteratedDeriv m ζ`,
`Φ := d.centerMap ζ` and `Rem : ℝ → X` opaque (the `(C)` lower-order bucket) — the translation secant
of `W` between `y` and `y'` decomposes as the difference of the `(Φ′)⁻ᵐ • L`-self-references at the
inverse-center preimages `Ψ y, Ψ y'` plus the difference of remainders.  Uses only `Φ (Ψ y) = y`
(right inverse of the bijective center map).  This exhibits the exact `p·F(c·x) + (lower order)`
SHAPE — the self-reference term is `L` applied to `W` sampled at points separated by
`≤ lower⁻¹ · dist y y'` (via `inverseCenter_dist_scale_le`), and the remainder difference is the
lower-order forcing — WITHOUT discharging the `(C)` estimate (which stays inside the opaque `Rem`). -/
theorem subtracted_cocycle_changeOfVariables
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) (m : ℕ) (Rem : ℝ → X)
    (hcocycle : ∀ w : ℝ,
      iteratedDeriv m (ζ : ℝ → X) (d.centerMap ζ w)
        = (deriv (d.centerMap ζ) w)⁻¹ ^ m • d.L (iteratedDeriv m (ζ : ℝ → X) w) + Rem w)
    (y y' : ℝ) :
    iteratedDeriv m (ζ : ℝ → X) y - iteratedDeriv m (ζ : ℝ → X) y'
      = ((deriv (d.centerMap ζ) (d.inverseCenter ζ y))⁻¹ ^ m •
            d.L (iteratedDeriv m (ζ : ℝ → X) (d.inverseCenter ζ y))
          - (deriv (d.centerMap ζ) (d.inverseCenter ζ y'))⁻¹ ^ m •
            d.L (iteratedDeriv m (ζ : ℝ → X) (d.inverseCenter ζ y')))
        + (Rem (d.inverseCenter ζ y) - Rem (d.inverseCenter ζ y')) := by
  -- `Φ (Ψ y) = y` and `Φ (Ψ y') = y'` (right inverse of the bijective center map).
  have hΨ_def : d.inverseCenter ζ = Function.invFun (d.centerMap ζ) := d.inverseCenter_eq ζ
  have hΦΨ : ∀ z : ℝ, d.centerMap ζ (d.inverseCenter ζ z) = z := by
    intro z
    rw [hΨ_def]
    exact Function.rightInverse_invFun (d.centerMap_bijective ζ).2 z
  -- Rewrite `W y` and `W y'` through `Φ (Ψ ·) = ·`, then apply the cocycle at `w = Ψ y, Ψ y'`.
  have hy : iteratedDeriv m (ζ : ℝ → X) y
      = (deriv (d.centerMap ζ) (d.inverseCenter ζ y))⁻¹ ^ m •
          d.L (iteratedDeriv m (ζ : ℝ → X) (d.inverseCenter ζ y))
        + Rem (d.inverseCenter ζ y) := by
    conv_lhs => rw [← hΦΨ y]
    exact hcocycle (d.inverseCenter ζ y)
  have hy' : iteratedDeriv m (ζ : ℝ → X) y'
      = (deriv (d.centerMap ζ) (d.inverseCenter ζ y'))⁻¹ ^ m •
          d.L (iteratedDeriv m (ζ : ℝ → X) (d.inverseCenter ζ y'))
        + Rem (d.inverseCenter ζ y') := by
    conv_lhs => rw [← hΦΨ y']
    exact hcocycle (d.inverseCenter ζ y')
  rw [hy, hy']
  abel

/-- **(A.3) Cocycle in `Rem`-form is available from the solved cocycle.**  Specializes
`iteratedDeriv_fixedGraph_cocycle_solved` to exhibit the opaque remainder `Rem` consumed by
`subtracted_cocycle_changeOfVariables`: `Rem w` is exactly the fiber-remainder derivative minus the
Faà-di-Bruno `ζ`-remainder, scaled by `(Φ′w)⁻ᵐ`.  This packages the `(C)` bucket as a concrete but
still-unestimated field, so downstream `(B)/(C)` work operates on a named object. -/
theorem exists_cocycle_remainder_form
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    (m : ℕ) (hmν : m ≤ d.nu) (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (hζ1 : ContDiff ℝ 1 (ζ : ℝ → X)) :
    ∃ Rem : ℝ → X, ∀ w : ℝ,
      iteratedDeriv m (ζ : ℝ → X) (d.centerMap ζ w)
        = (deriv (d.centerMap ζ) w)⁻¹ ^ m • d.L (iteratedDeriv m (ζ : ℝ → X) w) + Rem w := by
  refine ⟨fun w ↦
      (deriv (d.centerMap ζ) w)⁻¹ ^ m •
        (iteratedDeriv m (fun z ↦ (d.R (z, (ζ : ℝ → X) z)).2) w
          - ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m)),
              iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ w)
                (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) w)), ?_⟩
  intro w
  have hsolved := iteratedDeriv_fixedGraph_cocycle_solved d ζ hfixed m hmν hprev hζ1 w
  rw [hsolved]
  -- Distribute the scalar `(Φ′w)⁻ᵐ` over the `(L(W w) + fiber) − Σ` bracket and regroup so the
  -- self-reference `(Φ′w)⁻ᵐ • L(W w)` is isolated and the rest is the opaque remainder `Rem w`.
  simp only [smul_sub, smul_add]
  abel

/-! ## (B) The contracted self-reference bound at the inverse-center base point.

The `a(u)`-factored piece of the self-reference difference — `a(u) • L z` with
`a(u) := (Φ′(Ψ u))⁻ᵐ` and `z` the inner increment/defect of `W` at the `Ψ`-image — is bounded by
`p · ‖z‖` with `p = rate · lower⁻ᵐ < 1`.  This is `operator_linear_part_norm_le` (the `L`-only
bound, coefficient `linearRate`) at the base point `Ψ u`, upgraded to the metric rate via
`linearRate_add_epsilon_le_metricGraphTransformRate_real`.  Note this bounds the `L`-part ALONE (the
fiber `derivFiber` piece is inside the opaque `Rem`, not here), which is exactly the shape (A.2)'s
self-reference term takes. -/

/-- **(B) Self-reference contraction bound.**  `‖(Φ′(Ψ u))⁻ᵐ • L z‖ ≤ (rate · lower⁻ᵐ) · ‖z‖ = p·‖z‖`.
Reuses `operator_linear_part_norm_le` at base point `Ψ u` and upgrades `linearRate ≤ rate`. -/
theorem selfReference_contraction_norm_le
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hζ1 : ContDiff ℝ 1 (ζ : ℝ → X)) (m : ℕ) (u : ℝ) (z : X) :
    ‖(deriv (d.centerMap ζ) (d.inverseCenter ζ u))⁻¹ ^ m • d.L z‖ ≤
      ((metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ m) * ‖z‖ := by
  have hbase := operator_linear_part_norm_le d ζ hζ1 m (d.inverseCenter ζ u) z
  have hrate_le :
      (d.linearRate : ℝ) ≤
        (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) := by
    have hchain :=
      linearRate_add_epsilon_le_metricGraphTransformRate_real d.lower d.linearRate d.epsilon d.slope
    have hε_nonneg : (0 : ℝ) ≤ (d.epsilon : ℝ) := (d.epsilon).coe_nonneg
    linarith
  have hpow_nonneg : (0 : ℝ) ≤ (d.lower : ℝ)⁻¹ ^ m := by positivity
  have hcoeff_le :
      ((d.linearRate : ℝ)) * (d.lower : ℝ)⁻¹ ^ m ≤
        (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
          (d.lower : ℝ)⁻¹ ^ m :=
    mul_le_mul_of_nonneg_right hrate_le hpow_nonneg
  refine hbase.trans ?_
  exact mul_le_mul_of_nonneg_right hcoeff_le (norm_nonneg _)

end LocalInvariantGraph
