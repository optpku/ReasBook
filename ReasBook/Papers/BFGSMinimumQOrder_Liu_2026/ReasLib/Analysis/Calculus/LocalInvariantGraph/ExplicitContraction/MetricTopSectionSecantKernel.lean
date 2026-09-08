module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionHolonomicBridge
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionDerivativeBridge
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Module.FiniteDimension

public section
noncomputable section
open scoped NNReal Topology
open Filter Set
universe u
namespace LocalInvariantGraph
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## The master differentiated identity.

Write `S := iteratedDeriv m ζ`, `φ := d.centerMap ζ`, `g u := (d.R (u, ζ u)).2`.
The fixed-point equation reads `ζ ∘ φ = L ∘ ζ + g` as functions.  Differentiating
`m` times gives an identity relating `iteratedDeriv m (ζ ∘ φ)` to `L (S ·)` plus the
continuous jet of `g`. -/

/-- The fixed-point equation packaged as an equality of scalar functions `ζ ∘ φ = L ∘ ζ + g`. -/
theorem fixedGraph_comp_eq [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) :
    ((ζ : ℝ → X) ∘ d.centerMap ζ)
      = fun u ↦ d.L ((ζ : ℝ → X) u) + (d.R (u, (ζ : ℝ → X) u)).2 := by
  funext u
  simpa only [Function.comp_apply] using
    d.fixedGraph_equation ζ hfixed u

/-! ## The center map as identity plus remainder.

`φ u = u + c u` with `c u := (d.R (u, ζ u)).1`.  The center-map derivative estimates
(`epsilon`-Lipschitz remainder, `φ' u ≥ lower > 0`, nonvanishing) are the Stage-A helpers of
`MetricTopSectionHolonomicBridge`, imported above; only the identity decomposition `φ = id + c`
is stated here (it is unique to this file). -/

/-- The center map differs from the identity by the center remainder: `φ = id + c`. -/
theorem centerMap_eq_add_remainder
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) :
    d.centerMap ζ = fun u ↦ u + (d.R (u, (ζ : ℝ → X) u)).1 := d.centerMap_eq ζ

/-! ## Iterated derivatives commute with left composition by a continuous linear map.

The fixed-graph equation `ζ ∘ Φ = L ∘ ζ + g` (with `g u = (d.R (u, ζ u)).2`) is differentiated
`m` times below.  The `L ∘ ζ` term is linear in `ζ`, so its `m`-th iterated derivative is `L`
applied to `iteratedDeriv m ζ` — this lets the self-referential `L (S ·)` term (with
`S := iteratedDeriv m ζ`) be isolated.  Both forks of the analytic core need this and neither
stated it. -/

/-- The `m`-th iterated derivative of `L ∘ ζ` at `u` is `L` applied to the `m`-th iterated
derivative of `ζ` at `u`, whenever `ζ` is `Cᵐ` at `u`.  Follows from
`ContinuousLinearMap.iteratedFDeriv_comp_left` plus the definition of `iteratedDeriv` as the
diagonal `fun _ ↦ (1 : ℝ)` of `iteratedFDeriv`. -/
theorem iteratedDeriv_clm_comp_left
    (L : X →L[ℝ] X) (ζ : ℝ → X) {m : ℕ} {u : ℝ} (hζ : ContDiffAt ℝ m ζ u) :
    iteratedDeriv m (L ∘ ζ) u = L (iteratedDeriv m ζ u) := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  -- `iteratedFDeriv_comp_left` rewrites the LHS multilinear map to the postcomposition
  -- `L.compContinuousMultilinearMap (iteratedFDeriv m ζ u)`; then evaluate on the diagonal
  -- `fun _ ↦ 1`, where `compContinuousMultilinearMap_coe` turns the postcomposition into `L ∘ (·)`.
  change (iteratedFDeriv ℝ m (L ∘ ζ) u) (fun _ ↦ 1) =
    L ((iteratedFDeriv ℝ m ζ u) (fun _ ↦ 1))
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left (g := L) (f := ζ) (x := u) hζ (le_refl _)]
  rw [ContinuousLinearMap.compContinuousMultilinearMap_coe]
  rfl

/-- The fiber remainder coordinate `g u = (d.R (u, ζ u)).2` is `ContDiff ℝ m` whenever `ζ` is,
provided `m ≤ d.nu`.  Written as `Prod.snd ∘ d.R ∘ (fun u ↦ (u, ζ u))`. -/
theorem centerFiberRemainder_contDiff
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {m : ℕ} (hmν : (m : WithTop ℕ∞) ≤ d.nu) (hζ : ContDiff ℝ m (ζ : ℝ → X)) :
    ContDiff ℝ m (fun u : ℝ ↦ (d.R (u, (ζ : ℝ → X) u)).2) := by
  have hgraph : ContDiff ℝ m (fun u : ℝ ↦ (u, (ζ : ℝ → X) u)) :=
    contDiff_id.prodMk hζ
  have hR : ContDiff ℝ m d.R := d.hR_smooth.of_le hmν
  exact contDiff_snd.comp (hR.comp hgraph)

end LocalInvariantGraph
