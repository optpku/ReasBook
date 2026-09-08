module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricPicardCertificate
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.Tangent
import all ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricPicardCertificate

public section

noncomputable section

open Filter
open scoped NNReal Topology

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-!
# Invariant-graph output for metric Picard certificates

The metric Picard package constructs a fixed graph for a globally Lipschitz remainder.  This
module gives that construction the same map-level output as the local invariant-graph theorem.
The finite-smooth fixed-point regularity and the zero derivative of the remainder remain explicit
certificates; neither is inferred from the metric contraction alone.
-/

/-- Helper for Infrastructure I.16a: the map represented by a linear center-stable block and a
metric Picard remainder. -/
def metricCenterStableMap (d : MetricGraphTransformData X) : ℝ × X → ℝ × X :=
  (LocalCutoff.centerStable d.L : ℝ × X → ℝ × X) + d.R

/-- The metric center-stable map is the pointwise sum of its linear block and remainder. -/
theorem metricCenterStableMap_eq (d : MetricGraphTransformData X) :
    metricCenterStableMap d =
      fun x ↦ LocalCutoff.centerStable d.L x + d.R x := by
  rfl

/-- Helper for Infrastructure I.16a: the metric center-stable map has the expected coordinate
formula on a graph point. -/
theorem metricCenterStableMap_apply (d : MetricGraphTransformData X) (u : ℝ) (z : X) :
    metricCenterStableMap d (u, z) =
      (u + (d.R (u, z)).1, d.L z + (d.R (u, z)).2) := by
  change LocalCutoff.centerStable d.L (u, z) + d.R (u, z) = _
  rw [LocalCutoff.centerStable_apply]
  rfl

/-- Helper for Infrastructure I.16a: a smooth metric remainder makes the represented map
smooth of the same finite order. -/
theorem metricCenterStableMap_contDiff
    (d : MetricGraphTransformData X) :
    ContDiff ℝ d.nu (metricCenterStableMap d) := by
  have hsum := (LocalCutoff.centerStable d.L).contDiff.add d.hR_smooth
  unfold metricCenterStableMap
  exact hsum

/-- Helper for Infrastructure I.16a: a zero derivative of the metric remainder gives the
center-stable derivative of the represented map. -/
theorem metricCenterStableMap_hasFDerivAt_of_zeroDerivative
    (d : MetricGraphTransformData X)
    (hR_deriv : HasFDerivAt d.R
      (0 : (ℝ × X) →L[ℝ] (ℝ × X)) (0, 0)) :
    HasFDerivAt (metricCenterStableMap d)
      (LocalCutoff.centerStable d.L) (0, 0) := by
  have hsum := (LocalCutoff.centerStable d.L).hasFDerivAt.add hR_deriv
  have hprod_add :
      (Prod.instAddCommGroup : AddCommGroup (ℝ × X)) =
        Prod.normedAddCommGroup.toAddCommGroup := by
    with_reducible_and_instances rfl
  have hprod_module :
      (Prod.instModule : Module ℝ (ℝ × X)) =
        Prod.normedSpace.toModule := by
    with_reducible_and_instances rfl
  have hprod_top :
      (instTopologicalSpaceProd : TopologicalSpace (ℝ × X)) =
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    with_reducible_and_instances rfl
  unfold metricCenterStableMap
  simpa only [hprod_add, hprod_module, hprod_top, add_zero] using hsum

/-- Helper for Infrastructure I.16a: the represented metric map fixes the origin. -/
theorem metricCenterStableMap_zero (d : MetricGraphTransformData X) :
    metricCenterStableMap d (0, 0) = (0, 0) := by
  have hR_zero : d.R (0, 0) = 0 := by
    simpa only [Prod.mk_zero_zero] using d.hR_zero
  change LocalCutoff.centerStable d.L (0, 0) + d.R (0, 0) = (0, 0)
  rw [hR_zero]
  simp only [LocalCutoff.centerStable_apply, map_zero, add_zero]

/-- Helper for Infrastructure I.16a: a metric transform fixed graph satisfies the invariant
equation for the represented center-stable map. -/
theorem metricFixedGraph_invariant
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hζ_fixed : d.transform ζ = ζ) :
    (fun u ↦ (metricCenterStableMap d (u, ζ u)).2) =ᶠ[𝓝 0]
      fun u ↦ ζ (metricCenterStableMap d (u, ζ u)).1 := by
  filter_upwards [] with u
  have hpoint := d.fixedGraph_equation ζ hζ_fixed u
  change ζ (u + (d.R (u, ζ u)).1) = d.L (ζ u) + (d.R (u, ζ u)).2 at hpoint
  simpa only [metricCenterStableMap_apply] using hpoint.symm

/-- Infrastructure I.16a (metric Picard certificate with a finite-smooth fixed graph): an
explicit metric contraction, a zero-derivative remainder certificate, and regularity of its
fixed point produce a finite-smooth invariant graph tangent to the center axis. -/
theorem exists_metricInvariantGraph_of_regularFixedPoint
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (hR_deriv : HasFDerivAt d.R
      (0 : (ℝ × X) →L[ℝ] (ℝ × X)) (0, 0))
    (hregular : ∀ ζ : SmallLipschitzGraph X d.radius d.slope,
      d.transform ζ = ζ → ContDiffAt ℝ d.nu (ζ : ℝ → X) 0) :
    ∃ ζ : ℝ → X,
      ContDiffAt ℝ d.nu ζ 0 ∧
        ζ 0 = 0 ∧
          HasFDerivAt ζ (0 : ℝ →L[ℝ] X) 0 ∧
            (fun u ↦ (metricCenterStableMap d (u, ζ u)).2) =ᶠ[𝓝 0]
              fun u ↦ ζ (metricCenterStableMap d (u, ζ u)).1 := by
  obtain ⟨ζ, hζ_fixed⟩ := d.exists_metricFixedGraph
  have hζ_smooth := hregular ζ hζ_fixed
  have hζ_zero : (ζ : ℝ → X) 0 = 0 := SmallLipschitzGraph.zero_apply ζ
  have hzero_lt_two : (0 : ℕ) < 2 := by
    norm_num
  have hν_pos : 0 < d.nu := by
    exact hzero_lt_two.trans_le d.hnu
  have hν_ne : d.nu ≠ 0 := Nat.ne_of_gt hν_pos
  have hζ_deriv : HasFDerivAt (ζ : ℝ → X) (fderiv ℝ ζ 0) 0 := by
    exact (hζ_smooth.differentiableAt (Nat.cast_ne_zero.mpr hν_ne)).hasFDerivAt
  have hmap_zero := metricCenterStableMap_zero d
  have hmap_deriv := metricCenterStableMap_hasFDerivAt_of_zeroDerivative d hR_deriv
  have hlinearRate_real : (d.linearRate : ℝ) < 1 := by
    exact_mod_cast d.hlinearRate
  have hL : ‖d.L‖ < 1 := d.hL.trans_lt hlinearRate_real
  have hinvariant := metricFixedGraph_invariant d ζ hζ_fixed
  have htangent := tangent_zero_of_centerStable_invariant
    (ζ : ℝ → X) (fderiv ℝ ζ 0) (metricCenterStableMap d) d.L hζ_zero hζ_deriv
    hmap_zero hmap_deriv hinvariant hL
  exact ⟨ζ, hζ_smooth, hζ_zero, htangent, hinvariant⟩

/-- Infrastructure I.16a (metric Picard germ transfer): the preceding invariant graph transfers
from the metric model to any original map with the same germ at the fixed point. -/
theorem invariantGraph_of_metricFixedPoint_germ
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (hR_deriv : HasFDerivAt d.R
      (0 : (ℝ × X) →L[ℝ] (ℝ × X)) (0, 0))
    (hregular : ∀ ζ : SmallLipschitzGraph X d.radius d.slope,
      d.transform ζ = ζ → ContDiffAt ℝ d.nu (ζ : ℝ → X) 0)
    (F : ℝ × X → ℝ × X)
    (hF_germ : F =ᶠ[𝓝 (0, 0)] metricCenterStableMap d) :
    ∃ ζ : ℝ → X,
      ContDiffAt ℝ d.nu ζ 0 ∧
        ζ 0 = 0 ∧
          HasFDerivAt ζ (0 : ℝ →L[ℝ] X) 0 ∧
            (fun u ↦ (F (u, ζ u)).2) =ᶠ[𝓝 0]
              fun u ↦ ζ (F (u, ζ u)).1 := by
  obtain ⟨ζ, hζ_smooth, hζ_zero, hζ_deriv, hmetric_invariant⟩ :=
    exists_metricInvariantGraph_of_regularFixedPoint d hR_deriv hregular
  have hζ_cont : Tendsto (ζ : ℝ → X) (𝓝 0) (𝓝 0) := by
    have hcont : Tendsto (ζ : ℝ → X) (𝓝 0) (𝓝 (ζ 0)) :=
      hζ_smooth.continuousAt
    rw [hζ_zero] at hcont
    exact hcont
  have hgraph_tendsto : Tendsto (fun u : ℝ ↦ (u, ζ u))
      (𝓝 0) (𝓝 (0, 0)) := by
    have hfirst : Tendsto (fun u : ℝ ↦ u) (𝓝 0) (𝓝 (0 : ℝ)) := tendsto_id
    simpa only [nhds_prod_eq] using hfirst.prodMk hζ_cont
  have hF_graph : (fun u : ℝ ↦ F (u, ζ u)) =ᶠ[𝓝 0]
      (fun u ↦ metricCenterStableMap d (u, ζ u)) := by
    simpa only [Function.comp_def] using hF_germ.comp_tendsto hgraph_tendsto
  refine ⟨ζ, hζ_smooth, hζ_zero, hζ_deriv, ?_⟩
  filter_upwards [hmetric_invariant, hF_graph] with u hu hFu
  rw [hFu]
  exact hu

end LocalInvariantGraph
