module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform
import all ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction
import all ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform

public section

noncomputable section

open Filter
open scoped NNReal Topology

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {radius slope : ℝ≥0}

/-!
This companion supplies the regularity side of Infrastructure I.16a once the
quantitative contraction package has been assembled.  It deliberately keeps the
quantitative certificate explicit and does not attempt to manufacture one from a
bare local derivative bound.
-/

/-- Helper for Infrastructure I.16a: a fixed point of the explicit graph-transform map is
finite-smooth when the transform satisfies the bunching inequality at every order. -/
theorem transform_fixedPoint_contDiff_of_bunching
    [CompleteSpace X] [FiniteDimensional ℝ X]
    (d : GraphTransformContractionData (X := X) (radius := radius) (slope := slope))
    (h_bunching : ∀ r, 1 ≤ r → r ≤ d.ν →
      LocalCutoff.GraphTransform.rate d.lower d.linearRate d.stableCenter d.stableFiber
        d.centerFiber slope * (d.lower : ℝ)⁻¹ ^ r < 1)
    (ζ : SmallLipschitzGraph X radius slope)
    (hζ_fixed :
      LocalCutoff.GraphTransform.map d.ν d.χ d.ρ d.L d.N d.lower d.linearRate
        d.stableBound d.stableCenter d.stableFiber d.hν d.h_center_smooth
        d.h_lower_pos d.h_lower d.hN_zero d.hL d.h_stable_bound
        d.h_stable_lipschitz d.h_radius d.h_slope ζ = ζ) :
    ContDiff ℝ d.ν (ζ : ℝ → X) := by
  exact LocalCutoff.GraphTransform.fixedPoint_contDiff
    d.ν d.χ d.ρ d.L d.N d.lower d.linearRate d.stableBound d.stableCenter
    d.stableFiber d.centerFiber d.hν d.hχ_smooth d.hχ_support d.hρ d.hN_smooth
    d.h_center_smooth d.h_lower_pos d.h_lower d.hN_zero d.hL d.h_linearRate
    d.h_stable_bound d.h_stable_lipschitz d.h_center_fiber d.h_radius d.h_slope
    d.h_rate h_bunching ζ hζ_fixed

/-- Infrastructure I.16a (finite-smooth invariant graph under an explicit stable contraction):
the explicit graph-transform map has a finite-smooth fixed graph under the same bunching
certificate. -/
theorem exists_finiteSmooth_fixedGraph_of_bunching
    [CompleteSpace X] [FiniteDimensional ℝ X]
    (d : GraphTransformContractionData (X := X) (radius := radius) (slope := slope))
    (h_bunching : ∀ r, 1 ≤ r → r ≤ d.ν →
      LocalCutoff.GraphTransform.rate d.lower d.linearRate d.stableCenter d.stableFiber
        d.centerFiber slope * (d.lower : ℝ)⁻¹ ^ r < 1) :
    ∃ ζ : SmallLipschitzGraph X radius slope,
      LocalCutoff.GraphTransform.map d.ν d.χ d.ρ d.L d.N d.lower d.linearRate
        d.stableBound d.stableCenter d.stableFiber d.hν d.h_center_smooth
        d.h_lower_pos d.h_lower d.hN_zero d.hL d.h_stable_bound
        d.h_stable_lipschitz d.h_radius d.h_slope ζ = ζ ∧
        ContDiff ℝ d.ν (ζ : ℝ → X) := by
  let T : SmallLipschitzGraph X radius slope → SmallLipschitzGraph X radius slope :=
    LocalCutoff.GraphTransform.map d.ν d.χ d.ρ d.L d.N d.lower d.linearRate
      d.stableBound d.stableCenter d.stableFiber d.hν d.h_center_smooth
      d.h_lower_pos d.h_lower d.hN_zero d.hL d.h_stable_bound
      d.h_stable_lipschitz d.h_radius d.h_slope
  have hT : ContractingWith
      (LocalCutoff.GraphTransform.rate d.lower d.linearRate d.stableCenter
        d.stableFiber d.centerFiber slope) T := by
    dsimp only [T]
    exact LocalCutoff.GraphTransform.contractingWith_of_center_fiber
      d.ν d.χ d.ρ d.L d.N d.lower d.linearRate d.stableBound d.stableCenter
      d.stableFiber d.centerFiber d.hν d.h_center_smooth d.h_lower_pos d.h_lower
      d.hN_zero d.hL d.h_linearRate d.h_stable_bound d.h_stable_lipschitz
      d.h_center_fiber d.h_radius d.h_slope d.h_rate
  let ζ : SmallLipschitzGraph X radius slope := ContractingWith.fixedPoint T hT
  have hζ_fixed : T ζ = ζ := hT.fixedPoint_isFixedPt
  have hζ_smooth : ContDiff ℝ d.ν (ζ : ℝ → X) := by
    apply transform_fixedPoint_contDiff_of_bunching d h_bunching ζ
    simpa only [T] using hζ_fixed
  refine ⟨ζ, ?_, hζ_smooth⟩
  simpa only [T] using hζ_fixed

/-- Helper for Infrastructure I.16a: an explicit fixed graph of the inverse-center transform
obeys the forward-invariance equation before the center inverse is cancelled. -/
theorem fixedGraph_invariant_of_explicit_map
    [CompleteSpace X] [FiniteDimensional ℝ X]
    (d : GraphTransformContractionData (X := X) (radius := radius) (slope := slope))
    (ζ : SmallLipschitzGraph X radius slope)
    (hζ_fixed :
      LocalCutoff.GraphTransform.map d.ν d.χ d.ρ d.L d.N d.lower d.linearRate
        d.stableBound d.stableCenter d.stableFiber d.hν d.h_center_smooth
        d.h_lower_pos d.h_lower d.hN_zero d.hL d.h_stable_bound
        d.h_stable_lipschitz d.h_radius d.h_slope ζ = ζ) :
    (fun u ↦ (LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N
      (u, ζ u)).2) =ᶠ[𝓝 0] fun u ↦ ζ
        (LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N (u, ζ u)).1 := by
  have hzero_lt_two : (0 : ℕ) < 2 := by norm_num
  have hν_pos : 0 < d.ν := hzero_lt_two.trans_le d.hν
  have hν_ne : d.ν ≠ 0 := Nat.ne_of_gt hν_pos
  have hdiff : Differentiable ℝ
      (LocalCutoff.CenterProjection.map d.χ d.ρ d.L d.N ζ) :=
    (d.h_center_smooth ζ).differentiable (Nat.cast_ne_zero.mpr hν_ne)
  have hbij : Function.Bijective
      (LocalCutoff.CenterProjection.map d.χ d.ρ d.L d.N ζ) :=
    Real.bijective_of_pos_le_deriv hdiff d.h_lower_pos (d.h_lower ζ)
  have hpointwise : ∀ u : ℝ,
      (LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N (u, ζ u)).2 =
        ζ (LocalCutoff.CenterProjection.map d.χ d.ρ d.L d.N ζ u) := by
    intro u
    have hfixed_apply := congrArg
      (fun η : SmallLipschitzGraph X radius slope ↦ η
        (LocalCutoff.CenterProjection.map d.χ d.ρ d.L d.N ζ u)) hζ_fixed
    rw [LocalCutoff.GraphTransform.map_apply] at hfixed_apply
    have hinverse :
        LocalCutoff.CenterProjection.inverse d.χ d.ρ d.L d.N ζ
            (LocalCutoff.CenterProjection.map d.χ d.ρ d.L d.N ζ u) = u := by
      rw [LocalCutoff.CenterProjection.inverse_def]
      exact Function.leftInverse_invFun hbij.1 u
    rw [hinverse] at hfixed_apply
    exact hfixed_apply
  filter_upwards [] with u
  simpa only [LocalCutoff.CenterProjection.map_apply] using hpointwise u

/-- A quantitative cutoff certificate and its bunching inequalities transfer a finite-smooth
  invariant graph to any original map with the same germ at the fixed point.

  The certificate is intentionally an explicit input: local differentiability of an original
  map alone does not provide the global support, radius, inverse-center, or Lipschitz bounds
  required by the graph transform.
-/
theorem invariantGraph_of_bunched_cutoff_germ
    [CompleteSpace X] [FiniteDimensional ℝ X]
    (d : GraphTransformContractionData (X := X) (radius := radius) (slope := slope))
    (h_bunching : ∀ r, 1 ≤ r → r ≤ d.ν →
      LocalCutoff.GraphTransform.rate d.lower d.linearRate d.stableCenter d.stableFiber
        d.centerFiber slope * (d.lower : ℝ)⁻¹ ^ r < 1)
    (hS_deriv : HasFDerivAt
      (LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N)
      (LocalCutoff.centerStable d.L) (0, 0))
    (F : ℝ × X → ℝ × X)
    (hF_germ : F =ᶠ[𝓝 (0, 0)]
      LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N) :
    ∃ ζ : ℝ → X,
      ContDiffAt ℝ d.ν ζ 0 ∧
        ζ 0 = 0 ∧
          HasFDerivAt ζ (0 : ℝ →L[ℝ] X) 0 ∧
            (fun u ↦ (F (u, ζ u)).2) =ᶠ[𝓝 0] fun u ↦ ζ (F (u, ζ u)).1 := by
  obtain ⟨ζ, hζ_transform_fixed⟩ := d.exists_fixedGraph
  have hζ_fixed :
      LocalCutoff.GraphTransform.map d.ν d.χ d.ρ d.L d.N d.lower d.linearRate
        d.stableBound d.stableCenter d.stableFiber d.hν d.h_center_smooth
        d.h_lower_pos d.h_lower d.hN_zero d.hL d.h_stable_bound
        d.h_stable_lipschitz d.h_radius d.h_slope ζ = ζ := by
    rw [GraphTransformContractionData.transform_apply] at hζ_transform_fixed
    exact hζ_transform_fixed
  have hζ_global := transform_fixedPoint_contDiff_of_bunching d h_bunching ζ hζ_fixed
  have hζ_zero : ζ 0 = 0 := SmallLipschitzGraph.zero_apply ζ
  have hζ_smooth : ContDiffAt ℝ d.ν (ζ : ℝ → X) 0 := hζ_global.contDiffAt
  have hν_pos : 0 < d.ν := by
    exact (show (0 : ℕ) < 2 by norm_num).trans_le d.hν
  have hζ_deriv : HasFDerivAt (ζ : ℝ → X) (fderiv ℝ ζ 0) 0 := by
    exact (hζ_smooth.differentiableAt
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hν_pos))).hasFDerivAt
  have hS_zero :
      LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N (0, 0) = (0, 0) := by
    change LocalCutoff.linearize d.χ d.ρ (LocalCutoff.centerStable d.L) d.N
      (0 : ℝ × X) = (0 : ℝ × X)
    exact LocalCutoff.linearize_zero d.χ d.ρ (LocalCutoff.centerStable d.L) d.N d.hN_zero
  have hlinearRate_real : (d.linearRate : ℝ) < 1 := by
    exact_mod_cast d.h_linearRate
  have hL : ‖d.L‖ < 1 := d.hL.trans_lt hlinearRate_real
  have hS_invariant := fixedGraph_invariant_of_explicit_map d ζ hζ_fixed
  have hζ_deriv_zero := tangent_zero_of_centerStable_invariant
    (ζ : ℝ → X) (fderiv ℝ ζ 0)
    (LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N) d.L hζ_zero hζ_deriv
    hS_zero hS_deriv hS_invariant hL
  have hζ_cont : Tendsto (ζ : ℝ → X) (𝓝 0) (𝓝 (ζ 0)) :=
    hζ_smooth.continuousAt
  rw [hζ_zero] at hζ_cont
  have hgraph_tendsto : Tendsto (fun u : ℝ ↦ (u, ζ u))
      (𝓝 0) (𝓝 (0, 0)) := by
    have hfirst : Tendsto (fun u : ℝ ↦ u) (𝓝 0) (𝓝 (0 : ℝ)) := tendsto_id
    simpa only [nhds_prod_eq] using hfirst.prodMk hζ_cont
  have hF_graph : (fun u : ℝ ↦ F (u, ζ u)) =ᶠ[𝓝 0]
      (fun u ↦ LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N (u, ζ u)) := by
    simpa only [Function.comp_def] using hF_germ.comp_tendsto hgraph_tendsto
  refine ⟨ζ, hζ_smooth, hζ_zero, hζ_deriv_zero, ?_⟩
  filter_upwards [hS_invariant, hF_graph] with u hu hFu
  rw [hFu] at *
  exact hu

end LocalInvariantGraph
