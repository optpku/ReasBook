module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphTransform.Contraction
public import ReasLib.Topology.ContinuousMap.SmallLipschitzGraph.FixedPoint

public section

open scoped NNReal

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {radius slope : ℝ≥0}

/-!
# Quantitative graph-transform data

The finite-smooth invariant-graph theorem needs a long list of local estimates before the
fixed-point argument can start.  This module gives those estimates a single owner-facing
interface and keeps the fixed-point extraction independent of how the estimates were obtained.
-/

/-- Quantitative hypotheses under which the cutoff graph transform is a strict contraction. -/
structure GraphTransformContractionData where
  ν : ℕ
  χ : ℝ × X → ℝ
  ρ : ℝ
  L : X →L[ℝ] X
  N : ℝ × X → ℝ × X
  lower : ℝ≥0
  linearRate : ℝ≥0
  stableBound : ℝ≥0
  stableCenter : ℝ≥0
  stableFiber : ℝ≥0
  centerFiber : ℝ≥0
  hν : 2 ≤ ν
  hχ_smooth : ContDiff ℝ ν χ
  hχ_support : HasCompactSupport χ
  hρ : ρ ≠ 0
  hN_smooth : ContDiff ℝ ν N
  h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
    ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ)
  h_lower_pos : 0 < lower
  h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
    (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u
  hN_zero : N 0 = 0
  hL : ‖L‖ ≤ (linearRate : ℝ)
  h_linearRate : linearRate < 1
  h_stable_bound : ∀ p : ℝ × X,
    ‖(LocalCutoff.remainder χ ρ N p).2‖ ≤ (stableBound : ℝ)
  h_stable_lipschitz : ∀ u v : ℝ, ∀ z w : X,
    ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
        (LocalCutoff.remainder χ ρ N (v, w)).2‖ ≤
      (stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖z - w‖
  h_center_fiber : ∀ u : ℝ, ∀ z w : X,
    |(LocalCutoff.remainder χ ρ N (u, z)).1 -
        (LocalCutoff.remainder χ ρ N (u, w)).1| ≤
      (centerFiber : ℝ) * ‖z - w‖
  h_radius : linearRate * radius + stableBound ≤ radius
  h_slope : (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ ≤ slope
  h_rate : LocalCutoff.GraphTransform.rate lower linearRate stableCenter stableFiber
    centerFiber slope < 1

/-- The self-map represented by quantitative graph-transform data. -/
noncomputable def GraphTransformContractionData.transform
    (d : GraphTransformContractionData (X := X) (radius := radius) (slope := slope)) :
    SmallLipschitzGraph X radius slope → SmallLipschitzGraph X radius slope :=
  LocalCutoff.GraphTransform.map d.ν d.χ d.ρ d.L d.N d.lower d.linearRate d.stableBound
    d.stableCenter d.stableFiber d.hν d.h_center_smooth d.h_lower_pos d.h_lower d.hN_zero
    d.hL d.h_stable_bound d.h_stable_lipschitz d.h_radius d.h_slope

/-- Expose the concrete formula for the packaged graph-transform map so downstream modules do
not need to unfold an opaque definition across an import boundary. -/
theorem GraphTransformContractionData.transform_apply
    (d : GraphTransformContractionData (X := X) (radius := radius) (slope := slope))
    (ζ : SmallLipschitzGraph X radius slope) :
    d.transform ζ =
      LocalCutoff.GraphTransform.map d.ν d.χ d.ρ d.L d.N d.lower d.linearRate
        d.stableBound d.stableCenter d.stableFiber d.hν d.h_center_smooth
        d.h_lower_pos d.h_lower d.hN_zero d.hL d.h_stable_bound
        d.h_stable_lipschitz d.h_radius d.h_slope ζ := by
  rfl

/-- The packaged transform is contracting with the rate supplied by the data. -/
theorem GraphTransformContractionData.transform_contracting
    (d : GraphTransformContractionData (X := X) (radius := radius) (slope := slope)) :
    ContractingWith
      (LocalCutoff.GraphTransform.rate d.lower d.linearRate d.stableCenter d.stableFiber
        d.centerFiber slope)
      d.transform := by
  dsimp only [GraphTransformContractionData.transform]
  exact LocalCutoff.GraphTransform.contractingWith_of_center_fiber
    d.ν d.χ d.ρ d.L d.N d.lower d.linearRate d.stableBound d.stableCenter d.stableFiber
    d.centerFiber d.hν d.h_center_smooth d.h_lower_pos d.h_lower d.hN_zero d.hL
    d.h_linearRate d.h_stable_bound d.h_stable_lipschitz d.h_center_fiber d.h_radius d.h_slope
    d.h_rate

/-- A complete quantitative data package produces a fixed graph of the cutoff transform. -/
theorem GraphTransformContractionData.exists_fixedGraph
    [CompleteSpace X]
    (d : GraphTransformContractionData (X := X) (radius := radius) (slope := slope)) :
    ∃ ζ : SmallLipschitzGraph X radius slope, d.transform ζ = ζ := by
  let hT := d.transform_contracting
  refine ⟨ContractingWith.fixedPoint d.transform hT, ?_⟩
  exact hT.fixedPoint_isFixedPt

/-- The fixed graph supplied by the contraction package is forward invariant after the
center-coordinate inverse is cancelled. -/
theorem GraphTransformContractionData.fixedGraph_invariant
    (d : GraphTransformContractionData (X := X) (radius := radius) (slope := slope))
    (ζ : SmallLipschitzGraph X radius slope) (hζ : d.transform ζ = ζ) :
    ∀ u : ℝ,
      ζ (LocalCutoff.CenterProjection.map d.χ d.ρ d.L d.N ζ u) =
        (LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N (u, ζ u)).2 := by
  intro u
  have hfixed_apply := congrArg
    (fun η : SmallLipschitzGraph X radius slope ↦ η
      (LocalCutoff.CenterProjection.map d.χ d.ρ d.L d.N ζ u)) hζ
  rw [GraphTransformContractionData.transform, LocalCutoff.GraphTransform.map_apply] at hfixed_apply
  have hone : (1 : ℕ) ≤ 2 := by norm_num
  have hzero_lt_one : (0 : ℕ) < 1 := by norm_num
  have hν_one : 1 ≤ d.ν := hone.trans d.hν
  have hν_ne : d.ν ≠ 0 := Nat.ne_of_gt (hzero_lt_one.trans_le hν_one)
  have hdiff : Differentiable ℝ (LocalCutoff.CenterProjection.map d.χ d.ρ d.L d.N ζ) :=
    (d.h_center_smooth ζ).differentiable (Nat.cast_ne_zero.mpr hν_ne)
  have hbij : Function.Bijective (LocalCutoff.CenterProjection.map d.χ d.ρ d.L d.N ζ) :=
    Real.bijective_of_pos_le_deriv hdiff d.h_lower_pos (d.h_lower ζ)
  have hinverse :
      LocalCutoff.CenterProjection.inverse d.χ d.ρ d.L d.N ζ
          (LocalCutoff.CenterProjection.map d.χ d.ρ d.L d.N ζ u) = u := by
    rw [LocalCutoff.CenterProjection.inverse_def]
    exact Function.leftInverse_invFun hbij.1 u
  rw [hinverse] at hfixed_apply
  exact hfixed_apply.symm

end LocalInvariantGraph
