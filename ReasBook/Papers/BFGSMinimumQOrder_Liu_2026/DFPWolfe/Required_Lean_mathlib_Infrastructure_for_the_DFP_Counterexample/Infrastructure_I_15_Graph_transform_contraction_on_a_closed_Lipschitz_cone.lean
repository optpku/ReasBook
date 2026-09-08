module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphTransform
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

public section

open scoped NNReal

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable {radius slope : ℝ≥0}
variable (ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
  (N : ℝ × X → ℝ × X)
  (lower linearRate stableBound stableCenter stableFiber centerFiber : ℝ≥0)
  (hν : 2 ≤ ν)
  (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
    ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
  (h_lower_pos : 0 < lower)
  (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
    (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
  (hN_zero : N 0 = 0)
  (hL : ‖L‖ ≤ (linearRate : ℝ))
  (h_linearRate : linearRate < 1)
  (h_stable_bound : ∀ p : ℝ × X,
    ‖(LocalCutoff.remainder χ ρ N p).2‖ ≤ (stableBound : ℝ))
  (h_stable_lipschitz : ∀ u v : ℝ, ∀ z w : X,
    ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
        (LocalCutoff.remainder χ ρ N (v, w)).2‖ ≤
      (stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖z - w‖)
  (h_center_fiber : ∀ u : ℝ, ∀ z w : X,
    |(LocalCutoff.remainder χ ρ N (u, z)).1 -
        (LocalCutoff.remainder χ ρ N (u, w)).1| ≤
      (centerFiber : ℝ) * ‖z - w‖)
  (h_radius : linearRate * radius + stableBound ≤ radius)
  (h_slope : (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ ≤ slope)
  (h_rate : LocalCutoff.GraphTransform.rate lower linearRate stableCenter stableFiber
    centerFiber slope < 1)

/- Infrastructure I.15 (Graph-transform contraction on a closed Lipschitz cone) (1): the
inverse-center formula defines a concrete self-map of the closed cone of small Lipschitz graphs. -/
#check (LocalCutoff.GraphTransform.map ν χ ρ L N lower linearRate stableBound stableCenter
  stableFiber hν h_center_smooth h_lower_pos h_lower hN_zero hL h_stable_bound
  h_stable_lipschitz h_radius h_slope :
    SmallLipschitzGraph X radius slope → SmallLipschitzGraph X radius slope)

/- Infrastructure I.15 (Graph-transform contraction on a closed Lipschitz cone) (2): the
graph transform vanishes at zero and obeys the prescribed radius and Lipschitz bounds. -/
#check (LocalCutoff.GraphTransform.map_spec ν χ ρ L N lower linearRate stableBound stableCenter
  stableFiber hν h_center_smooth h_lower_pos h_lower hN_zero hL h_stable_bound
  h_stable_lipschitz h_radius h_slope :
    ∀ ζ : SmallLipschitzGraph X radius slope,
      let T := LocalCutoff.GraphTransform.map ν χ ρ L N lower linearRate stableBound
        stableCenter stableFiber hν h_center_smooth h_lower_pos h_lower hN_zero hL
        h_stable_bound h_stable_lipschitz h_radius h_slope ζ
      T 0 = 0 ∧ ‖(T : BoundedContinuousFunction ℝ X)‖ ≤ (radius : ℝ) ∧
        LipschitzWith slope T)

/- Infrastructure I.15 (Graph-transform contraction on a closed Lipschitz cone) (3): under
the center-fiber estimate and the explicit strict-rate inequality, the graph transform is a
`ContractingWith` self-map of the complete cone. -/
#check (LocalCutoff.GraphTransform.contractingWith ν χ ρ L N lower linearRate stableBound
  stableCenter stableFiber centerFiber hν h_center_smooth h_lower_pos h_lower hN_zero hL
  h_linearRate h_stable_bound h_stable_lipschitz h_center_fiber h_radius h_slope h_rate :
    ContractingWith
      (LocalCutoff.GraphTransform.rate lower linearRate stableCenter stableFiber centerFiber slope)
      (LocalCutoff.GraphTransform.map ν χ ρ L N lower linearRate stableBound stableCenter
        stableFiber hν h_center_smooth h_lower_pos h_lower hN_zero hL h_stable_bound
        h_stable_lipschitz h_radius h_slope))
