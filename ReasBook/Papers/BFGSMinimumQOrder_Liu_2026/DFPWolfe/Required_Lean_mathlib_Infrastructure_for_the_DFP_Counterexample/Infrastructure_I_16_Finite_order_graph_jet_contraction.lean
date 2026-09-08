module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform

public section

open scoped NNReal

universe u

namespace LocalCutoff.GraphTransform

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable {radius slope : ℝ≥0}

/- Infrastructure I.16 (Finite-order graph-jet contraction) (1): at each fixed order
`1 ≤ r ≤ ν`, the concrete differentiated transform on bounded graph jets contracts
the top coefficient, when the lower coefficients agree, by the bunching factor
`rate lower linearRate stableCenter stableFiber centerFiber slope * lower⁻¹ ^ r`. -/
#check (LocalCutoff.GraphTransform.JetTransform.topCoeff_contraction :
  ∀ (r ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ)
    (L : X →L[ℝ] X) (N : ℝ × X → ℝ × X)
    (lower linearRate stableBound stableCenter stableFiber centerFiber : ℝ≥0)
    (hν : 2 ≤ ν) (hr_pos : 1 ≤ r) (hrν : r ≤ ν)
    (hχ_smooth : ContDiff ℝ ν χ) (hχ_support : HasCompactSupport χ)
    (hρ : ρ ≠ 0) (hN_smooth : ContDiff ℝ ν N)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hN_zero : N 0 = 0) (hL : ‖L‖ ≤ (linearRate : ℝ))
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
    (h_rate : rate lower linearRate stableCenter stableFiber centerFiber slope < 1)
    (h_bunching : rate lower linearRate stableCenter stableFiber centerFiber slope *
      lower⁻¹ ^ r < 1)
    (J K : BoundedGraphJet X radius slope r)
    (h_lower_coeff : ∀ u (n : Fin (r + 1)), (n : ℕ) < r →
      (J.jet u).coeff n = (K.jet u).coeff n),
    JetTransform.coeffDistance ⟨r, Nat.lt_succ_self r⟩
      (JetTransform.map r ν χ ρ L N lower linearRate stableBound stableCenter stableFiber
        hν hrν hχ_smooth hχ_support hρ hN_smooth h_center_smooth h_lower_pos h_lower
        hN_zero hL h_stable_bound h_stable_lipschitz h_radius h_slope J)
      (JetTransform.map r ν χ ρ L N lower linearRate stableBound stableCenter stableFiber
        hν hrν hχ_smooth hχ_support hρ hN_smooth h_center_smooth h_lower_pos h_lower
        hN_zero hL h_stable_bound h_stable_lipschitz h_radius h_slope K) ≤
      (rate lower linearRate stableCenter stableFiber centerFiber slope * lower⁻¹ ^ r : ℝ≥0) *
        JetTransform.coeffDistance ⟨r, Nat.lt_succ_self r⟩ J K)

/- Infrastructure I.16 (Finite-order graph-jet contraction) (2): at a fixed order
`1 ≤ r ≤ ν`, finite-order bunching upgrades a `C^(r - 1)` fixed graph of the
concrete cutoff graph transform to a `C^r` graph, using the differentiated jet
contraction above for the top-order coefficient. -/
#check (LocalCutoff.GraphTransform.contDiff_succ_of_fixedPoint :
  ∀ (r ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ)
    (L : X →L[ℝ] X) (N : ℝ × X → ℝ × X)
    (lower linearRate stableBound stableCenter stableFiber centerFiber : ℝ≥0)
    (hν : 2 ≤ ν) (hr_pos : 1 ≤ r) (hrν : r ≤ ν)
    (hχ_smooth : ContDiff ℝ ν χ) (hχ_support : HasCompactSupport χ)
    (hρ : ρ ≠ 0) (hN_smooth : ContDiff ℝ ν N)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hN_zero : N 0 = 0) (hL : ‖L‖ ≤ (linearRate : ℝ))
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
    (h_rate : rate lower linearRate stableCenter stableFiber centerFiber slope < 1)
    (h_bunching : rate lower linearRate stableCenter stableFiber centerFiber slope *
      lower⁻¹ ^ r < 1)
    (ζ : SmallLipschitzGraph X radius slope) (hζ_prev : ContDiff ℝ (r - 1) ζ)
    (hζ_fixed : map ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν
      h_center_smooth h_lower_pos h_lower hN_zero hL h_stable_bound h_stable_lipschitz
      h_radius h_slope ζ = ζ),
    ContDiff ℝ r ζ)

/- Infrastructure I.16 (Finite-order graph-jet contraction) (3): if the cutoff has been
shrunk so that the bunching inequality holds at every order through `ν`, then the
Lipschitz fixed graph of the concrete graph transform is `C^ν`. -/
#check (LocalCutoff.GraphTransform.fixedPoint_contDiff :
  ∀ (ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X)
    (lower linearRate stableBound stableCenter stableFiber centerFiber : ℝ≥0)
    (hν : 2 ≤ ν) (hχ_smooth : ContDiff ℝ ν χ) (hχ_support : HasCompactSupport χ)
    (hρ : ρ ≠ 0) (hN_smooth : ContDiff ℝ ν N)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hN_zero : N 0 = 0) (hL : ‖L‖ ≤ (linearRate : ℝ))
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
    (h_rate : rate lower linearRate stableCenter stableFiber centerFiber slope < 1)
    (h_bunching : ∀ r, 1 ≤ r → r ≤ ν →
      rate lower linearRate stableCenter stableFiber centerFiber slope * lower⁻¹ ^ r < 1)
    (ζ : SmallLipschitzGraph X radius slope)
    (hζ_fixed : map ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν
      h_center_smooth h_lower_pos h_lower hN_zero hL h_stable_bound h_stable_lipschitz
      h_radius h_slope ζ = ζ),
    ContDiff ℝ ν ζ)

end LocalCutoff.GraphTransform
