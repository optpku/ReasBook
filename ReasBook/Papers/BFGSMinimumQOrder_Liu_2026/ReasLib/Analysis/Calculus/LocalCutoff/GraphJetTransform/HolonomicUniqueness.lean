module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.FixedPointRegularity
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetRealization

public section

open scoped NNReal

universe u

namespace LocalCutoff.GraphTransform.JetTransform

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]
variable {radius slope : ℝ≥0}

/-!
This module separates the coefficient-contraction argument from the final
holonomicity argument.  The latter only needs the canonical coefficient
formula for a holonomic jet and a nonzero factorial scalar.
-/

/-- Helper for Infrastructure I.16 (finite-order graph-jet contraction): two
holonomic fixed graph jets with the same lower coefficients have the same
`r`-th iterated derivative of their graph components. -/
theorem iteratedFDeriv_eq_of_holonomic_fixedPoints
    (r ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ)
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
    (h_lower_coeff : ∀ v (n : Fin (r + 1)), (n : ℕ) < r →
      (J.jet v).coeff n = (K.jet v).coeff n)
    (hJ_fixed :
      map r ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν hrν
        hχ_smooth hχ_support hρ hN_smooth h_center_smooth h_lower_pos h_lower hN_zero
        hL h_stable_bound h_stable_lipschitz h_radius h_slope J = J)
    (hK_fixed :
      map r ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν hrν
        hχ_smooth hχ_support hρ hN_smooth h_center_smooth h_lower_pos h_lower hN_zero
        hL h_stable_bound h_stable_lipschitz h_radius h_slope K = K)
    (hJ_holonomic : LocalCutoff.GraphTransform.IsHolonomic r J)
    (hK_holonomic : LocalCutoff.GraphTransform.IsHolonomic r K)
    (u : ℝ) :
    iteratedFDeriv ℝ r (J.graph : ℝ → X) u =
      iteratedFDeriv ℝ r (K.graph : ℝ → X) u := by
  have htop := topCoeff_eq_of_fixedPoints r ν χ ρ L N lower linearRate stableBound
    stableCenter stableFiber centerFiber hν hr_pos hrν hχ_smooth hχ_support hρ
    hN_smooth h_center_smooth h_lower_pos h_lower hN_zero hL h_linearRate
    h_stable_bound h_stable_lipschitz h_center_fiber h_radius h_slope h_rate h_bunching
    J K h_lower_coeff hJ_fixed hK_fixed u
  have hJ_top := LocalCutoff.GraphTransform.holonomic_topCoeff_eq_iteratedFDeriv
    r J hJ_holonomic u
  have hK_top := LocalCutoff.GraphTransform.holonomic_topCoeff_eq_iteratedFDeriv
    r K hK_holonomic u
  have hscaled := congrArg
    (fun A ↦ ((r.factorial : ℕ) : ℝ) • A) htop
  rw [hJ_top, hK_top] at hscaled
  have hfactorial : ((r.factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero r)
  simpa [smul_smul, hfactorial] using hscaled

end LocalCutoff.GraphTransform.JetTransform
