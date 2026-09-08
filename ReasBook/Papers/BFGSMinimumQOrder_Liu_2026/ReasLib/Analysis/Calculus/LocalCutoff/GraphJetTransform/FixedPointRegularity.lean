module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform
import all ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform

public section

/-!
# Fixed-point uniqueness for the top graph-jet coefficient

The existing differentiated graph transform contracts its top coefficient once
all lower coefficients agree. This file records the corresponding uniqueness
statement for fixed bounded graph jets.

This is only the contraction/uniqueness part of finite-order fixed-point
regularity. A full `ContDiff` bootstrap still requires both construction of a
fixed top-coefficient section and a holonomicity theorem identifying that
section with the derivative of the lower-order jet.
-/

open scoped NNReal

universe u

namespace LocalCutoff.GraphTransform.JetTransform

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]
variable {radius slope : ℝ≥0}

/-- Two fixed bounded order-`r` graph jets with identical lower coefficients
have zero uniform distance between their top coefficients. -/
theorem coeffDistance_top_eq_zero_of_fixedPoints
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
    (h_lower_coeff : ∀ u (n : Fin (r + 1)), (n : ℕ) < r →
      (J.jet u).coeff n = (K.jet u).coeff n)
    (hJ_fixed :
      map r ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν hrν
        hχ_smooth hχ_support hρ hN_smooth h_center_smooth h_lower_pos h_lower hN_zero
        hL h_stable_bound h_stable_lipschitz h_radius h_slope J = J)
    (hK_fixed :
      map r ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν hrν
        hχ_smooth hχ_support hρ hN_smooth h_center_smooth h_lower_pos h_lower hN_zero
        hL h_stable_bound h_stable_lipschitz h_radius h_slope K = K) :
    coeffDistance ⟨r, Nat.lt_succ_self r⟩ J K = 0 := by
  let q : ℝ≥0 :=
    rate lower linearRate stableCenter stableFiber centerFiber slope * lower⁻¹ ^ r
  have hcontract := topCoeff_contraction r ν χ ρ L N lower linearRate stableBound
    stableCenter stableFiber centerFiber hν hr_pos hrν hχ_smooth hχ_support hρ
    hN_smooth h_center_smooth h_lower_pos h_lower hN_zero hL h_linearRate
    h_stable_bound h_stable_lipschitz h_center_fiber h_radius h_slope h_rate
    h_bunching J K h_lower_coeff
  rw [hJ_fixed, hK_fixed] at hcontract
  have hinputBdd : BddAbove (Set.range fun u ↦
      ‖(J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
        (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩‖) := by
    refine ⟨(J.coeffBound ⟨r, Nat.lt_succ_self r⟩ : ℝ) +
      (K.coeffBound ⟨r, Nat.lt_succ_self r⟩ : ℝ), ?_⟩
    rintro _ ⟨u, rfl⟩
    exact (norm_sub_le _ _).trans (add_le_add
      (J.coeff_le u ⟨r, Nat.lt_succ_self r⟩)
      (K.coeff_le u ⟨r, Nat.lt_succ_self r⟩))
  have hdistance_nonneg :
      0 ≤ coeffDistance ⟨r, Nat.lt_succ_self r⟩ J K := by
    rw [coeffDistance.eq_def]
    exact (norm_nonneg ((J.jet 0).coeff ⟨r, Nat.lt_succ_self r⟩ -
      (K.jet 0).coeff ⟨r, Nat.lt_succ_self r⟩)).trans
        (le_csSup hinputBdd ⟨0, rfl⟩)
  have hq_lt : (q : ℝ) < 1 := by
    exact_mod_cast h_bunching
  change coeffDistance ⟨r, Nat.lt_succ_self r⟩ J K ≤
    (q : ℝ) * coeffDistance ⟨r, Nat.lt_succ_self r⟩ J K at hcontract
  nlinarith

/-- Two fixed bounded order-`r` graph jets with identical lower coefficients
have identical top coefficients at every center parameter. -/
theorem topCoeff_eq_of_fixedPoints
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
    (u : ℝ) :
    (J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ =
      (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ := by
  have hzero := coeffDistance_top_eq_zero_of_fixedPoints r ν χ ρ L N lower
    linearRate stableBound stableCenter stableFiber centerFiber hν hr_pos hrν hχ_smooth
    hχ_support hρ hN_smooth h_center_smooth h_lower_pos h_lower hN_zero hL h_linearRate
    h_stable_bound h_stable_lipschitz h_center_fiber h_radius h_slope h_rate h_bunching
    J K h_lower_coeff hJ_fixed hK_fixed
  have hinputBdd : BddAbove (Set.range fun v ↦
      ‖(J.jet v).coeff ⟨r, Nat.lt_succ_self r⟩ -
        (K.jet v).coeff ⟨r, Nat.lt_succ_self r⟩‖) := by
    refine ⟨(J.coeffBound ⟨r, Nat.lt_succ_self r⟩ : ℝ) +
      (K.coeffBound ⟨r, Nat.lt_succ_self r⟩ : ℝ), ?_⟩
    rintro _ ⟨v, rfl⟩
    exact (norm_sub_le _ _).trans (add_le_add
      (J.coeff_le v ⟨r, Nat.lt_succ_self r⟩)
      (K.coeff_le v ⟨r, Nat.lt_succ_self r⟩))
  have hle :
      ‖(J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
        (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩‖ ≤
          coeffDistance ⟨r, Nat.lt_succ_self r⟩ J K := by
    rw [coeffDistance.eq_def]
    exact le_csSup hinputBdd ⟨u, rfl⟩
  have hnorm :
      ‖(J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ -
        (K.jet u).coeff ⟨r, Nat.lt_succ_self r⟩‖ = 0 := by
    apply le_antisymm
    · exact hle.trans_eq hzero
    · exact norm_nonneg _
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end LocalCutoff.GraphTransform.JetTransform
