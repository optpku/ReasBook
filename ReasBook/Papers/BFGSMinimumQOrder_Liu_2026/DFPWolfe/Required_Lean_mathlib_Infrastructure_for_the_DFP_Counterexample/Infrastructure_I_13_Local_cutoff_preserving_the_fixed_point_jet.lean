module

public import ReasLib.Analysis.Calculus.ContDiff.SupportBounds
public import ReasLib.Analysis.Calculus.LocalCutoff.CenterStable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

public section

noncomputable section

open Filter Set
open scoped Topology

universe u uE uF

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]

/- Infrastructure I.13 (Local cutoff preserving the fixed-point jet)
The rescaled plateau cutoff modifies only the nonlinear remainder while retaining the
original map near zero, its finite jet at zero, and the linear map outside the cutoff.
-/
#check (LocalCutoff.linearize :
  (X → ℝ) → ℝ → (X →L[ℝ] X) → (X → X) → X → X)

#check (LocalCutoff.remainder :
  (E → ℝ) → ℝ → (E → F) → E → F)

#check (LocalCutoff.remainder_apply :
  ∀ (χ : E → ℝ) (ρ : ℝ) (N : E → F) (x : E),
    LocalCutoff.remainder χ ρ N x = χ (ρ⁻¹ • x) • N x)

#check (LocalCutoff.linearize_apply :
  ∀ (χ : E → ℝ) (ρ : ℝ) (A : E →L[ℝ] F) (N : E → F) (x : E),
    LocalCutoff.linearize χ ρ A N x = A x + χ (ρ⁻¹ • x) • N x)

#check (LocalCutoff.linearize_eq_add_of_mem_closedBall :
  ∀ (χ : E → ℝ) (ρ rIn : ℝ) (A : E →L[ℝ] F) (N : E → F),
    0 < ρ →
    (∀ y ∈ Metric.closedBall (0 : E) rIn, χ y = 1) →
    ∀ {x : E}, x ∈ Metric.closedBall 0 (ρ * rIn) →
      LocalCutoff.linearize χ ρ A N x = A x + N x)

#check (LocalCutoff.linearize_eq_linear_of_outer_radius_le_norm :
  ∀ (χ : E → ℝ) (ρ rOut : ℝ) (A : E →L[ℝ] F) (N : E → F),
    0 < ρ →
    (∀ y, rOut ≤ ‖y‖ → χ y = 0) →
    ∀ {x : E}, ρ * rOut ≤ ‖x‖ → LocalCutoff.linearize χ ρ A N x = A x)

#check (LocalCutoff.linearize_eventuallyEq :
  ∀ (χ : E → ℝ) (ρ : ℝ) (A : E →L[ℝ] F) (N : E → F),
    χ =ᶠ[𝓝 0] 1 →
    LocalCutoff.linearize χ ρ A N =ᶠ[𝓝 0] fun x ↦ A x + N x)

#check (LocalCutoff.iteratedFDeriv_linearize_zero :
  ∀ (χ : E → ℝ) (ρ : ℝ) (A : E →L[ℝ] F) (N : E → F),
    χ =ᶠ[𝓝 0] 1 → ∀ n : ℕ,
    iteratedFDeriv ℝ n (LocalCutoff.linearize χ ρ A N) 0 =
      iteratedFDeriv ℝ n (fun x ↦ A x + N x) 0)

#check (LocalCutoff.linearize_zero :
  ∀ (χ : E → ℝ) (ρ : ℝ) (A : E →L[ℝ] F) (N : E → F),
    N 0 = 0 → LocalCutoff.linearize χ ρ A N 0 = 0)

#check (LocalCutoff.fderiv_linearize_zero :
  ∀ (χ : E → ℝ) (ρ : ℝ) (A : E →L[ℝ] F) (N : E → F),
    DifferentiableAt ℝ (fun x ↦ χ (ρ⁻¹ • x)) 0 →
    DifferentiableAt ℝ N 0 → N 0 = 0 → fderiv ℝ N 0 = 0 →
    fderiv ℝ (LocalCutoff.linearize χ ρ A N) 0 = A)

#check (LocalCutoff.contDiff_linearize :
  ∀ (ν : ℕ) (χ : E → ℝ) (ρ : ℝ) (A : E →L[ℝ] F) (N : E → F)
    (U : Set E), IsOpen U → U ∈ 𝓝 0 →
    ContDiff ℝ ν (fun x ↦ χ (ρ⁻¹ • x)) → ContDiffOn ℝ ν N U →
    tsupport (fun x ↦ χ (ρ⁻¹ • x)) ⊆ U →
    ContDiff ℝ ν (LocalCutoff.linearize χ ρ A N))

#check (LocalCutoff.exists_scale_norm_fderiv_remainder_le :
  ∀ (χ : E → ℝ) (N : E → F) (U : Set E),
    IsOpen U → U ∈ 𝓝 0 → ContDiff ℝ 1 χ → HasCompactSupport χ →
    ContDiffOn ℝ 1 N U → N 0 = 0 → fderiv ℝ N 0 = 0 →
    (∀ η : ℝ, 0 < η → ∃ δ > 0, ∀ x, ‖x‖ < δ → ‖N x‖ ≤ η * ‖x‖) →
    (∀ η : ℝ, 0 < η → ∃ δ > 0, ∀ x, ‖x‖ < δ → ‖fderiv ℝ N x‖ ≤ η) →
    ∀ {ε : ℝ}, 0 < ε →
    ∃ δ > 0, ∀ ρ, 0 < ρ → ρ < δ → ∀ x,
      ‖fderiv ℝ (LocalCutoff.remainder χ ρ N) x‖ ≤ ε)

#check (LocalCutoff.hasCompactSupport_remainder :
  ∀ (χ : E → ℝ) (ρ : ℝ) (N : E → F),
    ρ ≠ 0 → HasCompactSupport χ → HasCompactSupport (LocalCutoff.remainder χ ρ N))

#check (LocalCutoff.centerStable :
  (X →L[ℝ] X) → ℝ × X →L[ℝ] ℝ × X)

#check (LocalCutoff.centerStableLinearize :
  (ℝ × X → ℝ) → ℝ → (X →L[ℝ] X) →
    (ℝ × X → ℝ × X) → ℝ × X → ℝ × X)

#check (LocalCutoff.centerStable_apply :
  ∀ (L : X →L[ℝ] X) (u : ℝ) (z : X),
    LocalCutoff.centerStable L (u, z) = (u, L z))

#check (LocalCutoff.centerStableLinearize_apply :
  ∀ (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (x : ℝ × X),
    LocalCutoff.centerStableLinearize χ ρ L N x =
      LocalCutoff.centerStable L x + χ (ρ⁻¹ • x) • N x)

#check (LocalCutoff.centerStableLinearize_eventuallyEq :
  ∀ (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X), χ =ᶠ[𝓝 0] 1 →
    LocalCutoff.centerStableLinearize χ ρ L N =ᶠ[𝓝 0]
      fun x ↦ LocalCutoff.centerStable L x + N x)

#check (LocalCutoff.centerStableLinearize_eq_linear :
  ∀ (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) {x : ℝ × X},
    x ∉ tsupport (fun y ↦ χ (ρ⁻¹ • y)) →
    LocalCutoff.centerStableLinearize χ ρ L N x = LocalCutoff.centerStable L x)

#check (HasCompactSupport.exists_norm_iteratedFDeriv_le :
  ∀ {f : E → F} {n : ℕ}, HasCompactSupport f → ContDiff ℝ n f →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C)
