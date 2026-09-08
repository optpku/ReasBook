module

public import ReasLib.Analysis.Calculus.LocalCutoff
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

public section

noncomputable section

open Filter Set
open scoped Topology

universe u

namespace LocalCutoff

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The block continuous linear map `(u, z) ↦ (u, L z)` on `ℝ × X`. -/
def centerStable (L : X →L[ℝ] X) : ℝ × X →L[ℝ] ℝ × X :=
  (ContinuousLinearMap.id ℝ ℝ).prodMap L

/-- The cutoff perturbation of the center-stable block map. -/
noncomputable def centerStableLinearize (χ : ℝ × X → ℝ) (ρ : ℝ)
    (L : X →L[ℝ] X) (N : ℝ × X → ℝ × X) : ℝ × X → ℝ × X :=
  linearize χ ρ (centerStable L) N

/-- The center-stable block map sends `(u, z)` to `(u, L z)`. -/
theorem centerStable_apply (L : X →L[ℝ] X) (u : ℝ) (z : X) :
    centerStable L (u, z) = (u, L z) := by
  rfl

/-- The center-stable cutoff perturbation evaluates as its block-linear part plus the
rescaled cutoff remainder. -/
theorem centerStableLinearize_apply (χ : ℝ × X → ℝ) (ρ : ℝ)
    (L : X →L[ℝ] X) (N : ℝ × X → ℝ × X) (x : ℝ × X) :
    centerStableLinearize χ ρ L N x =
      centerStable L x + χ (ρ⁻¹ • x) • N x := by
  simpa only [centerStableLinearize] using linearize_apply χ ρ (centerStable L) N x

/-- A cutoff equal to one near zero makes the center-stable cutoff perturbation and the
original nonlinear center-stable map have the same germ at zero. -/
theorem centerStableLinearize_eventuallyEq (χ : ℝ × X → ℝ) (ρ : ℝ)
    (L : X →L[ℝ] X) (N : ℝ × X → ℝ × X) (hχ : χ =ᶠ[𝓝 0] 1) :
    centerStableLinearize χ ρ L N =ᶠ[𝓝 0]
      fun x ↦ centerStable L x + N x := by
  simpa only [centerStableLinearize] using linearize_eventuallyEq χ ρ (centerStable L) N hχ

/-- Outside the topological support of the rescaled cutoff, the center-stable cutoff
perturbation equals its block-linear part. -/
theorem centerStableLinearize_eq_linear (χ : ℝ × X → ℝ) (ρ : ℝ)
    (L : X →L[ℝ] X) (N : ℝ × X → ℝ × X) {x : ℝ × X}
    (hx : x ∉ tsupport fun y ↦ χ (ρ⁻¹ • y)) :
    centerStableLinearize χ ρ L N x = centerStable L x := by
  have hzero : χ (ρ⁻¹ • x) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y ↦ χ (ρ⁻¹ • y)) hx
  rw [centerStableLinearize_apply, hzero, zero_smul, add_zero]

end LocalCutoff
