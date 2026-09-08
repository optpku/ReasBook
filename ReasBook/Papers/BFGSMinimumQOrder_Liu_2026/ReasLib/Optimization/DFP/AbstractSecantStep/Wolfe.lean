module

public import ReasLib.Optimization.DFP.AbstractSecantStep.Curvature
public import ReasLib.Optimization.LineSearch.Wolfe

public section

/-!
# Wolfe curvature for abstract DFP secant steps
-/

noncomputable section

open scoped Matrix

namespace DFP.AbstractSecantStep

/-- The initial directional slope of an abstract secant step. -/
def slope {n : Type u} [Fintype n] (z : AbstractSecantStep n) : ℝ :=
  z.gradient ⬝ᵥ z.displacement

/-- The next directional slope of an abstract secant step. -/
def nextSlope {n : Type u} [Fintype n] (z : AbstractSecantStep n) : ℝ :=
  z.nextGradient ⬝ᵥ z.displacement

/-- The initial slope is the gradient-displacement pairing. -/
theorem slope_def {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.slope = z.gradient ⬝ᵥ z.displacement := by
  rfl

/-- The next slope is the next-gradient-displacement pairing. -/
theorem nextSlope_def {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.nextSlope = z.nextGradient ⬝ᵥ z.displacement := by
  rfl

/-- The next slope is the initial slope plus the secant curvature. -/
theorem nextSlope_eq_add_secantCurvature {n : Type u} [Fintype n]
    (z : AbstractSecantStep n) :
    z.nextSlope = z.slope + z.secantCurvature := by
  rw [nextSlope_def, slope_def]
  rw [z.secantCurvature_def]
  exact z.nextGradient_pairing_eq_add_secantCurvature

/-- The initial slope is the negative predicted decrease. -/
theorem slope_eq_neg_predictedDecrease {n : Type u} [Fintype n]
    (z : AbstractSecantStep n) : z.slope = -z.predictedDecrease := by
  rw [slope, z.predictedDecrease_def]
  ring

/-- The next slope is `(1 - τ)` times the initial slope. -/
theorem nextSlope_eq {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.nextSlope = (1 - z.tau) * z.slope := by
  rw [nextSlope,
    z.nextGradient_pairing_eq,
    z.slope_eq_neg_predictedDecrease]
  ring

/-- An absolute bound on `1 - τ` gives the strong-Wolfe scalar curvature condition. -/
theorem strongCurvature {n : Type u} [Fintype n] (z : AbstractSecantStep n) {c₂ : ℝ}
    (h : |1 - z.tau| ≤ c₂) :
    LineSearch.Wolfe.IsStrongCurvature c₂ z.slope z.nextSlope := by
  exact LineSearch.Wolfe.IsStrongCurvature.of_eq_mul z.nextSlope_eq h

/-- A lower bound on `τ` gives the weak-Wolfe scalar curvature condition. -/
theorem weakCurvature {n : Type u} [Fintype n] (z : AbstractSecantStep n) {c₂ : ℝ}
    (h : 1 - c₂ ≤ z.tau) :
    LineSearch.Wolfe.IsWeakCurvature c₂ z.slope z.nextSlope := by
  apply LineSearch.Wolfe.isWeakCurvature_iff.mpr
  exact z.weakCurvature_of_tau_lower_bound h

end DFP.AbstractSecantStep
