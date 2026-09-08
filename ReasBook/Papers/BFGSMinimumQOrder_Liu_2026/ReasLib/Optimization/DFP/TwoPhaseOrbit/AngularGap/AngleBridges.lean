module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Tactic

public section

namespace DFP.TwoPhaseOrbit.AngularGap

/-- Helper for the angular-gap cast bridge: subtracting the canonical real
representatives of two angles and re-embedding gives their angle subtraction. -/
theorem coe_toReal_sub_eq_sub
    (θ ψ : Real.Angle) :
    ((θ.toReal - ψ.toReal : ℝ) : Real.Angle) = θ - ψ := by
  rw [Real.Angle.coe_sub, Real.Angle.coe_toReal θ, Real.Angle.coe_toReal ψ]

/-- Helper for the angular-gap cast bridge: the absolute real representative
is unchanged by choosing either of the two subtraction presentations. -/
theorem abs_toReal_coe_sub_eq_abs_toReal_sub
    (θ ψ : Real.Angle) :
    |((θ.toReal - ψ.toReal : ℝ) : Real.Angle).toReal| =
      |(θ - ψ).toReal| := by
  rw [coe_toReal_sub_eq_sub]

/-- Helper for the signed angular-gap bridge: a lift difference determines the
absolute value of the oppositely oriented principal angle difference. -/
theorem abs_sub_toReal_eq_abs_neg_sub_of_lift_sub
    {θ₁ θ₂ : Real.Angle} {L₁ L₂ : ℝ}
    (hsub : L₂ - L₁ = (θ₂ - θ₁).toReal) :
    |(θ₁ - θ₂).toReal| = |-(L₁ - L₂)| := by
  calc
    |(θ₁ - θ₂).toReal| = |(θ₂ - θ₁).toReal| := by
      rw [show θ₁ - θ₂ = -(θ₂ - θ₁) by abel, Real.Angle.abs_toReal_neg]
    _ = |L₂ - L₁| := by rw [hsub]
    _ = |-(L₁ - L₂)| := by
      congr 1
      ring

end DFP.TwoPhaseOrbit.AngularGap
