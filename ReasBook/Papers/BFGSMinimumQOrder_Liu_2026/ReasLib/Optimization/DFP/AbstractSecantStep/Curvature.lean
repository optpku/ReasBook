module

public import ReasLib.Optimization.DFP.AbstractSecantStep.Identities

public section

open scoped Matrix

namespace DFP.AbstractSecantStep

/-- The next-gradient pairing equals the initial-gradient pairing plus the
secant curvature. -/
theorem nextGradient_pairing_eq_add_secantCurvature
    {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.nextGradient ⬝ᵥ z.displacement =
      z.gradient ⬝ᵥ z.displacement + z.displacement ⬝ᵥ z.gradientChange := by
  rw [z.nextGradient_def, add_dotProduct, z.gradientChange_def]
  rw [dotProduct_comm z.gradient z.displacement]
  rw [dotProduct_comm (z.secantMatrix *ᵥ z.displacement) z.displacement]

/-- The next-gradient pairing of an abstract secant step is
`-(1 - τ)` times its predicted decrease. -/
theorem nextGradient_pairing_eq
    {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.nextGradient ⬝ᵥ z.displacement =
      -(1 - z.tau) * z.predictedDecrease := by
  rw [z.nextGradient_def, add_dotProduct]
  have hcurvature : z.gradientChange ⬝ᵥ z.displacement = z.secantCurvature := by
    rw [z.secantCurvature_def, dotProduct_comm]
  have hpairing : z.gradient ⬝ᵥ z.displacement = -z.predictedDecrease := by
    rw [z.predictedDecrease_def]
    ring
  rw [hcurvature, z.secantCurvature_eq_tau_mul_predictedDecrease, hpairing]
  ring

/-- A lower bound `1 - c₂ ≤ τ` gives the weak-curvature inequality for an
abstract secant step. -/
theorem weakCurvature_of_tau_lower_bound
    {n : Type u} [Fintype n] (z : AbstractSecantStep n) {c₂ : ℝ}
    (h_tau : 1 - c₂ ≤ z.tau) :
    c₂ * (z.gradient ⬝ᵥ z.displacement) ≤
      z.nextGradient ⬝ᵥ z.displacement := by
  have hq : 0 ≤ z.predictedDecrease := z.predictedDecrease_pos.le
  have hcoeff : -c₂ ≤ z.tau - 1 := by
    linarith
  have hscaled : (-c₂) * z.predictedDecrease ≤
      (z.tau - 1) * z.predictedDecrease :=
    mul_le_mul_of_nonneg_right hcoeff hq
  have hleft : c₂ * (z.gradient ⬝ᵥ z.displacement) =
      (-c₂) * z.predictedDecrease := by
    rw [z.predictedDecrease_def]
    ring
  have hright : (-(1 - z.tau)) * z.predictedDecrease =
      (z.tau - 1) * z.predictedDecrease := by
    ring
  rw [nextGradient_pairing_eq]
  rw [hleft, hright]
  exact hscaled

end DFP.AbstractSecantStep
