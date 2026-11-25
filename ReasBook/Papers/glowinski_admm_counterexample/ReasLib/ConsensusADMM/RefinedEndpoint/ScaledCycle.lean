/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.PhaseZero

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM.RefinedEndpoint

universe u

variable {N : ℕ} {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Fixing the scaled multiplier vertices fixes the primal residuals,
independently of the multiplier factor. -/
def displacement (w : ZMod N → E) (i : ZMod N) : E := w i - w (i - 1)

/-- The first-block vertices in the fixed-data parametrization of Appendix C.3. -/
def imageVertex (η w : ZMod N → E) (i : ZMod N) : E := η i + displacement w i

/-- The first normal is affine in the factor with the primal vertices fixed. -/
def firstSupportNormal (γ : ℝ) (η w : ZMod N → E) (i : ZMod N) : E :=
  η (i - 1) - imageVertex η w i - γ • w (i - 1)

/-- The second normal is affine in the factor with the primal vertices fixed. -/
def secondSupportNormal (γ : ℝ) (w : ZMod N → E) (i : ZMod N) : E :=
  displacement w i + γ • w (i - 1)

/-- Scaling every multiplier vertex by the positive factor cancels the
inverse factor in the projection-cycle residual. -/
theorem residual_scaled (γ : ℝ) (hγ : γ ≠ 0) (w : ZMod N → E) (i : ZMod N) :
    ProjectionCycle.residual γ (fun k ↦ γ • w k) i = displacement w i := by
  rw [ProjectionCycle.residual_apply, ← smul_sub, smul_smul,
    inv_mul_cancel₀ hγ, one_smul]
  rfl

/-- Consequently the first-block vertices do not vary with the factor. -/
theorem xVertex_scaled (γ : ℝ) (hγ : γ ≠ 0) (η w : ZMod N → E) (i : ZMod N) :
    ProjectionCycle.xVertex γ η (fun k ↦ γ • w k) i = imageVertex η w i := by
  rw [ProjectionCycle.xVertex_apply, residual_scaled γ hγ]
  rfl

/-- The unscaled first normal agrees with the ordinary projection-cycle normal. -/
theorem firstNormal_scaled (γ : ℝ) (hγ : γ ≠ 0) (η w : ZMod N → E)
    (i : ZMod N) :
    ProjectionCycle.firstNormal γ η (fun k ↦ γ • w k) i =
      firstSupportNormal γ η w i := by
  rw [ProjectionCycle.firstNormal_apply, xVertex_scaled γ hγ]
  dsimp only [firstSupportNormal]
  abel

/-- The unscaled second normal agrees with the ordinary projection-cycle normal. -/
theorem secondNormal_scaled (γ : ℝ) (hγ : γ ≠ 0) (w : ZMod N → E)
    (i : ZMod N) :
    ProjectionCycle.secondNormal γ (fun k ↦ γ • w k) i =
      secondSupportNormal γ w i := by
  rw [ProjectionCycle.secondNormal_apply, residual_scaled γ hγ]
  dsimp only [secondSupportNormal]
  abel

/-- Each fixed first-block comparison has an exact real affine dependence on
the multiplier factor, as used in the strict left-continuation argument. -/
theorem first_support_affine (γ : ℝ) (η w : ZMod N → E)
    (i : ZMod N) (z : E) :
    inner ℝ (firstSupportNormal γ η w i) z =
      inner ℝ (η (i - 1) - imageVertex η w i) z -
        γ * inner ℝ (w (i - 1)) z := by
  simp only [firstSupportNormal, inner_sub_left, real_inner_smul_left]

/-- Each fixed second-block comparison has the corresponding affine dependence. -/
theorem second_support_affine (γ : ℝ) (w : ZMod N → E)
    (i : ZMod N) (z : E) :
    inner ℝ (secondSupportNormal γ w i) z =
      inner ℝ (displacement w i) z + γ * inner ℝ (w (i - 1)) z := by
  simp only [secondSupportNormal, inner_add_left, real_inner_smul_left]

/-- Scaling the multiplier vertices preserves the supplied orthogonal phase shift. -/
theorem scaled_hasOrthogonalCyclicSymmetry (γ : ℝ) (η w : ZMod N → E)
    (symmetry : ProjectionCycle.HasOrthogonalCyclicSymmetry η w) :
    ProjectionCycle.HasOrthogonalCyclicSymmetry η (fun k ↦ γ • w k) := by
  obtain ⟨U, advance⟩ := symmetry
  refine ⟨U, fun i ↦ ⟨(advance i).1, ?_⟩⟩
  rw [U.map_smul, (advance i).2]

/-- Derive the strict endpoint bound from two strict phase-zero support lists
and a positive residual. The concrete Fourier data supply these parameters in
`Certificate.UpperBound`. -/
theorem endpoint_lt_of_scaled_zeroPhase [NeZero N] (γ : ℝ) (η w : ZMod N → E)
    (hN : 2 ≤ N) (hγ : 0 < γ) (hγtwo : γ < 2)
    (symmetry : ProjectionCycle.HasOrthogonalCyclicSymmetry η w)
    (hfirst : ZeroPhaseStrictSupports (imageVertex η w) (firstSupportNormal γ η w))
    (hsecond : ZeroPhaseStrictSupports η (secondSupportNormal γ w))
    (hresidual : 0 < ‖displacement w 0‖ ^ 2) :
    ADMM.uniformConvergenceEndpoint < γ := by
  apply endpoint_lt_of_zeroPhase γ η (fun k ↦ γ • w k) hN hγ hγtwo
    (scaled_hasOrthogonalCyclicSymmetry γ η w symmetry)
  · simpa only [ZeroPhaseStrictSupports, xVertex_scaled γ hγ.ne',
      firstNormal_scaled γ hγ.ne'] using hfirst
  · simpa only [ZeroPhaseStrictSupports, secondNormal_scaled γ hγ.ne'] using hsecond
  · simpa only [residual_scaled γ hγ.ne'] using hresidual

end ConsensusADMM.RefinedEndpoint
