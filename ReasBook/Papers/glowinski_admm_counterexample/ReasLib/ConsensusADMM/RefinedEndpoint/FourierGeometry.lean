/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.ScaledCycle
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM.RefinedEndpoint

noncomputable section

variable {K : Type*} {N : ℕ}

/-- Multiplication by one complex unit is a real orthogonal map. -/
def unitRotation (c : ℂ) (hc : ‖c‖ = 1) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  let hc0 : c ≠ 0 := by
    intro hz
    simp [hz] at hc
  { toLinearEquiv :=
      (LinearEquiv.smulOfUnit (R := ℂ) (M := ℂ) (Units.mk0 c hc0)).restrictScalars ℝ
    norm_map' := fun z ↦ by
      change ‖c * z‖ = ‖z‖
      rw [norm_mul, hc, one_mul] }

@[simp]
theorem unitRotation_apply (c : ℂ) (hc : ‖c‖ = 1) (z : ℂ) :
    unitRotation c hc z = c * z := rfl

/-- Independent plane rotations act orthogonally on the stacked real and
imaginary Fourier coordinates. -/
def blockRotation [Fintype K] (c : K → ℂ) (hc : ∀ h, ‖c h‖ = 1) :
    EuclideanSpace ℂ K ≃ₗᵢ[ℝ] EuclideanSpace ℂ K :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun h ↦ unitRotation (c h) (hc h))

@[simp]
theorem blockRotation_apply [Fintype K] (c : K → ℂ) (hc : ∀ h, ‖c h‖ = 1)
    (x : EuclideanSpace ℂ K) (h : K) :
    blockRotation c hc x h = c h * x h := rfl

/-- Fourier coordinates with arbitrary complex amplitudes. The paper's
normalization `sqrt(m_j/N)` is absorbed into each amplitude. -/
def fourierFamily (χ : K → ZMod N → ℂ) (a : K → ℂ) :
    ZMod N → EuclideanSpace ℂ K :=
  fun i ↦ WithLp.toLp 2 (fun h ↦ χ h i * a h)

@[simp]
theorem fourierFamily_apply (χ : K → ZMod N → ℂ) (a : K → ℂ)
    (i : ZMod N) (h : K) : fourierFamily χ a i h = χ h i * a h := rfl

/-- The same diagonal plane rotation advances both Fourier families whenever
their phase factors obey the cyclic successor law. -/
theorem fourierFamily_hasOrthogonalCyclicSymmetry [Fintype K]
    (χ : K → ZMod N → ℂ) (hunit : ∀ h, ‖χ h 1‖ = 1)
    (hphase : ∀ h i, χ h (i + 1) = χ h 1 * χ h i)
    (a b : K → ℂ) :
    ProjectionCycle.HasOrthogonalCyclicSymmetry (fourierFamily χ a) (fourierFamily χ b) := by
  refine ⟨blockRotation (fun h ↦ χ h 1) hunit, fun i ↦ ⟨?_, ?_⟩⟩
  · ext h
    simp only [blockRotation_apply, fourierFamily_apply, hphase, mul_assoc]
  · ext h
    simp only [blockRotation_apply, fourierFamily_apply, hphase, mul_assoc]

/-- The real inner products used by the numerical Gram certificate are the
real parts of the corresponding finite complex products, with the conjugate
on the first argument. -/
theorem fourierFamily_inner [Fintype K] (χ : K → ZMod N → ℂ) (a b : K → ℂ)
    (i j : ZMod N) :
    inner ℝ (fourierFamily χ a i) (fourierFamily χ b j) =
      ∑ h, ((χ h j * b h) * star (χ h i * a h)).re := by
  simp only [PiLp.inner_apply, Complex.inner, fourierFamily]
  rfl

/-- The squared residual has the direct nonnegative sum-of-squares Fourier
representation. This formula keeps square roots out of later Gram checks. -/
theorem fourier_displacement_norm_sq [Fintype K] (χ : K → ZMod N → ℂ) (a : K → ℂ)
    (i : ZMod N) :
    ‖displacement (fourierFamily χ a) i‖ ^ 2 =
      ∑ h, ‖(χ h i - χ h (i - 1)) * a h‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro h _
  simp only [displacement, WithLp.ofLp_sub, fourierFamily, Pi.sub_apply, sub_mul]

/-- Stacking any two Fourier families produces a real positive-semidefinite
Gram matrix by construction, rather than by a numerical eigenvalue test. -/
theorem fourier_gram_posSemidef [Fintype K] [NeZero N]
    (χ : K → ZMod N → ℂ) (a b : K → ℂ) :
    (Matrix.gram ℝ (fun p : Fin 2 × ZMod N ↦
      if p.1 = 0 then fourierFamily χ a p.2 else fourierFamily χ b p.2)).PosSemidef := by
  exact Matrix.posSemidef_gram ℝ _

/-- Derive the strict endpoint conclusion from the Fourier representation and
strict phase-zero support data. `Certificate.UpperBound` supplies the concrete
checked root enclosures and support data. -/
theorem endpoint_lt_of_fourier_phase_zero [Fintype K] [NeZero N] (γ : ℝ)
    (χ : K → ZMod N → ℂ) (a b : K → ℂ)
    (hN : 2 ≤ N) (hγ : 0 < γ) (hγtwo : γ < 2)
    (hunit : ∀ h, ‖χ h 1‖ = 1)
    (hphase : ∀ h i, χ h (i + 1) = χ h 1 * χ h i)
    (hfirst : ZeroPhaseStrictSupports (imageVertex (fourierFamily χ a) (fourierFamily χ b))
      (firstSupportNormal γ (fourierFamily χ a) (fourierFamily χ b)))
    (hsecond : ZeroPhaseStrictSupports (fourierFamily χ a)
      (secondSupportNormal γ (fourierFamily χ b)))
    (hresidual : 0 < ‖displacement (fourierFamily χ b) 0‖ ^ 2) :
    ADMM.uniformConvergenceEndpoint < γ := by
  exact endpoint_lt_of_scaled_zeroPhase γ _ _ hN hγ hγtwo
    (fourierFamily_hasOrthogonalCyclicSymmetry χ hunit hphase a b) hfirst hsecond hresidual

end

end ConsensusADMM.RefinedEndpoint
