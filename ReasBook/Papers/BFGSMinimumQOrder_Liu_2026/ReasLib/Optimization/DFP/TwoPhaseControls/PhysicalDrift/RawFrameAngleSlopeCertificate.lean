module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawFrameAngleGermAdapter

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-- Infrastructure I.16a: a factorization certificate for the raw relative-frame
    tangent records the smooth coefficient that remains after removing one radius
    factor from `mixedIndependentRawFrameAngleSlopeAlongInput`. -/
structure MixedIndependentRawFrameAngleSlopeFactorCertificate
    (K : Set (ℝ × ℝ × ℝ)) where
  factor : (ℝ × ℝ × ℝ) → ℝ → ℝ
  factor_regular : ∀ θ, θ ∈ K →
    ContDiffAt ℝ 2 (Function.uncurry factor) (θ, 0)
  factor_zero : ∀ θ, θ ∈ K → factor θ 0 = -3
  factorization : ∀ θ, θ ∈ K →
    Function.uncurry mixedIndependentRawFrameAngleSlopeAlongInput =ᶠ[𝓝 (θ, 0)]
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.2 * factor z.1 z.2)

/-- Helper for Infrastructure I.16a: a factor certificate gives the `C²` regularity
    of the raw slope as an uncurried function at every parameter base point. -/
theorem MixedIndependentRawFrameAngleSlopeFactorCertificate.slope_regular
    {K : Set (ℝ × ℝ × ℝ)}
    (certificate : MixedIndependentRawFrameAngleSlopeFactorCertificate K)
    (θ : ℝ × ℝ × ℝ) (hθ : θ ∈ K) :
    ContDiffAt ℝ 2
      (Function.uncurry mixedIndependentRawFrameAngleSlopeAlongInput) (θ, 0) := by
  have hradius : ContDiffAt ℝ 2
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.2) (θ, 0) := by
    fun_prop
  have hproduct : ContDiffAt ℝ 2
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.2 * certificate.factor z.1 z.2) (θ, 0) := by
    have hraw := hradius.mul (certificate.factor_regular θ hθ)
    simpa only [Function.uncurry, Pi.mul_apply] using hraw
  exact hproduct.congr_of_eventuallyEq (certificate.factorization θ hθ)

/-- Helper for Infrastructure I.16a: the same factor certificate computes the first
    radius derivative of the raw slope from the coefficient value at radius zero. -/
theorem MixedIndependentRawFrameAngleSlopeFactorCertificate.slope_derivative
    {K : Set (ℝ × ℝ × ℝ)}
    (certificate : MixedIndependentRawFrameAngleSlopeFactorCertificate K)
    (θ : ℝ × ℝ × ℝ) (hθ : θ ∈ K) :
    deriv (mixedIndependentRawFrameAngleSlopeAlongInput θ) 0 = -3 := by
  have htwo_ne_zero : (2 : WithTop ENat) ≠ 0 := by
    norm_num
  have hsliceMap : ContDiffAt ℝ 2
      (fun r : ℝ ↦ (θ, r)) 0 := by
    fun_prop
  have hfactorSlice : ContDiffAt ℝ 2 (certificate.factor θ) 0 := by
    have hcomp := (certificate.factor_regular θ hθ).comp 0 hsliceMap
    have hfun : (Function.uncurry certificate.factor ∘ Prod.mk θ) = certificate.factor θ := by
      funext r
      rfl
    rw [hfun] at hcomp
    exact hcomp
  have hfactorDerivative : HasDerivAt (certificate.factor θ)
      (deriv (certificate.factor θ) 0) 0 :=
    (hfactorSlice.differentiableAt htwo_ne_zero).hasDerivAt
  have hproductDerivative : HasDerivAt
      (fun r : ℝ ↦ r * certificate.factor θ r)
      (certificate.factor θ 0) 0 := by
    have hraw := (hasDerivAt_id 0).mul hfactorDerivative
    have hfun : id * certificate.factor θ =
        (fun r : ℝ ↦ r * certificate.factor θ r) := by
      funext r
      rfl
    rw [hfun] at hraw
    simpa using hraw
  have hpath : Tendsto (fun r : ℝ ↦ (θ, r)) (𝓝 (0 : ℝ)) (𝓝 (θ, 0)) := by
    simpa [id, nhds_prod_eq] using tendsto_const_nhds.prodMk tendsto_id
  have hscalar : mixedIndependentRawFrameAngleSlopeAlongInput θ =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ ↦ r * certificate.factor θ r) := by
    have hcomposed := (certificate.factorization θ hθ).comp_tendsto hpath
    simpa only [Function.comp_def, Function.uncurry] using hcomposed
  rw [hscalar.deriv_eq, hproductDerivative.deriv, certificate.factor_zero θ hθ]

/-- Infrastructure I.16a: the raw slope factor certificate closes the uniform
    `[0, -3]` independent-radius germ of the canonical mixed frame angle. -/
theorem mixedIndependentRawFrameAngleAlongInput_truncatedGerm_of_factorCertificate
    {K : Set (ℝ × ℝ × ℝ)}
    (certificate : MixedIndependentRawFrameAngleSlopeFactorCertificate K) :
    IndependentRadiusTruncatedGerm
      (fun θ r ↦ mixedIndependentRawFrameAngle θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)) K 2
      (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n) := by
  apply mixedIndependentRawFrameAngleAlongInput_truncatedGerm_of_slopeCertificate
  · intro θ hθ
    exact certificate.slope_regular θ hθ
  · intro θ hθ
    exact certificate.slope_derivative θ hθ

end DFP.TwoLeg.Mixed
