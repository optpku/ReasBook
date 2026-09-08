module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseAnalyticity
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseScaleJetCertificate

public section

noncomputable section

open Filter
open scoped Topology

universe u

namespace FiniteTaylorJet

/-- Helper for Infrastructure I.16a companion: a zero normalized Taylor coefficient of a
scalar-input map gives a zero iterated Fréchet derivative in the same order. -/
theorem iteratedFDeriv_eq_zero_of_scalarCoeff_eq_zero
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} {f : ℝ → F} {n : Fin (m + 1)}
    (hcoeff : (ofFunction ℝ m f 0).scalarCoeff n = 0) :
    iteratedFDeriv ℝ (n : ℕ) f 0 = 0 := by
  rw [scalarCoeff_ofFunction] at hcoeff
  have hfactorial : (((n : ℕ).factorial : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n : ℕ))
  have hcancel := congrArg
    (fun y : F ↦ (((n : ℕ).factorial : ℝ)) • y) hcoeff
  have hderiv : iteratedDeriv (n : ℕ) f 0 = 0 := by
    simpa only [smul_smul, mul_inv_cancel₀ hfactorial, one_smul, smul_zero] using hcancel
  apply ContinuousMultilinearMap.ext_ring
  simpa only [iteratedDeriv_eq_iteratedFDeriv, zero_apply] using hderiv

end FiniteTaylorJet

namespace DFP.SecondLeg

/-!
# Taylor certificate for the transverse cubic scale factor

The public second-leg API proves joint regularity and zero-scale constancy.  The source-facing
certificate below isolates the two remaining Taylor coefficients.  Once they are supplied, the
public finite Taylor estimate constructs a bounded removable cubic quotient and hence an actual
`LowGradientTransverseScaleFactorizationCertificate`.
-/

/-- Helper for Infrastructure I.16a companion: the two normalized nonconstant Taylor
coefficients whose vanishing remains to be checked from the explicit second-leg formulas. -/
structure LowGradientTransverseScaleTaylorCertificate : Prop where
  first_scale_coefficient :
    ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      (FiniteTaylorJet.ofFunction ℝ 2
        (lowGradientTransverseFDerivFamily z) 0).scalarCoeff (1 : Fin 3) = 0
  second_scale_coefficient :
    ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      (FiniteTaylorJet.ofFunction ℝ 2
        (lowGradientTransverseFDerivFamily z) 0).scalarCoeff (2 : Fin 3) = 0

/-- Helper for Infrastructure I.16a companion: the explicit first and second normalized Taylor
coefficient identities give the corresponding iterated scale-jet vanishings. -/
theorem LowGradientTransverseScaleTaylorCertificate.firstSecondScaleJet
    (certificate : LowGradientTransverseScaleTaylorCertificate) :
    (∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 1 (lowGradientTransverseFDerivFamily z) 0 = 0) ∧
    (∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 2 (lowGradientTransverseFDerivFamily z) 0 = 0) := by
  have hfirst : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 1 (lowGradientTransverseFDerivFamily z) 0 = 0 := by
    filter_upwards [certificate.first_scale_coefficient] with z hz
    have hindex : (((1 : Fin 3) : ℕ)) = 1 := rfl
    rw [← hindex]
    exact FiniteTaylorJet.iteratedFDeriv_eq_zero_of_scalarCoeff_eq_zero hz
  have hsecond : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 2 (lowGradientTransverseFDerivFamily z) 0 = 0 := by
    filter_upwards [certificate.second_scale_coefficient] with z hz
    have hindex : (((2 : Fin 3) : ℕ)) = 2 := rfl
    rw [← hindex]
    exact FiniteTaylorJet.iteratedFDeriv_eq_zero_of_scalarCoeff_eq_zero hz
  exact And.intro hfirst hsecond

/-- Helper for Infrastructure I.16a companion: zero first and second scale jets give a uniform
cubic norm bound for the public transverse derivative family itself. -/
theorem lowGradientTransverseFDerivFamily_eventually_cubic_bound_of_firstSecondScaleJet
    (hfirst : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 1 (lowGradientTransverseFDerivFamily z) 0 = 0)
    (hsecond : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 2 (lowGradientTransverseFDerivFamily z) 0 = 0) :
    ∃ C > 0, ∀ᶠ x : ℝ × (ℝ × ℝ) in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      ‖lowGradientTransverseFDerivFamily x.2 x.1‖ ≤
        C * ‖x.1 ^ (3 : ℕ)‖ := by
  have hthreeFinite :
      (3 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    norm_num
  have hsliceContinuous : ContinuousAt
      (fun z : ℝ × ℝ ↦ (z, (0 : ℝ))) ((2, 1) : ℝ × ℝ) :=
    continuousAt_id.prodMk continuousAt_const
  have hjoint : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      ContDiffAt ℝ 3
        (Function.uncurry lowGradientTransverseFDerivFamily) (z, 0) :=
    hsliceContinuous.eventually
      (lowGradientTransverseFDerivFamily_contDiffAt.eventually hthreeFinite)
  have htwoPositive : (0 : ℝ) < 2 := by
    norm_num
  have hpositive : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      0 < z.1 := by
    exact continuousAt_fst.eventually (Ioi_mem_nhds htwoPositive)
  have hall := hjoint.and (hpositive.and (hfirst.and hsecond))
  rcases Metric.nhds_basis_closedBall.eventually_iff.1 hall with
    ⟨radius, hradius, hball⟩
  apply FiniteTaylorJet.eventually_cubic_bound_of_contDiffAt_of_iteratedFDeriv_eq_zero
    (K := Metric.closedBall ((2, 1) : ℝ × ℝ) radius)
    (isCompact_closedBall ((2, 1) : ℝ × ℝ) radius)
    (Metric.closedBall_mem_nhds ((2, 1) : ℝ × ℝ) hradius)
  · intro z hz
    exact (hball hz).1
  · intro z hz n hn
    by_cases hnzero : n = 0
    · subst n
      exact iteratedFDeriv_zero_lowGradientTransverseFDerivFamily z
        (hball hz).2.1
    · have hnCases : n = 1 ∨ n = 2 := by
        omega
      rcases hnCases with hnOne | hnTwo
      · subst n
        exact (hball hz).2.2.1
      · subst n
        exact (hball hz).2.2.2

/-- Helper for Infrastructure I.16a companion: the removable cubic quotient of the transverse
derivative family, set to zero on the zero-scale slice. -/
def lowGradientTransverseScaleCubicQuotient
    (x : ℝ × ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  if x.1 = 0 then 0
  else (x.1 ^ (3 : ℕ))⁻¹ • lowGradientTransverseFDerivFamily x.2 x.1

/-- Helper for Infrastructure I.16a companion: on the positive transverse slice, the cubic
quotient restores the transverse derivative family exactly. -/
theorem lowGradientTransverseFDerivFamily_eq_cube_smul_scaleCubicQuotient
    (x : ℝ × ℝ × ℝ) (hpositive : 0 < x.2.1) :
    lowGradientTransverseFDerivFamily x.2 x.1 =
      x.1 ^ (3 : ℕ) • lowGradientTransverseScaleCubicQuotient x := by
  by_cases hscale : x.1 = 0
  · rw [hscale]
    rw [lowGradientTransverseFDerivFamily_zeroScale x.2 hpositive,
      lowGradientTransverseScaleCubicQuotient, if_pos hscale, smul_zero]
  · have hcube : x.1 ^ (3 : ℕ) ≠ 0 := pow_ne_zero 3 hscale
    rw [lowGradientTransverseScaleCubicQuotient, if_neg hscale, smul_smul,
      mul_inv_cancel₀ hcube, one_smul]

/-- Helper for Infrastructure I.16a companion: a cubic norm bound controls the removable
quotient coefficient pointwise. -/
theorem lowGradientTransverseScaleCubicQuotient_norm_le
    {x : ℝ × ℝ × ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ‖lowGradientTransverseFDerivFamily x.2 x.1‖ ≤
      C * ‖x.1 ^ (3 : ℕ)‖) :
    ‖lowGradientTransverseScaleCubicQuotient x‖ ≤ C := by
  by_cases hscale : x.1 = 0
  · rw [lowGradientTransverseScaleCubicQuotient, if_pos hscale, norm_zero]
    exact hC
  · have hcube : x.1 ^ (3 : ℕ) ≠ 0 := pow_ne_zero 3 hscale
    have hnorm : 0 < ‖x.1 ^ (3 : ℕ)‖ := norm_pos_iff.mpr hcube
    rw [lowGradientTransverseScaleCubicQuotient, if_neg hscale, norm_smul,
      norm_inv, inv_mul_eq_div]
    exact (div_le_iff₀ hnorm).2 hbound

/-- Helper for Infrastructure I.16a companion: first and second scale-jet vanishings construct
a bounded cubic factorization certificate for the public transverse derivative family. -/
theorem exists_lowGradientTransverseScaleFactorizationCertificate_of_firstSecondScaleJet
    (hfirst : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 1 (lowGradientTransverseFDerivFamily z) 0 = 0)
    (hsecond : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 2 (lowGradientTransverseFDerivFamily z) 0 = 0) :
    ∃ C > 0, LowGradientTransverseScaleFactorizationCertificate
      lowGradientTransverseScaleCubicQuotient C := by
  obtain ⟨C, hC, hbound⟩ :=
    lowGradientTransverseFDerivFamily_eventually_cubic_bound_of_firstSecondScaleJet
      hfirst hsecond
  have htwoPositive : (0 : ℝ) < 2 := by
    norm_num
  have hpositive : ∀ᶠ x : ℝ × ℝ × ℝ in
      𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), 0 < x.2.1 := by
    exact (continuousAt_snd.fst).eventually (Ioi_mem_nhds htwoPositive)
  have hfactorization : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      lowGradientTransverseFDerivFamily x.2 x.1 =
        x.1 ^ (3 : ℕ) • lowGradientTransverseScaleCubicQuotient x := by
    filter_upwards [hpositive] with x hx
    exact lowGradientTransverseFDerivFamily_eq_cube_smul_scaleCubicQuotient x hx
  have hcoefficientBound : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      ‖lowGradientTransverseScaleCubicQuotient x‖ ≤ C := by
    filter_upwards [hbound] with x hx
    exact lowGradientTransverseScaleCubicQuotient_norm_le hC.le hx
  have hcertificate : LowGradientTransverseScaleFactorizationCertificate
      lowGradientTransverseScaleCubicQuotient C :=
    { factorization := hfactorization
      coefficient_bound := hcoefficientBound }
  exact ⟨C, hC, hcertificate⟩

/-- Infrastructure I.16a companion: the two explicit normalized Taylor coefficient identities
construct an actual bounded cubic scale-factorization certificate. -/
theorem LowGradientTransverseScaleTaylorCertificate.existsScaleFactorizationCertificate
    (certificate : LowGradientTransverseScaleTaylorCertificate) :
    ∃ C > 0, LowGradientTransverseScaleFactorizationCertificate
      lowGradientTransverseScaleCubicQuotient C := by
  rcases certificate.firstSecondScaleJet with ⟨hfirst, hsecond⟩
  exact exists_lowGradientTransverseScaleFactorizationCertificate_of_firstSecondScaleJet
    hfirst hsecond

end DFP.SecondLeg
