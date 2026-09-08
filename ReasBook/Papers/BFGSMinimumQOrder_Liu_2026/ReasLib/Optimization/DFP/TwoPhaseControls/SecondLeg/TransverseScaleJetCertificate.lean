module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.PeanoComparison
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseCubicJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseSourceCertificate
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseCubicJet

public section

noncomputable section

open Filter
open scoped Topology

universe u

namespace FiniteTaylorJet

/-- Helper for Infrastructure I.16a companion: a twice continuously differentiable scalar-input
map that is `O(ε³)` has vanishing first and second iterated Fréchet derivatives at zero. -/
theorem firstSecondIteratedFDeriv_eq_zero_of_isBigO_cube
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F}
    (hf : ContDiffAt ℝ 2 f 0)
    (hcubic : f =O[𝓝 0] fun ε : ℝ ↦ ε ^ (3 : ℕ)) :
    iteratedFDeriv ℝ 1 f 0 = 0 ∧ iteratedFDeriv ℝ 2 f 0 = 0 := by
  have hzeroRegular : ContDiffAt ℝ 2 (fun _ : ℝ ↦ (0 : F)) 0 := contDiffAt_const
  have hjet :
      ofFunction ℝ 2 f 0 = ofFunction ℝ 2 (fun _ : ℝ ↦ (0 : F)) 0 := by
    apply ofFunction_eq_of_sub_isBigO_succ hf hzeroRegular
    simpa only [zero_add, sub_zero, Nat.reduceAdd] using hcubic
  have hderivatives :
      ∀ n : Fin 3, iteratedDeriv (n : ℕ) f 0 = 0 :=
    (ofFunction_eq_zeroFunction_iff 2 f 0).mp hjet
  have hfirstDerivative : iteratedDeriv 1 f 0 = 0 := by
    simpa using hderivatives (1 : Fin 3)
  have hsecondDerivative : iteratedDeriv 2 f 0 = 0 := by
    simpa using hderivatives (2 : Fin 3)
  constructor
  · apply ContinuousMultilinearMap.ext_ring
    simpa only [iteratedDeriv_eq_iteratedFDeriv, zero_apply] using
      hfirstDerivative
  · apply ContinuousMultilinearMap.ext_ring
    simpa only [iteratedDeriv_eq_iteratedFDeriv, zero_apply] using
      hsecondDerivative

end FiniteTaylorJet

namespace DFP.SecondLeg

/-!
# Scale-jet certificates for the transverse low-gradient factor

The source calculation may expose the transverse derivative either directly as a bounded
`ε³` factorization or through the numerator and denominator derivative data in
`LowGradientTransverseSourceCertificate`.  This module converts either interface into the
first and second scale-jet vanishings used by the finite Taylor estimate.
-/

/-- Helper for Infrastructure I.16a companion: a local bounded `ε³` factorization of
`lowGradientTransverseFDerivFamily` near the canceled base point. -/
structure LowGradientTransverseScaleFactorizationCertificate
    (Q : (ℝ × ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ)
    (C : ℝ) : Prop where
  factorization : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
    lowGradientTransverseFDerivFamily x.2 x.1 =
      x.1 ^ (3 : ℕ) • Q x
  coefficient_bound : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
    ‖Q x‖ ≤ C

/-- Helper for Infrastructure I.16a companion: a bounded local scale factorization gives an
eventual `O(ε³)` estimate on every nearby transverse slice. -/
theorem LowGradientTransverseScaleFactorizationCertificate.eventually_isBigO_cube
    {Q : (ℝ × ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    {C : ℝ}
    (certificate : LowGradientTransverseScaleFactorizationCertificate Q C) :
    ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      lowGradientTransverseFDerivFamily z =O[𝓝 0]
        fun ε : ℝ ↦ ε ^ (3 : ℕ) := by
  have hproduct := certificate.factorization.and certificate.coefficient_bound
  rw [nhds_prod_eq] at hproduct
  rcases Filter.eventually_prod_iff.mp hproduct with
    ⟨scaleGood, hscale, transverseGood, htransverse, hrect⟩
  filter_upwards [htransverse] with z hz
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hscale] with ε hε
  have hdata := hrect hε hz
  rw [hdata.1, norm_smul]
  calc
    ‖ε ^ (3 : ℕ)‖ * ‖Q (ε, z)‖ ≤ ‖ε ^ (3 : ℕ)‖ * C :=
      mul_le_mul_of_nonneg_left hdata.2 (norm_nonneg _)
    _ = C * ‖ε ^ (3 : ℕ)‖ := by ring

/-- Helper for Infrastructure I.16a companion: the transverse derivative family is eventually
`C²` in the scale variable near the canceled transverse base point. -/
theorem lowGradientTransverseFDerivFamily_eventually_contDiffAt_two :
    ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      ContDiffAt ℝ 2 (lowGradientTransverseFDerivFamily z) 0 := by
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
  have htwoLeThree : (2 : WithTop ℕ∞) ≤ 3 := by
    norm_num
  filter_upwards [hjoint] with z hz
  have hscalePath : ContDiffAt ℝ 3 (fun ε : ℝ ↦ (z, ε)) 0 := by
    fun_prop
  have hsliceThree :
      ContDiffAt ℝ 3 (lowGradientTransverseFDerivFamily z) 0 := by
    have hcomp := hz.comp 0 hscalePath
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using hcomp
  exact hsliceThree.of_le htwoLeThree

/-- Infrastructure I.16a companion: a bounded local cubic scale factorization supplies the
eventual first- and second-scale iterated Fréchet derivative vanishings. -/
theorem LowGradientTransverseScaleFactorizationCertificate.firstSecondScaleJet
    {Q : (ℝ × ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    {C : ℝ}
    (certificate : LowGradientTransverseScaleFactorizationCertificate Q C) :
    (∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 1 (lowGradientTransverseFDerivFamily z) 0 = 0) ∧
    (∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 2 (lowGradientTransverseFDerivFamily z) 0 = 0) := by
  have hcubic := certificate.eventually_isBigO_cube
  have hregular := lowGradientTransverseFDerivFamily_eventually_contDiffAt_two
  have hboth : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 1 (lowGradientTransverseFDerivFamily z) 0 = 0 ∧
        iteratedFDeriv ℝ 2 (lowGradientTransverseFDerivFamily z) 0 = 0 := by
    filter_upwards [hregular, hcubic] with z hzRegular hzCubic
    exact FiniteTaylorJet.firstSecondIteratedFDeriv_eq_zero_of_isBigO_cube
      hzRegular hzCubic
  constructor
  · exact hboth.mono fun _ hz ↦ hz.1
  · exact hboth.mono fun _ hz ↦ hz.2

/-- Helper for Infrastructure I.16a companion: a bounded local cubic scale factorization yields the
uniform transverse derivative norm bound through the first/second scale-jet interface. -/
theorem LowGradientTransverseScaleFactorizationCertificate.normBound
    {Q : (ℝ × ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    {C : ℝ}
    (certificate : LowGradientTransverseScaleFactorizationCertificate Q C) :
    ∃ C > 0, ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      ‖fderiv ℝ (fun z : ℝ × ℝ ↦
        (gradientFactors x.1 z.1 z.2).1) (x.2.1, x.2.2)‖ ≤
        C * ‖x.1 ^ (3 : ℕ)‖ := by
  rcases certificate.firstSecondScaleJet with ⟨hfirst, hsecond⟩
  exact lowGradientFactorTransverseFDeriv_norm_bound_of_firstSecondScaleJet
    hfirst hsecond

/-- Helper for Infrastructure I.16a companion: numerator, denominator, frame, and coefficient
data expose the local cubic scale factorization of the transverse derivative family. -/
theorem lowGradientTransverseFDerivFamily_factorization_of_sourceCertificate
    {A B : (ℝ × ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    {C : ℝ}
    (source : LowGradientTransverseSourceCertificate
      ((0, 2, 1) : ℝ × ℝ × ℝ) A B C) :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      lowGradientTransverseFDerivFamily x.2 x.1 =
        x.1 ^ (3 : ℕ) •
          transverseQuotientDerivative
            (lowGradientTransverseNumerator x)
            (lowGradientTransverseDenominator x) (A x) (B x) := by
  filter_upwards [source.frame, source.numerator, source.denominator,
    source.denominator_ne] with x hframe hnum hden hdenNe
  simpa only [lowGradientTransverseFDerivFamily] using
    lowGradientTransverseFDeriv_of_frame_certificates
      hframe hnum hden hdenNe

/-- Helper for Infrastructure I.16a companion: source-side numerator and denominator derivative
data form a bounded local cubic scale-factorization certificate; existence of that source data
remains an explicit obligation. -/
theorem LowGradientTransverseSourceCertificate.toScaleFactorizationCertificate
    {A B : (ℝ × ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    {C : ℝ}
    (source : LowGradientTransverseSourceCertificate
      ((0, 2, 1) : ℝ × ℝ × ℝ) A B C) :
    LowGradientTransverseScaleFactorizationCertificate
      (fun x : ℝ × ℝ × ℝ ↦
        transverseQuotientDerivative
          (lowGradientTransverseNumerator x)
          (lowGradientTransverseDenominator x) (A x) (B x)) C := by
  constructor
  · exact lowGradientTransverseFDerivFamily_factorization_of_sourceCertificate source
  · exact source.coefficient_bound

/-- Helper for Infrastructure I.16a companion: source-side numerator and denominator derivative
data imply the eventual first- and second-scale iterated Fréchet derivative vanishings. -/
theorem LowGradientTransverseSourceCertificate.firstSecondScaleJet
    {A B : (ℝ × ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    {C : ℝ}
    (source : LowGradientTransverseSourceCertificate
      ((0, 2, 1) : ℝ × ℝ × ℝ) A B C) :
    (∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 1 (lowGradientTransverseFDerivFamily z) 0 = 0) ∧
    (∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 2 (lowGradientTransverseFDerivFamily z) 0 = 0) := by
  exact source.toScaleFactorizationCertificate.firstSecondScaleJet

end DFP.SecondLeg
