module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.CubicVanishingUniform
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.PublicFactors

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.SecondLeg

/-- Helper for Lemma 4.15 (Near-return winding number is nonzero): the low
second-leg gradient factor as a scalar function of signed scale and transverse
coordinates. -/
def lowGradientFactor (x : ℝ × ℝ × ℝ) : ℝ :=
  (gradientFactors x.1 x.2.1 x.2.2).1

/-- Helper for Lemma 4.15 (Near-return winding number is nonzero): the low
second-leg gradient factor is analytic at the canceled base point. -/
theorem lowGradientFactor_analyticAt :
    AnalyticAt ℝ lowGradientFactor ((0, 2, 1) : ℝ × ℝ × ℝ) := by
  have hlow := analyticAt_fst.comp gradientFactors_analyticAt_base
  apply hlow.congr
  filter_upwards [] with x
  rfl

/-- Helper for Lemma 4.15 (Near-return winding number is nonzero): the transverse
Fréchet derivative of the low second-leg gradient factor, viewed as a family in the
signed scale. -/
def lowGradientTransverseFDerivFamily
    (z : ℝ × ℝ) (ε : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (fun w : ℝ × ℝ ↦ (gradientFactors ε w.1 w.2).1) z

/-- Helper for Lemma 4.15 (Near-return winding number is nonzero): analyticity of
the gradient factors makes their transverse derivative family jointly `C³` at the
canceled base point. -/
theorem lowGradientTransverseFDerivFamily_contDiffAt :
    ContDiffAt ℝ 3
      (Function.uncurry lowGradientTransverseFDerivFamily)
      (((2, 1) : ℝ × ℝ), 0) := by
  have hinput : ContDiffAt ℝ 4
      (fun q : ((ℝ × ℝ) × ℝ) × (ℝ × ℝ) ↦ (q.1.2, q.2))
      ((((2, 1) : ℝ × ℝ), 0), ((2, 1) : ℝ × ℝ)) := by
    fun_prop
  have huncurried : ContDiffAt ℝ 4
      (Function.uncurry
        (fun q : (ℝ × ℝ) × ℝ ↦ fun w : ℝ × ℝ ↦
          lowGradientFactor (q.2, w)))
      ((((2, 1) : ℝ × ℝ), 0), ((2, 1) : ℝ × ℝ)) := by
    have hcomp := lowGradientFactor_analyticAt.contDiffAt (n := 4) |>.comp
      ((((2, 1) : ℝ × ℝ), 0), ((2, 1) : ℝ × ℝ)) hinput
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [] with q
    rfl
  have horder : (3 : WithTop ℕ∞) + 1 ≤ 4 := by
    norm_num
  have hpartial : ContDiffAt ℝ 3
      (fun q : (ℝ × ℝ) × ℝ ↦
        fderiv ℝ (fun w : ℝ × ℝ ↦ lowGradientFactor (q.2, w)) q.1)
      (((2, 1) : ℝ × ℝ), 0) := by
    exact ContDiffAt.fderiv huncurried contDiffAt_fst horder
  apply hpartial.congr_of_eventuallyEq
  filter_upwards [] with q
  rfl

/-- Helper for Lemma 4.15 (Near-return winding number is nonzero): on the positive
zero-scale slice, the transverse derivative of the low gradient factor vanishes. -/
theorem lowGradientTransverseFDerivFamily_zeroScale
    (z : ℝ × ℝ) (hz : 0 < z.1) :
    lowGradientTransverseFDerivFamily z 0 = 0 := by
  have hpositive : ∀ᶠ w : ℝ × ℝ in 𝓝 z, 0 < w.1 := by
    have hcontinuous : ContinuousAt (fun w : ℝ × ℝ ↦ w.1) z := continuousAt_fst
    exact hcontinuous.eventually (Ioi_mem_nhds hz)
  have hconstant :
      (fun w : ℝ × ℝ ↦ (gradientFactors 0 w.1 w.2).1) =ᶠ[𝓝 z]
        (fun _ : ℝ × ℝ ↦ (1 : ℝ)) := by
    filter_upwards [hpositive] with w hw
    exact gradientFactors_low_zeroScale w.1 w.2 hw
  rw [lowGradientTransverseFDerivFamily, hconstant.fderiv_eq]
  simp

/-- Helper for Lemma 4.15 (Near-return winding number is nonzero): the zeroth scale
jet of the transverse derivative family vanishes on the positive slice. -/
theorem iteratedFDeriv_zero_lowGradientTransverseFDerivFamily
    (z : ℝ × ℝ) (hz : 0 < z.1) :
    iteratedFDeriv ℝ 0 (lowGradientTransverseFDerivFamily z) 0 = 0 := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [iteratedFDeriv_zero_apply,
    lowGradientTransverseFDerivFamily_zeroScale z hz]
  rfl

/-- Lemma 4.15 (Near-return winding number is nonzero): joint `C³` regularity and
vanishing of the first two nonconstant scale jets imply the required uniform cubic
bound for the transverse derivative of the low second-leg gradient factor.  This is
the finite-jet input consumed by Infrastructure I.16. -/
theorem lowGradientFactorTransverseFDeriv_norm_bound_of_scaleJet
    {K : Set (ℝ × ℝ)}
    (hKcompact : IsCompact K)
    (hKneighborhood : K ∈ 𝓝 ((2, 1) : ℝ × ℝ))
    (hpositive : ∀ z ∈ K, 0 < z.1)
    (hjoint : ∀ z ∈ K,
      ContDiffAt ℝ 3
        (Function.uncurry lowGradientTransverseFDerivFamily) (z, 0))
    (hhigherZero : ∀ z ∈ K, ∀ n : ℕ, 0 < n → n < 3 →
      iteratedFDeriv ℝ n (lowGradientTransverseFDerivFamily z) 0 = 0) :
    ∃ C > 0, ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      ‖fderiv ℝ (fun z : ℝ × ℝ ↦
        (gradientFactors x.1 z.1 z.2).1) (x.2.1, x.2.2)‖ ≤
        C * ‖x.1 ^ (3 : ℕ)‖ := by
  apply FiniteTaylorJet.eventually_cubic_bound_of_contDiffAt_of_iteratedFDeriv_eq_zero
    hKcompact hKneighborhood hjoint
  intro z hz n hn
  by_cases hnzero : n = 0
  · subst n
    exact iteratedFDeriv_zero_lowGradientTransverseFDerivFamily z (hpositive z hz)
  · exact hhigherZero z hz n (Nat.pos_of_ne_zero hnzero) hn

/-- Helper for Lemma 4.15 (Near-return winding number is nonzero): a base-point
`C³` certificate and locally vanishing first and second scale jets suffice for the
uniform cubic transverse-derivative bound. -/
theorem lowGradientFactorTransverseFDeriv_norm_bound_of_localScaleJet
    (hjoint : ContDiffAt ℝ 3
      (Function.uncurry lowGradientTransverseFDerivFamily)
      (((2, 1) : ℝ × ℝ), 0))
    (hhigherZero : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      ∀ n : ℕ, 0 < n → n < 3 →
        iteratedFDeriv ℝ n (lowGradientTransverseFDerivFamily z) 0 = 0) :
    ∃ C > 0, ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      ‖fderiv ℝ (fun z : ℝ × ℝ ↦
        (gradientFactors x.1 z.1 z.2).1) (x.2.1, x.2.2)‖ ≤
        C * ‖x.1 ^ (3 : ℕ)‖ := by
  have hthreeFinite :
      (3 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    norm_num
  have hsliceContinuous : ContinuousAt
      (fun z : ℝ × ℝ ↦ (z, (0 : ℝ))) ((2, 1) : ℝ × ℝ) :=
    continuousAt_id.prodMk continuousAt_const
  have hjointEventually : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      ContDiffAt ℝ 3
        (Function.uncurry lowGradientTransverseFDerivFamily) (z, 0) :=
    hsliceContinuous.eventually (hjoint.eventually hthreeFinite)
  have htwoPositive : (0 : ℝ) < 2 := by
    norm_num
  have hpositiveEventually : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      0 < z.1 := by
    exact continuousAt_fst.eventually (Ioi_mem_nhds htwoPositive)
  have hall := hjointEventually.and (hpositiveEventually.and hhigherZero)
  rcases Metric.nhds_basis_closedBall.eventually_iff.1 hall with
    ⟨radius, hradius, hball⟩
  apply lowGradientFactorTransverseFDeriv_norm_bound_of_scaleJet
    (K := Metric.closedBall ((2, 1) : ℝ × ℝ) radius)
    (isCompact_closedBall ((2, 1) : ℝ × ℝ) radius)
    (Metric.closedBall_mem_nhds ((2, 1) : ℝ × ℝ) hradius)
  · intro z hz
    exact (hball hz).2.1
  · intro z hz
    exact (hball hz).1
  · intro z hz n hn hnlt
    exact (hball hz).2.2 n hn hnlt

/-- Helper for Lemma 4.15 (Near-return winding number is nonzero): vanishing of
the first and second scale derivatives of the transverse family is the only
remaining local input needed for the uniform cubic estimate. -/
theorem lowGradientFactorTransverseFDeriv_norm_bound_of_firstSecondScaleJet
    (hfirstZero : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 1 (lowGradientTransverseFDerivFamily z) 0 = 0)
    (hsecondZero : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 2 (lowGradientTransverseFDerivFamily z) 0 = 0) :
    ∃ C > 0, ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      ‖fderiv ℝ (fun z : ℝ × ℝ ↦
        (gradientFactors x.1 z.1 z.2).1) (x.2.1, x.2.2)‖ ≤
        C * ‖x.1 ^ (3 : ℕ)‖ := by
  apply lowGradientFactorTransverseFDeriv_norm_bound_of_localScaleJet
    lowGradientTransverseFDerivFamily_contDiffAt
  filter_upwards [hfirstZero, hsecondZero] with z hfirst hsecond
  intro n hn hnlt
  have hnCases : n = 1 ∨ n = 2 := by
    omega
  rcases hnCases with hnOne | hnTwo
  · subst n
    exact hfirst
  · subst n
    exact hsecond

end DFP.SecondLeg
