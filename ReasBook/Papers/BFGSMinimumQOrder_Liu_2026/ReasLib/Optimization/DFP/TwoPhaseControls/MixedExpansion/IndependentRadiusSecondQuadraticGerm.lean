module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondOrderJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondOrderJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-!
This companion isolates the interface needed by the physical-drift amplitude remainder.
The chart calculation itself lives in `IndependentRadiusSecondOrderJet`; the canonical
component certificates are intentionally kept as a separate proof obligation.
-/

/-- Helper for Appendix Lemma A.6: component quadratic germs and a pointwise chart
factorization determine the normalized second-gradient low germ. -/
theorem independentRadiusSecondGradientLow_quadraticGerm_of_componentCertificate
    (θ : ℝ × ℝ × ℝ)
    {radius metricA metricC metricD gradientQ gradientU : ℝ → ℝ}
    {a₂ c₁ c₂ d₁ d₂ q₁ q₂ u₁ u₂ : ℝ}
    (hradius : HasQuadraticGerm radius 0 1 0)
    (hmetricA : HasQuadraticGerm metricA 0 0 a₂)
    (hmetricC : HasQuadraticGerm metricC 0 c₁ c₂)
    (hmetricD : HasQuadraticGerm metricD 1 d₁ d₂)
    (hgradientQ : HasQuadraticGerm gradientQ 1 q₁ q₂)
    (hgradientU : HasQuadraticGerm gradientU 0 u₁ u₂)
    (hpath : ∀ r : ℝ,
      lowGradientChartPath radius metricA metricC metricD gradientQ gradientU r =
        (independentRadiusSecondGradient (θ, r)).1) :
    HasQuadraticGerm
      (fun r ↦ (independentRadiusSecondGradient (θ, r)).1) 1 q₁
        (q₂ - c₁ ^ 2 / 2) := by
  exact independentRadiusSecondGradientLow_quadraticGerm_of_chartFactorization θ
    hradius hmetricA hmetricC hmetricD hgradientQ hgradientU hpath

/-- Helper for Appendix Lemma A.6: the canonical second-leg component coefficients
specialize the chart certificate to the displayed low-gradient coefficient. -/
theorem independentRadiusSecondGradientLow_quadraticGerm_of_explicitComponentCertificates
    (θ : ℝ × ℝ × ℝ)
    {radius metricA metricC metricD gradientQ gradientU : ℝ → ℝ}
    (hradius : HasQuadraticGerm radius 0 1 0)
    (hmetricA : HasQuadraticGerm metricA 0 0 6)
    (hmetricC : HasQuadraticGerm metricC 0 2
      (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3))
    (hmetricD : HasQuadraticGerm metricD 1 (8 * θ.1)
      (4 * (6 * θ.2.2 * θ.1 ^ 2 + θ.2.1 * θ.1 ^ 2 +
        78 * θ.1 ^ 2 - 3) / 3))
    (hgradientQ : HasQuadraticGerm gradientQ 1 0
      ((24 * θ.2.2 * θ.1 ^ 2 - 4 * θ.2.1 * θ.1 ^ 2 +
        384 * θ.1 ^ 2 - 81) / 18))
    (hgradientU : HasQuadraticGerm gradientU 0
      (-θ.1 * (6 * θ.2.2 - θ.2.1 + 60) / 9)
      (-(3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 + 288 * θ.2.2 * θ.1 ^ 2 -
        θ.2.1 ^ 2 * θ.1 ^ 2 + 48 * θ.2.1 * θ.1 ^ 2 +
        1314 * θ.1 ^ 2 - 162) / 27))
    (hpath : ∀ r : ℝ,
      lowGradientChartPath radius metricA metricC metricD gradientQ gradientU r =
        (independentRadiusSecondGradient (θ, r)).1) :
    HasQuadraticGerm
      (fun r ↦ (independentRadiusSecondGradient (θ, r)).1)
      1 0 ((θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18) := by
  have hcertificate :=
    independentRadiusSecondGradientLow_quadraticGerm_of_componentCertificate θ
      hradius hmetricA hmetricC hmetricD hgradientQ hgradientU hpath
  have hconstant : (1 : ℝ) = 1 := rfl
  have hlinear : (0 : ℝ) = 0 := rfl
  have hquadratic :
      (24 * θ.2.2 * θ.1 ^ 2 - 4 * θ.2.1 * θ.1 ^ 2 +
        384 * θ.1 ^ 2 - 81) / 18 - (2 : ℝ) ^ 2 / 2 =
        (θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18 := by
    ring
  exact hcertificate.congrCoefficients hconstant hlinear hquadratic

/-- Helper for Appendix Lemma A.6: the first normalized spectral and gradient
factors have explicit quadratic germs along the independent-radius path. -/
theorem independentRadiusFirstFactorQuadraticGerms (θ : ℝ × ℝ × ℝ) :
    HasQuadraticGerm
        (fun r ↦ (independentRadiusFirstSpectral (θ, r)).1)
        2 (θ.1 * (2 * θ.2.2 + θ.2.1 + 4))
          (θ.2.1 * θ.2.2 * θ.1 ^ 2 + 4 * θ.2.2 * θ.1 ^ 2 +
            2 * θ.2.1 * θ.1 ^ 2 - 10 * θ.1 ^ 2 + 2) ∧
      HasQuadraticGerm
        (fun r ↦ (independentRadiusFirstSpectral (θ, r)).2)
        1 (-2 * θ.1) (6 * θ.1 ^ 2) ∧
      HasQuadraticGerm
        (fun r ↦ (independentRadiusFirstGradient (θ, r)).1)
        1 (-2 * θ.1)
          (-2 * θ.2.1 * θ.1 ^ 2 / 3 + 4 * θ.1 ^ 2 - 5 / 2) ∧
      HasQuadraticGerm
        (fun r ↦ (independentRadiusFirstGradient (θ, r)).2)
        1 (θ.1 * (θ.2.1 - 6) / 3)
          (-2 * θ.2.2 * θ.1 ^ 2 - θ.2.1 * θ.1 ^ 2 - 1 / 2) := by
  let b : ℝ := θ.1
  let P : ℝ := θ.2.1
  let J : ℝ := θ.2.2
  let X : ℝ → ℝ := fun r ↦ r
  let A : ℝ → ℝ := fun r ↦ (independentRadiusFirstResiduals (θ, r)).1
  let C : ℝ → ℝ := fun r ↦ (independentRadiusFirstResiduals (θ, r)).2.1
  let D : ℝ → ℝ := fun r ↦ (independentRadiusFirstResiduals (θ, r)).2.2
  let q : ℝ → ℝ := fun r ↦ (independentRadiusFirstGradientResiduals (θ, r)).1
  let u : ℝ → ℝ := fun r ↦ (independentRadiusFirstGradientResiduals (θ, r)).2
  obtain ⟨hA, hC, hD, hq, hu⟩ := independentFirstResidualQuadraticGerms b P J
  have hA' : HasQuadraticGerm A 3 (b * (2 * J + P - 2))
      (J * P * b ^ 2 - 1) := by
    apply hA.congrFunction
    intro r
    simp [A, b, P, J, independentRadiusFirstResiduals]
  have hC' : HasQuadraticGerm C 1 (-4 * b)
      (-2 * J * b ^ 2 - P * b ^ 2 + 6 * b ^ 2 - 3) := by
    apply hC.congrFunction
    intro r
    simp [C, b, P, J, independentRadiusFirstResiduals]
  have hD' : HasQuadraticGerm D 1 (-2 * b) (6 * b ^ 2 - 1) := by
    apply hD.congrFunction
    intro r
    simp [D, b, P, J, independentRadiusFirstResiduals]
  have hq' : HasQuadraticGerm q 1 (-2 * b)
      (-2 * P * b ^ 2 / 3 + 4 * b ^ 2 - 2) := by
    apply hq.congrFunction
    intro r
    simp [q, b, P, independentRadiusFirstGradientResiduals]
  have hu' : HasQuadraticGerm u 0 (b * (P + 6) / 3)
      (2 * P * b ^ 2 / 3 - 4 * b ^ 2 + 2) := by
    apply hu.congrFunction
    intro r
    simp [u, b, P, independentRadiusFirstGradientResiduals]
  have hX : HasQuadraticGerm X 0 1 0 := by
    apply (HasQuadraticGerm.model 0 1 0).congrFunction
    intro r
    simp [X, quadraticModel]
  let mA : ℝ → ℝ := fun r ↦ X r ^ 2 * A r
  let mC : ℝ → ℝ := fun r ↦ X r * C r
  let mD : ℝ → ℝ := D
  have hmAraw := (hX.mul hX).mul hA'
  have hmApath : ∀ r : ℝ, mA r = X r * X r * A r := by
    intro r
    simp [mA, pow_two]
  have hmAcoeff := hmAraw.congrFunction hmApath
  have hmA : HasQuadraticGerm mA 0 0 3 := by
    apply hmAcoeff.congrCoefficients
    · ring
    · ring
    · ring
  have hmCraw := hX.mul hC'
  have hmCpath : ∀ r : ℝ, mC r = X r * C r := by
    intro r
    rfl
  have hmCcoeff := hmCraw.congrFunction hmCpath
  have hmC : HasQuadraticGerm mC 0 1 (-4 * b) := by
    apply hmCcoeff.congrCoefficients
    · ring
    · ring
    · ring
  have hmD : HasQuadraticGerm mD 1 (-2 * b) (6 * b ^ 2 - 1) := by
    simpa only [mD] using hD'
  let rad : ℝ → ℝ := fun r ↦ (mA r - mD r) ^ 2 + 4 * (mC r) ^ 2
  have hradRaw := ((hmA.sub hmD).mul (hmA.sub hmD)).add
    ((hmC.mul hmC).constMul 4)
  have hradPath : ∀ r : ℝ,
      rad r = (mA r - mD r) * (mA r - mD r) + 4 * (mC r * mC r) := by
    intro r
    simp [rad, pow_two]
  have hradCoeff := hradRaw.congrFunction hradPath
  have hrad : HasQuadraticGerm rad 1 (-4 * b) (16 * b ^ 2 - 4) := by
    apply hradCoeff.congrCoefficients
    · ring
    · ring
    · ring
  let gap : ℝ → ℝ := fun r ↦ Real.sqrt (rad r)
  have hgapRaw := hrad.sqrtOne
  have hgapPath : ∀ r : ℝ, gap r = Real.sqrt (rad r) := by
    intro r
    rfl
  have hgapCoeff := hgapRaw.congrFunction hgapPath
  have hgap : HasQuadraticGerm gap 1 (-2 * b) (2 * (3 * b ^ 2 - 1)) := by
    apply hgapCoeff.congrCoefficients
    · ring
    · ring
    · ring
  let high : ℝ → ℝ := fun r ↦ (mA r + mD r + gap r) / 2
  let low : ℝ → ℝ := fun r ↦ (mA r + mD r - gap r) / 2
  have hhighRaw := ((hmA.add hmD).add hgap).constMul (1 / 2 : ℝ)
  have hhighPath : ∀ r : ℝ,
      high r = (1 / 2 : ℝ) * (mA r + mD r + gap r) := by
    intro r
    simp [high]
    ring
  have hhighCoeff := hhighRaw.congrFunction hhighPath
  have hhigh : HasQuadraticGerm high 1 (-2 * b) (6 * b ^ 2) := by
    apply hhighCoeff.congrCoefficients
    · ring
    · ring
    · ring
  have hlowRaw := ((hmA.add hmD).sub hgap).constMul (1 / 2 : ℝ)
  have hlowPath : ∀ r : ℝ,
      low r = (1 / 2 : ℝ) * (mA r + mD r - gap r) := by
    intro r
    simp [low]
    ring
  have hlowCoeff := hlowRaw.congrFunction hlowPath
  have hlow : HasQuadraticGerm low 0 0 2 := by
    apply hlowCoeff.congrCoefficients
    · ring
    · ring
    · ring
  let numeratorSpectral : ℝ → ℝ := fun r ↦ A r * D r - C r ^ 2
  have hnumRaw := (hA'.mul hD').sub (hC'.mul hC')
  have hnumPath : ∀ r : ℝ,
      numeratorSpectral r = A r * D r - C r * C r := by
    intro r
    dsimp [numeratorSpectral]
    ring
  have hnumCoeff := hnumRaw.congrFunction hnumPath
  have hnum : HasQuadraticGerm numeratorSpectral 2
      (b * (2 * J + P))
      (J * P * b ^ 2 - 6 * b ^ 2 + 2) := by
    apply hnumCoeff.congrCoefficients
    · ring
    · ring
    · ring
  have hbase : (1 : ℝ) ≠ 0 := by
    norm_num
  have hLraw := hnum.div hhigh hbase
  have hL : HasQuadraticGerm
      (fun r ↦ numeratorSpectral r / high r) 2
      (b * (2 * J + P + 4))
      (J * P * b ^ 2 + 4 * J * b ^ 2 + 2 * P * b ^ 2 -
        10 * b ^ 2 + 2) := by
    apply hLraw.congrCoefficients
    · ring
    · ring
    · ring
  let denomRad : ℝ → ℝ := fun r ↦ (mD r - low r) ^ 2 + (mC r) ^ 2
  have hdenomRadRaw := ((hmD.sub hlow).mul (hmD.sub hlow)).add (hmC.mul hmC)
  have hdenomRadPath : ∀ r : ℝ,
      denomRad r = (mD r - low r) * (mD r - low r) + mC r * mC r := by
    intro r
    simp [denomRad, pow_two]
  have hdenomRadCoeff := hdenomRadRaw.congrFunction hdenomRadPath
  have hdenomRad : HasQuadraticGerm denomRad 1 (-4 * b) (16 * b ^ 2 - 5) := by
    apply hdenomRadCoeff.congrCoefficients
    · ring
    · ring
    · ring
  let denom : ℝ → ℝ := fun r ↦ Real.sqrt (denomRad r)
  have hdenomRaw := hdenomRad.sqrtOne
  have hdenomPath : ∀ r : ℝ, denom r = Real.sqrt (denomRad r) := by
    intro r
    rfl
  have hdenomCoeff := hdenomRaw.congrFunction hdenomPath
  have hdenom : HasQuadraticGerm denom 1 (-2 * b) (6 * b ^ 2 - 5 / 2) := by
    apply hdenomCoeff.congrCoefficients
    · ring
    · ring
    · ring
  let numeratorLow : ℝ → ℝ := fun r ↦
    (mD r - low r) * q r - X r ^ 2 * C r * u r
  have hnumLowRaw := ((hmD.sub hlow).mul hq').sub
    (((hX.mul hX).mul hC').mul hu')
  have hnumLowPath : ∀ r : ℝ,
      numeratorLow r = (mD r - low r) * q r -
        (X r * X r) * C r * u r := by
    intro r
    simp [numeratorLow, pow_two]
  have hnumLowCoeff := hnumLowRaw.congrFunction hnumLowPath
  have hnumLow : HasQuadraticGerm numeratorLow 1 (-4 * b)
      (-2 * P * b ^ 2 / 3 + 14 * b ^ 2 - 5) := by
    apply hnumLowCoeff.congrCoefficients
    · ring
    · ring
    · ring
  let numeratorHigh : ℝ → ℝ := fun r ↦
    C r * q r + (mD r - low r) * u r
  have hnumHighRaw := (hC'.mul hq').add ((hmD.sub hlow).mul hu')
  have hnumHighPath : ∀ r : ℝ,
      numeratorHigh r = C r * q r + (mD r - low r) * u r := by
    intro r
    rfl
  have hnumHighCoeff := hnumHighRaw.congrFunction hnumHighPath
  have hnumHigh : HasQuadraticGerm numeratorHigh 1
      (b * (P - 12) / 3)
      (-2 * J * b ^ 2 - 5 * P * b ^ 2 / 3 + 10 * b ^ 2 - 3) := by
    apply hnumHighCoeff.congrCoefficients
    · ring
    · ring
    · ring
  have hQraw := hnumLow.div hdenom hbase
  have hQ : HasQuadraticGerm
      (fun r ↦ numeratorLow r / denom r) 1 (-2 * b)
      (-2 * P * b ^ 2 / 3 + 4 * b ^ 2 - 5 / 2) := by
    apply hQraw.congrCoefficients
    · ring
    · ring
    · ring
  have hUraw := hnumHigh.div hdenom hbase
  have hU : HasQuadraticGerm
      (fun r ↦ numeratorHigh r / denom r) 1
      (b * (P - 6) / 3) (-2 * J * b ^ 2 - P * b ^ 2 - 1 / 2) := by
    apply hUraw.congrCoefficients
    · ring
    · ring
    · ring
  have hLpath : ∀ r : ℝ,
      numeratorSpectral r / high r =
        (independentRadiusFirstSpectral (θ, r)).1 := by
    intro r
    simp [independentRadiusFirstSpectral, independentRadiusFirstGradient,
      independentRadiusFirstMetricTriple, independentRadiusFirstResiduals,
      independentRadiusFirstGradientResiduals, RealSymmetric2.high,
      RealSymmetric2.low, RealSymmetric2.gap, RealSymmetric2.lowDenom,
      numeratorSpectral, high, gap, mA, mC, mD, rad, A, C, D, X]
    ring
  have hHpath : ∀ r : ℝ,
      high r = (independentRadiusFirstSpectral (θ, r)).2 := by
    intro r
    simp [independentRadiusFirstSpectral, independentRadiusFirstGradient,
      independentRadiusFirstMetricTriple, independentRadiusFirstResiduals,
      independentRadiusFirstGradientResiduals, RealSymmetric2.high,
      RealSymmetric2.low, RealSymmetric2.gap, RealSymmetric2.lowDenom,
      high, gap, mA, mC, mD, rad, A, C, D, X]
    ring
  have hQpath : ∀ r : ℝ,
      numeratorLow r / denom r =
        (independentRadiusFirstGradient (θ, r)).1 := by
    intro r
    simp [independentRadiusFirstSpectral, independentRadiusFirstGradient,
      independentRadiusFirstMetricTriple, independentRadiusFirstResiduals,
      independentRadiusFirstGradientResiduals, RealSymmetric2.high,
      RealSymmetric2.low, RealSymmetric2.gap, RealSymmetric2.lowDenom,
      numeratorLow, denom, denomRad, low, gap, mA, mC, mD, rad, A, C, D,
      q, u, X]
    ring
  have hUpath : ∀ r : ℝ,
      numeratorHigh r / denom r =
        (independentRadiusFirstGradient (θ, r)).2 := by
    intro r
    simp [independentRadiusFirstSpectral, independentRadiusFirstGradient,
      independentRadiusFirstMetricTriple, independentRadiusFirstResiduals,
      independentRadiusFirstGradientResiduals, RealSymmetric2.high,
      RealSymmetric2.low, RealSymmetric2.gap, RealSymmetric2.lowDenom,
      numeratorHigh, denom, denomRad, low, gap, mA, mC, mD, rad, A, C, D,
      q, u, X]
    ring
  have hLfinal := hL.congrFunction (fun r ↦ (hLpath r).symm)
  have hHfinal := hhigh.congrFunction (fun r ↦ (hHpath r).symm)
  have hQfinal := hQ.congrFunction (fun r ↦ (hQpath r).symm)
  have hUfinal := hU.congrFunction (fun r ↦ (hUpath r).symm)
  have hLout : HasQuadraticGerm
      (fun r ↦ (independentRadiusFirstSpectral (θ, r)).1)
      2 (θ.1 * (2 * θ.2.2 + θ.2.1 + 4))
        (θ.2.1 * θ.2.2 * θ.1 ^ 2 + 4 * θ.2.2 * θ.1 ^ 2 +
          2 * θ.2.1 * θ.1 ^ 2 - 10 * θ.1 ^ 2 + 2) := by
    apply hLfinal.congrCoefficients
    · rfl
    · rfl
    · dsimp [b, P, J]
      ring
  have hHout : HasQuadraticGerm
      (fun r ↦ (independentRadiusFirstSpectral (θ, r)).2)
      1 (-2 * θ.1) (6 * θ.1 ^ 2) := by
    apply hHfinal.congrCoefficients
    · rfl
    · rfl
    · rfl
  have hQout : HasQuadraticGerm
      (fun r ↦ (independentRadiusFirstGradient (θ, r)).1)
      1 (-2 * θ.1)
        (-2 * θ.2.1 * θ.1 ^ 2 / 3 + 4 * θ.1 ^ 2 - 5 / 2) := by
    apply hQfinal.congrCoefficients
    · rfl
    · rfl
    · rfl
  have hUout : HasQuadraticGerm
      (fun r ↦ (independentRadiusFirstGradient (θ, r)).2)
      1 (θ.1 * (θ.2.1 - 6) / 3)
        (-2 * θ.2.2 * θ.1 ^ 2 - θ.2.1 * θ.1 ^ 2 - 1 / 2) := by
    apply hUfinal.congrCoefficients
    · rfl
    · rfl
    · rfl
  exact ⟨hLout, hHout, hQout, hUout⟩

/-! The next certificate is the algebraic second-leg transport.  It is kept
separate from the raw-step identification so that the latter can be supplied
by the mixed-expansion owner without changing this chart calculation. -/

/-- Helper for Appendix Lemma A.6: the explicit component germs for the second
normalized residual and gradient paths are obtained by composing the rational
normal form with the first-leg factor germs. -/
theorem independentRadiusSecondComponentQuadraticGerms
    (θ : ℝ × ℝ × ℝ) :
    HasQuadraticGerm
        (fun r ↦
          (independentSecondResiduals θ.1 r
            (independentRadiusFirstSpectral (θ, r)).1
            (independentRadiusFirstSpectral (θ, r)).2
            (independentRadiusFirstGradient (θ, r)).1
            (independentRadiusFirstGradient (θ, r)).2).1)
        6 (θ.1 * (30 * θ.2.2 + 7 * θ.2.1 + 204) / 3)
          ((12 * θ.2.2 ^ 2 * θ.1 ^ 2 + 11 * θ.2.2 * θ.2.1 * θ.1 ^ 2 +
              540 * θ.2.2 * θ.1 ^ 2 - θ.2.1 ^ 2 * θ.1 ^ 2 +
              78 * θ.2.1 * θ.1 ^ 2 + 2058 * θ.1 ^ 2 - 66) / 3) ∧
      HasQuadraticGerm
        (fun r ↦
          (independentSecondResiduals θ.1 r
            (independentRadiusFirstSpectral (θ, r)).1
            (independentRadiusFirstSpectral (θ, r)).2
            (independentRadiusFirstGradient (θ, r)).1
            (independentRadiusFirstGradient (θ, r)).2).2.1)
        2 (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3)
          ((3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 + 432 * θ.2.2 * θ.1 ^ 2 -
              θ.2.1 ^ 2 * θ.1 ^ 2 + 72 * θ.2.1 * θ.1 ^ 2 +
              2538 * θ.1 ^ 2 - 126) / 9) ∧
      HasQuadraticGerm
        (fun r ↦
          (independentSecondResiduals θ.1 r
            (independentRadiusFirstSpectral (θ, r)).1
            (independentRadiusFirstSpectral (θ, r)).2
            (independentRadiusFirstGradient (θ, r)).1
            (independentRadiusFirstGradient (θ, r)).2).2.2)
        1 (8 * θ.1)
          (4 * (6 * θ.2.2 * θ.1 ^ 2 + θ.2.1 * θ.1 ^ 2 +
              78 * θ.1 ^ 2 - 3) / 3) ∧
      HasQuadraticGerm
        (fun r ↦
          (independentSecondGradientResiduals θ.1 r
            (independentRadiusFirstSpectral (θ, r)).1
            (independentRadiusFirstSpectral (θ, r)).2
            (independentRadiusFirstGradient (θ, r)).1
            (independentRadiusFirstGradient (θ, r)).2).1)
        1 0
          ((24 * θ.2.2 * θ.1 ^ 2 - 4 * θ.2.1 * θ.1 ^ 2 +
              384 * θ.1 ^ 2 - 81) / 18) ∧
      HasQuadraticGerm
        (fun r ↦
          (independentSecondGradientResiduals θ.1 r
            (independentRadiusFirstSpectral (θ, r)).1
            (independentRadiusFirstSpectral (θ, r)).2
            (independentRadiusFirstGradient (θ, r)).1
            (independentRadiusFirstGradient (θ, r)).2).2)
        0 (-θ.1 * (6 * θ.2.2 - θ.2.1 + 60) / 9)
          (-(3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 + 288 * θ.2.2 * θ.1 ^ 2 -
              θ.2.1 ^ 2 * θ.1 ^ 2 + 48 * θ.2.1 * θ.1 ^ 2 +
              1314 * θ.1 ^ 2 - 162) / 27) := by
  let b : ℝ := θ.1
  let P : ℝ := θ.2.1
  let J : ℝ := θ.2.2
  let X : ℝ → ℝ := fun r ↦ r
  let L : ℝ → ℝ := fun r ↦ (independentRadiusFirstSpectral (θ, r)).1
  let H : ℝ → ℝ := fun r ↦ (independentRadiusFirstSpectral (θ, r)).2
  let Q : ℝ → ℝ := fun r ↦ (independentRadiusFirstGradient (θ, r)).1
  let U : ℝ → ℝ := fun r ↦ (independentRadiusFirstGradient (θ, r)).2
  obtain ⟨hL0, hH0, hQ0, hU0⟩ := independentRadiusFirstFactorQuadraticGerms θ
  have hL : HasQuadraticGerm L 2 (b * (2 * J + P + 4))
      (J * P * b ^ 2 + 4 * J * b ^ 2 + 2 * P * b ^ 2 -
        10 * b ^ 2 + 2) := by
    apply hL0.congrCoefficients
    · rfl
    · rfl
    · dsimp [b, P, J]
      ring
  have hH : HasQuadraticGerm H 1 (-2 * b) (6 * b ^ 2) := by
    simpa only [H, b, P, J] using hH0
  have hQ : HasQuadraticGerm Q 1 (-2 * b)
      (-2 * P * b ^ 2 / 3 + 4 * b ^ 2 - 5 / 2) := by
    simpa only [Q, b, P, J] using hQ0
  have hU : HasQuadraticGerm U 1 (b * (P - 6) / 3)
      (-2 * J * b ^ 2 - P * b ^ 2 - 1 / 2) := by
    simpa only [U, b, P, J] using hU0
  have hX : HasQuadraticGerm X 0 1 0 := by
    apply (HasQuadraticGerm.model 0 1 0).congrFunction
    intro r
    simp [X, quadraticModel]
  let K : ℝ → ℝ := fun _ ↦ 2 * b
  have hK : HasQuadraticGerm K (2 * b) 0 0 := by
    apply (HasQuadraticGerm.model (2 * b) 0 0).congrFunction
    intro r
    simp [K, quadraticModel]
  have hXLQRaw := (hX.mul hL).mul hQ
  have hHUraw := hH.mul hU
  let w₁ : ℝ → ℝ := fun r ↦ X r * L r * Q r - K r * H r * U r
  let w₂ : ℝ → ℝ := fun r ↦ H r * U r - K r * X r * L r * Q r
  have hKHUraw := (hK.mul hH).mul hU
  have hw₁raw := hXLQRaw.sub hKHUraw
  have hw₁path : ∀ r : ℝ,
      w₁ r = X r * L r * Q r - K r * H r * U r := by
    intro r
    rfl
  have hw₁ := hw₁raw.congrFunction hw₁path
  have hKXLQraw := (hK.mul hXLQRaw)
  have hw₂raw := hHUraw.sub hKXLQraw
  have hw₂path : ∀ r : ℝ,
      w₂ r = H r * U r - K r * (X r * L r * Q r) := by
    intro r
    ring
  have hw₂ := hw₂raw.congrFunction hw₂path
  let β : ℝ → ℝ := fun r ↦ X r * L r * Q r * w₁ r + H r * U r * w₂ r
  let γ : ℝ → ℝ := fun r ↦ X r ^ 2 * L r * w₁ r ^ 2 + H r * w₂ r ^ 2
  have hβraw := hXLQRaw.mul hw₁ |>.add (hHUraw.mul hw₂)
  have hβpath : ∀ r : ℝ,
      β r = (X r * L r * Q r) * w₁ r + (H r * U r) * w₂ r := by
    intro r
    rfl
  have hβ := hβraw.congrFunction hβpath
  have hγraw := ((hX.mul hX).mul hL).mul (hw₁.mul hw₁) |>.add (hH.mul (hw₂.mul hw₂))
  have hγpath : ∀ r : ℝ,
      γ r = (X r * X r * L r) * (w₁ r * w₁ r) +
        H r * (w₂ r * w₂ r) := by
    intro r
    simp [γ, pow_two]
  have hγ := hγraw.congrFunction hγpath
  have hβbase :
      0 * 2 * 1 * (0 * 2 * 1 - 2 * b * 1 * 1) +
          1 * 1 * (1 * 1 - 2 * b * (0 * 2 * 1)) ≠ 0 := by
    norm_num
  have hγbase :
      0 * 0 * 2 * ((0 * 2 * 1 - 2 * b * 1 * 1) *
          (0 * 2 * 1 - 2 * b * 1 * 1)) +
          1 * ((1 * 1 - 2 * b * (0 * 2 * 1)) *
            (1 * 1 - 2 * b * (0 * 2 * 1))) ≠ 0 := by
    norm_num
  let A : ℝ → ℝ := fun r ↦
    L r - X r ^ 2 * L r ^ 2 * w₁ r ^ 2 / γ r + L r ^ 2 * Q r ^ 2 / β r
  let C : ℝ → ℝ := fun r ↦
    -(X r * L r * H r * w₁ r * w₂ r) / γ r +
      L r * Q r * H r * U r / β r
  let D : ℝ → ℝ := fun r ↦
    H r - H r ^ 2 * w₂ r ^ 2 / γ r + H r ^ 2 * U r ^ 2 / β r
  have htermAγ := (((hX.mul hX).mul (hL.mul hL)).mul (hw₁.mul hw₁)).div hγ hγbase
  have htermAβ := ((hL.mul hL).mul (hQ.mul hQ)).div hβ hβbase
  have hAraw := (hL.sub htermAγ).add htermAβ
  have hApath : ∀ r : ℝ,
      A r = L r - X r * X r * (L r * L r) * (w₁ r * w₁ r) / γ r +
        (L r * L r) * (Q r * Q r) / β r := by
    intro r
    simp [A, pow_two]
  have hAraw' := hAraw.congrFunction hApath
  have hA : HasQuadraticGerm A 6
      (b * (30 * J + 7 * P + 204) / 3)
      ((12 * J ^ 2 * b ^ 2 + 11 * J * P * b ^ 2 + 540 * J * b ^ 2 -
          P ^ 2 * b ^ 2 + 78 * P * b ^ 2 + 2058 * b ^ 2 - 66) / 3) := by
    apply hAraw'.congrCoefficients
    · ring
    · ring
    · ring
  have htermCγ := (((((hX.mul hL).mul hH).mul hw₁).mul hw₂).div hγ hγbase).neg
  have htermCβ := (((hL.mul hQ).mul hH).mul hU).div hβ hβbase
  have hCraw := htermCγ.add htermCβ
  have hCpath : ∀ r : ℝ,
      C r = -(X r * L r * H r * w₁ r * w₂ r / γ r) +
        L r * Q r * H r * U r / β r := by
    intro r
    simp [C]
    ring
  have hCraw' := hCraw.congrFunction hCpath
  have hC : HasQuadraticGerm C 2
      (b * (6 * J + P + 84) / 3)
      ((3 * P * J * b ^ 2 + 432 * J * b ^ 2 - P ^ 2 * b ^ 2 +
          72 * P * b ^ 2 + 2538 * b ^ 2 - 126) / 9) := by
    apply hCraw'.congrCoefficients
    · ring
    · ring
    · ring
  have htermDγ := ((hH.mul hH).mul (hw₂.mul hw₂)).div hγ hγbase
  have htermDβ := ((hH.mul hH).mul (hU.mul hU)).div hβ hβbase
  have hDraw := (hH.sub htermDγ).add htermDβ
  have hDpath : ∀ r : ℝ,
      D r = H r - H r * H r * (w₂ r * w₂ r) / γ r +
        H r * H r * (U r * U r) / β r := by
    intro r
    simp [D, pow_two]
  have hDraw' := hDraw.congrFunction hDpath
  have hD : HasQuadraticGerm D 1 (8 * b)
      (4 * (6 * J * b ^ 2 + P * b ^ 2 + 78 * b ^ 2 - 3) / 3) := by
    apply hDraw'.congrCoefficients
    · ring
    · ring
    · ring
  let δ : ℝ → ℝ := fun r ↦ L r * Q r ^ 2 + H r * U r ^ 2
  have hδraw := (hL.mul (hQ.mul hQ)).add (hH.mul (hU.mul hU))
  have hδpath : ∀ r : ℝ,
      δ r = L r * (Q r * Q r) + H r * (U r * U r) := by
    intro r
    simp [δ, pow_two]
  have hδ := hδraw.congrFunction hδpath
  let threeβ : ℝ → ℝ := fun r ↦ 3 * β r
  have hthreeβ := hβ.constMul 3
  have hthree :
      3 * (0 * 2 * 1 * (0 * 2 * 1 - 2 * b * 1 * 1) +
        1 * 1 * (1 * 1 - 2 * b * (0 * 2 * 1))) ≠ 0 := by
    norm_num
  let q : ℝ → ℝ := fun r ↦ Q r - X r * δ r * w₁ r / threeβ r
  let u : ℝ → ℝ := fun r ↦ U r - δ r * w₂ r / threeβ r
  have hqraw := hQ.sub (((hX.mul hδ).mul hw₁).div hthreeβ hthree)
  have huRaw := hU.sub ((hδ.mul hw₂).div hthreeβ hthree)
  have hqpath : ∀ r : ℝ,
      q r = Q r - X r * δ r * w₁ r / (3 * β r) := by
    intro r
    rfl
  have hupath : ∀ r : ℝ,
      u r = U r - δ r * w₂ r / (3 * β r) := by
    intro r
    rfl
  have hqraw' := hqraw.congrFunction hqpath
  have huRaw' := huRaw.congrFunction hupath
  have hq : HasQuadraticGerm q 1 0
      ((24 * J * b ^ 2 - 4 * P * b ^ 2 + 384 * b ^ 2 - 81) / 18) := by
    apply hqraw'.congrCoefficients
    · ring
    · ring
    · ring
  have hu : HasQuadraticGerm u 0
      (-b * (6 * J - P + 60) / 9)
      (-(3 * P * J * b ^ 2 + 288 * J * b ^ 2 - P ^ 2 * b ^ 2 +
          48 * P * b ^ 2 + 1314 * b ^ 2 - 162) / 27) := by
    apply huRaw'.congrCoefficients
    · ring
    · ring
    · ring
  have hApath : ∀ r : ℝ,
      A r = (independentSecondResiduals θ.1 r (L r) (H r) (Q r) (U r)).1 := by
    intro r
    simp [b, A, independentSecondResiduals, β, γ, w₁, w₂, X, K]
  have hCpath : ∀ r : ℝ,
      C r = (independentSecondResiduals θ.1 r (L r) (H r) (Q r) (U r)).2.1 := by
    intro r
    simp [b, C, independentSecondResiduals, β, γ, w₁, w₂, X, K]
  have hDpath : ∀ r : ℝ,
      D r = (independentSecondResiduals θ.1 r (L r) (H r) (Q r) (U r)).2.2 := by
    intro r
    simp [b, D, independentSecondResiduals, β, γ, w₁, w₂, X, K]
  have hqpath : ∀ r : ℝ,
      q r = (independentSecondGradientResiduals θ.1 r (L r) (H r) (Q r) (U r)).1 := by
    intro r
    simp [b, q, independentSecondGradientResiduals, threeβ, δ, β, w₁, w₂, X, K]
  have hupath : ∀ r : ℝ,
      u r = (independentSecondGradientResiduals θ.1 r (L r) (H r) (Q r) (U r)).2 := by
    intro r
    simp [b, u, independentSecondGradientResiduals, threeβ, δ, β, w₁, w₂, X, K]
  have hAout := hA.congrFunction (fun r ↦ (hApath r).symm)
  have hCout := hC.congrFunction (fun r ↦ (hCpath r).symm)
  have hDout := hD.congrFunction (fun r ↦ (hDpath r).symm)
  have hqout := hq.congrFunction (fun r ↦ (hqpath r).symm)
  have huout := hu.congrFunction (fun r ↦ (hupath r).symm)
  have hAout' : HasQuadraticGerm
      (fun r ↦
        (independentSecondResiduals θ.1 r
          (independentRadiusFirstSpectral (θ, r)).1
          (independentRadiusFirstSpectral (θ, r)).2
          (independentRadiusFirstGradient (θ, r)).1
          (independentRadiusFirstGradient (θ, r)).2).1)
      6 (θ.1 * (30 * θ.2.2 + 7 * θ.2.1 + 204) / 3)
        ((12 * θ.2.2 ^ 2 * θ.1 ^ 2 + 11 * θ.2.2 * θ.2.1 * θ.1 ^ 2 +
            540 * θ.2.2 * θ.1 ^ 2 - θ.2.1 ^ 2 * θ.1 ^ 2 +
            78 * θ.2.1 * θ.1 ^ 2 + 2058 * θ.1 ^ 2 - 66) / 3) := by
    apply hAout.congrCoefficients
    · rfl
    · dsimp [b, P, J]
    · dsimp [b, P, J]
  have hCout' : HasQuadraticGerm
      (fun r ↦
        (independentSecondResiduals θ.1 r
          (independentRadiusFirstSpectral (θ, r)).1
          (independentRadiusFirstSpectral (θ, r)).2
          (independentRadiusFirstGradient (θ, r)).1
          (independentRadiusFirstGradient (θ, r)).2).2.1)
      2 (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3)
        ((3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 + 432 * θ.2.2 * θ.1 ^ 2 -
            θ.2.1 ^ 2 * θ.1 ^ 2 + 72 * θ.2.1 * θ.1 ^ 2 +
            2538 * θ.1 ^ 2 - 126) / 9) := by
    apply hCout.congrCoefficients
    · rfl
    · dsimp [b, P, J]
    · dsimp [b, P, J]
  have hDout' : HasQuadraticGerm
      (fun r ↦
        (independentSecondResiduals θ.1 r
          (independentRadiusFirstSpectral (θ, r)).1
          (independentRadiusFirstSpectral (θ, r)).2
          (independentRadiusFirstGradient (θ, r)).1
          (independentRadiusFirstGradient (θ, r)).2).2.2)
      1 (8 * θ.1)
        (4 * (6 * θ.2.2 * θ.1 ^ 2 + θ.2.1 * θ.1 ^ 2 +
            78 * θ.1 ^ 2 - 3) / 3) := by
    apply hDout.congrCoefficients
    · rfl
    · dsimp [b]
    · dsimp [b, P, J]
  have hqout' : HasQuadraticGerm
      (fun r ↦
        (independentSecondGradientResiduals θ.1 r
          (independentRadiusFirstSpectral (θ, r)).1
          (independentRadiusFirstSpectral (θ, r)).2
          (independentRadiusFirstGradient (θ, r)).1
          (independentRadiusFirstGradient (θ, r)).2).1)
      1 0 ((24 * θ.2.2 * θ.1 ^ 2 - 4 * θ.2.1 * θ.1 ^ 2 +
        384 * θ.1 ^ 2 - 81) / 18) := by
    apply hqout.congrCoefficients
    · rfl
    · rfl
    · dsimp [b, P, J]
  have huout' : HasQuadraticGerm
      (fun r ↦
        (independentSecondGradientResiduals θ.1 r
          (independentRadiusFirstSpectral (θ, r)).1
          (independentRadiusFirstSpectral (θ, r)).2
          (independentRadiusFirstGradient (θ, r)).1
          (independentRadiusFirstGradient (θ, r)).2).2)
      0 (-θ.1 * (6 * θ.2.2 - θ.2.1 + 60) / 9)
        (-(3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 + 288 * θ.2.2 * θ.1 ^ 2 -
            θ.2.1 ^ 2 * θ.1 ^ 2 + 48 * θ.2.1 * θ.1 ^ 2 +
            1314 * θ.1 ^ 2 - 162) / 27) := by
    apply huout.congrCoefficients
    · rfl
    · dsimp [b, P, J]
    · dsimp [b, P, J]
  exact ⟨hAout', hCout', hDout', hqout', huout'⟩

/-- Appendix Lemma A.6: the normalized second-gradient low coordinate has the
displayed quadratic germ along the independent-radius path. -/
theorem independentRadiusSecondGradientLow_quadraticGerm
    (θ : ℝ × ℝ × ℝ) :
    HasQuadraticGerm
      (fun r ↦ (independentRadiusSecondGradient (θ, r)).1)
      1 0 ((θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18) := by
  obtain ⟨hA, hC, hD, hq, hu⟩ :=
    independentRadiusSecondComponentQuadraticGerms θ
  let radius : ℝ → ℝ := fun r ↦ r
  let residualA : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2).1
  let residualC : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2).2.1
  let residualD : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2).2.2
  let residualQ : ℝ → ℝ := fun r ↦
    (independentSecondGradientResiduals θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2).1
  let residualU : ℝ → ℝ := fun r ↦
    (independentSecondGradientResiduals θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2).2
  have hA' : HasQuadraticGerm residualA 6
      (θ.1 * (30 * θ.2.2 + 7 * θ.2.1 + 204) / 3)
      ((12 * θ.2.2 ^ 2 * θ.1 ^ 2 + 11 * θ.2.2 * θ.2.1 * θ.1 ^ 2 +
          540 * θ.2.2 * θ.1 ^ 2 - θ.2.1 ^ 2 * θ.1 ^ 2 +
          78 * θ.2.1 * θ.1 ^ 2 + 2058 * θ.1 ^ 2 - 66) / 3) := by
    simpa only [residualA] using hA
  have hC' : HasQuadraticGerm residualC 2
      (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3)
      ((3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 + 432 * θ.2.2 * θ.1 ^ 2 -
          θ.2.1 ^ 2 * θ.1 ^ 2 + 72 * θ.2.1 * θ.1 ^ 2 +
          2538 * θ.1 ^ 2 - 126) / 9) := by
    simpa only [residualC] using hC
  have hD' : HasQuadraticGerm residualD 1 (8 * θ.1)
      (4 * (6 * θ.2.2 * θ.1 ^ 2 + θ.2.1 * θ.1 ^ 2 +
        78 * θ.1 ^ 2 - 3) / 3) := by
    simpa only [residualD] using hD
  have hq' : HasQuadraticGerm residualQ 1 0
      ((24 * θ.2.2 * θ.1 ^ 2 - 4 * θ.2.1 * θ.1 ^ 2 +
        384 * θ.1 ^ 2 - 81) / 18) := by
    simpa only [residualQ] using hq
  have hu' : HasQuadraticGerm residualU 0
      (-θ.1 * (6 * θ.2.2 - θ.2.1 + 60) / 9)
      (-(3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 + 288 * θ.2.2 * θ.1 ^ 2 -
        θ.2.1 ^ 2 * θ.1 ^ 2 + 48 * θ.2.1 * θ.1 ^ 2 +
        1314 * θ.1 ^ 2 - 162) / 27) := by
    simpa only [residualU] using hu
  have hradius : HasQuadraticGerm radius 0 1 0 := by
    apply (HasQuadraticGerm.model 0 1 0).congrFunction
    intro r
    simp [radius, quadraticModel]
  let metricA : ℝ → ℝ := fun r ↦ radius r * radius r * residualA r
  let metricC : ℝ → ℝ := fun r ↦ radius r * residualC r
  let metricD : ℝ → ℝ := residualD
  let gradientQ : ℝ → ℝ := residualQ
  let gradientU : ℝ → ℝ := residualU
  have hmetricARaw := (hradius.mul hradius).mul hA'
  have hmetricAPath : ∀ r : ℝ,
      metricA r = radius r * radius r * residualA r := by
    intro r
    rfl
  have hmetricACoeff := hmetricARaw.congrFunction hmetricAPath
  have hmetricA : HasQuadraticGerm metricA 0 0 6 := by
    apply hmetricACoeff.congrCoefficients
    · ring
    · ring
    · ring
  have hmetricCRaw := hradius.mul hC'
  have hmetricCPath : ∀ r : ℝ,
      metricC r = radius r * residualC r := by
    intro r
    rfl
  have hmetricCCoeff := hmetricCRaw.congrFunction hmetricCPath
  have hmetricC : HasQuadraticGerm metricC 0 2
      (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) := by
    apply hmetricCCoeff.congrCoefficients
    · ring
    · ring
    · ring
  have hmetricD : HasQuadraticGerm metricD 1 (8 * θ.1)
      (4 * (6 * θ.2.2 * θ.1 ^ 2 + θ.2.1 * θ.1 ^ 2 +
        78 * θ.1 ^ 2 - 3) / 3) := by
    simpa only [metricD] using hD'
  have hgradientQ : HasQuadraticGerm gradientQ 1 0
      ((24 * θ.2.2 * θ.1 ^ 2 - 4 * θ.2.1 * θ.1 ^ 2 +
        384 * θ.1 ^ 2 - 81) / 18) := by
    simpa only [gradientQ] using hq'
  have hgradientU : HasQuadraticGerm gradientU 0
      (-θ.1 * (6 * θ.2.2 - θ.2.1 + 60) / 9)
      (-(3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 + 288 * θ.2.2 * θ.1 ^ 2 -
        θ.2.1 ^ 2 * θ.1 ^ 2 + 48 * θ.2.1 * θ.1 ^ 2 +
        1314 * θ.1 ^ 2 - 162) / 27) := by
    simpa only [gradientU] using hu'
  have hchartIdentity : ∀ (b : ℝ) (L H Q U : ℝ → ℝ) (r : ℝ),
      lowGradientChartPath
          (fun s ↦ s)
          (fun s ↦ s * s * (independentSecondResiduals b s (L s) (H s) (Q s) (U s)).1)
          (fun s ↦ s * (independentSecondResiduals b s (L s) (H s) (Q s) (U s)).2.1)
          (fun s ↦ (independentSecondResiduals b s (L s) (H s) (Q s) (U s)).2.2)
          (fun s ↦ (independentSecondGradientResiduals b s (L s) (H s) (Q s) (U s)).1)
          (fun s ↦ (independentSecondGradientResiduals b s (L s) (H s) (Q s) (U s)).2) r =
        (independentSecondGradientFactors b r (L r) (H r) (Q r) (U r)).1 := by
    intro b L H Q U r
    simp only [lowGradientChartPath, independentSecondGradientFactors,
      RealSymmetric2.gap_apply, RealSymmetric2.low_apply,
      RealSymmetric2.lowDenom_apply, pow_two]
    ring
  have hpath : ∀ r : ℝ,
      lowGradientChartPath radius metricA metricC metricD gradientQ gradientU r =
        (independentRadiusSecondGradient (θ, r)).1 := by
    intro r
    change lowGradientChartPath
        (fun s : ℝ ↦ s)
        (fun s ↦ s * s * residualA s)
        (fun s ↦ s * residualC s)
        residualD residualQ residualU r =
      (independentSecondGradientFactors θ.1 r
        (independentRadiusFirstSpectral (θ, r)).1
        (independentRadiusFirstSpectral (θ, r)).2
        (independentRadiusFirstGradient (θ, r)).1
        (independentRadiusFirstGradient (θ, r)).2).1
    have hidentity := hchartIdentity θ.1
      (fun s ↦ (independentRadiusFirstSpectral (θ, s)).1)
      (fun s ↦ (independentRadiusFirstSpectral (θ, s)).2)
      (fun s ↦ (independentRadiusFirstGradient (θ, s)).1)
      (fun s ↦ (independentRadiusFirstGradient (θ, s)).2) r
    simpa only [residualA, residualC, residualD, residualQ, residualU] using hidentity
  exact independentRadiusSecondGradientLow_quadraticGerm_of_explicitComponentCertificates
    θ hradius hmetricA hmetricC hmetricD hgradientQ hgradientU hpath

end DFP.TwoLeg.Mixed
