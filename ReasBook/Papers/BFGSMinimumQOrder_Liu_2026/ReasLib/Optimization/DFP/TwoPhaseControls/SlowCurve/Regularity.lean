module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.Positivity
import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.OrbitBounds
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg

public section

open Filter
open scoped Matrix Topology

namespace DFP.TwoLeg

/-- Any property holding near `(0, 2, 1)` holds along every sufficiently small forward
orbit on an invariant slow graph. -/
private theorem eventuallyOnSmallSlowCurveOrbits (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (εbar : ℝ) (h_εbar : εbar ∈ Set.Ioo 0 (1 / 4))
    (P : ℝ × ℝ × ℝ → Prop)
    (hP : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), P x) :
    ∃ ε₀ ∈ Set.Ioc 0 εbar, ∀ ε ∈ Set.Ioc 0 ε₀, ∀ n : ℕ,
      P (stateMap^[n] (ε, p ε, h ε)) := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hpowFiveTendsto : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num
  have hp₀Tendsto : Tendsto p₀ (𝓝 0) (𝓝 2) := by
    have hcontinuous : ContinuousAt p₀ 0 := by
      dsimp only [p₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [p₀]
  have hh₀Tendsto : Tendsto h₀ (𝓝 0) (𝓝 1) := by
    have hcontinuous : ContinuousAt h₀ 0 := by
      dsimp only [h₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [h₀]
  have hpDiff : (fun ε ↦ p ε - p₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀] using h_pJet
  have hhDiff : (fun ε ↦ h ε - h₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀] using h_hJet
  have hpTendsto : Tendsto p (𝓝 0) (𝓝 2) := by
    simpa only [sub_add_cancel, zero_add] using
      (hpDiff.trans_tendsto hpowFiveTendsto).add hp₀Tendsto
  have hhTendsto : Tendsto h (𝓝 0) (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using
      (hhDiff.trans_tendsto hpowFiveTendsto).add hh₀Tendsto
  have hgraphTendsto : Tendsto (fun ε : ℝ ↦ (ε, p ε, h ε)) (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    simpa only [id_eq, nhds_prod_eq] using
      tendsto_id.prodMk (hpTendsto.prodMk hhTendsto)
  have hPAlong : ∀ᶠ ε in 𝓝 (0 : ℝ), P (ε, p ε, h ε) :=
    hgraphTendsto.eventually hP
  obtain ⟨r, hr, hrule⟩ := Metric.eventually_nhds_iff.mp hPAlong
  obtain ⟨η, hη, horbit⟩ :=
    slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let ε₀ := min εbar (min η (r / 2))
  have hε₀pos : 0 < ε₀ := by
    exact lt_min h_εbar.1 (lt_min hη.1 (half_pos hr))
  have hε₀le : ε₀ ≤ εbar := min_le_left _ _
  refine ⟨ε₀, ⟨hε₀pos, hε₀le⟩, ?_⟩
  intro ε hε n
  have hεη : ε ≤ η := by
    exact hε.2.trans
      ((min_le_right εbar (min η (r / 2))).trans (min_le_left η (r / 2)))
  have hεrhalf : ε ≤ r / 2 := by
    exact hε.2.trans
      ((min_le_right εbar (min η (r / 2))).trans (min_le_right η (r / 2)))
  have hxn := horbit ε ⟨hε.1, hεη⟩ n
  dsimp only at hxn
  have hscaleR : (stateMap^[n] (ε, p ε, h ε)).1 < r := by
    exact hxn.2.2.trans_lt (hεrhalf.trans_lt (half_lt_self hr))
  have hdist : dist (stateMap^[n] (ε, p ε, h ε)).1 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hxn.2.1]
    exact hscaleR
  rw [hxn.1]
  exact hrule hdist

/-- The ten removable factors from the two DFP legs, ordered as in
`slowCurveFactorsUniformlyPositive`. -/
private noncomputable def removableFactorVector
    (x : ℝ × ℝ × ℝ) : Fin 10 → ℝ :=
  let spectral₁ := DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2
  let gradient₁ := DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2
  let canonical₁ := DFP.FirstLeg.canonicalFactors x.1 x.2.1 x.2.2
  let spectral₂ := DFP.SecondLeg.spectralFactors x.1 x.2.1 x.2.2
  let gradient₂ := DFP.SecondLeg.gradientFactors x.1 x.2.1 x.2.2
  let canonical₂ := DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2
  ![spectral₁.1, spectral₁.2, gradient₁.1, gradient₁.2, canonical₁.1,
    spectral₂.1, spectral₂.2, gradient₂.1, gradient₂.2, canonical₂.1]

/-- Each coordinate of the two-leg removable-factor vector is continuous at the
common zero-scale base point. -/
private theorem removableFactorVector_continuousAt (i : Fin 10) : ContinuousAt
    (fun x : ℝ × ℝ × ℝ ↦ removableFactorVector x i) (0, 2, 1) := by
  have hFirstSpectral : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2)
      (0, 2, 1) :=
    analyticAt_fst.comp DFP.FirstLeg.factorsAnalytic
  have hFirstGradient : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2)
      (0, 2, 1) :=
    (analyticAt_fst.comp analyticAt_snd).comp DFP.FirstLeg.factorsAnalytic
  have hFirstCanonical : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.canonicalFactors x.1 x.2.1 x.2.2)
      (0, 2, 1) :=
    (analyticAt_snd.comp analyticAt_snd).comp DFP.FirstLeg.factorsAnalytic
  have hSecondSpectral : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ DFP.SecondLeg.spectralFactors x.1 x.2.1 x.2.2)
      (0, 2, 1) :=
    analyticAt_fst.comp DFP.SecondLeg.factorsAnalytic
  have hSecondGradient : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ DFP.SecondLeg.gradientFactors x.1 x.2.1 x.2.2)
      (0, 2, 1) :=
    (analyticAt_fst.comp analyticAt_snd).comp DFP.SecondLeg.factorsAnalytic
  have hSecondCanonical : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2)
      (0, 2, 1) :=
    (analyticAt_snd.comp analyticAt_snd).comp DFP.SecondLeg.factorsAnalytic
  fin_cases i
  · change ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
      (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).1) (0, 2, 1)
    exact (analyticAt_fst.comp hFirstSpectral).continuousAt
  · change ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
      (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).2) (0, 2, 1)
    exact (analyticAt_snd.comp hFirstSpectral).continuousAt
  · change ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
      (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1) (0, 2, 1)
    exact (analyticAt_fst.comp hFirstGradient).continuousAt
  · change ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
      (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2) (0, 2, 1)
    exact (analyticAt_snd.comp hFirstGradient).continuousAt
  · change ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
      (DFP.FirstLeg.canonicalFactors x.1 x.2.1 x.2.2).1) (0, 2, 1)
    exact (analyticAt_fst.comp hFirstCanonical).continuousAt
  · change ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
      (DFP.SecondLeg.spectralFactors x.1 x.2.1 x.2.2).1) (0, 2, 1)
    exact (analyticAt_fst.comp hSecondSpectral).continuousAt
  · change ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
      (DFP.SecondLeg.spectralFactors x.1 x.2.1 x.2.2).2) (0, 2, 1)
    exact (analyticAt_snd.comp hSecondSpectral).continuousAt
  · change ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
      (DFP.SecondLeg.gradientFactors x.1 x.2.1 x.2.2).1) (0, 2, 1)
    exact (analyticAt_fst.comp hSecondGradient).continuousAt
  · change ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
      (DFP.SecondLeg.gradientFactors x.1 x.2.1 x.2.2).2) (0, 2, 1)
    exact (analyticAt_snd.comp hSecondGradient).continuousAt
  · change ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
      (DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2).1) (0, 2, 1)
    exact (analyticAt_fst.comp hSecondCanonical).continuousAt

/-- At `(0, 2, 1)`, every entry of the two-leg removable-factor vector is at least one. -/
private theorem removableFactorVector_base :
    removableFactorVector ((0, 2, 1) : ℝ × ℝ × ℝ) =
      ![(2 : ℝ), 1, 1, 1, 2, 2, 1, 1, 2, 1] := by
  have hFirstSpectral : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hFirstGradient : DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase
  have hFirstCanonical : DFP.FirstLeg.canonicalFactors 0 2 1 = (2, 1 / 2) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y ↦ y.2.2) DFP.FirstLeg.factorsBase
  have hSecondSpectral : DFP.SecondLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.SecondLeg.factors] using
      congrArg Prod.fst DFP.SecondLeg.factorsBase
  have hSecondGradient : DFP.SecondLeg.gradientFactors 0 2 1 = (1, 2) := by
    simpa only [DFP.SecondLeg.factors] using
      congrArg (fun y ↦ y.2.1) DFP.SecondLeg.factorsBase
  have hSecondCanonical : DFP.SecondLeg.canonicalFactors 0 2 1 = (1, 2) := by
    simpa only [DFP.SecondLeg.factors] using
      congrArg (fun y ↦ y.2.2) DFP.SecondLeg.factorsBase
  simp only [removableFactorVector]
  rw [hFirstSpectral, hFirstGradient, hFirstCanonical, hSecondSpectral,
    hSecondGradient, hSecondCanonical]

/-- Near `(0, 2, 1)`, all ten removable factors are bounded below by `1 / 2`. -/
private theorem removableFactorVector_eventually_half_le :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      ∀ i, (1 / 2 : ℝ) ≤ removableFactorVector x i := by
  apply Filter.eventually_all.mpr
  intro i
  have hbase : (1 / 2 : ℝ) <
      removableFactorVector ((0, 2, 1) : ℝ × ℝ × ℝ) i := by
    rw [removableFactorVector_base]
    fin_cases i
    all_goals norm_num
  have heventually := (removableFactorVector_continuousAt i).eventually
    (Ioi_mem_nhds hbase)
  exact heventually.mono fun _ hx ↦ hx.le

/-- In a neighborhood of `(0, 2, 1)`, the explicit eigenvalues of both output metrics
are strictly ordered. -/
private theorem twoLegSpectraEventuallyOrdered :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      (DFP.FirstLeg.eigenvalues x.1 x.2.1 x.2.2).1 <
          (DFP.FirstLeg.eigenvalues x.1 x.2.1 x.2.2).2 ∧
        (DFP.SecondLeg.eigenvalues x.1 x.2.1 x.2.2).1 <
          (DFP.SecondLeg.eigenvalues x.1 x.2.1 x.2.2).2 := by
  have hFirstSpectral : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2)
      (0, 2, 1) :=
    analyticAt_fst.comp DFP.FirstLeg.factorsAnalytic
  have hSecondSpectral : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ DFP.SecondLeg.spectralFactors x.1 x.2.1 x.2.2)
      (0, 2, 1) :=
    analyticAt_fst.comp DFP.SecondLeg.factorsAnalytic
  have hFirstDifference : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦
      (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).2 -
        x.1 ^ 4 * (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).1)
      (0, 2, 1) :=
    (analyticAt_snd.comp hFirstSpectral).sub
      ((analyticAt_fst.pow 4).mul (analyticAt_fst.comp hFirstSpectral))
  have hSecondDifference : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦
      (DFP.SecondLeg.spectralFactors x.1 x.2.1 x.2.2).2 -
        x.1 ^ 4 * (DFP.SecondLeg.spectralFactors x.1 x.2.1 x.2.2).1)
      (0, 2, 1) :=
    (analyticAt_snd.comp hSecondSpectral).sub
      ((analyticAt_fst.pow 4).mul (analyticAt_fst.comp hSecondSpectral))
  have hFirstSpectralBase : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hSecondSpectralBase : DFP.SecondLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.SecondLeg.factors] using
      congrArg Prod.fst DFP.SecondLeg.factorsBase
  have hFirstPositive : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      0 < (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).2 -
        x.1 ^ 4 * (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).1 := by
    apply hFirstDifference.continuousAt.eventually
    have hbase : 0 < (DFP.FirstLeg.spectralFactors 0 2 1).2 -
        0 ^ 4 * (DFP.FirstLeg.spectralFactors 0 2 1).1 := by
      rw [hFirstSpectralBase]
      norm_num
    exact Ioi_mem_nhds hbase
  have hSecondPositive : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      0 < (DFP.SecondLeg.spectralFactors x.1 x.2.1 x.2.2).2 -
        x.1 ^ 4 * (DFP.SecondLeg.spectralFactors x.1 x.2.1 x.2.2).1 := by
    apply hSecondDifference.continuousAt.eventually
    have hbase : 0 < (DFP.SecondLeg.spectralFactors 0 2 1).2 -
        0 ^ 4 * (DFP.SecondLeg.spectralFactors 0 2 1).1 := by
      rw [hSecondSpectralBase]
      norm_num
    exact Ioi_mem_nhds hbase
  have hFirstOrdered : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      (DFP.FirstLeg.eigenvalues x.1 x.2.1 x.2.2).1 <
        (DFP.FirstLeg.eigenvalues x.1 x.2.1 x.2.2).2 := by
    filter_upwards [DFP.FirstLeg.spectrumFactorization, hFirstPositive]
      with x hspectrum hpositive
    rw [hspectrum]
    dsimp only
    linarith
  have hSecondOrdered : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      (DFP.SecondLeg.eigenvalues x.1 x.2.1 x.2.2).1 <
        (DFP.SecondLeg.eigenvalues x.1 x.2.1 x.2.2).2 := by
    filter_upwards [DFP.SecondLeg.spectrumFactorization, hSecondPositive]
      with x hspectrum hpositive
    rw [hspectrum]
    dsimp only
    linarith
  exact hFirstOrdered.and hSecondOrdered

/-- Along every sufficiently small orbit on an invariant slow graph, the ten removable
factors from the two legs share a strictly positive lower bound. -/
theorem slowCurveFactorsUniformlyPositive (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5))
    (εbar : ℝ) (h_εbar : εbar ∈ Set.Ioo 0 (1 / 4)) :
    ∃ ε₀ ∈ Set.Ioc 0 εbar, ∃ m > 0, ∀ ε ∈ Set.Ioc 0 ε₀, ∀ n : ℕ,
      let xₙ := stateMap^[n] (ε, p ε, h ε)
      let spectral₁ := DFP.FirstLeg.spectralFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let gradient₁ := DFP.FirstLeg.gradientFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let canonical₁ := DFP.FirstLeg.canonicalFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let spectral₂ := DFP.SecondLeg.spectralFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let gradient₂ := DFP.SecondLeg.gradientFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let canonical₂ := DFP.SecondLeg.canonicalFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let factors : Fin 10 → ℝ :=
        ![spectral₁.1, spectral₁.2, gradient₁.1, gradient₁.2, canonical₁.1,
          spectral₂.1, spectral₂.2, gradient₂.1, gradient₂.2, canonical₂.1]
      ∀ i, m ≤ factors i := by
  let P : ℝ × ℝ × ℝ → Prop := fun x ↦
    ∀ i, (1 / 2 : ℝ) ≤ removableFactorVector x i
  obtain ⟨ε₀, hε₀, horbit⟩ := eventuallyOnSmallSlowCurveOrbits
    p h h_invariant h_pJet h_hJet εbar h_εbar P
      removableFactorVector_eventually_half_le
  have hhalf : 0 < (1 / 2 : ℝ) := by
    norm_num
  refine ⟨ε₀, hε₀, 1 / 2, hhalf, ?_⟩
  intro ε hε n
  dsimp only
  have hbound := horbit ε hε n
  simpa only [P, removableFactorVector] using hbound

/-- Along every sufficiently small orbit on an invariant slow graph, both eigenvalues
of each leg's output metric have algebraic multiplicity one. -/
theorem slowCurveSpectraSimple (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5))
    (εbar : ℝ) (h_εbar : εbar ∈ Set.Ioo 0 (1 / 4)) :
    ∃ ε₀ ∈ Set.Ioc 0 εbar, ∀ ε ∈ Set.Ioc 0 ε₀, ∀ n : ℕ,
      let xₙ := stateMap^[n] (ε, p ε, h ε)
      let metrics : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ :=
        ![DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2,
          DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2]
      let eigenvalues : Fin 2 → Fin 2 → ℝ :=
        ![![
            (DFP.FirstLeg.eigenvalues xₙ.1 xₙ.2.1 xₙ.2.2).1,
            (DFP.FirstLeg.eigenvalues xₙ.1 xₙ.2.1 xₙ.2.2).2],
          ![
            (DFP.SecondLeg.eigenvalues xₙ.1 xₙ.2.1 xₙ.2.2).1,
            (DFP.SecondLeg.eigenvalues xₙ.1 xₙ.2.1 xₙ.2.2).2]]
      ∀ i j, (Matrix.toLin' (metrics i)).charpoly.rootMultiplicity (eigenvalues i j) = 1 := by
  let P : ℝ × ℝ × ℝ → Prop := fun x ↦
    (DFP.FirstLeg.eigenvalues x.1 x.2.1 x.2.2).1 <
        (DFP.FirstLeg.eigenvalues x.1 x.2.1 x.2.2).2 ∧
      (DFP.SecondLeg.eigenvalues x.1 x.2.1 x.2.2).1 <
        (DFP.SecondLeg.eigenvalues x.1 x.2.1 x.2.2).2
  obtain ⟨ε₀, hε₀, horbit⟩ := eventuallyOnSmallSlowCurveOrbits
    p h h_invariant h_pJet h_hJet εbar h_εbar P twoLegSpectraEventuallyOrdered
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε n
  have hordered := horbit ε hε n
  dsimp only [P] at hordered
  let xₙ := stateMap^[n] (ε, p ε, h ε)
  have hFirstLowHigh :
      RealSymmetric2.low
          (DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 0)
          (DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 1)
          (DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 1 1) <
        RealSymmetric2.high
          (DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 0)
          (DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 1)
          (DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 1 1) := by
    simpa only [xₙ, DFP.FirstLeg.eigenvalues] using hordered.1
  have hFirstGap : 0 < RealSymmetric2.gap
      (DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 0)
      (DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 1)
      (DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 1 1) :=
    (RealSymmetric2.low_lt_high_iff_gap_pos _ _ _).mp hFirstLowHigh
  have hFirstMetric : RealSymmetric2.matrix
      (DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 0)
      (DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 1)
      (DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 1 1) =
        DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 := by
    unfold DFP.FirstLeg.outputMetric RealSymmetric2.matrix
    rfl
  have hFirstLowMultiplicity := RealSymmetric2.rootMultiplicity_low
    (DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 0)
    (DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 1)
    (DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 1 1) hFirstGap
  have hFirstHighMultiplicity := RealSymmetric2.rootMultiplicity_high
    (DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 0)
    (DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 1)
    (DFP.FirstLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 1 1) hFirstGap
  rw [hFirstMetric] at hFirstLowMultiplicity hFirstHighMultiplicity
  have hSecondLowHigh :
      RealSymmetric2.low
          (DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 0)
          (DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 1)
          (DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 1 1) <
        RealSymmetric2.high
          (DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 0)
          (DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 1)
          (DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 1 1) := by
    simpa only [xₙ, DFP.SecondLeg.eigenvalues] using hordered.2
  have hSecondGap : 0 < RealSymmetric2.gap
      (DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 0)
      (DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 1)
      (DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 1 1) :=
    (RealSymmetric2.low_lt_high_iff_gap_pos _ _ _).mp hSecondLowHigh
  have hSecondMetric : RealSymmetric2.matrix
      (DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 0)
      (DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 1)
      (DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 1 1) =
        DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 := by
    unfold DFP.SecondLeg.outputMetric RealSymmetric2.matrix
    rfl
  have hSecondLowMultiplicity := RealSymmetric2.rootMultiplicity_low
    (DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 0)
    (DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 1)
    (DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 1 1) hSecondGap
  have hSecondHighMultiplicity := RealSymmetric2.rootMultiplicity_high
    (DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 0)
    (DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 0 1)
    (DFP.SecondLeg.outputMetric xₙ.1 xₙ.2.1 xₙ.2.2 1 1) hSecondGap
  rw [hSecondMetric] at hSecondLowMultiplicity hSecondHighMultiplicity
  dsimp only
  intro i j
  fin_cases i
  · fin_cases j
    · simpa [xₙ, DFP.FirstLeg.eigenvalues] using hFirstLowMultiplicity
    · simpa [xₙ, DFP.FirstLeg.eigenvalues] using hFirstHighMultiplicity
  · fin_cases j
    · simpa [xₙ, DFP.SecondLeg.eigenvalues] using hSecondLowMultiplicity
    · simpa [xₙ, DFP.SecondLeg.eigenvalues] using hSecondHighMultiplicity

/-- Along every sufficiently small orbit on an invariant slow graph, the four
canonical recovery denominators share a strictly positive lower bound. -/
theorem slowCurveRecoveryDenominatorsUniformlyPositive (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5))
    (εbar : ℝ) (h_εbar : εbar ∈ Set.Ioo 0 (1 / 4)) :
    ∃ ε₀ ∈ Set.Ioc 0 εbar, ∃ m > 0, ∀ ε ∈ Set.Ioc 0 ε₀, ∀ n : ℕ,
      let xₙ := stateMap^[n] (ε, p ε, h ε)
      let spectral₁ := DFP.FirstLeg.spectralFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let gradient₁ := DFP.FirstLeg.gradientFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let spectral₂ := DFP.SecondLeg.spectralFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let gradient₂ := DFP.SecondLeg.gradientFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let denominators : Fin 4 → ℝ :=
        ![spectral₁.2 * gradient₁.2, spectral₁.1 * gradient₁.1 ^ 2,
          spectral₂.2 * gradient₂.2, spectral₂.1 * gradient₂.1 ^ 2]
      ∀ i, m ≤ denominators i := by
  obtain ⟨ε₀, hε₀, m, hm, hfactors⟩ :=
    slowCurveFactorsUniformlyPositive p h h_invariant h_pJet h_hJet εbar h_εbar
  let μ := min (m ^ 2) (m ^ 3)
  have hμ : 0 < μ := by
    exact lt_min (pow_pos hm 2) (pow_pos hm 3)
  refine ⟨ε₀, hε₀, μ, hμ, ?_⟩
  intro ε hε n
  have hall := hfactors ε hε n
  dsimp only at hall ⊢
  have hL₁ : m ≤ (DFP.FirstLeg.spectralFactors
      (stateMap^[n] (ε, p ε, h ε)).1
      (stateMap^[n] (ε, p ε, h ε)).2.1
      (stateMap^[n] (ε, p ε, h ε)).2.2).1 := by
    simpa using hall (0 : Fin 10)
  have hH₁ : m ≤ (DFP.FirstLeg.spectralFactors
      (stateMap^[n] (ε, p ε, h ε)).1
      (stateMap^[n] (ε, p ε, h ε)).2.1
      (stateMap^[n] (ε, p ε, h ε)).2.2).2 := by
    simpa using hall (1 : Fin 10)
  have hQ₁ : m ≤ (DFP.FirstLeg.gradientFactors
      (stateMap^[n] (ε, p ε, h ε)).1
      (stateMap^[n] (ε, p ε, h ε)).2.1
      (stateMap^[n] (ε, p ε, h ε)).2.2).1 := by
    simpa using hall (2 : Fin 10)
  have hU₁ : m ≤ (DFP.FirstLeg.gradientFactors
      (stateMap^[n] (ε, p ε, h ε)).1
      (stateMap^[n] (ε, p ε, h ε)).2.1
      (stateMap^[n] (ε, p ε, h ε)).2.2).2 := by
    simpa using hall (3 : Fin 10)
  have hL₂ : m ≤ (DFP.SecondLeg.spectralFactors
      (stateMap^[n] (ε, p ε, h ε)).1
      (stateMap^[n] (ε, p ε, h ε)).2.1
      (stateMap^[n] (ε, p ε, h ε)).2.2).1 := by
    simpa using hall (5 : Fin 10)
  have hH₂ : m ≤ (DFP.SecondLeg.spectralFactors
      (stateMap^[n] (ε, p ε, h ε)).1
      (stateMap^[n] (ε, p ε, h ε)).2.1
      (stateMap^[n] (ε, p ε, h ε)).2.2).2 := by
    simpa using hall (6 : Fin 10)
  have hQ₂ : m ≤ (DFP.SecondLeg.gradientFactors
      (stateMap^[n] (ε, p ε, h ε)).1
      (stateMap^[n] (ε, p ε, h ε)).2.1
      (stateMap^[n] (ε, p ε, h ε)).2.2).1 := by
    simpa using hall (7 : Fin 10)
  have hU₂ : m ≤ (DFP.SecondLeg.gradientFactors
      (stateMap^[n] (ε, p ε, h ε)).1
      (stateMap^[n] (ε, p ε, h ε)).2.1
      (stateMap^[n] (ε, p ε, h ε)).2.2).2 := by
    simpa using hall (8 : Fin 10)
  have hL₁nonneg := hm.le.trans hL₁
  have hH₁nonneg := hm.le.trans hH₁
  have hQ₁square : m ^ 2 ≤ (DFP.FirstLeg.gradientFactors
      (stateMap^[n] (ε, p ε, h ε)).1
      (stateMap^[n] (ε, p ε, h ε)).2.1
      (stateMap^[n] (ε, p ε, h ε)).2.2).1 ^ 2 :=
    pow_le_pow_left₀ hm.le hQ₁ 2
  have hL₂nonneg := hm.le.trans hL₂
  have hH₂nonneg := hm.le.trans hH₂
  have hQ₂square : m ^ 2 ≤ (DFP.SecondLeg.gradientFactors
      (stateMap^[n] (ε, p ε, h ε)).1
      (stateMap^[n] (ε, p ε, h ε)).2.1
      (stateMap^[n] (ε, p ε, h ε)).2.2).1 ^ 2 :=
    pow_le_pow_left₀ hm.le hQ₂ 2
  intro i
  fin_cases i
  · calc
      μ ≤ m ^ 2 := min_le_left _ _
      _ = m * m := by ring
      _ ≤ (DFP.FirstLeg.spectralFactors
          (stateMap^[n] (ε, p ε, h ε)).1
          (stateMap^[n] (ε, p ε, h ε)).2.1
          (stateMap^[n] (ε, p ε, h ε)).2.2).2 *
          (DFP.FirstLeg.gradientFactors
            (stateMap^[n] (ε, p ε, h ε)).1
            (stateMap^[n] (ε, p ε, h ε)).2.1
            (stateMap^[n] (ε, p ε, h ε)).2.2).2 :=
        mul_le_mul hH₁ hU₁ hm.le hH₁nonneg
  · calc
      μ ≤ m ^ 3 := min_le_right _ _
      _ = m * m ^ 2 := by ring
      _ ≤ (DFP.FirstLeg.spectralFactors
          (stateMap^[n] (ε, p ε, h ε)).1
          (stateMap^[n] (ε, p ε, h ε)).2.1
          (stateMap^[n] (ε, p ε, h ε)).2.2).1 *
          (DFP.FirstLeg.gradientFactors
            (stateMap^[n] (ε, p ε, h ε)).1
            (stateMap^[n] (ε, p ε, h ε)).2.1
            (stateMap^[n] (ε, p ε, h ε)).2.2).1 ^ 2 :=
        mul_le_mul hL₁ hQ₁square (pow_nonneg hm.le 2) hL₁nonneg
  · calc
      μ ≤ m ^ 2 := min_le_left _ _
      _ = m * m := by ring
      _ ≤ (DFP.SecondLeg.spectralFactors
          (stateMap^[n] (ε, p ε, h ε)).1
          (stateMap^[n] (ε, p ε, h ε)).2.1
          (stateMap^[n] (ε, p ε, h ε)).2.2).2 *
          (DFP.SecondLeg.gradientFactors
            (stateMap^[n] (ε, p ε, h ε)).1
            (stateMap^[n] (ε, p ε, h ε)).2.1
            (stateMap^[n] (ε, p ε, h ε)).2.2).2 :=
        mul_le_mul hH₂ hU₂ hm.le hH₂nonneg
  · calc
      μ ≤ m ^ 3 := min_le_right _ _
      _ = m * m ^ 2 := by ring
      _ ≤ (DFP.SecondLeg.spectralFactors
          (stateMap^[n] (ε, p ε, h ε)).1
          (stateMap^[n] (ε, p ε, h ε)).2.1
          (stateMap^[n] (ε, p ε, h ε)).2.2).1 *
          (DFP.SecondLeg.gradientFactors
            (stateMap^[n] (ε, p ε, h ε)).1
            (stateMap^[n] (ε, p ε, h ε)).2.1
            (stateMap^[n] (ε, p ε, h ε)).2.2).1 ^ 2 :=
        mul_le_mul hL₂ hQ₂square (pow_nonneg hm.le 2) hL₂nonneg

end DFP.TwoLeg
