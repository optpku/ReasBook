module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBump.GlobalRegularity

public section

noncomputable section

open Filter Set
open scoped Asymptotics Topology

/- Lemma 5.8 (Global $C^2$ extension of the disjoint bump sum) -/
#check (DFP.TwoLeg.SlowCurve.bumpCorrectionContDiffTwoAndZeroJets :
  ∀ (curve : DFP.TwoLeg.SlowCurve),
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ContDiff ℝ 2 (orbit.bumpCorrection Clim Glim) ∧
                EqOn (orbit.bumpCorrection Clim Glim) 0
                  (DFP.TwoPhaseOrbit.limitCircle Clim Glim) ∧
                EqOn (gradient (orbit.bumpCorrection Clim Glim)) 0
                  (DFP.TwoPhaseOrbit.limitCircle Clim Glim) ∧
                EqOn (EuclideanPlane.hessian (orbit.bumpCorrection Clim Glim)) 0
                  (DFP.TwoPhaseOrbit.limitCircle Clim Glim))

/-- The global bump correction is twice continuously differentiable along a
source-presented invariant slow curve. -/
theorem contDiff_two_slowCurveBumpCorrection (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ContDiff ℝ 2 (orbit.bumpCorrection Clim Glim) := by
  let curve := DFP.TwoLeg.SlowCurve.ofAsymptotics
    p h h_pJet h_hJet h_invariant
  obtain ⟨εbar, hεbar, hcore⟩ :=
    DFP.TwoLeg.SlowCurve.bumpCorrectionContDiffTwoAndZeroJets curve
  have hcore' := hcore
  simp only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] at hcore'
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  intro Clim hClim Glim hGlim hGlimTendsto
  exact (hcore' ε₀ hε₀ Clim hClim Glim hGlim hGlimTendsto).1

/-- The source-presented global bump correction vanishes on its limiting circle. -/
theorem slowCurveBumpCorrection_eqOn_zero (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              EqOn (orbit.bumpCorrection Clim Glim) 0
                (DFP.TwoPhaseOrbit.limitCircle Clim Glim) := by
  let curve := DFP.TwoLeg.SlowCurve.ofAsymptotics
    p h h_pJet h_hJet h_invariant
  obtain ⟨εbar, hεbar, hcore⟩ :=
    DFP.TwoLeg.SlowCurve.bumpCorrectionContDiffTwoAndZeroJets curve
  have hcore' := hcore
  simp only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] at hcore'
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  intro Clim hClim Glim hGlim hGlimTendsto
  exact (hcore' ε₀ hε₀ Clim hClim Glim hGlim hGlimTendsto).2.1

/-- The source-presented gradient of the global bump correction vanishes on
its limiting circle. -/
theorem slowCurveBumpCorrection_gradient_eqOn_zero (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              EqOn (gradient (orbit.bumpCorrection Clim Glim)) 0
                (DFP.TwoPhaseOrbit.limitCircle Clim Glim) := by
  let curve := DFP.TwoLeg.SlowCurve.ofAsymptotics
    p h h_pJet h_hJet h_invariant
  obtain ⟨εbar, hεbar, hcore⟩ :=
    DFP.TwoLeg.SlowCurve.bumpCorrectionContDiffTwoAndZeroJets curve
  have hcore' := hcore
  simp only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] at hcore'
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  intro Clim hClim Glim hGlim hGlimTendsto
  exact (hcore' ε₀ hε₀ Clim hClim Glim hGlim hGlimTendsto).2.2.1

/-- The source-presented Hessian of the global bump correction vanishes on its
limiting circle. -/
theorem slowCurveBumpCorrection_hessian_eqOn_zero (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              EqOn (EuclideanPlane.hessian (orbit.bumpCorrection Clim Glim)) 0
                (DFP.TwoPhaseOrbit.limitCircle Clim Glim) := by
  let curve := DFP.TwoLeg.SlowCurve.ofAsymptotics
    p h h_pJet h_hJet h_invariant
  obtain ⟨εbar, hεbar, hcore⟩ :=
    DFP.TwoLeg.SlowCurve.bumpCorrectionContDiffTwoAndZeroJets curve
  have hcore' := hcore
  simp only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] at hcore'
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  intro Clim hClim Glim hGlim hGlimTendsto
  exact (hcore' ε₀ hε₀ Clim hClim Glim hGlim hGlimTendsto).2.2.2
