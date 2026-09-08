module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.Regularity

public section

open Filter
open scoped Matrix Topology

/- Lemma 3.19a (Uniform positivity of factored coordinates and local denominators) (1):
after shrinking any preliminary scale below `1 / 4`, the ten removable factors on
both legs have one positive lower bound along every resulting slow-curve orbit. -/
#check (DFP.TwoLeg.slowCurveFactorsUniformlyPositive :
  ∀ (p h : ℝ → ℝ)
    (_ :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (_ :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (_ : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5))
    (εbar : ℝ) (_ : εbar ∈ Set.Ioo 0 (1 / 4)),
    ∃ ε₀ ∈ Set.Ioc 0 εbar, ∃ m > 0, ∀ ε ∈ Set.Ioc 0 ε₀, ∀ n : ℕ,
      let xₙ := DFP.TwoLeg.stateMap^[n] (ε, p ε, h ε)
      let spectral₁ := DFP.FirstLeg.spectralFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let gradient₁ := DFP.FirstLeg.gradientFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let canonical₁ := DFP.FirstLeg.canonicalFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let spectral₂ := DFP.SecondLeg.spectralFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let gradient₂ := DFP.SecondLeg.gradientFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let canonical₂ := DFP.SecondLeg.canonicalFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let factors : Fin 10 → ℝ :=
        ![spectral₁.1, spectral₁.2, gradient₁.1, gradient₁.2, canonical₁.1,
          spectral₂.1, spectral₂.2, gradient₂.1, gradient₂.2, canonical₂.1]
      ∀ i, m ≤ factors i)

/- Lemma 3.19a (Uniform positivity of factored coordinates and local denominators) (2):
after shrinking the preliminary scale, both eigenvalues of both leg metrics have
algebraic multiplicity one along every resulting slow-curve orbit. -/
#check (DFP.TwoLeg.slowCurveSpectraSimple :
  ∀ (p h : ℝ → ℝ)
    (_ :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (_ :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (_ : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5))
    (εbar : ℝ) (_ : εbar ∈ Set.Ioo 0 (1 / 4)),
    ∃ ε₀ ∈ Set.Ioc 0 εbar, ∀ ε ∈ Set.Ioc 0 ε₀, ∀ n : ℕ,
      let xₙ := DFP.TwoLeg.stateMap^[n] (ε, p ε, h ε)
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
      ∀ i j, (Matrix.toLin' (metrics i)).charpoly.rootMultiplicity (eigenvalues i j) = 1)

/- Lemma 3.19a (Uniform positivity of factored coordinates and local denominators) (3):
after shrinking the preliminary scale, the four factored canonical-recovery
denominators have one positive lower bound along every resulting slow-curve orbit. -/
#check (DFP.TwoLeg.slowCurveRecoveryDenominatorsUniformlyPositive :
  ∀ (p h : ℝ → ℝ)
    (_ :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (_ :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (_ : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5))
    (εbar : ℝ) (_ : εbar ∈ Set.Ioo 0 (1 / 4)),
    ∃ ε₀ ∈ Set.Ioc 0 εbar, ∃ m > 0, ∀ ε ∈ Set.Ioc 0 ε₀, ∀ n : ℕ,
      let xₙ := DFP.TwoLeg.stateMap^[n] (ε, p ε, h ε)
      let spectral₁ := DFP.FirstLeg.spectralFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let gradient₁ := DFP.FirstLeg.gradientFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let spectral₂ := DFP.SecondLeg.spectralFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let gradient₂ := DFP.SecondLeg.gradientFactors xₙ.1 xₙ.2.1 xₙ.2.2
      let denominators : Fin 4 → ℝ :=
        ![spectral₁.2 * gradient₁.2, spectral₁.1 * gradient₁.1 ^ 2,
          spectral₂.2 * gradient₂.2, spectral₂.1 * gradient₂.1 ^ 2]
      ∀ i, m ≤ denominators i)
