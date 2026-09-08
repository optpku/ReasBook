module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg

public section

noncomputable section

open Filter
open scoped Matrix Topology

/- Lemma 3.10 (Second-leg removable-factor decomposition) (1): applying the prescribed
second control with the same `ε` to the first-leg factored state gives the explicit
second-leg metric and gradient. -/
#check (DFP.SecondLeg.outputEqStep :
  ∀ (z : DFP.AbstractSecantStep (Fin 2)) (ε p h G : ℝ),
    z.inverseHessian = Matrix.diagonal
        ![ε ^ 4 * (DFP.FirstLeg.spectralFactors ε p h).1,
          (DFP.FirstLeg.spectralFactors ε p h).2] →
    z.gradient = G • ![(DFP.FirstLeg.gradientFactors ε p h).1,
        ε ^ 2 * (DFP.FirstLeg.gradientFactors ε p h).2] →
    z.secantMatrix = (TwoPhaseControls.second ε).matrix →
    z.tau = (TwoPhaseControls.second ε).tau →
    (z.nextInverseHessian, z.nextGradient) =
      (DFP.SecondLeg.outputMetric ε p h, G • DFP.SecondLeg.outputGradient ε p h))

/- Lemma 3.10 (Second-leg removable-factor decomposition) (2): near the base point,
the fixed analytic low eigenvector is oriented toward the normalized second-leg
gradient. -/
#check (DFP.SecondLeg.frameOriented :
  ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
    0 < (DFP.SecondLeg.coordinates x.1 x.2.1 x.2.2).1)

/- Lemma 3.10 (Second-leg removable-factor decomposition) (3): the second-leg spectrum
has its low factor `ε ^ 4` removed. -/
#check (DFP.SecondLeg.spectrumFactorization :
  ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
    DFP.SecondLeg.eigenvalues x.1 x.2.1 x.2.2 =
      (x.1 ^ 4 * (DFP.SecondLeg.spectralFactors x.1 x.2.1 x.2.2).1,
        (DFP.SecondLeg.spectralFactors x.1 x.2.1 x.2.2).2))

/- Lemma 3.10 (Second-leg removable-factor decomposition) (4): algebraically for every
scalar `G`, the fixed-frame second-leg gradient coordinates have their factor `ε ^ 2`
removed; for the source's positive amplitude, (2) identifies the oriented branch. -/
#check (DFP.SecondLeg.gradientFactorization :
  ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), ∀ G : ℝ,
    (DFP.SecondLeg.frame x.1 x.2.1 x.2.2).transpose *ᵥ
        (G • DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2) =
      G • ![(DFP.SecondLeg.gradientFactors x.1 x.2.1 x.2.2).1,
        x.1 ^ 2 * (DFP.SecondLeg.gradientFactors x.1 x.2.1 x.2.2).2])

/- Lemma 3.10 (Second-leg removable-factor decomposition) (5): away from `ε = 0`,
raw canonical recovery agrees with the removable radius and shape factors. -/
#check (DFP.SecondLeg.canonicalFactorization :
  ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), x.1 ≠ 0 →
    DFP.SecondLeg.recovered x.1 x.2.1 x.2.2 =
      (x.1 ^ 2 * (DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2).1,
        (DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2).2))

/- Lemma 3.10 (Second-leg removable-factor decomposition) (6): all six removable
second-leg factors form a jointly real-analytic map at the base point. -/
#check (DFP.SecondLeg.factorsAnalytic :
  AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ DFP.SecondLeg.factors x.1 x.2.1 x.2.2)
    (0, 2, 1))

/- Lemma 3.10 (Second-leg removable-factor decomposition) (7): the six removable
second-leg factors have the stated base values. -/
#check (DFP.SecondLeg.factorsBase :
  DFP.SecondLeg.factors 0 2 1 = ((2, 1), (1, 2), (1, 2)))
