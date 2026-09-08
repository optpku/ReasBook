module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg

public section

noncomputable section

open Filter
open scoped Matrix Topology

/- Lemma 3.9 (First-leg removable-factor decomposition) (1): the first-leg spectrum
has its low factor `ε ^ 4` removed. -/
#check (DFP.FirstLeg.spectrumFactorization :
  ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
    DFP.FirstLeg.eigenvalues x.1 x.2.1 x.2.2 =
      (x.1 ^ 4 * (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).1,
        (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).2))

/- Lemma 3.9 (First-leg removable-factor decomposition) (2): the oriented first-leg
gradient coordinates have their high-coordinate factor `ε ^ 2` removed. -/
#check (DFP.FirstLeg.gradientFactorization :
  ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), ∀ G : ℝ,
    (DFP.FirstLeg.frame x.1 x.2.1 x.2.2).transpose *ᵥ
        (G • DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2) =
      G • ![(DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1,
        x.1 ^ 2 * (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2])

/- Lemma 3.9 (First-leg removable-factor decomposition) (3): away from `ε = 0`,
raw canonical recovery agrees with the removable radius and shape factors. -/
#check (DFP.FirstLeg.canonicalFactorization :
  ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), x.1 ≠ 0 →
    DFP.FirstLeg.recovered x.1 x.2.1 x.2.2 =
      (x.1 ^ 2 * (DFP.FirstLeg.canonicalFactors x.1 x.2.1 x.2.2).1,
        (DFP.FirstLeg.canonicalFactors x.1 x.2.1 x.2.2).2))

/- Lemma 3.9 (First-leg removable-factor decomposition) (4): all six removable
first-leg factors form a jointly real-analytic map at the base point. -/
#check (DFP.FirstLeg.factorsAnalytic :
  AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.factors x.1 x.2.1 x.2.2)
    (0, 2, 1))

/- Lemma 3.9 (First-leg removable-factor decomposition) (5): the six removable
first-leg factors have the stated base values. -/
#check (DFP.FirstLeg.factorsBase :
  DFP.FirstLeg.factors 0 2 1 = ((2, 1), (1, 1), (2, 1 / 2)))
