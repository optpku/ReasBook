module

public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap

public section

noncomputable section

open Filter
open scoped Matrix Topology

/- Appendix Proposition A.5a (Exact complete two-leg state map) (1): the first exact
DFP update before truncation. -/
#check (DFP.FirstLeg.outputEqStep :
  ∀ (z : DFP.AbstractSecantStep (Fin 2)) (ε p h G : ℝ),
    z.inverseHessian = Matrix.diagonal ![h * p * ε ^ 4, h] →
    z.gradient = G • ![(1 : ℝ), p * ε ^ 2] →
    z.secantMatrix = (TwoPhaseControls.first ε).matrix →
    z.tau = (TwoPhaseControls.first ε).tau →
    (z.nextInverseHessian, z.nextGradient) =
      (DFP.FirstLeg.outputMetric ε p h, G • DFP.FirstLeg.outputGradient ε p h))

/- Appendix Proposition A.5a (Exact complete two-leg state map) (2): the first
oriented frame diagonalizes the first updated metric on the common neighborhood. -/
#check (DFP.FirstLeg.frameDiagonalization :
  ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
    (DFP.FirstLeg.frame x.1 x.2.1 x.2.2).transpose *
        DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 *
        DFP.FirstLeg.frame x.1 x.2.1 x.2.2 =
      Matrix.diagonal
        ![x.1 ^ 4 * (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).1,
          (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).2])

/- Appendix Proposition A.5a (Exact complete two-leg state map) (3): the exact
first-leg oriented-gradient factorization before truncation. -/
#check (DFP.FirstLeg.gradientFactorization :
  ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), ∀ G : ℝ,
    (DFP.FirstLeg.frame x.1 x.2.1 x.2.2).transpose *ᵥ
        (G • DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2) =
      G • ![(DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1,
        x.1 ^ 2 * (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2])

/- Appendix Proposition A.5a (Exact complete two-leg state map) (4): first-leg
canonical recovery on the common neighborhood away from `ε = 0`. -/
#check (DFP.FirstLeg.canonicalFactorization :
  ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), x.1 ≠ 0 →
    DFP.FirstLeg.recovered x.1 x.2.1 x.2.2 =
      (x.1 ^ 2 * (DFP.FirstLeg.canonicalFactors x.1 x.2.1 x.2.2).1,
        (DFP.FirstLeg.canonicalFactors x.1 x.2.1 x.2.2).2))

/- Appendix Proposition A.5a (Exact complete two-leg state map) (5): the second exact
DFP update, using the same scale `ε`, before truncation. -/
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

/- Appendix Proposition A.5a (Exact complete two-leg state map) (6): the second
oriented frame diagonalizes the second updated metric on the common neighborhood. -/
#check (DFP.SecondLeg.frameDiagonalization :
  ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
    (DFP.SecondLeg.frame x.1 x.2.1 x.2.2).transpose *
        DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 *
        DFP.SecondLeg.frame x.1 x.2.1 x.2.2 =
      Matrix.diagonal
        ![x.1 ^ 4 * (DFP.SecondLeg.spectralFactors x.1 x.2.1 x.2.2).1,
          (DFP.SecondLeg.spectralFactors x.1 x.2.1 x.2.2).2])

/- Appendix Proposition A.5a (Exact complete two-leg state map) (7): the exact
second-leg oriented-gradient factorization before truncation. -/
#check (DFP.SecondLeg.gradientFactorization :
  ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), ∀ G : ℝ,
    (DFP.SecondLeg.frame x.1 x.2.1 x.2.2).transpose *ᵥ
        (G • DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2) =
      G • ![(DFP.SecondLeg.gradientFactors x.1 x.2.1 x.2.2).1,
        x.1 ^ 2 * (DFP.SecondLeg.gradientFactors x.1 x.2.1 x.2.2).2])

/- Appendix Proposition A.5a (Exact complete two-leg state map) (8): second-leg
canonical recovery on the common neighborhood away from `ε = 0`. -/
#check (DFP.SecondLeg.canonicalFactorization :
  ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), x.1 ≠ 0 →
    DFP.SecondLeg.recovered x.1 x.2.1 x.2.2 =
      (x.1 ^ 2 * (DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2).1,
        (DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2).2))

/- Appendix Proposition A.5a (Exact complete two-leg state map) (9): the signed
factored state map has its exact three-coordinate formula before truncation. -/
#check (DFP.TwoLeg.stateMap_apply :
  ∀ ε p h : ℝ,
    DFP.TwoLeg.stateMap (ε, p, h) =
      (ε * Real.sqrt (DFP.SecondLeg.canonicalFactors ε p h).1,
        (DFP.SecondLeg.canonicalFactors ε p h).2,
        (DFP.SecondLeg.spectralFactors ε p h).2))

/- Appendix Proposition A.5a (Exact complete two-leg state map) (10): locally on
the positive-scale branch, the signed map agrees with the raw recovered state. -/
#check (DFP.TwoLeg.stateMap_eventuallyEq_recovered :
  ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), 0 < x.1 →
    DFP.TwoLeg.stateMap x =
      (Real.sqrt (DFP.SecondLeg.recovered x.1 x.2.1 x.2.2).1,
        (DFP.SecondLeg.recovered x.1 x.2.1 x.2.2).2,
        (DFP.SecondLeg.eigenvalues x.1 x.2.1 x.2.2).2))

/- Appendix Proposition A.5a (Exact complete two-leg state map) (11): the exact
factored state map fixes the common base point. -/
#check (DFP.TwoLeg.stateMap_base :
  DFP.TwoLeg.stateMap (0, 2, 1) = (0, 2, 1))

/- Appendix Proposition A.5a (Exact complete two-leg state map) (12): the signed
factored state map is real analytic at the common base point. -/
#check (DFP.TwoLeg.stateMapAnalytic :
  AnalyticAt ℝ DFP.TwoLeg.stateMap ((0, 2, 1) : ℝ × ℝ × ℝ))
