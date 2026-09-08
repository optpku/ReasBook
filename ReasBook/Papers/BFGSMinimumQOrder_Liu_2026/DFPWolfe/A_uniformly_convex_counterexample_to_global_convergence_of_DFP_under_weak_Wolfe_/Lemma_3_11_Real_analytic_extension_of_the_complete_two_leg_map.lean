module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_11_Real_analytic_extension_of_the_complete_two_leg_map_Map

public section

noncomputable section

open Filter
open scoped Topology

/- Lemma 3.11 (Real-analytic extension of the complete two-leg map) (1): the
complete map has the signed removable-factor coordinates. -/
#check (DFP.TwoLeg.stateMap_apply :
  ∀ (ε p h : ℝ),
    DFP.TwoLeg.stateMap (ε, p, h) =
      (ε * Real.sqrt (DFP.SecondLeg.canonicalFactors ε p h).1,
        (DFP.SecondLeg.canonicalFactors ε p h).2,
        (DFP.SecondLeg.spectralFactors ε p h).2))

/- Lemma 3.11 (Real-analytic extension of the complete two-leg map) (2): the
signed next-scale coordinate is jointly real analytic at `(0, 2, 1)`. -/
#check (DFP.TwoLeg.analyticAt_signedEpsilon :
  AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ DFP.TwoLeg.signedEpsilon x.1 x.2.1 x.2.2)
    ((0, 2, 1) : ℝ × ℝ × ℝ))

/- Lemma 3.11 (Real-analytic extension of the complete two-leg map) (3): the
complete two-leg map is jointly real analytic at `(0, 2, 1)`. -/
#check (DFP.TwoLeg.stateMapAnalytic :
  AnalyticAt ℝ DFP.TwoLeg.stateMap ((0, 2, 1) : ℝ × ℝ × ℝ))

/- Lemma 3.11 (Real-analytic extension of the complete two-leg map) (4): near
`(0, 2, 1)`, the complete map agrees with the recovered positive-square-root
state whenever the incoming scale is positive. -/
#check (DFP.TwoLeg.stateMap_eventuallyEq_recovered :
  ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), 0 < x.1 →
    DFP.TwoLeg.stateMap x =
      (Real.sqrt (DFP.SecondLeg.recovered x.1 x.2.1 x.2.2).1,
        (DFP.SecondLeg.recovered x.1 x.2.1 x.2.2).2,
        (DFP.SecondLeg.eigenvalues x.1 x.2.1 x.2.2).2))
