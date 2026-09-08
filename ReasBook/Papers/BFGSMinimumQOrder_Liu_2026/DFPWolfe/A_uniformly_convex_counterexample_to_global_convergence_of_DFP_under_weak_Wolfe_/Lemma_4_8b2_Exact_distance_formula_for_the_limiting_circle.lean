module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.Distance

public section

/- Lemma 4.8b2 (Exact distance formula for the limiting circle) -/
#check (DFP.TwoPhaseOrbit.infDist_limitCircle :
  ∀ (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ), 0 < G →
    ∀ (x : EuclideanSpace ℝ (Fin 2)),
      Metric.infDist x (DFP.TwoPhaseOrbit.limitCircle C G) = |‖x - C‖ - G|)
