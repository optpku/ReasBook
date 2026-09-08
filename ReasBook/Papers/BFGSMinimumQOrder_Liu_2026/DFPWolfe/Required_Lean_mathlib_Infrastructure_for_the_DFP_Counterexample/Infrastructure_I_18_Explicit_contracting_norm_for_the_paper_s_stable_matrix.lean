module

public import ReasLib.Optimization.DFP.StableMatrix

public section

/- Infrastructure I.18 (Explicit contracting norm for the paper's stable matrix) (1):
the explicit weighted sum seminorm is equivalent to the standard norm on `Fin 2 → ℝ`. -/
#check (DFPStable.weightedSum_isEquivalent :
  DFPStable.weightedSum.IsEquivalent (normSeminorm ℝ (Fin 2 → ℝ)))

/- Infrastructure I.18 (Explicit contracting norm for the paper's stable matrix) (2):
the stable matrix contracts the explicit weighted sum seminorm by the rational rate `1 / 3 < 1`. -/
#check (DFPStable.weightedSum_contracts :
  (∀ x, DFPStable.weightedSum (DFPStable.map x) ≤
    (1 / 3 : ℝ) * DFPStable.weightedSum x) ∧
  (1 / 3 : ℝ) < 1)
