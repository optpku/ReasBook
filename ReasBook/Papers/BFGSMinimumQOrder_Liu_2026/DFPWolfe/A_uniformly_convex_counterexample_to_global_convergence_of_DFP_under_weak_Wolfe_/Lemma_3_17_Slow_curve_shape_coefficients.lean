module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_16_Coefficient_equations_for_the_invariant_graph
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.ShapeCoefficients

public section

open Filter
open scoped Topology

export DFP.TwoLeg (slowGraphShapeCoefficients slowGraphPJet slowGraphHJet)

/- Lemma 3.17 (Slow-curve shape coefficients) (1): the four graph coefficient
equations uniquely determine the cubic and quartic shape coefficients. -/
#check (DFP.TwoLeg.slowGraphShapeCoefficients :
  ∀ (P₃ H₃ P₄ H₄ : ℝ),
    3 * H₃ - 5 * P₃ + 174 = 0 →
    8 - H₃ = 0 →
    3 * H₄ - 5 * P₄ - 9 = 0 →
    H₄ = 0 →
    ((P₃, H₃), (P₄, H₄)) = (((198 / 5 : ℝ), 8), (-(9 / 5), 0)))

/- Lemma 3.17 (Slow-curve shape coefficients) (2): substituting the solved
shape coefficients into the generic `p`-jet gives its fixed expansion. -/
#check (DFP.TwoLeg.slowGraphPJet :
  ∀ (p : ℝ → ℝ) (P₃ P₄ : ℝ),
    ((fun ε ↦ p ε - (2 + P₃ * ε ^ 3 + P₄ * ε ^ 4)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    P₃ = 198 / 5 →
    P₄ = -(9 / 5) →
    (fun ε ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5))

/- Lemma 3.17 (Slow-curve shape coefficients) (3): substituting the solved
shape coefficients into the generic `h`-jet gives its fixed expansion. -/
#check (DFP.TwoLeg.slowGraphHJet :
  ∀ (h : ℝ → ℝ) (H₃ H₄ : ℝ),
    ((fun ε ↦ h ε - (1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    H₃ = 8 →
    H₄ = 0 →
    (fun ε ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5))
