module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_15b_Taylor_ansatz_of_the_invariant_slow_graph
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.CoefficientEquations

public section

open Filter
open scoped Topology

/- Lemma 3.16 (Coefficient equations for the invariant graph): for a graph
with cubic--quartic fifth-order jets, invariance under the two-leg map forces
the complete system of four coefficient equations. -/
#check (DFP.TwoLeg.invariantSlowGraphCoefficientEquations :
  ∀ (p h : ℝ → ℝ) (P₃ H₃ P₄ H₄ : ℝ),
    ((fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε ↦ p ε - (2 + P₃ * ε ^ 3 + P₄ * ε ^ 4)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    ((fun ε ↦ h ε - (1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    3 * H₃ - 5 * P₃ + 174 = 0 ∧
      8 - H₃ = 0 ∧
      3 * H₄ - 5 * P₄ - 9 = 0 ∧
      H₄ = 0)
