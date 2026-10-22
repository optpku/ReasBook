/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_3_18_Parabolic_center_recurrence.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.RadiusJet

public section

open Filter
open scoped Topology

/- Lemma 3.18 (Parabolic center recurrence): for functions with the fixed
slow-graph shape jets, the signed first coordinate of the two-leg map satisfies
`ε₊ = ε - (3 / 2) * ε ^ 4 + (5 / 4) * ε ^ 5 + O(ε ^ 6)`. -/
#check (DFP.TwoLeg.slowGraphSignedRecurrence :
  ∀ (p h : ℝ → ℝ),
    ((fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    (fun ε : ℝ ↦
      DFP.TwoLeg.signedEpsilon ε (p ε) (h ε) -
        (ε - (3 / 2) * ε ^ 4 + (5 / 4) * ε ^ 5)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 6))
