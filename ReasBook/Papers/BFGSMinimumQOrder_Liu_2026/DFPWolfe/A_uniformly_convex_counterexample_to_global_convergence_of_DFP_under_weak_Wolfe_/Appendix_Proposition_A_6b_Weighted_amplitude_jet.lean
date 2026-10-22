/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Appendix_Proposition_A_6b_Weighted_amplitude_jet.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.AmplitudeJet

public section

noncomputable section

open Filter
open scoped Topology

export DFP.TwoLeg (slowGraphAmplitudeJet slowGraphAmplitudeRemainder)

/- Appendix Proposition A.6b (Weighted amplitude jet): after substituting the
polynomial slow graph, the normalized amplitude has the displayed expansion
with local remainder `O(ε ^ 8)`. -/
#check (DFP.TwoLeg.slowGraphAmplitudeRemainder :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)).amplitudeRatio -
        (1 - (13 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - (976 / 5) * ε ^ 7)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 8))

/- The same expansion gives the complete order-seven finite Taylor jet. -/
#check (DFP.TwoLeg.slowGraphAmplitudeJet :
    FiniteTaylorJet.ofFunction ℝ 7
        (fun ε : ℝ ↦
          (DFP.TwoLeg.observableMap
            (DFP.TwoLeg.slowGraphJetPath ε)).amplitudeRatio) 0 =
      FiniteTaylorJet.ofFunction ℝ 7
        (fun ε : ℝ ↦
          1 - (13 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - (976 / 5) * ε ^ 7) 0)
