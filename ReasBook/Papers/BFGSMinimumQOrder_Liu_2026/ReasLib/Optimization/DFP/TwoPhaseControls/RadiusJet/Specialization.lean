module

public import ReasLib.Optimization.DFP.TwoPhaseControls.RadiusJet

public section

/-!
# Specialization of the weighted radius jet

This companion isolates the algebraic specialization from the general weighted radius jet to
the fixed slow-graph coefficients.  The general jet certificate remains an explicit input.
-/

namespace DFP.TwoLeg

/-- Specializing the general weighted radius jet at the slow-graph coefficients gives
the displayed slow-graph jet. -/
theorem slowGraphNormalizedRadiusJet_of_weighted
    (hjet :
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ ↦
            let x := graphJetPath (198 / 5) 8 (-9 / 5) 0 ε
            radiusFactor x.1 x.2.1 x.2.2) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ ↦
            1 + ((6 * 8 + 5 * (198 / 5) - 300) / 18) * ε ^ 3 +
              ((6 * 0 + 5 * (-9 / 5) + 54) / 18) * ε ^ 4) 0) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦
          let x := slowGraphJetPath ε
          radiusFactor x.1 x.2.1 x.2.2) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦ 1 - 3 * ε ^ 3 + (5 / 2) * ε ^ 4) 0 := by
  have hpath (ε : ℝ) :
      slowGraphJetPath ε = graphJetPath (198 / 5) 8 (-9 / 5) 0 ε := by
    rw [slowGraphJetPath_apply, graphJetPath_apply]
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> ring
  have hinput :
      (fun ε : ℝ ↦
        let x := slowGraphJetPath ε
        radiusFactor x.1 x.2.1 x.2.2) =
        (fun ε : ℝ ↦
          let x := graphJetPath (198 / 5) 8 (-9 / 5) 0 ε
          radiusFactor x.1 x.2.1 x.2.2) := by
    funext ε
    rw [hpath]
  have houtput :
      (fun ε : ℝ ↦ 1 - 3 * ε ^ 3 + (5 / 2) * ε ^ 4) =
        (fun ε : ℝ ↦
          1 + ((6 * 8 + 5 * (198 / 5) - 300) / 18) * ε ^ 3 +
            ((6 * 0 + 5 * (-9 / 5) + 54) / 18) * ε ^ 4) := by
    funext ε
    ring
  rw [hinput, houtput]
  exact hjet

end DFP.TwoLeg
