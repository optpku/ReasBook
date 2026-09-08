module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift

public section

noncomputable section

open Filter
open scoped Topology

/- Appendix Lemma A.6 (Mixed-variable physical drift expansion); eq:appendix-G -/
#check (DFP.TwoLeg.Mixed.amplitudeExpansion :
  ∀ (β B : ℝ), 0 < β → β < 1 / 4 → 0 ≤ B →
    ∃ C > 0, Asymptotics.IsUniformRemainderOn
      (fun θ r ↦
        let observable := DFP.TwoLeg.Mixed.observableMap θ.1
          (DFP.TwoLeg.Mixed.input θ r)
        observable.amplitudeRatio - 1 -
          ((θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18) * r ^ 2)
      (DFP.TwoLeg.Mixed.parameterSet β B) C 3)

/- Appendix Lemma A.6 (Mixed-variable physical drift expansion); eq:appendix-phi -/
#check (DFP.TwoLeg.Mixed.frameAngleExpansion :
  ∀ (β B : ℝ), 0 < β → β < 1 / 4 → 0 ≤ B →
    ∃ C > 0, Asymptotics.IsUniformRemainderOn
      (fun θ r ↦
        let observable := DFP.TwoLeg.Mixed.observableMap θ.1
          (DFP.TwoLeg.Mixed.input θ r)
        observable.frameAngleIncrement - (-3 * r))
      (DFP.TwoLeg.Mixed.parameterSet β B) C 2)

/- Appendix Lemma A.6 (Mixed-variable physical drift expansion); eq:appendix-C -/
#check (DFP.TwoLeg.Mixed.centerDisplacementExpansion :
  ∀ (G β B : ℝ), 0 < G → 0 < β → β < 1 / 4 → 0 ≤ B →
    ∃ C > 0, Asymptotics.IsBigOWith C
      (principal (DFP.TwoLeg.Mixed.parameterSet β B) ×ˢ 𝓝 0)
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        let θ := z.1
        let r := z.2
        let observable := DFP.TwoLeg.Mixed.observableMap θ.1
          (DFP.TwoLeg.Mixed.input θ r)
        G * observable.fullCenterDisplacement 0 -
          (-(2 * θ.1 ^ 2 * (6 * θ.2.2 - θ.2.1 + 96) / 9) * G * r ^ 2))
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ G * |z.1.1| * |z.2| ^ 3))
