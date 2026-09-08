module

public import ReasLib.Analysis.Asymptotics.UniformRemainder.ContinuousLinearMap
public import ReasLib.Optimization.DFP.TwoPhaseControls.StateJet.Basic

public section

/-!
# Transverse projection of the joint state remainder

The transverse graph-invariance remainder is the second projection of the joint state-jet
remainder.  This post-StateJet companion records the projection without creating an import
cycle back into `TransverseJet`.
-/

namespace DFP.TwoLeg.StateJet

noncomputable section

/-- The transverse pair obtained by dropping the radius component of the joint state residual. -/
def transverseRemainder (θ : (ℝ × ℝ) × (ℝ × ℝ)) (ε : ℝ) : ℝ × ℝ :=
  let x := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
  let y := DFP.TwoLeg.stateMap x
  let nextGraph := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 y.1
  (y.2.1 - nextGraph.2.1 -
      (((6 * θ.1.2 - 10 * θ.1.1 + 348) / 9) * ε ^ 3 +
        ((6 * θ.2.2 - 10 * θ.2.1 - 18) / 9) * ε ^ 4),
    y.2.2 - nextGraph.2.2 -
      ((8 - θ.1.2) * ε ^ 3 - θ.2.2 * ε ^ 4))

/-- The transverse remainder is exactly the second projection of the joint state remainder. -/
theorem transverseRemainder_eq_snd
    (θ : (ℝ × ℝ) × (ℝ × ℝ)) (ε : ℝ) :
    transverseRemainder θ ε = (remainder θ ε).2 := by
  rw [remainder_apply]
  rfl

/-- A uniform joint state-remainder bound gives the same bound for its transverse pair. -/
theorem transverseRemainder_uniform_of_state
    {s : Set ((ℝ × ℝ) × (ℝ × ℝ))} {C : ℝ}
    (hR : Asymptotics.IsUniformRemainderOn remainder s C 5) :
    Asymptotics.IsUniformRemainderOn transverseRemainder s C 5 := by
  have hfun : transverseRemainder = fun θ ε => (remainder θ ε).2 := by
    funext θ ε
    exact transverseRemainder_eq_snd θ ε
  rw [hfun]
  exact Asymptotics.IsUniformRemainderOn.snd hR

end

end DFP.TwoLeg.StateJet
