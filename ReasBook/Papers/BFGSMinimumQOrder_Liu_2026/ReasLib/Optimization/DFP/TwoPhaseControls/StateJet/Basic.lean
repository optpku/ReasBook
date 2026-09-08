module

public import ReasLib.Optimization.DFP.TwoPhaseControls.StateJet

public section

/-!
# Basic interfaces for the joint state jet

This companion exposes the residual and common-domain interfaces independently of the
analytic jet certificates in the pipeline-owned module.
-/

open scoped Matrix

namespace DFP.TwoLeg.StateJet

/-- The joint state-jet residual unfolds to its three coordinate remainders. -/
theorem remainder_eq (θ : (ℝ × ℝ) × (ℝ × ℝ)) (ε : ℝ) :
    remainder θ ε =
      let x := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
      let y := DFP.TwoLeg.stateMap x
      let nextGraph := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 y.1
      (DFP.TwoLeg.radiusFactor x.1 x.2.1 x.2.2 -
          (1 + ((6 * θ.1.2 + 5 * θ.1.1 - 300) / 18) * ε ^ 3 +
            ((6 * θ.2.2 + 5 * θ.2.1 + 54) / 18) * ε ^ 4),
        y.2.1 - nextGraph.2.1 -
          (((6 * θ.1.2 - 10 * θ.1.1 + 348) / 9) * ε ^ 3 +
            ((6 * θ.2.2 - 10 * θ.2.1 - 18) / 9) * ε ^ 4),
        y.2.2 - nextGraph.2.2 -
          ((8 - θ.1.2) * ε ^ 3 - θ.2.2 * ε ^ 4)) := by
  exact remainder_apply θ ε

/-- The ordered regularity-factor vector unfolds to its thirteen explicit entries. -/
theorem domainFactors_eq (θ : (ℝ × ℝ) × (ℝ × ℝ)) (ε : ℝ) (i : Fin 13) :
    domainFactors θ ε i =
      (let x := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
       let p := x.2.1
       let h := x.2.2
       let B₁ := 1 + 2 * ε ^ 3 + ε ^ 4
       let C₁ := (1 + ε ^ 3) ^ 2 + p * ε ^ 6 * (1 + ε) ^ 2
       let metric₁ := DFP.FirstLeg.outputMetric ε p h
       let spectral₁ := DFP.FirstLeg.spectralFactors ε p h
       let gradient₁ := DFP.FirstLeg.gradientFactors ε p h
       let L := spectral₁.1
       let H := spectral₁.2
       let Q := gradient₁.1
       let U := gradient₁.2
       let w₁ := ε * L * Q - 2 * H * U
       let w₂ := H * U - 2 * ε ^ 3 * L * Q
       let beta := ε ^ 3 * L * Q * w₁ + H * U * w₂
       let gamma := ε ^ 6 * L * w₁ ^ 2 + H * w₂ ^ 2
       let metric₂ := DFP.SecondLeg.outputMetric ε p h
       let spectral₂ := DFP.SecondLeg.spectralFactors ε p h
       let gradient₂ := DFP.SecondLeg.gradientFactors ε p h
       ![B₁, C₁,
         RealSymmetric2.high (metric₁ 0 0) (metric₁ 0 1) (metric₁ 1 1),
         RealSymmetric2.lowDenom (metric₁ 0 0) (metric₁ 0 1) (metric₁ 1 1),
         spectral₁.2 * gradient₁.2, spectral₁.1 * gradient₁.1 ^ 2,
         beta, gamma,
         RealSymmetric2.high (metric₂ 0 0) (metric₂ 0 1) (metric₂ 1 1),
         RealSymmetric2.lowDenom (metric₂ 0 0) (metric₂ 0 1) (metric₂ 1 1),
         spectral₂.2 * gradient₂.2, spectral₂.1 * gradient₂.1 ^ 2,
         DFP.TwoLeg.radiusFactor ε p h] i) := by
  exact domainFactors_apply θ ε i

/-- The joint bound part of a common-domain certificate is a uniform remainder estimate. -/
theorem uniformRemainderOn_of_commonDomain
    {B C m δ : ℝ} (hδ : 0 < δ)
    (hcommon :
      ∀ θ ∈ Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B,
        ∀ ε : ℝ, |ε| < δ →
          ‖remainder θ ε‖ ≤ C * |ε| ^ 5 ∧
            ∀ i : Fin 13, m ≤ domainFactors θ ε i) :
    Asymptotics.IsUniformRemainderOn remainder
      (Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B) C 5 := by
  apply Asymptotics.IsUniformRemainderOn.of_bound hδ
  intro θ hθ ε hε
  have hpow : |ε| ^ (5 : ℝ) = |ε| ^ (5 : ℕ) :=
    Real.rpow_natCast |ε| 5
  rw [hpow]
  exact (hcommon θ hθ ε hε).1

end DFP.TwoLeg.StateJet
