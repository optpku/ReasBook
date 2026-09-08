module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.StateJetDomainFactors
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.StateJetRemainderUniform
import all ReasLib.Analysis.Asymptotics.UniformRemainder

public section

noncomputable section

namespace DFP.TwoLeg.StateJet

/-- The uniform fifth-order remainder bound and the thirteen uniform positivity bounds
share one radius on every bounded graph-coefficient ball. -/
theorem stateJetsCommonDomain_via_uniform_remainder (B : ℝ) (hB : 0 ≤ B) :
    ∃ C > 0, ∃ m > 0, ∃ δ ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ θ ∈ Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B,
        ∀ ε : ℝ, |ε| < δ →
          ‖remainder θ ε‖ ≤ C * |ε| ^ 5 ∧
            ∀ i : Fin 13, m ≤ domainFactors θ ε i := by
  obtain ⟨C, hC, δr, hδr, hr⟩ := remainder_uniform_orderFive B
  obtain ⟨m, hm, δp, hδp, hp⟩ :=
    domainFactors_uniform_lower_bound B hB
  let δ : ℝ := min δr (min δp (1 / 8))
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min hδr (lt_min hδp (by norm_num))
  have hδquarter : δ < 1 / 4 := by
    have hδeighth : δ ≤ 1 / 8 := by
      dsimp only [δ]
      exact (min_le_right _ _).trans (min_le_right _ _)
    linarith
  refine ⟨C, hC, m, hm, δ, ⟨hδ, hδquarter⟩, ?_⟩
  intro θ hθ ε hε
  have hεr : |ε| < δr := by
    exact lt_of_lt_of_le hε (by
      dsimp only [δ]
      exact min_le_left _ _)
  have hεp : |ε| < δp := by
    exact lt_of_lt_of_le hε (by
      dsimp only [δ]
      exact (min_le_right _ _).trans (min_le_left _ _))
  exact ⟨hr θ hθ ε hεr, fun i => hp θ hθ i ε hεp⟩

/-- Axiom-clean uniform-remainder certificate obtained from the common-domain theorem. -/
theorem uniformRemainderOn_via_commonDomain (B : ℝ) (hB : 0 ≤ B) :
    ∃ C > 0,
      Asymptotics.IsUniformRemainderOn remainder
        (Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B) C 5 := by
  obtain ⟨C, hC, m, hm, δ, hδ, hcommon⟩ :=
    stateJetsCommonDomain_via_uniform_remainder B hB
  refine ⟨C, hC, ?_⟩
  unfold Asymptotics.IsUniformRemainderOn
  refine ⟨δ, hδ.1, ?_⟩
  intro θ hθ ε hε
  have hpow : |ε| ^ (5 : ℝ) = |ε| ^ (5 : ℕ) :=
    Real.rpow_natCast |ε| 5
  rw [hpow]
  exact (hcommon θ hθ ε hε).1

end DFP.TwoLeg.StateJet

