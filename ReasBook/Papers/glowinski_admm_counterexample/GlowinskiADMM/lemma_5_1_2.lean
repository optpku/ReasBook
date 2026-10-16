module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycleStrictification

@[expose] public section

universe u

/- Lemma 5.1.2 (1): a nontrivial projection cycle with one strict block can be
strictified in dimension at most `2 * N`, while preserving orthogonal cyclic symmetry. -/
#check (ConsensusADMM.IsProjectionCycle.strictifyOneBlock :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (γ : ℝ) (η ν : ZMod N → E),
    2 ≤ N → 0 < γ → γ < 2 → ConsensusADMM.IsProjectionCycle γ η ν →
    (∃ i, ConsensusADMM.ProjectionCycle.residual γ ν i ≠ 0) →
    ConsensusADMM.HasStrictBlock γ η ν →
    ∃ d : ℕ, d ≤ 2 * N ∧
      ∃ eta' nu' : ZMod N → EuclideanSpace ℝ (Fin d),
        ConsensusADMM.IsStrictProjectionCycle γ eta' nu' ∧
          (∃ i, ConsensusADMM.ProjectionCycle.residual γ nu' i ≠ 0) ∧
          (ConsensusADMM.ProjectionCycle.HasOrthogonalCyclicSymmetry η ν →
            ConsensusADMM.ProjectionCycle.HasOrthogonalCyclicSymmetry eta' nu'))

/- Lemma 5.1.2 (2): a nontrivial projection cycle with one strict block lies
strictly above the uniform-convergence endpoint. -/
#check (ConsensusADMM.IsProjectionCycle.uniformConvergenceEndpoint_lt :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (γ : ℝ) (η ν : ZMod N → E),
    2 ≤ N → 0 < γ → γ < 2 → ConsensusADMM.IsProjectionCycle γ η ν →
    (∃ i, ConsensusADMM.ProjectionCycle.residual γ ν i ≠ 0) →
    ConsensusADMM.HasStrictBlock γ η ν → ADMM.uniformConvergenceEndpoint < γ)
