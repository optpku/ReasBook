module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycleStrictification

@[expose] public section

universe u

/- Lemma 5.1.1 (1): strictification of a projection cycle with one strict block. -/
#check (ConsensusADMM.IsProjectionCycle.strictifyOneBlock :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ : ℝ) (η ν : ZMod N → E) (hN : 2 ≤ N) (hγ : 0 < γ) (hγtwo : γ < 2)
    (hcycle : ConsensusADMM.IsProjectionCycle γ η ν)
    (hnonzero : ∃ i, ConsensusADMM.ProjectionCycle.residual γ ν i ≠ 0)
    (hstrict : ConsensusADMM.HasStrictBlock γ η ν),
    ∃ d : ℕ, d ≤ 2 * N ∧
      ∃ eta' nu' : ZMod N → EuclideanSpace ℝ (Fin d),
        ConsensusADMM.IsStrictProjectionCycle γ eta' nu' ∧
          (∃ i, ConsensusADMM.ProjectionCycle.residual γ nu' i ≠ 0) ∧
          (ConsensusADMM.ProjectionCycle.HasOrthogonalCyclicSymmetry η ν →
            ConsensusADMM.ProjectionCycle.HasOrthogonalCyclicSymmetry eta' nu'))

/- Lemma 5.1.1 (2): the uniform-convergence endpoint lies strictly below the cycle factor. -/
#check (ConsensusADMM.IsProjectionCycle.uniformConvergenceEndpoint_lt :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ : ℝ) (η ν : ZMod N → E) (hN : 2 ≤ N) (hγ : 0 < γ) (hγtwo : γ < 2)
    (hcycle : ConsensusADMM.IsProjectionCycle γ η ν)
    (hnonzero : ∃ i, ConsensusADMM.ProjectionCycle.residual γ ν i ≠ 0)
    (hstrict : ConsensusADMM.HasStrictBlock γ η ν),
    ADMM.uniformConvergenceEndpoint < γ)
