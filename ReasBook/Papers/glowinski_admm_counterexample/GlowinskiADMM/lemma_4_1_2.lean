/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycleTrajectory

@[expose] public section

open Filter

universe u

/- Lemma 4.1.2 (1): the prescribed cyclic sequences form a unit-penalty consensus
ADMM trajectory for the indicators of the two cycle polytopes. -/
#check (ConsensusADMM.IsProjectionCycle.isTrajectory :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (γ : ℝ) (η ν : ZMod N → E), 2 ≤ N → 0 < γ →
    ConsensusADMM.IsProjectionCycle γ η ν →
      ConsensusADMM.IsTrajectory γ
        (ConsensusADMM.extendedIndicator (ConsensusADMM.ProjectionCycle.xSet γ η ν))
        (ConsensusADMM.extendedIndicator (ConsensusADMM.ProjectionCycle.ySet η))
        (ConsensusADMM.ProjectionCycle.xSequence γ η ν)
        (ConsensusADMM.ProjectionCycle.ySequence η)
        (ConsensusADMM.ProjectionCycle.dualSequence ν))

/- Lemma 4.1.2 (2): every block minimum along the prescribed trajectory is unique. -/
#check (ConsensusADMM.IsProjectionCycle.hasUniqueUpdates :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (γ : ℝ) (η ν : ZMod N → E), 2 ≤ N → 0 < γ →
    ConsensusADMM.IsProjectionCycle γ η ν →
      ConsensusADMM.HasUniqueUpdates
        (ConsensusADMM.extendedIndicator (ConsensusADMM.ProjectionCycle.xSet γ η ν))
        (ConsensusADMM.extendedIndicator (ConsensusADMM.ProjectionCycle.ySet η))
        (ConsensusADMM.ProjectionCycle.xSequence γ η ν)
        (ConsensusADMM.ProjectionCycle.ySequence η)
        (ConsensusADMM.ProjectionCycle.dualSequence ν))

/- Lemma 4.1.2 (3): the origin triple satisfies the consensus KKT conditions. -/
#check (ConsensusADMM.IsProjectionCycle.isKKT :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (γ : ℝ) (η ν : ZMod N → E), 2 ≤ N → 0 < γ →
    ConsensusADMM.IsProjectionCycle γ η ν →
      ConsensusADMM.IsKKT
        (ConsensusADMM.extendedIndicator (ConsensusADMM.ProjectionCycle.xSet γ η ν))
        (ConsensusADMM.extendedIndicator (ConsensusADMM.ProjectionCycle.ySet η)) 0 0 0)

/- Lemma 4.1.2 (4): the origin is primal optimal and has objective value zero. -/
#check (ConsensusADMM.IsProjectionCycle.isOptimalValueZero :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (γ : ℝ) (η ν : ZMod N → E), 2 ≤ N → 0 < γ →
    ConsensusADMM.IsProjectionCycle γ η ν →
      ConsensusADMM.IsPrimalMinimizer
          (ConsensusADMM.extendedIndicator (ConsensusADMM.ProjectionCycle.xSet γ η ν))
          (ConsensusADMM.extendedIndicator (ConsensusADMM.ProjectionCycle.ySet η)) 0 ∧
        ConsensusADMM.extendedIndicator (ConsensusADMM.ProjectionCycle.xSet γ η ν) 0 +
          ConsensusADMM.extendedIndicator (ConsensusADMM.ProjectionCycle.ySet η) 0 = 0)

/- Lemma 4.1.2 (5): a nonzero cycle residual prevents primal-residual convergence
to zero. -/
#check (ConsensusADMM.IsProjectionCycle.residual_not_tendsto :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (γ : ℝ) (η ν : ZMod N → E), 2 ≤ N → 0 < γ →
    ConsensusADMM.IsProjectionCycle γ η ν →
      (∃ i, ConsensusADMM.ProjectionCycle.residual γ ν i ≠ 0) →
        ¬ Tendsto (ConsensusADMM.ProjectionCycle.primalResidual γ η ν) atTop (nhds 0))

/- Lemma 4.1.2 (6): the positive minimal period of the prescribed trajectory
divides the number of phases. -/
#check (ConsensusADMM.IsProjectionCycle.minimalPeriod_dvd :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (γ : ℝ) (η ν : ZMod N → E), 2 ≤ N → 0 < γ →
    ConsensusADMM.IsProjectionCycle γ η ν →
      ∃ d : ℕ, 0 < d ∧ d ∣ N ∧
        ConsensusADMM.HasExactPeriod d
          (ConsensusADMM.ProjectionCycle.xSequence γ η ν)
          (ConsensusADMM.ProjectionCycle.ySequence η)
          (ConsensusADMM.ProjectionCycle.dualSequence ν))
