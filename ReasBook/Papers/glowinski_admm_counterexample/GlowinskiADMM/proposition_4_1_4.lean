module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.GramCycle

@[expose] public section

/- Proposition 4.1.4 (1): the canonical positive-semidefinite square-root map
converts the standard Euclidean pairing into a matrix-linear Gram pairing. -/
#check (ConsensusADMM.GramCycle.gramMap_inner :
  ∀ {N : ℕ} (G : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)
      (hG : G.PosSemidef) (z w : (Fin 2 × Fin N) → ℝ),
    dotProduct (ConsensusADMM.GramCycle.gramMap G z)
        (ConsensusADMM.GramCycle.gramMap G w) =
      ConsensusADMM.GramCycle.supportFunctional z w G)

/- Proposition 4.1.4 (2): for fixed coefficient vectors, the Gram support
functional is linear in the matrix argument. -/
#check (ConsensusADMM.GramCycle.supportLinearInGram :
  ∀ {N : ℕ} (z w : (Fin 2 × Fin N) → ℝ) (a b : ℝ)
      (G H : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ),
    ConsensusADMM.GramCycle.supportFunctional z w (a • G + b • H) =
      a * ConsensusADMM.GramCycle.supportFunctional z w G +
        b * ConsensusADMM.GramCycle.supportFunctional z w H)

/- Proposition 4.1.4 (3): simultaneous cyclic invariance makes the three
independent Gram blocks circulant, while positive semidefiniteness identifies
the fourth block as the transpose of the mixed block. -/
#check (ConsensusADMM.GramCycle.circulantBlocks :
  ∀ {N : ℕ} (hN : 2 ≤ N)
      (G : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)
      (hG : G.PosSemidef) (hcyclic : ConsensusADMM.GramCycle.SimultaneouslyCyclic G),
    ∃ r₀₀ r₀₁ r₁₁ : Fin N → ℝ,
      ConsensusADMM.GramCycle.block G 0 0 = Matrix.circulant r₀₀ ∧
        ConsensusADMM.GramCycle.block G 0 1 = Matrix.circulant r₀₁ ∧
          ConsensusADMM.GramCycle.block G 1 1 = Matrix.circulant r₁₁ ∧
            ConsensusADMM.GramCycle.block G 1 0 =
              (ConsensusADMM.GramCycle.block G 0 1).transpose)

/- Proposition 4.1.4 (4): finite semidefinite feasibility is equivalent to
the projection-cycle conditions for the two fixed convex hulls under the
canonical square-root realization. -/
#check (ConsensusADMM.GramCycle.feasible_iff_projectionCycle :
  ∀ {N : ℕ} (hN : 2 ≤ N) (γ : ℝ) (hγ : 0 < γ)
      (G : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)
      (hG : G.PosSemidef) (hcyclic : ConsensusADMM.GramCycle.SimultaneouslyCyclic G),
    ConsensusADMM.GramCycle.Feasible γ G ↔
      ConsensusADMM.IsProjectionCycle γ
        (fun i ↦ ConsensusADMM.GramCycle.gramMap G
          (ConsensusADMM.GramCycle.standardEta i))
        (fun i ↦ ConsensusADMM.GramCycle.gramMap G
          (ConsensusADMM.GramCycle.standardNu i)))
