module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.FixedPolytopes
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Realization

@[expose] public section

open scoped RealInnerProductSpace

/- Proposition 4.1.6 (1): the explicit period-48 Gram matrix H = 2K - I₉₆ + 3hhᵀ is positive definite. -/
#check (ConsensusADMM.Period48.FixedPolytopes.gramMatrix_posDef :
  (ConsensusADMM.Period48.gramMatrix).PosDef)

/- Proposition 4.1.6 (2): the realized cycle data η_i = S e_i, w_i = γ₀⁻¹ S e_{48+i}, ρ_i = w_i - w_{i-1}, ξ_i = η_i + ρ_i, the multiplier vertices ν_i(γ) = γ w_i, and the two hulls. -/
#check (ConsensusADMM.Period48.Realization.eta :
  Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ → ZMod 48 → EuclideanSpace ℝ (Fin 2 × Fin 48))
#check (ConsensusADMM.Period48.Realization.w :
  Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ → ZMod 48 → EuclideanSpace ℝ (Fin 2 × Fin 48))
#check (ConsensusADMM.Period48.Realization.rho :
  Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ → ZMod 48 → EuclideanSpace ℝ (Fin 2 × Fin 48))
#check (ConsensusADMM.Period48.Realization.xi :
  Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ → ZMod 48 → EuclideanSpace ℝ (Fin 2 × Fin 48))
#check (ConsensusADMM.Period48.Realization.nu :
  Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ → ℝ → ZMod 48 →
    EuclideanSpace ℝ (Fin 2 × Fin 48))
#check (ConsensusADMM.Period48.Realization.xSet :
  Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ → Set (EuclideanSpace ℝ (Fin 2 × Fin 48)))
#check (ConsensusADMM.Period48.Realization.ySet :
  Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ → Set (EuclideanSpace ℝ (Fin 2 × Fin 48)))
#check (ConsensusADMM.Period48.Realization.residual_eq :
  ∀ (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (γ : ℝ), γ ≠ 0 → ∀ i : ZMod 48,
    ConsensusADMM.ProjectionCycle.residual γ (ConsensusADMM.Period48.Realization.nu S γ) i =
      ConsensusADMM.Period48.Realization.rho S i)
#check (ConsensusADMM.Period48.Realization.xVertex_eq :
  ∀ (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (γ : ℝ), γ ≠ 0 → ∀ i : ZMod 48,
    ConsensusADMM.ProjectionCycle.xVertex γ (ConsensusADMM.Period48.Realization.eta S)
      (ConsensusADMM.Period48.Realization.nu S γ) i =
      ConsensusADMM.Period48.Realization.xi S i)

/- Proposition 4.1.6, normal formulas: aᵢ(γ) = ηᵢ₋₁ - γ wᵢ₋₁ - ξᵢ and cᵢ(γ) = γ wᵢ₋₁ + ρᵢ. -/
#check (ConsensusADMM.Period48.Realization.firstNormal_eq :
  ∀ (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (γ : ℝ), γ ≠ 0 → ∀ i : ZMod 48,
    ConsensusADMM.ProjectionCycle.firstNormal γ (ConsensusADMM.Period48.Realization.eta S)
        (ConsensusADMM.Period48.Realization.nu S γ) i =
      ConsensusADMM.Period48.Realization.eta S (i - 1) -
        γ • ConsensusADMM.Period48.Realization.w S (i - 1) -
        ConsensusADMM.Period48.Realization.xi S i)
#check (ConsensusADMM.Period48.Realization.secondNormal_eq :
  ∀ (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (γ : ℝ), γ ≠ 0 → ∀ i : ZMod 48,
    ConsensusADMM.ProjectionCycle.secondNormal γ (ConsensusADMM.Period48.Realization.nu S γ) i =
      γ • ConsensusADMM.Period48.Realization.w S (i - 1) +
        ConsensusADMM.Period48.Realization.rho S i)

/- Proposition 4.1.6 (3): the two convex hulls of the cycle are the fixed polytopes xSet S and ySet S on the critical half-line. -/
#check (ConsensusADMM.Period48.FixedPolytopes.xSet_ySet_eq :
  ∀ (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (γ : ℝ),
    ConsensusADMM.criticalFactor ≤ γ →
      ConsensusADMM.ProjectionCycle.xSet γ (ConsensusADMM.Period48.Realization.eta S)
            (ConsensusADMM.Period48.Realization.nu S γ) =
          ConsensusADMM.Period48.Realization.xSet S ∧
        ConsensusADMM.ProjectionCycle.ySet (ConsensusADMM.Period48.Realization.eta S) =
          ConsensusADMM.Period48.Realization.ySet S)

/- Proposition 4.1.6 (4): the realized families form a projection cycle for every Gram factor and every multiplier on the critical half-line. -/
#check (ConsensusADMM.Period48.FixedPolytopes.isProjectionCycle :
  ∀ (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ),
    S.transpose * S = ConsensusADMM.Period48.gramMatrix → ∀ (γ : ℝ),
      ConsensusADMM.criticalFactor ≤ γ →
        ConsensusADMM.IsProjectionCycle γ (ConsensusADMM.Period48.Realization.eta S)
          (ConsensusADMM.Period48.Realization.nu S γ))

/- Proposition 4.1.6 (5): the prescribed sequences are an indicator-objective consensus ADMM trajectory of exact period 48 on the critical half-line. -/
#check (ConsensusADMM.Period48.FixedPolytopes.trajectory_exactPeriod :
  ∀ (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ),
    S.transpose * S = ConsensusADMM.Period48.gramMatrix → ∀ (γ : ℝ),
      ConsensusADMM.criticalFactor ≤ γ →
        ConsensusADMM.IsTrajectory γ
            (ConsensusADMM.extendedIndicator
              (ConsensusADMM.Period48.Realization.xSet S))
            (ConsensusADMM.extendedIndicator
              (ConsensusADMM.Period48.Realization.ySet S))
            (ConsensusADMM.ProjectionCycle.xSequence γ
              (ConsensusADMM.Period48.Realization.eta S)
              (ConsensusADMM.Period48.Realization.nu S γ))
            (ConsensusADMM.ProjectionCycle.ySequence
              (ConsensusADMM.Period48.Realization.eta S))
            (ConsensusADMM.ProjectionCycle.dualSequence
              (ConsensusADMM.Period48.Realization.nu S γ)) ∧
          ConsensusADMM.HasExactPeriod 48
            (ConsensusADMM.ProjectionCycle.xSequence γ
              (ConsensusADMM.Period48.Realization.eta S)
              (ConsensusADMM.Period48.Realization.nu S γ))
            (ConsensusADMM.ProjectionCycle.ySequence
              (ConsensusADMM.Period48.Realization.eta S))
            (ConsensusADMM.ProjectionCycle.dualSequence
              (ConsensusADMM.Period48.Realization.nu S γ)))

/- Proposition 4.1.6 (6): the residual norm is constant and positive on the critical half-line. -/
#check (ConsensusADMM.Period48.FixedPolytopes.constantPositiveResidual :
  ∀ (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ),
    S.transpose * S = ConsensusADMM.Period48.gramMatrix → ∀ (γ : ℝ),
      ConsensusADMM.criticalFactor ≤ γ → ∃ c : ℝ, 0 < c ∧ ∀ i : ZMod 48,
        ‖ConsensusADMM.ProjectionCycle.residual γ
            (ConsensusADMM.Period48.Realization.nu S γ) i‖ = c)

/- Proposition 4.1.6 (7): at the critical factor every second-block support against the origin or a nonself phase is strict. -/
#check (ConsensusADMM.Period48.FixedPolytopes.secondSupports_strict :
  ∀ (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ),
    S.transpose * S = ConsensusADMM.Period48.gramMatrix → ∀ i : ZMod 48,
      0 < inner ℝ (ConsensusADMM.ProjectionCycle.secondNormal ConsensusADMM.criticalFactor
            (ConsensusADMM.Period48.Realization.nu S ConsensusADMM.criticalFactor) i)
          (ConsensusADMM.Period48.Realization.eta S i) ∧
        ∀ j : ZMod 48, j ≠ i →
          0 < inner ℝ (ConsensusADMM.ProjectionCycle.secondNormal ConsensusADMM.criticalFactor
                (ConsensusADMM.Period48.Realization.nu S ConsensusADMM.criticalFactor) i)
              (ConsensusADMM.Period48.Realization.eta S i -
                ConsensusADMM.Period48.Realization.eta S j))

/- Proposition 4.1.6 (8): first-block origin supports are strict, and among nonself phases equality occurs exactly at displacement -10. -/
#check (ConsensusADMM.Period48.FixedPolytopes.firstSupports_zero_iff :
  ∀ (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ),
    S.transpose * S = ConsensusADMM.Period48.gramMatrix → ∀ i : ZMod 48,
      0 < inner ℝ (ConsensusADMM.ProjectionCycle.firstNormal ConsensusADMM.criticalFactor
            (ConsensusADMM.Period48.Realization.eta S)
            (ConsensusADMM.Period48.Realization.nu S ConsensusADMM.criticalFactor) i)
          (ConsensusADMM.Period48.Realization.xi S i) ∧
        ∀ j : ZMod 48, j ≠ i →
          (inner ℝ (ConsensusADMM.ProjectionCycle.firstNormal ConsensusADMM.criticalFactor
                (ConsensusADMM.Period48.Realization.eta S)
                (ConsensusADMM.Period48.Realization.nu S ConsensusADMM.criticalFactor) i)
              (ConsensusADMM.Period48.Realization.xi S i -
                ConsensusADMM.Period48.Realization.xi S j) = 0 ↔ j = i - 10))

/- The realized hulls are compact convex polytopes, the geometric input of the period-48 counterexample. -/
#check (ConsensusADMM.Period48.FixedPolytopes.xSet_ySet_isCompactConvexPolytope :
  ∀ S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ,
    ConsensusADMM.IsCompactConvexPolytope (ConsensusADMM.Period48.Realization.xSet S) ∧
      ConsensusADMM.IsCompactConvexPolytope (ConsensusADMM.Period48.Realization.ySet S))
