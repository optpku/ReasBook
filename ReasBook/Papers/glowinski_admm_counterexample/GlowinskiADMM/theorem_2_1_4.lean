/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Counterexamples

@[expose] public section

/- Theorem 2.1.4 (1): one fixed pair of compact convex polytopes in ℝ⁹⁶
supports, for every multiplier factor at least ConsensusADMM.criticalFactor,
a unique-update consensus ADMM trajectory of exact period 48 and constant
positive residual. -/
#check (ConsensusADMM.fixedPolytopes :
    ∃ X Y : Set (EuclideanSpace ℝ (Fin 96)),
      ConsensusADMM.IsCompactConvexPolytope X ∧
      ConsensusADMM.IsCompactConvexPolytope Y ∧
      ConsensusADMM.IsKKT
        (ConsensusADMM.extendedIndicator X) (ConsensusADMM.extendedIndicator Y) 0 0 0 ∧
      ConsensusADMM.IsPrimalMinimizer
        (ConsensusADMM.extendedIndicator X) (ConsensusADMM.extendedIndicator Y) 0 ∧
      ConsensusADMM.extendedIndicator X 0 + ConsensusADMM.extendedIndicator Y 0 = 0 ∧
      ∀ γ, ConsensusADMM.criticalFactor ≤ γ →
        ∃ x y dual : ℕ → EuclideanSpace ℝ (Fin 96), ∃ c_r : ℝ,
          0 < c_r ∧
          ConsensusADMM.IsTrajectory γ
            (ConsensusADMM.extendedIndicator X) (ConsensusADMM.extendedIndicator Y)
            x y dual ∧
          ConsensusADMM.HasUniqueUpdates
            (ConsensusADMM.extendedIndicator X) (ConsensusADMM.extendedIndicator Y)
            x y dual ∧
          ConsensusADMM.HasExactPeriod 48 x y dual ∧
          ∀ k, ‖x (k + 1) - y (k + 1)‖ = c_r)

/- Theorem 2.1.4 (2): at ConsensusADMM.criticalFactor, smooth strongly
convex objectives on ℝ⁹⁶ with globally Lipschitz derivatives have a
unique-update period-48 trajectory of constant positive objective value,
while the origin is their unique primal optimum of value zero and forms a KKT
triple. -/
#check (ConsensusADMM.smoothCounterexample :
    ∃ f g : EuclideanSpace ℝ (Fin 96) → ℝ,
      ∃ μf μg : ℝ, ∃ Lf Lg : NNReal,
      ∃ x y dual : ℕ → EuclideanSpace ℝ (Fin 96), ∃ c_f : ℝ,
        0 < μf ∧ 0 < μg ∧
        StrongConvexOn Set.univ μf f ∧ StrongConvexOn Set.univ μg g ∧
        ContDiff ℝ 1 f ∧ ContDiff ℝ 1 g ∧
        LipschitzWith Lf (fderiv ℝ f) ∧ LipschitzWith Lg (fderiv ℝ g) ∧
        ConsensusADMM.IsTrajectory ConsensusADMM.criticalFactor
          (ConsensusADMM.ofReal f) (ConsensusADMM.ofReal g) x y dual ∧
        ConsensusADMM.HasUniqueUpdates
          (ConsensusADMM.ofReal f) (ConsensusADMM.ofReal g) x y dual ∧
        Function.Periodic (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) 48 ∧
        0 < c_f ∧ (∀ k, f (x (k + 1)) + g (y (k + 1)) = c_f) ∧
        ConsensusADMM.IsKKT
          (ConsensusADMM.ofReal f) (ConsensusADMM.ofReal g) 0 0 0 ∧
        ConsensusADMM.ofReal f 0 + ConsensusADMM.ofReal g 0 = 0 ∧
        ConsensusADMM.IsPrimalMinimizer
          (ConsensusADMM.ofReal f) (ConsensusADMM.ofReal g) 0 ∧
        ∀ z,
          ConsensusADMM.IsPrimalMinimizer
            (ConsensusADMM.ofReal f) (ConsensusADMM.ofReal g) z → z = 0)

/- Theorem 2.1.4 (3): finite closed convex piecewise-quadratic objectives at
ConsensusADMM.criticalFactor support a unique-update period-48 trajectory with
constant positive objective value, while the origin is KKT and has optimal
value zero. -/
#check (ConsensusADMM.periodicPiecewiseQuadratic :
    ∃ f g : EuclideanSpace ℝ (Fin 96) → ℝ,
      ∃ x y dual : ℕ → EuclideanSpace ℝ (Fin 96), ∃ c_f : ℝ,
        ConsensusADMM.IsFiniteClosedConvexPiecewiseQuadratic f ∧
        ConsensusADMM.IsFiniteClosedConvexPiecewiseQuadratic g ∧
        ConsensusADMM.IsTrajectory ConsensusADMM.criticalFactor
          (ConsensusADMM.ofReal f) (ConsensusADMM.ofReal g) x y dual ∧
        ConsensusADMM.HasUniqueUpdates
          (ConsensusADMM.ofReal f) (ConsensusADMM.ofReal g) x y dual ∧
        Function.Periodic (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) 48 ∧
        0 < c_f ∧ (∀ k, f (x (k + 1)) + g (y (k + 1)) = c_f) ∧
        ConsensusADMM.IsKKT
          (ConsensusADMM.ofReal f) (ConsensusADMM.ofReal g) 0 0 0 ∧
        ConsensusADMM.ofReal f 0 + ConsensusADMM.ofReal g 0 = 0 ∧
        ConsensusADMM.IsPrimalMinimizer
          (ConsensusADMM.ofReal f) (ConsensusADMM.ofReal g) 0)

/- Theorem 2.1.4 (4): another pair of finite closed convex
piecewise-quadratic objectives at ConsensusADMM.criticalFactor has uniquely
attained ADMM updates whose residual and objective values grow geometrically;
the origin is again KKT and has optimal value zero. -/
#check (ConsensusADMM.growingPiecewiseQuadratic :
    ∃ f g : EuclideanSpace ℝ (Fin 96) → ℝ,
      ∃ x y dual : ℕ → EuclideanSpace ℝ (Fin 96), ∃ c_r c_f κ : ℝ,
        ConsensusADMM.IsFiniteClosedConvexPiecewiseQuadratic f ∧
        ConsensusADMM.IsFiniteClosedConvexPiecewiseQuadratic g ∧
        ConsensusADMM.IsTrajectory ConsensusADMM.criticalFactor
          (ConsensusADMM.ofReal f) (ConsensusADMM.ofReal g) x y dual ∧
        ConsensusADMM.HasUniqueUpdates
          (ConsensusADMM.ofReal f) (ConsensusADMM.ofReal g) x y dual ∧
        0 < c_r ∧ 0 < c_f ∧ 1 < κ ∧
        (∀ k, ‖x (k + 1) - y (k + 1)‖ = c_r * κ ^ k) ∧
        (∀ k, f (x (k + 1)) + g (y (k + 1)) = c_f * κ ^ (2 * k)) ∧
        ConsensusADMM.IsKKT
          (ConsensusADMM.ofReal f) (ConsensusADMM.ofReal g) 0 0 0 ∧
        ConsensusADMM.ofReal f 0 + ConsensusADMM.ofReal g 0 = 0 ∧
        ConsensusADMM.IsPrimalMinimizer
          (ConsensusADMM.ofReal f) (ConsensusADMM.ofReal g) 0)
