module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Threshold
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Trajectory
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Optimality

@[expose] public section

open scoped RealInnerProductSpace

universe u

/- Compatibility checks for the migrated consensus ADMM threshold API. -/
#check (ConsensusADMM.criticalFactor : ℝ)
#check (ConsensusADMM.criticalFactor_eq :
  ConsensusADMM.criticalFactor = 542407991247 / 287451196000)
#check (ConsensusADMM.criticalFactor_pos : 0 < ConsensusADMM.criticalFactor)

/- Compatibility checks for the migrated consensus ADMM trajectory API. -/
#check (ConsensusADMM.IsTrajectory :
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    ℝ → (E → EReal) → (E → EReal) → (ℕ → E) → (ℕ → E) → (ℕ → E) → Prop)
#check (ConsensusADMM.trajectory_iff :
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      {γ : ℝ} {f g : E → EReal} {x y dual : ℕ → E},
    ConsensusADMM.IsTrajectory γ f g x y dual ↔
      ∀ k,
        (∀ z,
          f (x (k + 1)) +
              ((inner ℝ (dual k) (x (k + 1) - y k) +
                ‖x (k + 1) - y k‖ ^ 2 / 2 : ℝ) : EReal) ≤
            f z + ((inner ℝ (dual k) (z - y k) +
              ‖z - y k‖ ^ 2 / 2 : ℝ) : EReal)) ∧
        (∀ z,
          g (y (k + 1)) +
              ((inner ℝ (dual k) (x (k + 1) - y (k + 1)) +
                ‖x (k + 1) - y (k + 1)‖ ^ 2 / 2 : ℝ) : EReal) ≤
            g z + ((inner ℝ (dual k) (x (k + 1) - z) +
              ‖x (k + 1) - z‖ ^ 2 / 2 : ℝ) : EReal)) ∧
        f (x (k + 1)) ≠ ⊤ ∧ g (y (k + 1)) ≠ ⊤ ∧
        dual (k + 1) = dual k + γ • (x (k + 1) - y (k + 1)))
#check (ConsensusADMM.HasUniqueUpdates :
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    (E → EReal) → (E → EReal) → (ℕ → E) → (ℕ → E) → (ℕ → E) → Prop)
#check (ConsensusADMM.uniqueUpdates_iff :
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      {f g : E → EReal} {x y dual : ℕ → E},
    ConsensusADMM.HasUniqueUpdates f g x y dual ↔
      ∀ k,
        (∀ z,
          f z + ((inner ℝ (dual k) (z - y k) +
            ‖z - y k‖ ^ 2 / 2 : ℝ) : EReal) ≤
              f (x (k + 1)) +
                ((inner ℝ (dual k) (x (k + 1) - y k) +
                  ‖x (k + 1) - y k‖ ^ 2 / 2 : ℝ) : EReal) →
            z = x (k + 1)) ∧
        (∀ z,
          g z + ((inner ℝ (dual k) (x (k + 1) - z) +
            ‖x (k + 1) - z‖ ^ 2 / 2 : ℝ) : EReal) ≤
              g (y (k + 1)) +
                ((inner ℝ (dual k) (x (k + 1) - y (k + 1)) +
                  ‖x (k + 1) - y (k + 1)‖ ^ 2 / 2 : ℝ) : EReal) →
            z = y (k + 1)))
#check (ConsensusADMM.HasExactPeriod :
  ∀ {E : Type u}, ℕ → (ℕ → E) → (ℕ → E) → (ℕ → E) → Prop)
#check (ConsensusADMM.exactPeriod_iff :
  ∀ {E : Type u} {N : ℕ} {x y dual : ℕ → E},
    ConsensusADMM.HasExactPeriod N x y dual ↔
      Function.Periodic (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N ∧
        ∀ n, 0 < n →
          Function.Periodic
            (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) n → N ≤ n)

/- Compatibility checks for the migrated consensus optimality API. -/
#check (ConsensusADMM.IsKKT :
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    (E → EReal) → (E → EReal) → E → E → E → Prop)
#check (ConsensusADMM.kkt_iff :
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      {f g : E → EReal} {x y dual : E},
    ConsensusADMM.IsKKT f g x y dual ↔
      x = y ∧
        (∀ z, f x + ((inner ℝ (-dual) (z - x) : ℝ) : EReal) ≤ f z) ∧
        ∀ z, g y + ((inner ℝ dual (z - y) : ℝ) : EReal) ≤ g z)
#check (ConsensusADMM.IsPrimalMinimizer :
  ∀ {E : Type u}, (E → EReal) → (E → EReal) → E → Prop)
#check (ConsensusADMM.primalMinimizer_iff :
  ∀ {E : Type u} {f g : E → EReal} {z : E},
    ConsensusADMM.IsPrimalMinimizer f g z ↔
      ∀ w, f z + g z ≤ f w + g w)
