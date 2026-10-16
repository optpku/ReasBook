module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Problem

@[expose] public section

namespace ADMM

/-- A chosen exact ADMM trajectory whose two block objectives attain finite minima at every step. -/
structure Trajectory {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β γ : ℝ) where
  /-- The selected first-block iterates, including their arbitrary initial value. -/
  x : ℕ → Fin n₁ → ℝ
  /-- The selected second-block iterates, including their arbitrary initial value. -/
  y : ℕ → Fin n₂ → ℝ
  /-- The multiplier iterates, including their arbitrary initial value. -/
  multiplier : ℕ → Fin m → ℝ
  /-- Every first-block update attains a finite minimum. -/
  firstMinimizes : ∀ k,
    IsFiniteMinimizer (P.firstBlockObjective β (multiplier k) (y k)) (x (k + 1))
  /-- Every second-block update attains a finite minimum. -/
  secondMinimizes : ∀ k,
    IsFiniteMinimizer (P.secondBlockObjective β (multiplier k) (x (k + 1))) (y (k + 1))
  /-- The multiplier follows the relaxed residual update. -/
  multiplierStep : ∀ k, multiplier (k + 1) = multiplier k +
    (γ * β) • (P.A.mulVec (x (k + 1)) + P.B.mulVec (y (k + 1)) - P.b)

namespace Trajectory

/-- Construct an exact trajectory from explicit sequences and their three step laws. -/
def ofSequences {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m} {β γ : ℝ}
    (x : ℕ → Fin n₁ → ℝ) (y : ℕ → Fin n₂ → ℝ)
    (multiplier : ℕ → Fin m → ℝ)
    (hx : ∀ k, IsFiniteMinimizer (P.firstBlockObjective β (multiplier k) (y k)) (x (k + 1)))
    (hy : ∀ k,
      IsFiniteMinimizer (P.secondBlockObjective β (multiplier k) (x (k + 1))) (y (k + 1)))
    (hmultiplier : ∀ k, multiplier (k + 1) = multiplier k +
      (γ * β) • (P.A.mulVec (x (k + 1)) + P.B.mulVec (y (k + 1)) - P.b)) : Trajectory P β γ :=
  ⟨x, y, multiplier, hx, hy, hmultiplier⟩

/-- A trajectory is admissible when its objectives are closed proper convex and
its penalty and multiplier factors are positive. -/
def IsAdmissible {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m} {β γ : ℝ}
    (_ : Trajectory P β γ) : Prop :=
  P.IsClosedProperConvex ∧ 0 < β ∧ 0 < γ

/-- Characterization of the assumptions that make a trajectory admissible. -/
lemma isAdmissible_iff {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m} {β γ : ℝ}
    (t : Trajectory P β γ) :
    t.IsAdmissible ↔ P.IsClosedProperConvex ∧ 0 < β ∧ 0 < γ := by
  -- Unfolding admissibility exposes exactly the three stated assumptions.
  rfl

/-- At each step, a trajectory satisfies both finite-minimum laws and the multiplier recurrence. -/
lemma spec {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m} {β γ : ℝ}
    (t : Trajectory P β γ) (k : ℕ) :
    IsFiniteMinimizer (P.firstBlockObjective β (t.multiplier k) (t.y k)) (t.x (k + 1)) ∧
      IsFiniteMinimizer (P.secondBlockObjective β (t.multiplier k) (t.x (k + 1))) (t.y (k + 1)) ∧
      t.multiplier (k + 1) = t.multiplier k +
        (γ * β) • (P.A.mulVec (t.x (k + 1)) + P.B.mulVec (t.y (k + 1)) - P.b) := by
  -- Split the specification and expose the three corresponding trajectory fields.
  constructor
  · exact t.firstMinimizes k
  · constructor
    · exact t.secondMinimizes k
    · exact t.multiplierStep k

/-- An admissible trajectory is characterized by the objective assumptions,
positive parameters, sequential finite minimizations, and relaxed multiplier recurrence. -/
lemma admissible_spec {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m} {β γ : ℝ}
    (t : Trajectory P β γ) :
    t.IsAdmissible ↔
      P.IsClosedProperConvex ∧ 0 < β ∧ 0 < γ ∧ ∀ k,
        IsFiniteMinimizer
          (P.firstBlockObjective β (t.multiplier k) (t.y k)) (t.x (k + 1)) ∧
        IsFiniteMinimizer
          (P.secondBlockObjective β (t.multiplier k) (t.x (k + 1))) (t.y (k + 1)) ∧
        t.multiplier (k + 1) = t.multiplier k +
          (γ * β) • (P.A.mulVec (t.x (k + 1)) + P.B.mulVec (t.y (k + 1)) - P.b) := by
  -- Separate the admissibility assumptions from the update laws inherent in the trajectory.
  constructor
  · intro ht
    obtain ⟨hP, hβ, hγ⟩ := (isAdmissible_iff t).mp ht
    refine ⟨hP, hβ, hγ, ?_⟩
    intro k
    exact t.spec k
  · rintro ⟨hP, hβ, hγ, _⟩
    -- The quantified update laws are already structure fields, so admissibility uses only positivity.
    exact (isAdmissible_iff t).mpr ⟨hP, hβ, hγ⟩

/-- The primal feasibility residual `A (x k) + B (y k) - b`. -/
def primalResidual {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m} {β γ : ℝ}
    (t : Trajectory P β γ) (k : ℕ) : Fin m → ℝ :=
  P.A.mulVec (t.x k) + P.B.mulVec (t.y k) - P.b

/-- Evaluation of the primal feasibility residual. -/
lemma primalResidual_apply {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m} {β γ : ℝ}
    (t : Trajectory P β γ) (k : ℕ) :
    t.primalResidual k = P.A.mulVec (t.x k) + P.B.mulVec (t.y k) - P.b := by
  -- The displayed residual is the defining value of `primalResidual`.
  rfl

/-- The image under `B` of the change in the second primal block. -/
def secondIncrement {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m} {β γ : ℝ}
    (t : Trajectory P β γ) (k : ℕ) : Fin m → ℝ :=
  P.B.mulVec (t.y k - t.y (k - 1))

/-- For `1 ≤ k`, evaluation of the second-block increment `B (y k - y (k - 1))`. -/
lemma secondIncrement_apply {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m} {β γ : ℝ}
    (t : Trajectory P β γ) (k : ℕ) (hk : 1 ≤ k) :
    t.secondIncrement k = P.B.mulVec (t.y k - t.y (k - 1)) := by
  -- Natural subtraction makes the definition meaningful independently of `hk`.
  rfl

end Trajectory

end ADMM
