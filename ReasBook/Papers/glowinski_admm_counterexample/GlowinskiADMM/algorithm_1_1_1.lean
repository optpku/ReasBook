/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Trajectory

@[expose] public section

/- Algorithm 1.1.1: A trajectory of the relaxed two-block ADMM method for a
closed proper convex linearly constrained problem. The penalty `β` and
multiplier factor `γ` are positive. The first update minimizes with `y k`, the
second minimizes with the already updated `x (k + 1)`, and only the multiplier
update contains `γ`. -/
#check (ADMM.Trajectory.admissible_spec :
  ∀ {n₁ n₂ m : ℕ} {P : ADMM.Problem n₁ n₂ m} {β γ : ℝ}
      (t : ADMM.Trajectory P β γ),
    t.IsAdmissible ↔
      P.IsClosedProperConvex ∧ 0 < β ∧ 0 < γ ∧ ∀ k,
        ADMM.IsFiniteMinimizer
          (P.firstBlockObjective β (t.multiplier k) (t.y k)) (t.x (k + 1)) ∧
        ADMM.IsFiniteMinimizer
          (P.secondBlockObjective β (t.multiplier k) (t.x (k + 1))) (t.y (k + 1)) ∧
        t.multiplier (k + 1) = t.multiplier k +
          (γ * β) • (P.A.mulVec (t.x (k + 1)) + P.B.mulVec (t.y (k + 1)) - P.b))

#check (ADMM.Problem.objective_apply :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m)
      (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ),
    P.objective x y = P.f x + P.g y)

#check (ADMM.Problem.isFeasible_iff :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m)
      (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ),
    P.IsFeasible x y ↔ P.A.mulVec x + P.B.mulVec y = P.b)

#check (ADMM.Problem.firstBlockObjective_apply :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m) (β : ℝ)
      (multiplier : Fin m → ℝ) (y : Fin n₂ → ℝ) (x : Fin n₁ → ℝ),
    P.firstBlockObjective β multiplier y x =
      P.f x + dotProduct multiplier (P.A.mulVec x + P.B.mulVec y - P.b) +
        ((β / 2) * dotProduct (P.A.mulVec x + P.B.mulVec y - P.b)
          (P.A.mulVec x + P.B.mulVec y - P.b) : ℝ))

#check (ADMM.Problem.secondBlockObjective_apply :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m) (β : ℝ)
      (multiplier : Fin m → ℝ) (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ),
    P.secondBlockObjective β multiplier x y =
      P.g y + dotProduct multiplier (P.A.mulVec x + P.B.mulVec y - P.b) +
        ((β / 2) * dotProduct (P.A.mulVec x + P.B.mulVec y - P.b)
          (P.A.mulVec x + P.B.mulVec y - P.b) : ℝ))

#check (ADMM.Problem.multiplierUpdate_apply :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m) (β γ : ℝ)
      (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) (multiplier : Fin m → ℝ),
    P.multiplierUpdate β γ x y multiplier =
      multiplier + (γ * β) • (P.A.mulVec x + P.B.mulVec y - P.b))
