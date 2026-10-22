/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Algorithm_2_1.Iteration

public section

namespace LALM.Run

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {ρ β : ℝ}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- Fixed-penalty NR-LALM runs with the same functions, parameters, and initial data
are equal. -/
theorem eq (run₁ run₂ : Run f c ρ β x₀ multiplier₀) : run₁ = run₂ := by
  -- Simultaneously propagate equality of points, multipliers, and minimizing steps.
  have hsequences (k : ℕ) :
      run₁.point k = run₂.point k ∧
        run₁.multiplier k = run₂.multiplier k ∧ run₁.step k = run₂.step k := by
    induction k with
    | zero =>
        have hpoint : run₁.point 0 = run₂.point 0 :=
          run₁.point_zero.trans run₂.point_zero.symm
        have hmultiplier : run₁.multiplier 0 = run₂.multiplier 0 :=
          run₁.multiplier_zero.trans run₂.multiplier_zero.symm
        have hminimizes :
            IsMinOn (stepModel f c ρ β (run₂.point 0) (run₂.multiplier 0)) Set.univ
              (run₁.step 0) := by
          simpa only [hpoint, hmultiplier] using run₁.minimizes_step 0
        have hstep : run₁.step 0 = run₂.step 0 :=
          run₂.eq_step_of_minimizes 0 (run₁.step 0) hminimizes
        exact ⟨hpoint, hmultiplier, hstep⟩
    | succ k ih =>
        have hpoint : run₁.point (k + 1) = run₂.point (k + 1) := by
          calc
            run₁.point (k + 1) = run₁.point k + run₁.step k := run₁.point_succ k
            _ = run₂.point k + run₂.step k := congrArg₂ (fun x y ↦ x + y) ih.1 ih.2.2
            _ = run₂.point (k + 1) := (run₂.point_succ k).symm
        have hmultiplier :
            run₁.multiplier (k + 1) = run₂.multiplier (k + 1) := by
          calc
            run₁.multiplier (k + 1) =
                run₁.multiplier k + ρ • c (run₁.point (k + 1)) :=
              run₁.multiplier_succ k
            _ = run₂.multiplier k + ρ • c (run₂.point (k + 1)) := by
              rw [ih.2.1, hpoint]
            _ = run₂.multiplier (k + 1) := (run₂.multiplier_succ k).symm
        have hminimizes :
            IsMinOn
              (stepModel f c ρ β (run₂.point (k + 1)) (run₂.multiplier (k + 1)))
              Set.univ (run₁.step (k + 1)) := by
          simpa only [hpoint, hmultiplier] using run₁.minimizes_step (k + 1)
        have hstep : run₁.step (k + 1) = run₂.step (k + 1) :=
          run₂.eq_step_of_minimizes (k + 1) (run₁.step (k + 1)) hminimizes
        exact ⟨hpoint, hmultiplier, hstep⟩
  have hpoint : run₁.point = run₂.point :=
    funext fun k ↦ (hsequences k).1
  have hmultiplier : run₁.multiplier = run₂.multiplier :=
    funext fun k ↦ (hsequences k).2.1
  have hstep : run₁.step = run₂.step :=
    funext fun k ↦ (hsequences k).2.2
  -- The remaining fields are propositions, so equality of the data fields closes the structure.
  cases run₁
  cases run₂
  rw [Run.mk.injEq]
  exact ⟨hpoint, hmultiplier, hstep⟩

end LALM.Run

end
