/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Algorithm_2_1.Iteration

public section

namespace LALM

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {ρ β : ℝ}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

namespace Run

/-- The operational trace of a deterministic prefix: at transition `k`, the first
component is the exact objective-gradient oracle result and the second is the
stored solution of the Jacobian-induced linear system. -/
@[expose] noncomputable def exactGradientLinearSolveTrace
    (run : Run f c ρ β x₀ multiplier₀) (K : ℕ) :
    List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  (List.range K).map (fun k ↦ (gradient f (run.point k), run.step k))

/-- The deterministic operational trace is indexed by exactly the first `K`
transitions of the run. -/
theorem exactGradientLinearSolveTrace_def
    (run : Run f c ρ β x₀ multiplier₀) (K : ℕ) :
    run.exactGradientLinearSolveTrace K =
      (List.range K).map (fun k ↦ (gradient f (run.point k), run.step k)) := rfl

/-- Every trace entry records the exact gradient used at that transition and a
step satisfying the corresponding Jacobian-induced first-order linear system. -/
theorem exactGradientLinearSolveTrace_spec
    (run : Run f c ρ β x₀ multiplier₀) (K k : ℕ) (hk : k < K) :
    (gradient f (run.point k), run.step k) ∈
        run.exactGradientLinearSolveTrace K ∧
      β • run.step k + ρ •
          EqualityConstrained.constraintGradient c (run.point k)
            (fderiv ℝ c (run.point k) (run.step k)) =
        -gradient f (run.point k) -
          EqualityConstrained.constraintGradient c (run.point k)
            (run.multiplier k + ρ • c (run.point k)) := by
  refine ⟨?_, run.optimality k⟩
  simp only [exactGradientLinearSolveTrace, List.mem_map, List.mem_range]
  exact ⟨k, hk, rfl⟩

/-- The number of deterministic NR-LALM transitions in a traced prefix. -/
@[expose] noncomputable def iterationCount
    (run : Run f c ρ β x₀ multiplier₀) (K : ℕ) : ℕ :=
  (run.exactGradientLinearSolveTrace K).length

/-- The trace contains exactly one deterministic NR-LALM transition per index below `K`. -/
theorem iterationCount_spec
    (run : Run f c ρ β x₀ multiplier₀) (K : ℕ) :
    run.iterationCount K = K := by
  simp [iterationCount, exactGradientLinearSolveTrace]

/-- The number of exact first-order oracle evaluations in a deterministic prefix. -/
@[expose] noncomputable def firstOrderOracleEvaluationCount
    (run : Run f c ρ β x₀ multiplier₀) (K : ℕ) : ℕ :=
  (run.exactGradientLinearSolveTrace K).length

/-- Exact-gradient LALM performs exactly one first-order oracle evaluation per transition. -/
theorem firstOrderOracleEvaluationCount_spec
    (run : Run f c ρ β x₀ multiplier₀) (K : ℕ) :
    run.firstOrderOracleEvaluationCount K = K := by
  simp [firstOrderOracleEvaluationCount, exactGradientLinearSolveTrace]

/-- Theorem 2.12: the objective-gradient evaluations used by a deterministic
prefix, one at the current point of every transition. -/
@[expose] noncomputable def objectiveGradientEvaluationCount
    (run : Run f c ρ β x₀ multiplier₀) (K : ℕ) : ℕ :=
  ((List.range K).map (fun k ↦ gradient f (run.point k))).length

/-- Theorem 2.12: deterministic NR-LALM evaluates the objective gradient once
per transition. -/
theorem objectiveGradientEvaluationCount_spec
    (run : Run f c ρ β x₀ multiplier₀) (K : ℕ) :
    run.objectiveGradientEvaluationCount K = K := by
  simp [objectiveGradientEvaluationCount]

/-- Theorem 2.12: the constraint-residual evaluations consist of the one-time
initial value and the new residual produced by every transition. -/
@[expose] noncomputable def constraintEvaluationCount
    (run : Run f c ρ β x₀ multiplier₀) (K : ℕ) : ℕ :=
  ((List.range (K + 1)).map (fun k ↦ c (run.point k))).length

/-- Theorem 2.12: a length-`K` deterministic prefix uses `K + 1` constraint
evaluations when the one-time value `c x₀` is included. -/
theorem constraintEvaluationCount_spec
    (run : Run f c ρ β x₀ multiplier₀) (K : ℕ) :
    run.constraintEvaluationCount K = K + 1 := by
  simp [constraintEvaluationCount]

/-- Theorem 2.12: the constraint-Jacobian evaluations used at the current
point of every deterministic transition. -/
@[expose] noncomputable def jacobianEvaluationCount
    (run : Run f c ρ β x₀ multiplier₀) (K : ℕ) : ℕ :=
  ((List.range K).map (fun k ↦ fderiv ℝ c (run.point k))).length

/-- Theorem 2.12: deterministic NR-LALM evaluates one constraint Jacobian per
transition. -/
theorem jacobianEvaluationCount_spec
    (run : Run f c ρ β x₀ multiplier₀) (K : ℕ) :
    run.jacobianEvaluationCount K = K := by
  simp [jacobianEvaluationCount]

/-- The number of exact Jacobian-induced linear-system solves in a deterministic prefix. -/
@[expose] noncomputable def jacobianLinearSystemSolveCount
    (run : Run f c ρ β x₀ multiplier₀) (K : ℕ) : ℕ :=
  (run.exactGradientLinearSolveTrace K).length

/-- Exact-gradient LALM performs exactly one certified Jacobian-induced solve per transition. -/
theorem jacobianLinearSystemSolveCount_spec
    (run : Run f c ρ β x₀ multiplier₀) (K : ℕ) :
    run.jacobianLinearSystemSolveCount K = K := by
  simp [jacobianLinearSystemSolveCount, exactGradientLinearSolveTrace]

end Run

end LALM

end
