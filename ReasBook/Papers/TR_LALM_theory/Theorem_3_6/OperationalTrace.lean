/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Lemma_3_3.Iteration

public section

open MeasureTheory
open scoped BigOperators

namespace LALM.StochasticRun

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : LALM.Parameters h x₀ multiplier₀} {Q B b : ℕ+}

/-- The stochastic-gradient evaluations made by a SPIDER-driven stochastic
LALM prefix: a refresh uses `B` evaluations and an update uses `b` evaluations
at each of two consecutive points. -/
@[expose] def gradientEvaluationCount
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) : ℕ :=
  ((List.range K).flatMap (fun k ↦
    if k % (Q : ℕ) = 0 then
      (List.range B).map (fun i ↦ run.sample k i)
    else
      (List.range b).map (fun i ↦ run.sample k i) ++
        (List.range b).map (fun i ↦ run.sample k i))).length

/-- The SPIDER gradient counter is the sum of its refresh and recursive-update
batch costs. -/
theorem gradientEvaluationCount_spec
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) :
    run.gradientEvaluationCount K = ∑ k ∈ Finset.range K,
      if k % (Q : ℕ) = 0 then (B : ℕ) else 2 * (b : ℕ) := by
  unfold gradientEvaluationCount
  rw [List.length_flatMap]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  apply Finset.sum_congr rfl
  intro k hk
  split
  · simp
  · simp [two_mul]

/-- The constraint evaluations made by a stochastic NR-LALM prefix, one at the
new primal point of each transition. -/
@[expose] def constraintEvaluationCount
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) : ℕ :=
  ((List.range K).map (fun k ↦ fun ω ↦ c (run.point (k + 1) ω))).length

/-- A stochastic NR-LALM prefix evaluates the constraint once per transition. -/
theorem constraintEvaluationCount_spec
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) :
    run.constraintEvaluationCount K = K := by
  simp [constraintEvaluationCount]

/-- Theorem 3.6: the total constraint-residual work for a stochastic prefix
includes the one-time initialization value `c x₀` in addition to transition
residuals. -/
@[expose] noncomputable def totalConstraintEvaluationCount
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) : ℕ :=
  run.constraintEvaluationCount K + 1

/-- Theorem 3.6: a length-`K` stochastic prefix uses `K + 1` constraint
evaluations when initialization is charged. -/
theorem totalConstraintEvaluationCount_spec
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) :
    run.totalConstraintEvaluationCount K = K + 1 := by
  simp [totalConstraintEvaluationCount, constraintEvaluationCount]

/-- The constraint-Jacobian evaluations made by a stochastic NR-LALM prefix, one
at the current primal point of each transition. -/
@[expose] noncomputable def jacobianEvaluationCount
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) : ℕ :=
  ((List.range K).map (fun k ↦ fun ω ↦ fderiv ℝ c (run.point k ω))).length

/-- A stochastic NR-LALM prefix evaluates the constraint Jacobian once per
transition. -/
theorem jacobianEvaluationCount_spec
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) :
    run.jacobianEvaluationCount K = K := by
  simp [jacobianEvaluationCount]

/-- The Jacobian-induced linear-system solves made by a stochastic NR-LALM
prefix, represented by its computed step at each transition. -/
@[expose] def linearSystemSolveCount
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) : ℕ :=
  ((List.range K).map run.step).length

/-- A stochastic NR-LALM prefix performs one Jacobian-induced linear-system solve
per transition. -/
theorem linearSystemSolveCount_spec
    (run : LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) :
    run.linearSystemSolveCount K = K := by
  simp [linearSystemSolveCount]

end LALM.StochasticRun

end
