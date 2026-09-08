module

public import ReasLib.Optimization.DFP.WolfeCounterexample

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP

/-- The admissibility data for a finite-dimensional inverse-form DFP trajectory
under fixed weak-Wolfe coefficients. -/
def WeakWolfeAdmissible {n : ℕ} (m M c₁ c₂ : ℝ)
    (iteration : InverseIteration (Fin n)) : Prop :=
  0 < m ∧
    m ≤ M ∧
    ContDiff ℝ 2 iteration.objective ∧
    (∀ k, 0 < iteration.stepLength k) ∧
    HasHessianBounds m M iteration.objective ∧
    (∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))

/-- The fixed-coefficient global convergence claim for inverse-form DFP. -/
def GlobalWeakWolfeConvergenceAt (c₁ c₂ : ℝ) : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    ∀ (m M : ℝ) (iteration : InverseIteration (Fin n)),
      WeakWolfeAdmissible m M c₁ c₂ iteration →
        Tendsto
          (fun k ↦ ‖gradients iteration.objective iteration.point k‖)
          atTop (𝓝 0)

/-- The universal weak-Wolfe global convergence claim, including all admissible
Wolfe coefficients. -/
def UniversalGlobalWeakWolfeConvergence : Prop :=
  ∀ (c₁ c₂ : ℝ), 0 < c₁ → c₁ < c₂ → c₂ < 1 →
    GlobalWeakWolfeConvergenceAt c₁ c₂

/-- A certified weak-Wolfe counterexample supplies the admissibility data used by
the global convergence predicate. -/
theorem WolfeCounterexample.weakWolfeAdmissible
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (counterexample : WolfeCounterexample (Fin n) m M c₁ c₂)
    (hm : 0 < m) (hmM : m ≤ M) :
    WeakWolfeAdmissible m M c₁ c₂ counterexample.iteration := by
  exact ⟨hm, hmM, counterexample.objectiveContDiff,
    counterexample.stepLengthPos, counterexample.hessianBounds,
    counterexample.weakWolfe⟩

/-- A real sequence with a strictly positive limit cannot converge to zero. -/
theorem not_tendsto_zero_of_pos_limit {u : ℕ → ℝ} {L : ℝ}
    (hL : 0 < L) (hLIM : Tendsto u atTop (𝓝 L)) :
    ¬ Tendsto u atTop (𝓝 0) := by
  intro hzero
  have hEq : L = 0 := tendsto_nhds_unique hLIM hzero
  linarith

/-- Any weak-Wolfe counterexample disproves the fixed-coefficient global
convergence claim at its own coefficients. -/
theorem not_globalWeakWolfeConvergenceAt_of_counterexample
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (counterexample : WolfeCounterexample (Fin n) m M c₁ c₂)
    (hn : 2 ≤ n) (hm : 0 < m) (hmM : m ≤ M) :
    ¬ GlobalWeakWolfeConvergenceAt c₁ c₂ := by
  intro hGlobal
  have hzero := hGlobal n hn m M counterexample.iteration
    (WolfeCounterexample.weakWolfeAdmissible counterexample hm hmM)
  exact (not_tendsto_zero_of_pos_limit counterexample.gradientLimitPos
    counterexample.gradientNormTendsto) hzero

/-- A single admissible weak-Wolfe counterexample refutes the universal global
convergence claim over all Wolfe coefficients. -/
theorem not_universalGlobalWeakWolfeConvergence_of_counterexample
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (counterexample : WolfeCounterexample (Fin n) m M c₁ c₂)
    (hn : 2 ≤ n) (hm : 0 < m) (hmM : m ≤ M)
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ¬ UniversalGlobalWeakWolfeConvergence := by
  intro hGlobal
  exact (not_globalWeakWolfeConvergenceAt_of_counterexample counterexample hn hm hmM)
    (hGlobal c₁ c₂ hc₁ hc₁₂ hc₂)

end DFP
