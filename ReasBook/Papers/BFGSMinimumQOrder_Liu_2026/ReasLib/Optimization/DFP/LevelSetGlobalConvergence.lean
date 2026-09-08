module

public import ReasLib.Optimization.DFP.GlobalConvergence

public section

noncomputable section

universe u

open Filter
open scoped Topology
open scoped Matrix

namespace DFP

/-- Helper for TASK-15: The initial objective sublevel set of a finite-dimensional DFP
iteration. -/
def objectiveSublevel {n : ℕ} (iteration : InverseIteration (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {z | iteration.objective z ≤ iteration.objective (iteration.point 0)}

/-- Helper for TASK-15: membership in the initial objective sublevel set is
exactly the corresponding objective-value inequality. -/
theorem mem_objectiveSublevel_iff {n : ℕ}
    (iteration : InverseIteration (Fin n)) (z : EuclideanSpace ℝ (Fin n)) :
    z ∈ objectiveSublevel iteration ↔
      iteration.objective z ≤ iteration.objective (iteration.point 0) := by
  rfl

/-- Helper for TASK-15: Hessian bounds restricted to the initial objective sublevel set.
The bounds are not imposed at points outside that set. -/
def HasHessianBoundsOnObjectiveSublevel {n : ℕ} (m M : ℝ)
    (iteration : InverseIteration (Fin n)) : Prop :=
  ∀ z ∈ objectiveSublevel iteration,
    HasHessianBoundsAt m M iteration.objective z

/-- Helper for TASK-15: a global Hessian bound restricts to every objective
sublevel set. -/
theorem HasHessianBounds.toObjectiveSublevel {n : ℕ} {m M : ℝ}
    {iteration : InverseIteration (Fin n)}
    (h : HasHessianBounds m M iteration.objective) :
    HasHessianBoundsOnObjectiveSublevel m M iteration := by
  intro z hz
  exact HasHessianBounds.at h z

/-- Helper for TASK-15: the nonzero secant denominator of an inverse-form DFP
iteration rules out a zero gradient at every index. -/
theorem InverseIteration.gradientNeZeroOfSecantDenominator {n : ℕ}
    (iteration : InverseIteration (Fin n)) (k : ℕ) :
    gradients iteration.objective iteration.point k ≠ 0 := by
  intro hzero
  apply iteration.secantDenominatorNe k
  rw [steps_apply, directions_apply, hzero]
  simp

/-- Helper for TASK-15: a positive DFP step length and a positive-definite
inverse Hessian make the actual displacement a strict descent step. -/
theorem InverseIteration.gradientInnerDisplacementNeg {n : ℕ}
    (iteration : InverseIteration (Fin n)) (k : ℕ)
    (hStep : 0 < iteration.stepLength k) :
    inner ℝ (gradients iteration.objective iteration.point k)
      (iteration.point (k + 1) - iteration.point k) < 0 := by
  have hGradient : gradients iteration.objective iteration.point k ≠ 0 :=
    iteration.gradientNeZeroOfSecantDenominator k
  have hEnergy : 0 <
      WithLp.ofLp (gradients iteration.objective iteration.point k) ⬝ᵥ
        (iteration.inverseHessian k *ᵥ
          WithLp.ofLp (gradients iteration.objective iteration.point k)) := by
    have hCoordinates :
        WithLp.ofLp (gradients iteration.objective iteration.point k) ≠ 0 := by
      intro hzero
      apply hGradient
      apply WithLp.ofLp_injective 2
      simpa only [WithLp.ofLp_zero] using hzero
    exact (iteration.inverseHessianPosDef k).dotProduct_mulVec_pos hCoordinates
  have hDirection :
      inner ℝ (gradients iteration.objective iteration.point k)
          (directions iteration.inverseHessian
            (gradients iteration.objective iteration.point) k) =
        -(WithLp.ofLp (gradients iteration.objective iteration.point k) ⬝ᵥ
          (iteration.inverseHessian k *ᵥ
            WithLp.ofLp (gradients iteration.objective iteration.point k))) := by
    rw [directions_apply, inner_neg_right,
      EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial]
    rw [dotProduct_comm]
  have hDisplacement :
      iteration.point (k + 1) - iteration.point k =
        steps iteration.stepLength
          (directions iteration.inverseHessian
            (gradients iteration.objective iteration.point)) k := by
    rw [iteration.pointSucc k]
    abel
  rw [hDisplacement, steps_apply, real_inner_smul_right, hDirection]
  nlinarith

/-- Helper for TASK-15: Armijo along a positive inverse-form DFP step makes the
objective value nonincreasing at that step. -/
theorem InverseIteration.objectiveSuccLeOfWeakWolfe {n : ℕ}
    (iteration : InverseIteration (Fin n)) {c₁ c₂ : ℝ} (k : ℕ)
    (hStep : 0 < iteration.stepLength k)
    (hWolfe : LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    iteration.objective (iteration.point (k + 1)) ≤
      iteration.objective (iteration.point k) := by
  have hDescent := iteration.gradientInnerDisplacementNeg k hStep
  have hCorrection :
      c₁ * inner ℝ (gradient iteration.objective (iteration.point k))
        (iteration.point (k + 1) - iteration.point k) ≤ 0 := by
    rw [← gradients_apply]
    exact mul_nonpos_of_nonneg_of_nonpos hWolfe.c₁_pos.le hDescent.le
  have hArmijo := hWolfe.armijo
  have hEndpoint :
      iteration.point k + (iteration.point (k + 1) - iteration.point k) =
        iteration.point (k + 1) := by
    abel
  rw [hEndpoint] at hArmijo
  exact hArmijo.trans (add_le_of_nonpos_right hCorrection)

/-- Helper for TASK-15: positive inverse-form DFP weak-Wolfe steps make the
objective values along the whole trajectory antitone. -/
theorem InverseIteration.objectiveValuesAntitoneOfWeakWolfe {n : ℕ}
    (iteration : InverseIteration (Fin n)) {c₁ c₂ : ℝ}
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    Antitone (fun k ↦ iteration.objective (iteration.point k)) := by
  apply antitone_nat_of_succ_le
  intro k
  exact iteration.objectiveSuccLeOfWeakWolfe k (hStep k) (hWolfe k)

/-- Helper for TASK-15: every point of a positive-step inverse-form DFP
weak-Wolfe trajectory stays in its initial objective sublevel set. -/
theorem InverseIteration.pointMemObjectiveSublevelOfWeakWolfe {n : ℕ}
    (iteration : InverseIteration (Fin n)) {c₁ c₂ : ℝ}
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    ∀ k, iteration.point k ∈ objectiveSublevel iteration := by
  have hAntitone := iteration.objectiveValuesAntitoneOfWeakWolfe hStep hWolfe
  intro k
  rw [mem_objectiveSublevel_iff]
  exact hAntitone (Nat.zero_le k)

/-- Helper for TASK-15: Paper-facing admissibility for an inverse-form DFP trajectory when
the Hessian bounds are assumed only on the initial objective sublevel set. -/
def LevelSetWeakWolfeAdmissible {n : ℕ} (m M c₁ c₂ : ℝ)
    (iteration : InverseIteration (Fin n)) : Prop :=
  0 < m ∧
    m ≤ M ∧
    ContDiff ℝ 2 iteration.objective ∧
    (∀ k, 0 < iteration.stepLength k) ∧
    HasHessianBoundsOnObjectiveSublevel m M iteration ∧
    (∀ k, iteration.point k ∈ objectiveSublevel iteration) ∧
    (∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))

/-- Helper for TASK-15: The level-set weak-Wolfe global convergence claim for fixed
coefficients. -/
def LevelSetGlobalWeakWolfeConvergenceAt (c₁ c₂ : ℝ) : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    ∀ (m M : ℝ) (iteration : InverseIteration (Fin n)),
      LevelSetWeakWolfeAdmissible m M c₁ c₂ iteration →
        Tendsto
          (fun k ↦ ‖gradients iteration.objective iteration.point k‖)
          atTop (𝓝 0)

/-- Helper for TASK-15: The universal level-set weak-Wolfe global convergence claim,
including all admissible Wolfe coefficients. -/
def UniversalLevelSetGlobalWeakWolfeConvergence : Prop :=
  ∀ (c₁ c₂ : ℝ), 0 < c₁ → c₁ < c₂ → c₂ < 1 →
    LevelSetGlobalWeakWolfeConvergenceAt c₁ c₂

/-- Helper for TASK-15: A certified global weak-Wolfe counterexample supplies the
level-set admissibility data used by the paper-facing predicate. -/
theorem WolfeCounterexample.levelSetWeakWolfeAdmissible
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (counterexample : WolfeCounterexample (Fin n) m M c₁ c₂)
    (hm : 0 < m) (hmM : m ≤ M) :
    LevelSetWeakWolfeAdmissible m M c₁ c₂ counterexample.iteration := by
  have hBounds : HasHessianBoundsOnObjectiveSublevel m M counterexample.iteration :=
    HasHessianBounds.toObjectiveSublevel counterexample.hessianBounds
  have hContainment : ∀ k,
      counterexample.iteration.point k ∈ objectiveSublevel counterexample.iteration :=
    counterexample.iteration.pointMemObjectiveSublevelOfWeakWolfe
      counterexample.stepLengthPos counterexample.weakWolfe
  exact ⟨hm, hmM, counterexample.objectiveContDiff,
    counterexample.stepLengthPos, hBounds, hContainment, counterexample.weakWolfe⟩

/-- TASK-15: Any weak-Wolfe counterexample disproves the level-set global
convergence claim at its own coefficients. -/
theorem not_levelSetGlobalWeakWolfeConvergenceAt_of_counterexample
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (counterexample : WolfeCounterexample (Fin n) m M c₁ c₂)
    (hn : 2 ≤ n) (hm : 0 < m) (hmM : m ≤ M) :
    ¬ LevelSetGlobalWeakWolfeConvergenceAt c₁ c₂ := by
  intro hGlobal
  have hzero := hGlobal n hn m M counterexample.iteration
    (WolfeCounterexample.levelSetWeakWolfeAdmissible counterexample hm hmM)
  exact (not_tendsto_zero_of_pos_limit counterexample.gradientLimitPos
    counterexample.gradientNormTendsto) hzero

/-- Helper for TASK-15: A single admissible counterexample refutes the universal
level-set global convergence claim over all Wolfe coefficients. -/
theorem not_universalLevelSetGlobalWeakWolfeConvergence_of_counterexample
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (counterexample : WolfeCounterexample (Fin n) m M c₁ c₂)
    (hn : 2 ≤ n) (hm : 0 < m) (hmM : m ≤ M)
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ¬ UniversalLevelSetGlobalWeakWolfeConvergence := by
  intro hGlobal
  exact (not_levelSetGlobalWeakWolfeConvergenceAt_of_counterexample
    counterexample hn hm hmM) (hGlobal c₁ c₂ hc₁ hc₁₂ hc₂)

end DFP
