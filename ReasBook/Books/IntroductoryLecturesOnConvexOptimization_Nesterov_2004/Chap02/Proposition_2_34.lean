/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_33

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]
variable {m : ℕ} {μ L : ℝ}

section

variable {problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L}

variable {κ t0 tStar ε Qf : ℝ} {x0 : problem.ambientSet} {hL : 0 < L}
variable
  {hStep1a : ∀ xBar : problem.ambientSet, ∀ t : ℝ, ∃ j, step1aAt problem κ xBar t hL j}

local notation "initialViolation" =>
  problem.toLagrangianProblem.constrainedAuxiliaryObjective t0 x0

local notation "fullIterationBound" =>
  Real.log ((tStar - t0) / ((1 - κ) * ε)) / Real.log (2 * (1 - κ))

local notation "perIterationCost" =>
  1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / κ)

/- Primary domain: total internal complexity bounds for the Chapter 2 constrained minimization
scheme `(2.3.22)`.

Owner abstractions sampled before refining:
- `ConstrainedMinimizationMethod` in `Algorithm_2_11.lean`, the source-facing owner of the master
  process and the full internal stopping counts `j(k)`;
- `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` in
  `Definition_2_47.lean`, the owner fixed-`t` smooth minimax problem whose regularized exact
  value is the local-model quantity used in the stopping tests and terminal count bounds;
- `constrainedMinimization_error_le_target_of_iterationThreshold_le` in Proposition 2.29, the
  Chapter 2 owner of the logarithmic master-iteration bound `N(ε)`;
- `constrainedMinimization_totalIterationCount_le_logarithmic_bound` in Proposition 2.33, the
  owner corollary bound on `j* + ∑_{k=0}^N j(k)`;
- `LagrangianProblem.constrainedAuxiliaryObjective` in Lemma 2.21, the owner initial
  max-violation term `max {f₀(x₀) - t₀, fᵢ(x₀)}`.

Best owner abstraction:
- `ConstrainedMinimizationMethod`, together with the fixed-`t` owner
  `problem.toParametricSmoothMinimaxProblem t`; the displayed total-complexity estimate is then
  obtained by feeding the scheme's full-step counts into the upstream scalar owner bound from
  Proposition 2.33 and substituting the upstream master-iteration bound from Proposition 2.29.
  The textbook Euclidean statement is the specialization `E = EuclideanSpace ℝ (Fin n)`.

Primitive data here are the recursive outer owner together with the explicit Step `1(a)`
existence hypothesis `hStep1a`, the source index `N` of the last full master iteration, the final
internal-iteration count `jStar`, and the positive stage sequence `Δ` already used in
Proposition 2.33.
The public theorem below specializes the owner Proposition 2.33 hypotheses to
`j(k) = ConstrainedMinimizationMethod.stopIndex ... k` and then substitutes the Proposition 2.29
bound on `N`; it no longer stores the Proposition 2.33 conclusion itself as primitive input.

Source/core/bridge triage:
- source-facing: Proposition 2.34 itself, a bound for the total internal iterations of process
  `(2.3.22)`;
- core/canonical: `ConstrainedMinimizationMethod` and
  `constrainedMinimization_totalIterationCount_le_logarithmic_bound`;
- bridge/view: the specialization of Proposition 2.33 to `scheme.stopIndex` and the scalar
  substitution `N ≤ N(ε)`.
-/

namespace ConstrainedMinimizationMethod

local notation "stopSeq" => stopIndex problem κ t0 x0 hL hStep1a

/-- Helper for Proposition 2.34: the cost of one full outer update is nonnegative on the source
domain for `κ`. -/
private theorem perIterationCost_nonneg
    (hκ_domain : κ ∈ Set.Ioo (0 : ℝ) (2 * (Qf - 1))) :
    0 ≤ perIterationCost := by
  -- The logarithmic term is nonnegative, so adding the leading `1` keeps the cost nonnegative.
  have hlog_pos : 0 < Real.log (2 * (Qf - 1) / κ) := by
    refine Real.log_pos ?_
    rw [one_lt_div₀ hκ_domain.1]
    exact hκ_domain.2
  have hmul_nonneg :
      0 ≤ Real.sqrt Qf * Real.log (2 * (Qf - 1) / κ) := by
    exact mul_nonneg (Real.sqrt_nonneg _) hlog_pos.le
  linarith

/-- Proposition 2.34: if `N` is the source index of the last full iteration of process
`(2.3.22)`, if `N` satisfies the logarithmic master-iteration bound from Proposition 2.29, and if
the final count `j*`, the full-step counts `j(k) = scheme.stopIndex k`, and the stage sequence
`Δ` satisfy the specialized Proposition 2.33 hypotheses, then the total number of internal
iterations is bounded by the displayed formula `(2.3.27)`. The initial max-violation term is the
owner auxiliary objective
`initialViolation = problem.toLagrangianProblem.constrainedAuxiliaryObjective t0 x0`.
The textbook `ℝⁿ` statement is recovered by specializing `E = EuclideanSpace ℝ (Fin n)`. -/
theorem totalInternalIterations_le_logarithmic_bound
    (N jStar : ℕ) (Δ : ℕ → ℝ)
    (hκ_domain : κ ∈ Set.Ioo (0 : ℝ) (2 * (Qf - 1)))
    (hε : 0 < ε)
    (hΔ_zero : Δ 0 = initialViolation)
    (hfullIterations : (N : ℝ) ≤ fullIterationBound)
    (hΔ_pos : ∀ ⦃k : ℕ⦄, k ≤ N + 1 → 0 < Δ k)
    (hjStar_bound :
      (jStar : ℝ) ≤
        1 + Real.sqrt Qf * Real.log ((2 * (Qf - 1) * Δ (N + 1)) / (κ * ε)))
    (hj_bound :
      ∀ ⦃k : ℕ⦄, k ≤ N →
        (stopSeq k : ℝ) ≤
          1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / κ) +
            Real.sqrt Qf * Real.log (Δ k / Δ (k + 1))) :
    (jStar : ℝ) +
        Finset.sum (Finset.range (N + 1)) (fun k ↦ (stopSeq k : ℝ)) ≤
      (fullIterationBound + 2) * perIterationCost +
        Real.sqrt Qf * Real.log (initialViolation / ε) := by
  -- First package the entire inner-iteration accounting through Proposition 2.33.
  have htotalCount :
      (jStar : ℝ) +
          Finset.sum (Finset.range (N + 1)) (fun k ↦ (stopSeq k : ℝ)) ≤
        (N + 2 : ℝ) * perIterationCost +
          Real.sqrt Qf * Real.log (initialViolation / ε) :=
    by
      simpa [hΔ_zero] using
        constrainedMinimization_totalIterationCount_le_logarithmic_bound
          N
          (fun k ↦ (stopSeq k : ℝ))
          (jStar : ℝ)
          Δ
          Qf
          κ
          ε
          hκ_domain
          hε
          hΔ_pos
          hjStar_bound
          hj_bound
  -- Then substitute the logarithmic outer-iteration bound into the prefactor.
  have hperIterationBound :
      (N + 2 : ℝ) * perIterationCost ≤
        (fullIterationBound + 2) * perIterationCost := by
    refine mul_le_mul_of_nonneg_right ?_ (perIterationCost_nonneg hκ_domain)
    linarith
  have htotalCount' :
      (N + 2 : ℝ) * perIterationCost + Real.sqrt Qf * Real.log (initialViolation / ε) ≤
        (fullIterationBound + 2) * perIterationCost +
          Real.sqrt Qf * Real.log (initialViolation / ε) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hperIterationBound
        (Real.sqrt Qf * Real.log (initialViolation / ε))
  exact htotalCount.trans htotalCount'

end ConstrainedMinimizationMethod

end
