/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_34

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped ConstrainedArgmin LevelMethodNotation

variable {E : Type u} [NormedAddCommGroup E]

/- Proposition 3.51 lies in the chapter's complete-level-method / sampled-prefix-value domain.

Mandatory domain-style sampling before refinement:
- `CompleteLevelMethod` and `CompleteLevelMethod.history` in `Algorithm_3_10`, the source-facing
  owner of a level-method run together with its canonical scalar history;
- `levelMethodHistoryFromApproximateValues_optimalValue_eq` in `Proposition_3_50`, the bridge
  identifying the history
  coordinate `f_k^*` with the chapter owner `bestFunctionValueUpTo`;
- `SetConstrainedMinimizationProblem.optimalValue` and
  `SetConstrainedMinimizationProblem.IsApproximateMinimizer` in `Chap01/Definition_1_3_7`, the
  Chapter 1 owner abstraction for constrained `ε`-solutions;
- `argmin[problem.feasibleSet] problem` in `Chap01/Definition_1_3_3`, the canonical owner of a
  minimizing comparison point for the constrained problem.

Best owner abstraction:
- source-facing: a `CompleteLevelMethod problem`;
- core/canonical: `problem.IsApproximateMinimizer ε x` together with `problem.optimalValue`;
- bridge/view: the sampled-prefix bound on `fstar(method.history, N)` and the optional
  comparison-point reformulation relative to `xStar ∈ argmin[problem.feasibleSet] problem`.

Primitive data:
- the constrained problem `problem` and a complete level-method run `method`;
- the comparison point `xStar`, now required only as a minimizing point in the canonical owner set
  `argmin[problem.feasibleSet] problem`;
- the constant `Mf`, the tolerance `ε`, and the iteration budget `N`;
- the level-method estimate stated directly on the owner value `fstar(method.history, N)`.

Derived API:
- the owner bound `(fstar(method.history, N) : EReal) ≤ problem.optimalValue + ε`;
- an index `k ≤ N` with `problem.IsApproximateMinimizer ε (method k)`;
- the comparison-point bridge `IsApproximateSolution problem xStar ε (method k)`.

Source/core/bridge triage:
- source-facing: the finite-horizon level-method guarantee for a run with prescribed initial point;
- core/canonical: `CompleteLevelMethod`, `problem.optimalValue`, and
  `problem.IsApproximateMinimizer`;
- bridge/view: `levelMethodHistoryFromApproximateValues_optimalValue_eq`, the argmin witness
  `xStar`, and the
  comparison-point extraction.

The previous version already restored the run owner `CompleteLevelMethod problem`, but its main
result still stopped at the comparison-point predicate
`IsApproximateSolution problem xStar ε (method k)`. This refinement keeps the sampled-prefix
estimate as a bridge, but moves the public conclusion back to the Chapter 1 constrained owner
`problem.IsApproximateMinimizer ε (method k)`, using `xStar ∈ argmin[problem.feasibleSet] problem`
only to identify `problem.optimalValue` with `problem xStar`.
-/

namespace CompleteLevelMethod

variable {problem : SetConstrainedMinimizationProblem E}

/-- Helper for Proposition 3.51: rewrite the textbook budget into the square-threshold form
needed for the square-root comparison step. -/
private lemma complexity_square_threshold_of_budget
    {Mf D ε : ℝ} {N : ℕ}
    (hε : 0 < ε)
    (hN : (4 * Mf ^ (2 : ℕ) * D ^ (2 : ℕ)) / ε ^ (2 : ℕ) ≤ (N : ℝ)) :
    ((2 * Mf * D) / ε) ^ (2 : ℕ) ≤ (N : ℝ) := by
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  -- Clear the denominator `ε²` and expand the numerator into the source constant `4 M_f² D²`.
  have hrewrite :
      ((2 * Mf * D) / ε) ^ (2 : ℕ) =
        (4 * Mf ^ (2 : ℕ) * D ^ (2 : ℕ)) / ε ^ (2 : ℕ) := by
    field_simp [pow_two, hε_ne]
    ring
  rw [hrewrite]
  exact hN

/-- Helper for Proposition 3.51: a square-threshold bound implies the corresponding
`1 / √n` estimate needed in the complexity proof. -/
private lemma div_sqrt_le_epsilon_of_square_threshold
    {c ε n : ℝ}
    (hε : 0 < ε)
    (hn : 0 ≤ n)
    (hthreshold : (c / ε) ^ (2 : ℕ) ≤ n) :
    c / Real.sqrt n ≤ ε := by
  by_cases hc : c ≤ 0
  · -- If the numerator is nonpositive, the square-root term is already below `0 ≤ ε`.
    have hdiv_nonpos : c / Real.sqrt n ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hc (Real.sqrt_nonneg n)
    exact hdiv_nonpos.trans hε.le
  · have hc_pos : 0 < c := lt_of_not_ge hc
    have hdiv_nonneg : 0 ≤ c / ε := div_nonneg hc_pos.le hε.le
    -- Compare squares to move from the threshold on `(c / ε)^2` to a bound on `c / ε`.
    have hdiv_le_sqrt : c / ε ≤ Real.sqrt n := by
      refine (sq_le_sq₀ hdiv_nonneg (Real.sqrt_nonneg n)).1 ?_
      simpa [pow_two, Real.sq_sqrt hn] using hthreshold
    have hsq_pos : 0 < (c / ε) ^ (2 : ℕ) := by
      have hdiv_pos : 0 < c / ε := div_pos hc_pos hε
      nlinarith [sq_pos_of_pos hdiv_pos]
    have hn_pos : 0 < n := lt_of_lt_of_le hsq_pos hthreshold
    have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
    -- Divide by the positive square root to recover the desired bound.
    exact (div_le_iff₀ hsqrt_pos).2 <| by
      simpa [mul_comm] using (div_le_iff₀ hε).1 hdiv_le_sqrt

/-- Helper for Proposition 3.51: combine the level-method gap estimate with the inverted
iteration budget to obtain an `ε`-gap bound. -/
private lemma comparison_gap_le_epsilon_of_complexity_estimate
    (method : CompleteLevelMethod problem) {Mf : ℝ} {xStar : E} {ε : ℝ} {N : ℕ}
    (h_level_estimate :
      fstar(method.history, N) - problem xStar ≤
        2 * Mf * ‖method.initialPoint - xStar‖ / Real.sqrt (N : ℝ))
    (hε : 0 < ε)
    (hN :
      (4 * Mf ^ (2 : ℕ) * ‖method.initialPoint - xStar‖ ^ (2 : ℕ)) / ε ^ (2 : ℕ) ≤ (N : ℝ)) :
    fstar(method.history, N) - problem xStar ≤ ε := by
  let D : ℝ := ‖method.initialPoint - xStar‖
  -- Rewrite the budget into the square-threshold shape dictated by the source proof.
  have hthreshold : ((2 * Mf * D) / ε) ^ (2 : ℕ) ≤ (N : ℝ) := by
    simpa [D] using complexity_square_threshold_of_budget hε hN
  -- Convert the threshold into the square-root estimate appearing in the level-method bound.
  have hscalar : (2 * Mf * D) / Real.sqrt (N : ℝ) ≤ ε := by
    exact div_sqrt_le_epsilon_of_square_threshold hε (by positivity) hthreshold
  -- Chain the sampled-prefix gap estimate with the scalar bound.
  simpa [D] using h_level_estimate.trans hscalar

/-- Proposition 3.51, owner form: if a complete level-method run satisfies the standard estimate
`f_N^* - f(x*) ≤ 2 M_f ‖x₀ - x*‖ / √N` on the owner sampled-prefix value
`f_N^* = fstar(method.history, N)`, then every budget `N` above
`4 M_f² ‖x₀ - x*‖² / ε²` forces `f_N^* ≤ f(x*) + ε`. -/
theorem optimalValue_le_comparison_add_of_complexity_estimate
    (method : CompleteLevelMethod problem) {Mf : ℝ} {xStar : E} {ε : ℝ} {N : ℕ}
    (h_level_estimate :
      fstar(method.history, N) - problem xStar ≤
        2 * Mf * ‖method.initialPoint - xStar‖ / Real.sqrt (N : ℝ))
    (hε : 0 < ε)
    (hN :
      (4 * Mf ^ (2 : ℕ) * ‖method.initialPoint - xStar‖ ^ (2 : ℕ)) / ε ^ (2 : ℕ) ≤ (N : ℝ)) :
    fstar(method.history, N) ≤ problem xStar + ε := by
  -- The source proof first inverts the budget into a direct `ε`-gap estimate.
  have hgap : fstar(method.history, N) - problem xStar ≤ ε := by
    exact comparison_gap_le_epsilon_of_complexity_estimate
      (method := method) h_level_estimate hε hN
  -- Rewriting the gap inequality gives the desired additive form.
  exact sub_le_iff_le_add'.mp hgap

/-- Proposition 3.51, owner form: if `x*` is a constrained minimizer and the complete level
method satisfies the standard comparison-point complexity estimate, then the sampled-prefix owner
value `f_N^*` is within `ε` of the Chapter 1 constrained optimal value. -/
theorem historyOptimalValue_le_optimalValue_add_of_complexity_estimate
    (method : CompleteLevelMethod problem) {Mf : ℝ} {xStar : E} {ε : ℝ} {N : ℕ}
    (hxStar : xStar ∈ argmin[problem.feasibleSet] problem)
    (h_level_estimate :
      fstar(method.history, N) - problem xStar ≤
        2 * Mf * ‖method.initialPoint - xStar‖ / Real.sqrt (N : ℝ))
    (hε : 0 < ε)
    (hN :
      (4 * Mf ^ (2 : ℕ) * ‖method.initialPoint - xStar‖ ^ (2 : ℕ)) / ε ^ (2 : ℕ) ≤ (N : ℝ)) :
    (fstar(method.history, N) : EReal) ≤ problem.optimalValue + ε := by
  rw [problem.optimalValue_eq_of_mem_argmin hxStar]
  exact_mod_cast
    method.optimalValue_le_comparison_add_of_complexity_estimate
      h_level_estimate hε hN

/-- Proposition 3.51: under the same complexity budget, one of the iterates `x₀, …, x_N` of the
complete level-method run is an `ε`-approximate minimizer of the constrained problem in the
canonical Chapter 1 sense. -/
theorem exists_isApproximateMinimizer_of_complexity_estimate
    (method : CompleteLevelMethod problem) {Mf : ℝ} {xStar : E} {ε : ℝ} {N : ℕ}
    (hxStar : xStar ∈ argmin[problem.feasibleSet] problem)
    (h_level_estimate :
      fstar(method.history, N) - problem xStar ≤
        2 * Mf * ‖method.initialPoint - xStar‖ / Real.sqrt (N : ℝ))
    (hε : 0 < ε)
    (hN :
      (4 * Mf ^ (2 : ℕ) * ‖method.initialPoint - xStar‖ ^ (2 : ℕ)) / ε ^ (2 : ℕ) ≤ (N : ℝ)) :
    ∃ k ≤ N, problem.IsApproximateMinimizer ε (method k) := by
  have hbest :
      (fstar(method.history, N) : EReal) ≤ problem.optimalValue + ε :=
    method.historyOptimalValue_le_optimalValue_add_of_complexity_estimate
      hxStar h_level_estimate hε hN
  obtain ⟨j, hjbest⟩ :=
    bestFunctionValueUpTo_exists_eq (fun i ↦ problem (method i)) N
  have hjbest : problem (method j) ≤ fstar(method.history, N) := by
    rw [show fstar(method.history, N) =
        bestFunctionValueUpTo (fun i ↦ problem (method i)) N by
          simpa [CompleteLevelMethod.history] using
            levelMethodHistoryFromApproximateValues_optimalValue_eq
              method.approximateOptimalValue
              problem
              method.iterate
              N]
    rw [hjbest]
  have hjbest' : (problem (method j) : EReal) ≤ fstar(method.history, N) := by
    exact_mod_cast hjbest
  refine ⟨j, Nat.lt_succ_iff.mp j.2, ?_⟩
  rw [problem.isApproximateMinimizer_iff ε (method j)]
  exact ⟨method.iterate_mem j, hjbest'.trans hbest⟩

/-- The owner `ε`-minimizer conclusion of Proposition 3.51 recovers the textbook comparison-point
form once the comparison point `x*` is known to lie in the constrained argmin set. -/
theorem exists_isApproximateSolution_of_complexity_estimate
    (method : CompleteLevelMethod problem) {Mf : ℝ} {xStar : E} {ε : ℝ} {N : ℕ}
    (hxStar : xStar ∈ argmin[problem.feasibleSet] problem)
    (h_level_estimate :
      fstar(method.history, N) - problem xStar ≤
        2 * Mf * ‖method.initialPoint - xStar‖ / Real.sqrt (N : ℝ))
    (hε : 0 < ε)
    (hN :
      (4 * Mf ^ (2 : ℕ) * ‖method.initialPoint - xStar‖ ^ (2 : ℕ)) / ε ^ (2 : ℕ) ≤ (N : ℝ)) :
    ∃ k ≤ N, IsApproximateSolution problem xStar ε (method k) := by
  obtain ⟨k, hkN, hk⟩ :=
    method.exists_isApproximateMinimizer_of_complexity_estimate
      hxStar h_level_estimate hε hN
  rw [problem.isApproximateMinimizer_iff ε (method k)] at hk
  refine ⟨k, hkN, sub_le_iff_le_add'.mpr ?_⟩
  have hk' : (problem (method k) : EReal) ≤ (problem xStar : EReal) + ε := by
    simpa [problem.optimalValue_eq_of_mem_argmin hxStar] using hk.2
  exact_mod_cast hk'

end CompleteLevelMethod

end
