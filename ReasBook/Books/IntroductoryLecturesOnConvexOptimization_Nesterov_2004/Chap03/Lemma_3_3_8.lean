/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [PseudoMetricSpace E]

namespace ConstrainedLevelMethod

/-- Helper for Lemma 3.3.8: some produced internal iterate realizes the exact record value on
every sampled prefix of the internal history at master step `k`. -/
lemma exists_internalIterate_eq_optimalValue_prefix
    (method : ConstrainedLevelMethodInput E)
    (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative)
    (k p : ℕ) :
    ∃ jStar : ℕ,
      jStar ≤ p ∧
        method.exactObjectiveAt (parameter method hrelative hfinite k)
            (internalIterate method hrelative hfinite k jStar) =
          (history method hrelative hfinite k).optimalValue p := by
  let values : ℕ → ℝ := fun j ↦
    method.exactObjectiveAt (parameter method hrelative hfinite k)
      (internalIterate method hrelative hfinite k j)
  obtain ⟨jStar, hjStar_eq⟩ := bestFunctionValueUpTo_exists_eq values p
  refine ⟨jStar, Nat.lt_succ_iff.mp jStar.2, ?_⟩
  -- Read the record value as the sampled minimum over the produced prefix.
  calc
    method.exactObjectiveAt (parameter method hrelative hfinite k)
        (internalIterate method hrelative hfinite k jStar) =
      bestFunctionValueUpTo values p := by
        simpa [values] using hjStar_eq
    _ = (history method hrelative hfinite k).optimalValue p := by
        symm
        simpa [values, completeRun, history, internalIterate, CompleteLevelMethod.history] using
          levelMethodHistoryFromApproximateValues_optimalValue_eq
            (approximateOptimalValue := (completeRun method hrelative hfinite k).approximateOptimalValue)
            (f := method.stageProblemAt (parameter method hrelative hfinite k))
            (xSeq := completeRun method hrelative hfinite k)
            p

/-- Helper for Lemma 3.3.8: an exact constrained-value bound controls the objective once the
current parameter is bounded above by `tStar`. -/
lemma exactObjectiveAt_objective_le_of_le
    (method : ConstrainedLevelMethodInput E)
    {tk tStar : ℝ} {x : E}
    (hvalue : method.exactObjectiveAt tk x ≤ method.epsilon)
    (htk : tk ≤ tStar) :
    method.objective x ≤ tStar + method.epsilon := by
  -- Expand the exact constrained slice into its pointwise maximum and read off the first branch.
  rw [ConstrainedLevelMethodInput.exactObjectiveAt, setConstrainedParametricObjective_apply] at hvalue
  rcases max_le_iff.mp hvalue with ⟨hobjective, _⟩
  linarith

/-- Helper for Lemma 3.3.8: an exact constrained-value bound also controls the constraint
component. -/
lemma exactObjectiveAt_constraint_le_of_le
    (method : ConstrainedLevelMethodInput E)
    {tk : ℝ} {x : E}
    (hvalue : method.exactObjectiveAt tk x ≤ method.epsilon) :
    method.constraint x ≤ method.epsilon := by
  -- Expand the exact constrained slice into its pointwise maximum and read off the second branch.
  rw [ConstrainedLevelMethodInput.exactObjectiveAt, setConstrainedParametricObjective_apply] at hvalue
  exact (max_le_iff.mp hvalue).2

/-- Lemma 3.3.8: once the global-stop condition holds at master step `k`, some produced internal
iterate attains the stopping record value and therefore satisfies the displayed objective and
constraint bounds. -/
theorem global_stop_exists_internal_witness_and_component_bounds
    (method : ConstrainedLevelMethodInput E)
    (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative)
    (k : ℕ)
    (hstop : globallyStopsAt method hrelative hfinite k)
    (tStar : ℝ)
    (htk : parameter method hrelative hfinite k ≤ tStar) :
    ∃ jStar : ℕ,
      jStar ≤ globalStopIndex method hrelative hfinite k hstop ∧
        method.exactObjectiveAt (parameter method hrelative hfinite k)
            (internalIterate method hrelative hfinite k jStar) =
          (history method hrelative hfinite k).optimalValue
            (globalStopIndex method hrelative hfinite k hstop) ∧
        method.exactObjectiveAt (parameter method hrelative hfinite k)
            (internalIterate method hrelative hfinite k jStar) ≤
          method.epsilon ∧
        method.objective (internalIterate method hrelative hfinite k jStar) ≤
          tStar + method.epsilon ∧
        method.constraint (internalIterate method hrelative hfinite k jStar) ≤
          method.epsilon := by
  -- Route correction: work with the actual stage-`k` history and global-stop index.
  obtain ⟨jStar, hjStar_le, hjStar_eq⟩ :=
    exists_internalIterate_eq_optimalValue_prefix
      method
      hrelative
      hfinite
      k
      (globalStopIndex method hrelative hfinite k hstop)
  have hglobal :
      (history method hrelative hfinite k).optimalValue
          (globalStopIndex method hrelative hfinite k hstop) ≤
        method.epsilon := by
    simpa [globalStopCriterion] using
      global_stop_condition method hrelative hfinite k hstop
  have hvalue :
      method.exactObjectiveAt (parameter method hrelative hfinite k)
          (internalIterate method hrelative hfinite k jStar) ≤
        method.epsilon := by
    rw [hjStar_eq]
    exact hglobal
  refine ⟨jStar, hjStar_le, hjStar_eq, hvalue, ?_, ?_⟩
  · -- Use the exact-value estimate and the parameter bound to recover the source `f`-bound.
    exact
      exactObjectiveAt_objective_le_of_le
        method
        hvalue
        htk
  · -- The same exact-value estimate directly yields the source constraint bound.
    exact exactObjectiveAt_constraint_le_of_le method hvalue

end ConstrainedLevelMethod

end
