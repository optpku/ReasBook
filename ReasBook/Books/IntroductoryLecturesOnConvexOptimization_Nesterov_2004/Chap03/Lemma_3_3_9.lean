/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_3_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [PseudoMetricSpace E]

/- Lemma 3.3.9 lies in the chapter's iteration-cap comparison domain.

Relevant owner declarations sampled before refining:
- `levelMethodIterationCap` and `exists_stopping_index_le_levelMethodIterationCap` in
  `Theorem_3_3_1`, the chapter owners for the floor-plus-one iteration cap and its stopping-index
  consequence;
- `ConstrainedLevelMethod.history`, `ConstrainedLevelMethod.stoppingIndex`, and
  `ConstrainedLevelMethod.globalStopIndex` in `Algorithm_3_11`, the canonical inner-history and
  iteration-count owners for one master step;
- `constrainedLevelMethodInternalIterationBound` in `Theorem_3_3_3`, the owner of the displayed
  uniform real-valued per-step complexity bound;
- `levelParameterObjective` and `levelParameterObjective_pos` in `Definition_3_71`, the owner of
  the positive `α`-dependent denominator factor.

Best owner abstraction:
- source-facing: the full-step and last-step internal iteration counts of a constrained level
  method;
- core/canonical: `levelMethodIterationCap`, `ConstrainedLevelMethod.stoppingIndex`,
  `ConstrainedLevelMethod.globalStopIndex`, and
  `constrainedLevelMethodInternalIterationBound`;
- bridge/view: denominator monotonicity for positive factors.

Primitive data:
- the actual inner history at one master step and its canonical stopping/global-stopping indices;
- the block estimate needed to invoke `Theorem_3_3_1`;
- the predecessor-gap lower bound `χ ε ≤ δ_{j-1}` for the terminal inner run.

Derived API:
- the uniform full-step cap
  `stoppingIndex ≤ levelMethodIterationCap M_f D (χ ε) α`;
- the uniform terminal-step cap
  `globalStopIndex ≤ constrainedLevelMethodInternalIterationBound M_f D χ ε α`.
-/

private theorem le_div_of_mul_right_denominator_le
    {lhs num scale smallFactor largeFactor : ℝ}
    (hbound : lhs ≤ num / (scale * largeFactor))
    (hnum_nonneg : 0 ≤ num)
    (hscale_pos : 0 < scale)
    (hsmallFactor_pos : 0 < smallFactor)
    (hsmallFactor_le_largeFactor : smallFactor ≤ largeFactor) :
    lhs ≤ num / (scale * smallFactor) := by
  have hden_le : scale * smallFactor ≤ scale * largeFactor :=
    mul_le_mul_of_nonneg_left hsmallFactor_le_largeFactor hscale_pos.le
  have hden_pos : 0 < scale * smallFactor := mul_pos hscale_pos hsmallFactor_pos
  exact hbound.trans <| div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le

private theorem gap_le_kappa_mul_optimalValue_of_termination_rule
    (history : LevelMethodHistory) {κ : ℝ} (k : ℕ)
    (htermination :
      history.approximateOptimalValue k ≥ (1 - κ) * history.optimalValue k) :
    history.gap k ≤ κ * history.optimalValue k := by
  rw [history.gap_eq_sub]
  linarith

private theorem levelMethodIterationCap_antitone_tolerance
    {M_f D εLarge εSmall α : ℝ}
    (hεSmall_pos : 0 < εSmall)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hεSmall_le_εLarge : εSmall ≤ εLarge) :
    levelMethodIterationCap M_f D εLarge α ≤ levelMethodIterationCap M_f D εSmall α := by
  have hnum_nonneg : 0 ≤ M_f ^ (2 : ℕ) * D ^ (2 : ℕ) := by positivity
  have hlevel_pos : 0 < levelParameterObjective α := levelParameterObjective_pos hα
  have hεSmall_sq_le : εSmall ^ (2 : ℕ) ≤ εLarge ^ (2 : ℕ) := by
    nlinarith
  have hden_le :
      εSmall ^ (2 : ℕ) * levelParameterObjective α ≤
        εLarge ^ (2 : ℕ) * levelParameterObjective α :=
    mul_le_mul_of_nonneg_right hεSmall_sq_le hlevel_pos.le
  have hden_pos :
      0 < εSmall ^ (2 : ℕ) * levelParameterObjective α := by
    exact mul_pos (by positivity) hlevel_pos
  have hfrac :
      M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
          (εLarge ^ (2 : ℕ) * levelParameterObjective α) ≤
        M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
          (εSmall ^ (2 : ℕ) * levelParameterObjective α) :=
    div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le
  unfold levelMethodIterationCap
  exact Nat.add_le_add_right (Nat.floor_le_floor hfrac) 1

namespace ConstrainedLevelMethod

/-- Lemma 3.3.9 (1): if master step `k` is a full step in the sense that the selected exact
record value is still at least `ε`, and if the chapter owner hypotheses of Theorem `3.3.1` hold
for the inner history `method.history k`, then the canonical full-step count
`j(k) - j(k - 1)` represented by `method.stoppingIndex k` is bounded by the chapter owner
`levelMethodIterationCap` evaluated at the uniform tolerance `χ ε`. -/
theorem full_step_increment_le_uniform_internal_iteration_bound
    (method : ConstrainedLevelMethodInput E)
    (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative)
    (k : ℕ) (M_f D : ℝ)
    (hχ : 0 < method.chi)
    (hε : 0 < method.epsilon)
    (hα : method.levelCoefficient ∈ Set.Ioo (0 : ℝ) 1)
    (hblock :
      ∀ {i p : ℕ}, i ≤ p →
        (history method hrelative hfinite k).gap p ≥
          (1 - method.levelCoefficient) * (history method hrelative hfinite k).gap i →
        0 < (history method hrelative hfinite k).gap p →
        ((p + 1 - i : ℕ) : ℝ) ≤
          M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
            ((1 - method.levelCoefficient) ^ (2 : ℕ) *
              (history method hrelative hfinite k).gap p ^ (2 : ℕ)))
    (hfull_step :
      method.epsilon ≤
        (history method hrelative hfinite k).optimalValue
          (stoppingIndex method hrelative hfinite k)) :
    stoppingIndex method hrelative hfinite k ≤
      levelMethodIterationCap
        M_f D (method.chi * method.epsilon) method.levelCoefficient := by
  let history := history method hrelative hfinite k
  let j := stoppingIndex method hrelative hfinite k
  let τ := method.chi * history.optimalValue j
  have hτ_pos : 0 < τ := by
    have hopt_pos : 0 < history.optimalValue j := lt_of_lt_of_le hε hfull_step
    dsimp [τ]
    exact mul_pos hχ hopt_pos
  have hstopτ_j : history.shouldStop τ j := by
    rw [LevelMethodHistory.shouldStop_iff]
    have htermination :
        history.approximateOptimalValue j ≥ (1 - method.chi) * history.optimalValue j := by
      simpa [history, j, stoppingCriterion] using stopping_condition method hrelative hfinite k
    have hgap_le :
        history.gap j ≤ method.chi * history.optimalValue j :=
      gap_le_kappa_mul_optimalValue_of_termination_rule history j htermination
    simpa [τ] using hgap_le
  have hoptimal_succ : ∀ m : ℕ, history.optimalValue (m + 1) ≤ history.optimalValue m := by
    intro m
    simpa [history, ConstrainedLevelMethod.history, CompleteLevelMethod.history] using
      (show
          bestFunctionValueUpTo
              (fun i ↦
                method.stageProblemAt (parameter method hrelative hfinite k)
                  ((completeRun method hrelative hfinite k) i))
            (m + 1) ≤
            bestFunctionValueUpTo
              (fun i ↦
                method.stageProblemAt (parameter method hrelative hfinite k)
                  ((completeRun method hrelative hfinite k) i))
              m from
        bestFunctionValueUpTo_antitone_step m)
  have hoptimal_antitone : Antitone history.optimalValue :=
    antitone_nat_of_succ_le hoptimal_succ
  have hstopτ_min : ∀ {i : ℕ}, i < j → ¬ history.shouldStop τ i := by
    intro i hij
    rw [LevelMethodHistory.shouldStop_iff]
    have htermination_lt :
        history.approximateOptimalValue i <
          (1 - method.chi) * history.optimalValue i := by
      apply lt_of_not_ge
      intro htermination
      have hstop : stoppingCriterion method hrelative hfinite k i := by
        change history.approximateOptimalValue i ≥ (1 - method.chi) * history.optimalValue i
        exact htermination
      exact (stopping_condition_min method hrelative hfinite hij) hstop
    have hgap_gt : method.chi * history.optimalValue i < history.gap i := by
      rw [history.gap_eq_sub]
      nlinarith
    have hτ_le : τ ≤ method.chi * history.optimalValue i := by
      have hij' : i ≤ j := Nat.le_of_lt hij
      have hopt_mono : history.optimalValue j ≤ history.optimalValue i := hoptimal_antitone hij'
      exact mul_le_mul_of_nonneg_left hopt_mono hχ.le
    linarith
  have hstop_le_tau :
      j ≤ levelMethodIterationCap M_f D τ method.levelCoefficient := by
    obtain ⟨i, hi_bound, hi_stop⟩ :=
      exists_stopping_index_le_levelMethodIterationCap history hτ_pos hα hblock
    by_contra hji
    have hij : i < j := by
      apply lt_of_not_ge
      intro hij'
      exact hji (hij'.trans hi_bound)
    exact hstopτ_min hij hi_stop
  have huniform_pos : 0 < method.chi * method.epsilon := mul_pos hχ hε
  have hτ_ge_uniform : method.chi * method.epsilon ≤ τ := by
    dsimp [τ]
    exact mul_le_mul_of_nonneg_left hfull_step hχ.le
  exact hstop_le_tau.trans <|
    levelMethodIterationCap_antitone_tolerance huniform_pos hα hτ_ge_uniform

/-- If the canonical global-stop index at master step `k` is positive, then the preceding exact
record value is still above the global threshold `ε`. -/
theorem epsilon_le_optimalValue_pred_globalStopIndex
    (method : ConstrainedLevelMethodInput E)
    (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative)
    {k : ℕ}
    (hstop : globallyStopsAt method hrelative hfinite k)
    (hglobal_pos : 0 < globalStopIndex method hrelative hfinite k hstop) :
    method.epsilon ≤
      (history method hrelative hfinite k).optimalValue
        (globalStopIndex method hrelative hfinite k hstop - 1) := by
  have h_prev_lt_global :
      globalStopIndex method hrelative hfinite k hstop - 1 <
        globalStopIndex method hrelative hfinite k hstop := by
    simpa using hglobal_pos
  have hprev_not_global :
      ¬ globalStopCriterion method hrelative hfinite k
          (globalStopIndex method hrelative hfinite k hstop - 1) := by
    exact global_stop_condition_min method hrelative hfinite k hstop h_prev_lt_global
  change ¬
      ((history method hrelative hfinite k).optimalValue
          (globalStopIndex method hrelative hfinite k hstop - 1) ≤
        method.epsilon)
    at hprev_not_global
  exact le_of_lt (lt_of_not_ge hprev_not_global)

/-- If the first global-stop index occurs no later than the canonical relative stopping index,
then the predecessor gap is at least `χ ε`. -/
theorem chi_mul_epsilon_le_gap_pred_globalStopIndex
    (method : ConstrainedLevelMethodInput E)
    (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative)
    {k : ℕ}
    (hstop : globallyStopsAt method hrelative hfinite k)
    (hchi_nonneg : 0 ≤ method.chi)
    (hglobal_pos : 0 < globalStopIndex method hrelative hfinite k hstop)
    (hglobal_le_stopping :
      globalStopIndex method hrelative hfinite k hstop ≤
        stoppingIndex method hrelative hfinite k) :
    method.chi * method.epsilon ≤
      (history method hrelative hfinite k).gap
        (globalStopIndex method hrelative hfinite k hstop - 1) := by
  have h_prev_lt_stopping :
      globalStopIndex method hrelative hfinite k hstop - 1 <
        stoppingIndex method hrelative hfinite k := by
    omega
  have h_prev_ge_epsilon :
      method.epsilon ≤
        (history method hrelative hfinite k).optimalValue
          (globalStopIndex method hrelative hfinite k hstop - 1) :=
    epsilon_le_optimalValue_pred_globalStopIndex
      method hrelative hfinite hstop hglobal_pos
  have h_normal_stop_fails :
      method.chi *
          (history method hrelative hfinite k).optimalValue
            (globalStopIndex method hrelative hfinite k hstop - 1) ≤
        (history method hrelative hfinite k).gap
          (globalStopIndex method hrelative hfinite k hstop - 1) := by
    have hprev_not_stop :
        ¬ stoppingCriterion method hrelative hfinite k
            (globalStopIndex method hrelative hfinite k hstop - 1) :=
      stopping_condition_min method hrelative hfinite h_prev_lt_stopping
    change ¬
        ((history method hrelative hfinite k).approximateOptimalValue
            (globalStopIndex method hrelative hfinite k hstop - 1) ≥
          (1 - method.chi) *
            (history method hrelative hfinite k).optimalValue
              (globalStopIndex method hrelative hfinite k hstop - 1))
      at hprev_not_stop
    have hprev_lt :
        (history method hrelative hfinite k).approximateOptimalValue
            (globalStopIndex method hrelative hfinite k hstop - 1) <
          (1 - method.chi) *
            (history method hrelative hfinite k).optimalValue
              (globalStopIndex method hrelative hfinite k hstop - 1) :=
      lt_of_not_ge hprev_not_stop
    rw [(history method hrelative hfinite k).gap_eq_sub]
    nlinarith
  have hχ_mul :
      method.chi * method.epsilon ≤
        method.chi *
          (history method hrelative hfinite k).optimalValue
            (globalStopIndex method hrelative hfinite k hstop - 1) :=
    mul_le_mul_of_nonneg_left h_prev_ge_epsilon hchi_nonneg
  linarith

/-- Lemma 3.3.9 (2): if the final inner run at master step `k` globally stops at the canonical
index `globalStopIndex`, if this global-stop index occurs no later than the canonical relative
stopping index, and if the textbook predecessor-gap bound for that terminal run is available, then
the number of internal iterations executed up to that globally stopping step is bounded by the
displayed uniform chapter owner
`constrainedLevelMethodInternalIterationBound M_f D χ ε α`. -/
theorem last_step_internal_iterations_le_uniform_internal_iteration_bound
    (method : ConstrainedLevelMethodInput E)
    (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative)
    {k : ℕ}
    (hstop : globallyStopsAt method hrelative hfinite k)
    {M_f D : ℝ}
    (hχ : 0 < method.chi)
    (hε : 0 < method.epsilon)
    (hα : method.levelCoefficient ∈ Set.Ioo (0 : ℝ) 1)
    (hglobal_pos : 0 < globalStopIndex method hrelative hfinite k hstop)
    (hglobal_le_stopping :
      globalStopIndex method hrelative hfinite k hstop ≤
        stoppingIndex method hrelative hfinite k)
    (h_last_step_cap :
      (globalStopIndex method hrelative hfinite k hstop : ℝ) ≤
        M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
          ((history method hrelative hfinite k).gap
              (globalStopIndex method hrelative hfinite k hstop - 1) ^
              (2 : ℕ) *
            levelParameterObjective method.levelCoefficient)) :
    (globalStopIndex method hrelative hfinite k hstop : ℝ) ≤
      constrainedLevelMethodInternalIterationBound
        M_f D method.chi method.epsilon method.levelCoefficient := by
  let gapPrev :=
    (history method hrelative hfinite k).gap
      (globalStopIndex method hrelative hfinite k hstop - 1)
  have hgapPrev : method.chi * method.epsilon ≤ gapPrev := by
    simpa [gapPrev] using
      chi_mul_epsilon_le_gap_pred_globalStopIndex
        method hrelative hfinite hstop hχ.le hglobal_pos hglobal_le_stopping
  have hnum_nonneg : 0 ≤ M_f ^ (2 : ℕ) * D ^ (2 : ℕ) := by positivity
  have hlevel_pos : 0 < levelParameterObjective method.levelCoefficient :=
    levelParameterObjective_pos hα
  have hprod_pos : 0 < method.chi * method.epsilon := mul_pos hχ hε
  have hsmallFactor_pos : 0 < (method.chi * method.epsilon) ^ (2 : ℕ) := by positivity
  have hsmallFactor_le_largeFactor :
      (method.chi * method.epsilon) ^ (2 : ℕ) ≤ gapPrev ^ (2 : ℕ) := by
    nlinarith [hgapPrev, hprod_pos]
  have hsource_bound :
      (globalStopIndex method hrelative hfinite k hstop : ℝ) ≤
        M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
          (levelParameterObjective method.levelCoefficient * gapPrev ^ (2 : ℕ)) := by
    simpa [gapPrev, mul_assoc, mul_left_comm, mul_comm] using h_last_step_cap
  have hbound :
      (globalStopIndex method hrelative hfinite k hstop : ℝ) ≤
        M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
          (levelParameterObjective method.levelCoefficient *
            (method.chi * method.epsilon) ^ (2 : ℕ)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      le_div_of_mul_right_denominator_le
        hsource_bound
        hnum_nonneg
        hlevel_pos
        hsmallFactor_pos
        hsmallFactor_le_largeFactor
  simpa
      [constrainedLevelMethodInternalIterationBound, mul_assoc, mul_left_comm, mul_comm, mul_pow]
    using hbound

end ConstrainedLevelMethod

end
