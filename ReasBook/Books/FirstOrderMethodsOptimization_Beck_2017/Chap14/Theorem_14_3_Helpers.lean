/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap14.Theorem_14_3_Helpers.PrefixState

/-- alternatingMinimizationRecoverLimitArgminAlongPrefixState: along a refined
subsequence of
stage-`i` prefix states converging to `xBar`, recover a limit block coordinate in
`alternating_minimization_argmin F xBar i` that is also the limit of the actual next-iterate
active coordinates, while the corresponding recovered updates remain in `effective_domain F`. -/
theorem alternatingMinimizationRecoverLimitArgminAlongPrefixState :
    ∀ {p : ℕ} {Ei : Fin p → Type u}
      [(i : Fin p) → PseudoMetricSpace (Ei i)]
      [ProperSpace ((i : Fin p) → Ei i)]
      (F : ((i : Fin p) → Ei i) → EReal) (x : ℕ → (i : Fin p) → Ei i),
      LowerSemicontinuous F →
        ContinuousOn F (effective_domain F) →
          (∀ (α : ℝ), Bornology.IsBounded {x | F x ≤ ↑α}) →
            is_alternating_minimization_trajectory F x →
              ∀ {xBar : (j : Fin p) → Ei j} (i : Fin p) {ψ : ℕ → ℕ},
                Filter.Tendsto
                    (fun m ↦ alternating_minimization_prefix_state x (ψ m) ↑i)
                    Filter.atTop
                    (nhds xBar) →
                  (∀ ⦃zi : Ei i⦄,
                      Function.update xBar i zi ∈ effective_domain F →
                        F (Function.update xBar i zi) < ↑(F (x 0)).toReal →
                          ∀ s ∈ nhds zi,
                            {xBase |
                                ∃ zi' ∈ s,
                                  Function.update xBase i zi' ∈ effective_domain F ∧
                                    F (Function.update xBase i zi') <
                                      ↑(F (x 0)).toReal} ∈
                              nhds xBar) →
                    ∃ φ,
                      ∃ (_ : StrictMono φ),
                        ∃ ziLimit ∈ alternating_minimization_argmin F xBar i,
                          Filter.Tendsto (fun m ↦ x (ψ (φ m) + 1) i) Filter.atTop
                            (nhds ziLimit) ∧
                            ∀ m : ℕ,
                              Function.update
                                  (alternating_minimization_prefix_state x (ψ (φ m)) ↑i)
                                  i
                                  (x (ψ (φ m) + 1) i) ∈
                                effective_domain F := by
  intro p Ei _ _ F x hclosed hcont hlevels htraj xBar i ψ hstage hrecover
  classical
  rcases alternating_minimization_stage_succ_refinement_as_recovered_updates
      F x hclosed hlevels htraj i (ψ := ψ) with
    ⟨φ, hφ, y, hnext, hcoord, hdom⟩
  let ψ' : ℕ → ℕ := ψ ∘ φ
  have hstage' :
      Filter.Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ' m) i.1)
        Filter.atTop
        (nhds xBar) := by
    -- Refining the stage-`i` subsequence preserves convergence to the same base point.
    simpa [ψ', Function.comp] using hstage.comp hφ.tendsto_atTop
  have hnext' :
      Filter.Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ' m) (i.1 + 1))
        Filter.atTop
        (nhds y) := by
    -- The stage-`i+1` recovery theorem already packages the refined next-stage convergence.
    simpa [ψ', Function.comp] using hnext
  have hcoord' :
      Filter.Tendsto (fun m ↦ x (ψ' m + 1) i) Filter.atTop (nhds (y i)) := by
    -- The actual updated block coordinates converge to the active coordinate of the recovered
    -- stage-`i+1` limit.
    simpa [ψ', Function.comp] using hcoord
  have hdom' :
      ∀ m,
        Function.update
            (alternating_minimization_prefix_state x (ψ' m) i.1)
            i
            (x (ψ' m + 1) i) ∈
          effective_domain F := by
    -- The recovered updates are exactly the actual next-iterate block replacements.
    simpa [ψ', Function.comp] using hdom
  have hyUpdate :
      Inseparable y (Function.update xBar i (y i)) :=
    alternating_minimization_prefix_state_limit_inseparable_update x ψ' i hstage' hnext'
  have hnextUpdate :
      Filter.Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ' m) (i.1 + 1))
        Filter.atTop
        (nhds (Function.update xBar i (y i))) := by
    -- The limit point and its explicit updated-state spelling define the same neighborhood filter.
    simpa [hyUpdate.nhds_eq] using hnext'
  have hupdated_le_initial :
      F (Function.update xBar i (y i)) ≤ (((F (x 0)).toReal : ℝ) : EReal) := by
    -- Every stage-`i+1` prefix state lies in the initial real sublevel, so the updated limit does
    -- as well after transporting along inseparability.
    exact alternating_minimization_prefix_state_limit_mem_initial_sublevel
      F x hclosed htraj (i.1 + 1) (Nat.succ_le_of_lt i.is_lt) hnextUpdate
  have hinitial_lt_top : (((F (x 0)).toReal : ℝ) : EReal) < ⊤ := by
    simp
  have hupdated_dom :
      Function.update xBar i (y i) ∈ effective_domain F := by
    -- The initial real sublevel is finite, hence contained in the effective domain.
    exact mem_effective_domain.mpr <| lt_of_le_of_lt hupdated_le_initial hinitial_lt_top
  have hnext_dom :
      ∀ m, alternating_minimization_prefix_state x (ψ' m) (i.1 + 1) ∈ effective_domain F := by
    intro m
    -- Rewrite the packaged recovered update back to the stage-`i+1` prefix state.
    simpa [alternating_minimization_prefix_state_new_eq_partial_state,
      alternating_minimization_partial_state_eq_update_prefix_state] using hdom' m
  have hyArgmin :
      y i ∈ alternating_minimization_argmin F xBar i := by
    -- Prove the fixed-base block argmin fact directly from the strict-recovery hypothesis.
    refine (mem_alternating_minimization_argmin_update_iff).2 ?_
    rw [isMinOn_iff]
    intro zi hzi
    by_cases hzi_dom : Function.update xBar i zi ∈ effective_domain F
    · by_cases hzi_strict :
          F (Function.update xBar i zi) < (((F (x 0)).toReal : ℝ) : EReal)
      · let P : ℕ → ℕ → Prop :=
            fun n k ↦
              ∃ zi' ∈ Metric.ball zi (1 / (n + 1 : ℝ)),
                Function.update
                    (alternating_minimization_prefix_state x (ψ' k) i.1)
                    i
                    zi' ∈ effective_domain F ∧
                  F
                      (Function.update
                        (alternating_minimization_prefix_state x (ψ' k) i.1)
                        i
                        zi') <
                    (((F (x 0)).toReal : ℝ) : EReal)
        have hP :
            ∀ n, ∀ᶠ k in Filter.atTop, P n k := by
          intro n
          have hball :
              Metric.ball zi (1 / (n + 1 : ℝ)) ∈ nhds zi := by
            -- Query the recovery hypothesis on shrinking metric balls around `zi`.
            apply Metric.ball_mem_nhds
            positivity
          have hnear :
              {xBase |
                  ∃ zi' ∈ Metric.ball zi (1 / (n + 1 : ℝ)),
                    Function.update xBase i zi' ∈ effective_domain F ∧
                      F (Function.update xBase i zi') <
                        (((F (x 0)).toReal : ℝ) : EReal)} ∈
                nhds xBar :=
            hrecover hzi_dom hzi_strict _ hball
          exact hstage' hnear
        rcases Filter.extraction_forall_of_eventually hP with ⟨τ, hτ, hτ_good⟩
        let ziSeq : ℕ → Ei i := fun n ↦ Classical.choose (hτ_good n)
        have hziSeq_ball :
            ∀ n : ℕ, ziSeq n ∈ Metric.ball zi (1 / (n + 1 : ℝ)) := by
          intro n
          exact (Classical.choose_spec (hτ_good n)).1
        have hziSeq_dom :
            ∀ n : ℕ,
              Function.update
                  (alternating_minimization_prefix_state x (ψ' (τ n)) i.1)
                  i
                  (ziSeq n) ∈
                effective_domain F := by
          intro n
          exact (Classical.choose_spec (hτ_good n)).2.1
        have hziSeq :
            Filter.Tendsto ziSeq Filter.atTop (nhds zi) := by
          -- The shrinking-ball choice forces the recovered competitors back to `zi`.
          refine Metric.tendsto_atTop'.2 ?_
          intro ε hε
          rcases exists_nat_one_div_lt hε with ⟨N, hN⟩
          refine ⟨N, ?_⟩
          intro n hn
          have hdist :
              dist (ziSeq n) zi < 1 / (n + 1 : ℝ) := by
            simpa [Metric.mem_ball] using hziSeq_ball n
          have hsmall :
              (1 / (n + 1 : ℝ)) < ε := by
            exact lt_trans (Nat.one_div_lt_one_div hn) hN
          exact lt_trans hdist hsmall
        have hstageτ :
            Filter.Tendsto
                (fun m ↦ alternating_minimization_prefix_state x (ψ' (τ m)) i.1)
                Filter.atTop
                (nhds xBar) := by
          -- The stage-`i` prefix states keep the same limit after the diagonal extraction.
          exact hstage'.comp hτ.tendsto_atTop
        have hnextUpdateτ :
            Filter.Tendsto
                (fun m ↦ alternating_minimization_prefix_state x (ψ' (τ m)) (i.1 + 1))
                Filter.atTop
                (nhds (Function.update xBar i (y i))) := by
          -- The transported stage-`i+1` convergence also survives the same extraction.
          exact hnextUpdate.comp hτ.tendsto_atTop
        have hnextUpdateObj :
            Filter.Tendsto
                (fun m ↦ F (alternating_minimization_prefix_state x (ψ' (τ m)) (i.1 + 1)))
                Filter.atTop
                (nhds (F (Function.update xBar i (y i)))) := by
          -- Continuity identifies the limit objective value of the extracted stage-`i+1` states.
          exact alternating_minimization_tendsto_objective_of_tendsto
            F hcont hupdated_dom hnextUpdateτ (fun m ↦ hnext_dom (τ m))
        have hcompObj :
            Filter.Tendsto
                (fun m ↦
                  F
                    (Function.update
                      (alternating_minimization_prefix_state x (ψ' (τ m)) i.1)
                      i
                      (ziSeq m)))
                Filter.atTop
                (nhds (F (Function.update xBar i zi))) := by
          -- Continuity transports the recovered strict competitors to the fixed-base value.
          exact alternating_minimization_recovered_competitor_objective_tendsto
            F x hcont (i := i) hstageτ hzi_dom hziSeq hziSeq_dom
        have hstepCompare :
            ∀ m,
              F (alternating_minimization_prefix_state x (ψ' (τ m)) (i.1 + 1)) ≤
                F
                  (Function.update
                    (alternating_minimization_prefix_state x (ψ' (τ m)) i.1)
                    i
                    (ziSeq m)) := by
          intro m
          -- Each exact block update beats every recovered moving-base strict competitor.
          have hziSeq_mem : ziSeq m ∈ Set.univ := by
            simp
          have hstep :=
            (isMinOn_iff.mp (is_alternating_minimization_trajectory_step htraj (ψ' (τ m)) i))
              (ziSeq m) hziSeq_mem
          simpa [alternating_minimization_prefix_state_new_eq_partial_state,
            alternating_minimization_partial_state_eq_update_prefix_state,
            alternating_minimization_block_objective_apply] using hstep
        exact le_of_tendsto_of_tendsto' hnextUpdateObj hcompObj hstepCompare
      · -- If the competitor is feasible but not strictly below the initial level, the updated
        -- limit state already lies in that initial level, so the comparison is immediate.
        exact le_trans hupdated_le_initial (not_lt.mp hzi_strict)
    · have hzi_not_lt_top :
          ¬ F (Function.update xBar i zi) < ⊤ := by
        simpa using hzi_dom
      have hzi_top :
          F (Function.update xBar i zi) = ⊤ := by
        -- Outside the effective domain, the fixed-base competitor value is exactly `⊤`.
        exact top_unique <| not_lt.mp hzi_not_lt_top
      simp [hzi_top]
  exact ⟨φ, hφ, y i, hyArgmin, hcoord', hdom'⟩

/-- Helper for `alternatingMinimizationRecoverLimitArgminAlongPrefixState`: once strict fixed-base
competitors can be recovered along nearby stage-`i` bases, the stage-`i+1` limit coordinate
belongs to the fixed-base block argmin. -/
theorem alternating_minimization_limit_block_argmin_of_strictRecovery.{u} :
    ∀ {p : ℕ} {Ei : Fin p → Type u}
      [(i : Fin p) → PseudoMetricSpace (Ei i)]
      [ProperSpace ((i : Fin p) → Ei i)]
      (F : ((i : Fin p) → Ei i) → EReal) (x : ℕ → (i : Fin p) → Ei i),
      LowerSemicontinuous F →
        ContinuousOn F (effective_domain F) →
          is_alternating_minimization_trajectory F x →
            ∀ (xBar y : (j : Fin p) → Ei j) (i : Fin p) {ψ : ℕ → ℕ},
              xBar ∈ effective_domain F →
                Inseparable y (Function.update xBar i (y i)) →
                  Filter.Tendsto
                      (fun m ↦ alternating_minimization_prefix_state x (ψ m) ↑i)
                      Filter.atTop
                      (nhds xBar) →
                    Filter.Tendsto
                        (fun m ↦ alternating_minimization_prefix_state x (ψ m) (↑i + 1))
                        Filter.atTop
                        (nhds y) →
                      Filter.Tendsto
                          (fun m ↦ F (alternating_minimization_prefix_state x (ψ m) (↑i + 1)))
                          Filter.atTop
                          (nhds (F xBar)) →
                        (∀ ⦃zi : Ei i⦄,
                            Function.update xBar i zi ∈ effective_domain F →
                              F (Function.update xBar i zi) < F xBar →
                                ∀ s ∈ nhds zi,
                                  {xBase |
                                      ∃ zi' ∈ s,
                                        Function.update xBase i zi' ∈ effective_domain F ∧
                                          F (Function.update xBase i zi') < F xBar} ∈
                                    nhds xBar) →
                          y i ∈ alternating_minimization_argmin F xBar i := by
  intro p Ei _ _ F x hclosed hcont htraj xBar y i ψ hxBar hyUpdate hstage hnext hFnext hrecover
  rcases alternating_minimization_limit_block_updated_value_eq_cluster_value
      F x hclosed hcont htraj xBar y i hxBar hyUpdate hnext hFnext with
    ⟨hupdated_dom, hupdated_value⟩
  -- Discharge the strict branch only through explicit recovered competitors.
  refine (mem_alternating_minimization_argmin_update_iff).2 ?_
  rw [isMinOn_iff]
  intro zi hzi
  by_cases hzi_dom : Function.update xBar i zi ∈ effective_domain F
  · by_cases hzi_strict : F (Function.update xBar i zi) < F xBar
    · let P : ℕ → ℕ → Prop :=
          fun n k ↦
            ∃ zi' ∈ Metric.ball zi (1 / (n + 1 : ℝ)),
              Function.update
                  (alternating_minimization_prefix_state x (ψ k) i.1)
                  i
                  zi' ∈ effective_domain F ∧
                F
                    (Function.update
                      (alternating_minimization_prefix_state x (ψ k) i.1)
                      i
                      zi') <
                  F xBar
      have hP : ∀ n, ∀ᶠ k in Filter.atTop, P n k := by
        intro n
        have hball : Metric.ball zi (1 / (n + 1 : ℝ)) ∈ nhds zi := by
          -- The recovery premise is queried on shrinking metric balls around the competitor.
          apply Metric.ball_mem_nhds
          positivity
        have hnear :
            {xBase |
                ∃ zi' ∈ Metric.ball zi (1 / (n + 1 : ℝ)),
                  Function.update xBase i zi' ∈ effective_domain F ∧
                    F (Function.update xBase i zi') < F xBar} ∈
              nhds xBar :=
          hrecover hzi_dom hzi_strict _ hball
        exact hstage hnear
      rcases Filter.extraction_forall_of_eventually hP with ⟨τ, hτ, hτ_good⟩
      let ziSeq : ℕ → Ei i := fun n ↦ Classical.choose (hτ_good n)
      have hziSeq_ball :
          ∀ n : ℕ, ziSeq n ∈ Metric.ball zi (1 / (n + 1 : ℝ)) := by
        intro n
        exact (Classical.choose_spec (hτ_good n)).1
      have hziSeq_dom :
          ∀ n : ℕ,
            Function.update
                (alternating_minimization_prefix_state x (ψ (τ n)) i.1)
                i
                (ziSeq n) ∈
              effective_domain F := by
        intro n
        exact (Classical.choose_spec (hτ_good n)).2.1
      have hziSeq :
          Filter.Tendsto ziSeq Filter.atTop (nhds zi) := by
        -- The shrinking-ball construction sends the recovered competitors back to the target block.
        refine Metric.tendsto_atTop'.2 ?_
        intro ε hε
        rcases exists_nat_one_div_lt hε with ⟨N, hN⟩
        refine ⟨N, ?_⟩
        intro n hn
        have hdist : dist (ziSeq n) zi < 1 / (n + 1 : ℝ) := by
          simpa [Metric.mem_ball] using hziSeq_ball n
        have hsmall : (1 / (n + 1 : ℝ)) < ε := by
          exact lt_trans (Nat.one_div_lt_one_div hn) hN
        exact lt_trans hdist hsmall
      have hstageτ :
          Filter.Tendsto
              (fun m ↦ alternating_minimization_prefix_state x (ψ (τ m)) i.1)
              Filter.atTop
              (nhds xBar) := by
        -- Refining by the extracted diagonal subsequence preserves the stage-`i` limit.
        exact hstage.comp hτ.tendsto_atTop
      have hFnextτ :
          Filter.Tendsto
              (fun m ↦ F (alternating_minimization_prefix_state x (ψ (τ m)) (i.1 + 1)))
              Filter.atTop
              (nhds (F xBar)) := by
        -- The same extraction preserves convergence of the stage-`i+1` objective values.
        exact hFnext.comp hτ.tendsto_atTop
      -- The recovered-competitor comparison lemma finishes the only genuinely strict branch.
      exact alternating_minimization_limit_block_compare_with_recovered_competitor
        F x hcont htraj xBar y i hstageτ hFnextτ hupdated_value hzi_dom hziSeq hziSeq_dom
    · calc
        F (Function.update xBar i (y i)) = F xBar := hupdated_value
        _ ≤ F (Function.update xBar i zi) := not_lt.mp hzi_strict
  · have hzi_not_lt_top :
        ¬ F (Function.update xBar i zi) < ⊤ := by
      simpa using hzi_dom
    have hzi_top : F (Function.update xBar i zi) = ⊤ := by
      -- Outside the effective domain, the fixed-base competitor value is exactly `⊤`.
      exact top_unique <| not_lt.mp hzi_not_lt_top
    simp [hzi_top]

/-- Public owner for `alternatingMinimizationRecoverLimitArgminAlongPrefixState`: the fixed-base
block-argmin
owner packages the bounded-sublevel source-facing hypotheses and delegates the proof to the
strict-recovery version. -/
theorem alternating_minimization_limit_block_argmin.{u} :
    ∀ {p : ℕ} {Ei : Fin p → Type u}
      [(i : Fin p) → PseudoMetricSpace (Ei i)]
      [ProperSpace ((i : Fin p) → Ei i)]
      (F : ((i : Fin p) → Ei i) → EReal) (x : ℕ → (i : Fin p) → Ei i),
      LowerSemicontinuous F →
        ContinuousOn F (effective_domain F) →
          (∀ (α : ℝ), Bornology.IsBounded {x | F x ≤ ↑α}) →
            is_alternating_minimization_trajectory F x →
              ∀ (xBar y : (j : Fin p) → Ei j) (i : Fin p) {ψ : ℕ → ℕ},
                xBar ∈ effective_domain F →
                  Inseparable y (Function.update xBar i (y i)) →
                    Filter.Tendsto
                        (fun m ↦ alternating_minimization_prefix_state x (ψ m) ↑i)
                        Filter.atTop
                        (nhds xBar) →
                      Filter.Tendsto
                          (fun m ↦ alternating_minimization_prefix_state x (ψ m) (↑i + 1))
                          Filter.atTop
                          (nhds y) →
                        Filter.Tendsto
                            (fun m ↦
                              F (alternating_minimization_prefix_state x (ψ m) (↑i + 1)))
                            Filter.atTop
                            (nhds (F xBar)) →
                          (∀ ⦃zi : Ei i⦄,
                              Function.update xBar i zi ∈ effective_domain F →
                                F (Function.update xBar i zi) < F xBar →
                                  ∀ s ∈ nhds zi,
                                    {xBase |
                                        ∃ zi' ∈ s,
                                          Function.update xBase i zi' ∈ effective_domain F ∧
                                            F (Function.update xBase i zi') < F xBar} ∈
                                      nhds xBar) →
                            y i ∈ alternating_minimization_argmin F xBar i := by
  intro p Ei _ _ F x hclosed hcont hlevels htraj xBar y i ψ hxBar hyUpdate hstage hnext
    hFnext hrecover
  let _ := hlevels
  -- Delegate to the recovery-threaded owner.
  exact alternating_minimization_limit_block_argmin_of_strictRecovery
    F x hclosed hcont htraj xBar y i hxBar hyUpdate hstage hnext hFnext hrecover
