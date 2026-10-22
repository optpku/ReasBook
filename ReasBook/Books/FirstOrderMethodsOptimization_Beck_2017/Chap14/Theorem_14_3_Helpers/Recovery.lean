/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap14.Theorem_14_3_Helpers.PrefixState

private theorem alternatingMinimizationRecoverLimitArgminAlongPrefixState.{u} : ∀ {p : ℕ} {Ei : Fin p → Type u}
  [inst : (i : Fin p) → PseudoMetricSpace (Ei i)] [ProperSpace ((i : Fin p) → Ei i)]
  (F : ((i : Fin p) → Ei i) → EReal) (x : ℕ → (i : Fin p) → Ei i),
  LowerSemicontinuous F →
    ContinuousOn F (effective_domain F) →
      (∀ (α : ℝ), Bornology.IsBounded {x | F x ≤ ↑α}) →
        is_alternating_minimization_trajectory F x →
          ∀ {xBar : (j : Fin p) → Ei j} (i : Fin p) {ψ : ℕ → ℕ},
            Filter.Tendsto (fun m => alternating_minimization_prefix_state x (ψ m) ↑i) Filter.atTop (nhds xBar) →
              (∀ ⦃zi : Ei i⦄,
                  Function.update xBar i zi ∈ effective_domain F →
                    F (Function.update xBar i zi) < ↑(F (x 0)).toReal →
                      ∀ s ∈ nhds zi,
                        {xBase |
                            ∃ zi' ∈ s,
                              Function.update xBase i zi' ∈ effective_domain F ∧
                                F (Function.update xBase i zi') < ↑(F (x 0)).toReal} ∈
                          nhds xBar) →
                ∃ φ,
                    ∃ (_ : StrictMono φ),
                    ∃ ziLimit ∈ alternating_minimization_argmin F xBar i,
                      Filter.Tendsto (fun m => x (ψ (φ m) + 1) i) Filter.atTop (nhds ziLimit) ∧
                        ∀ (m : ℕ),
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
  have hupdated_dom :
      Function.update xBar i (y i) ∈ effective_domain F := by
    -- The initial real sublevel is finite, hence contained in the effective domain.
    exact mem_effective_domain.mpr <|
      lt_of_le_of_lt hupdated_le_initial (by simp)
  have hnext_dom :
      ∀ m, alternating_minimization_prefix_state x (ψ' m) (i.1 + 1) ∈ effective_domain F := by
    intro m
    -- Rewrite the packaged recovered update back to the stage-`i+1` prefix state.
    simpa [alternating_minimization_prefix_state_new_eq_partial_state,
      alternating_minimization_partial_state_eq_update_prefix_state] using hdom' m
  have hyArgmin :
      y i ∈ alternating_minimization_argmin F xBar i := by
    -- Route correction: prove the fixed-base block argmin statement directly from the theorem's
    -- strict-recovery hypothesis, instead of routing through the unresolved no-recovery owner.
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
            -- The recovery hypothesis is queried on shrinking metric balls around `zi`.
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
          -- Continuity also transports the recovered strict competitors back to the fixed-base
          -- competitor value.
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
          have hstep :=
            (isMinOn_iff.mp (is_alternating_minimization_trajectory_step htraj (ψ' (τ m)) i))
              (ziSeq m) (by simp)
          simpa [alternating_minimization_prefix_state_new_eq_partial_state,
            alternating_minimization_partial_state_eq_update_prefix_state,
            alternating_minimization_block_objective_apply] using hstep
        exact le_of_tendsto_of_tendsto' hnextUpdateObj hcompObj hstepCompare
      · -- If the competitor is feasible but not strictly below the initial level, the updated
        -- limit state already lies in that initial level, so the comparison is immediate.
        exact le_trans hupdated_le_initial (not_lt.mp hzi_strict)
    · have hzi_top :
          F (Function.update xBar i zi) = ⊤ := by
        -- Outside the effective domain, the fixed-base competitor value is exactly `⊤`.
        exact top_unique <| not_lt.mp (by simpa using hzi_dom)
      simpa [hzi_top] using (le_top : F (Function.update xBar i (y i)) ≤ ⊤)
  exact ⟨φ, hφ, y i, hyArgmin, hcoord', hdom'⟩

/-- Helper for Theorem 14.3: once strict fixed-base competitors can be recovered along nearby
stage-`i` bases, the stage-`i+1` limit coordinate belongs to the fixed-base block argmin. -/
private theorem alternating_minimization_limit_block_argmin_of_strictRecovery.{u} :
    ∀ {p : ℕ} {Ei : Fin p → Type u}
      [inst : (i : Fin p) → PseudoMetricSpace (Ei i)] [ProperSpace ((i : Fin p) → Ei i)]
      (F : ((i : Fin p) → Ei i) → EReal) (x : ℕ → (i : Fin p) → Ei i),
      LowerSemicontinuous F →
        ContinuousOn F (effective_domain F) →
          is_alternating_minimization_trajectory F x →
            ∀ (xBar y : (j : Fin p) → Ei j) (i : Fin p) {ψ : ℕ → ℕ},
              xBar ∈ effective_domain F →
                Inseparable y (Function.update xBar i (y i)) →
                  Filter.Tendsto (fun m => alternating_minimization_prefix_state x (ψ m) ↑i)
                    Filter.atTop (nhds xBar) →
                    Filter.Tendsto (fun m => alternating_minimization_prefix_state x (ψ m) (↑i + 1))
                      Filter.atTop (nhds y) →
                      Filter.Tendsto
                          (fun m => F (alternating_minimization_prefix_state x (ψ m) (↑i + 1)))
                          Filter.atTop (nhds (F xBar)) →
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
  -- Route correction: discharge the strict branch only through explicit recovered competitors.
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
  · have hzi_top : F (Function.update xBar i zi) = ⊤ := by
      -- Outside the effective domain, the fixed-base competitor value is exactly `⊤`.
      exact top_unique <| not_lt.mp (by simpa using hzi_dom)
    simpa [hzi_top] using (le_top : F (Function.update xBar i (y i)) ≤ ⊤)

private theorem alternating_minimization_limit_block_argmin.{u} : ∀ {p : ℕ} {Ei : Fin p → Type u}
  [inst : (i : Fin p) → PseudoMetricSpace (Ei i)] [ProperSpace ((i : Fin p) → Ei i)]
  (F : ((i : Fin p) → Ei i) → EReal) (x : ℕ → (i : Fin p) → Ei i),
  LowerSemicontinuous F →
    ContinuousOn F (effective_domain F) →
      (∀ (α : ℝ), Bornology.IsBounded {x | F x ≤ ↑α}) →
        is_alternating_minimization_trajectory F x →
          ∀ (xBar y : (j : Fin p) → Ei j) (i : Fin p) {ψ : ℕ → ℕ},
            xBar ∈ effective_domain F →
              Inseparable y (Function.update xBar i (y i)) →
                Filter.Tendsto (fun m => alternating_minimization_prefix_state x (ψ m) ↑i)
                  Filter.atTop (nhds xBar) →
                  Filter.Tendsto (fun m => alternating_minimization_prefix_state x (ψ m) (↑i + 1))
                    Filter.atTop (nhds y) →
                    Filter.Tendsto
                        (fun m => F (alternating_minimization_prefix_state x (ψ m) (↑i + 1)))
                        Filter.atTop (nhds (F xBar)) →
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
  intro p Ei _ _ F x hclosed hcont hlevels htraj xBar y i ψ hxBar hyUpdate hstage hnext hFnext
    hrecover
  -- Route correction: the public helper now threads the strict-recovery premise explicitly and
  -- reuses the proved recovery-threaded owner below.
  exact alternating_minimization_limit_block_argmin_of_strictRecovery
    F x hclosed hcont htraj xBar y i hxBar hyUpdate hstage hnext hFnext hrecover

theorem AlternatingMinimization.ClusterPoint.mem_effective_domain_of_initial_sublevel.{u} :
    ∀ {p : ℕ} {Ei : Fin p → Type u} [inst : (i : Fin p) → PseudoMetricSpace (Ei i)]
      (F : ((i : Fin p) → Ei i) → EReal) (x : ℕ → (i : Fin p) → Ei i),
      LowerSemicontinuous F →
        is_alternating_minimization_trajectory F x →
          ∀ {xBar : (i : Fin p) → Ei i},
            MapClusterPt xBar Filter.atTop x → xBar ∈ effective_domain F := by
  intro p Ei _ F x hclosed htraj xBar hxBar
  rcases MapClusterPt.tendsto_subseq hxBar with ⟨ψ, -, hψtendsto⟩
  have hx0_dom : x 0 ∈ effective_domain F :=
    is_alternating_minimization_trajectory_zero htraj
  have hx0_top : F (x 0) ≠ ⊤ := (mem_effective_domain.mp hx0_dom).ne
  have hsublevel_closed :
      IsClosed {z | F z ≤ (((F (x 0)).toReal : ℝ) : EReal)} := by
    -- Lower semicontinuity closes the initial real sublevel containing the whole trajectory.
    simpa using hclosed.isClosed_preimage ((((F (x 0)).toReal : ℝ) : EReal))
  have hxsublevel :
      xBar ∈ {z | F z ≤ (((F (x 0)).toReal : ℝ) : EReal)} := by
    -- Every iterate stays below the initial objective, so every subsequential limit stays in the
    -- same closed real sublevel.
    refine hsublevel_closed.mem_of_tendsto hψtendsto ?_
    exact Filter.Eventually.of_forall fun m ↦ by
      calc
        F (x (ψ m)) ≤ F (x 0) :=
          alternating_minimization_objective_le_initial F x htraj (ψ m)
        _ ≤ (((F (x 0)).toReal : ℝ) : EReal) := EReal.le_coe_toReal hx0_top
  -- Membership in a finite real sublevel excludes `⊤`, which is exactly effective-domain
  -- membership for `EReal`-valued objectives.
  exact mem_effective_domain.mpr <|
    lt_of_le_of_lt hxsublevel (by simp)

/-- Helper for Theorem 14.3: once the outer iterates and the stage-`i` prefix states converge to
the same cluster point, the stage-`i+1` objective values converge to that cluster value as well. -/
theorem alternating_minimization_prefix_state_stage_succ_objective_tendsto.{u} :
    ∀ {p : ℕ} {Ei : Fin p → Type u}
      [inst : (i : Fin p) → PseudoMetricSpace (Ei i)]
      (F : ((i : Fin p) → Ei i) → EReal) (x : ℕ → (i : Fin p) → Ei i),
      ContinuousOn F (effective_domain F) →
        is_alternating_minimization_trajectory F x →
          ∀ {ψ : ℕ → ℕ},
            StrictMono ψ →
              ∀ (i : Fin p) {xBar : (j : Fin p) → Ei j},
                xBar ∈ effective_domain F →
                  Filter.Tendsto (fun m => x (ψ m)) Filter.atTop (nhds xBar) →
                    Filter.Tendsto
                        (fun m => alternating_minimization_prefix_state x (ψ m) ↑i)
                        Filter.atTop (nhds xBar) →
                      Filter.Tendsto
                          (fun m => F (alternating_minimization_prefix_state x (ψ m) (↑i + 1)))
                          Filter.atTop (nhds (F xBar)) := by
  intro p Ei _ F x hcont htraj ψ hψ i xBar hxBar hiter hstage
  have hstage_dom :
      ∀ m, alternating_minimization_prefix_state x (ψ m) i.1 ∈ effective_domain F := by
    intro m
    -- Every stage-`i` prefix state remains in the effective domain along the trajectory.
    exact (alternating_minimization_prefix_state_mem_effective_domain_and_le
      F x htraj (ψ m)
      (alternating_minimization_iterate_mem_effective_domain F x htraj (ψ m))
      i.1 (Nat.le_of_lt i.is_lt)).1
  have hFiter :
      Filter.Tendsto (fun m ↦ F (x (ψ m))) Filter.atTop (nhds (F xBar)) := by
    -- Continuity identifies the objective limit along the convergent outer-iterate subsequence.
    exact alternating_minimization_tendsto_objective_of_tendsto
      F hcont hxBar hiter
      (fun m ↦ alternating_minimization_iterate_mem_effective_domain F x htraj (ψ m))
  have hFshift :
      Filter.Tendsto (fun m ↦ F (x (ψ m + 1))) Filter.atTop (nhds (F xBar)) := by
    -- Monotonicity of the objective transfers the same limit to the shifted subsequence.
    exact alternating_minimization_shifted_objective_tendsto F x htraj hψ hFiter
  have hFstage :
      Filter.Tendsto
          (fun m ↦ F (alternating_minimization_prefix_state x (ψ m) i.1))
          Filter.atTop
          (nhds (F xBar)) := by
    -- The stage-`i` prefix states converge to the same cluster point inside the effective domain.
    exact alternating_minimization_tendsto_objective_of_tendsto
      F hcont hxBar hstage hstage_dom
  -- The stage-`i+1` objective stays between the shifted iterate objective and the stage-`i`
  -- prefix objective, so it converges to the same cluster value.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hFshift hFstage ?_ ?_
  · intro m
    exact alternating_minimization_next_iterate_objective_le_prefix_state
      F x htraj (ψ m) (i.1 + 1)
  · intro m
    exact alternating_minimization_prefix_state_succ_objective_le
      F x htraj (ψ m) i.1 i.is_lt

theorem alternating_minimization_prefix_state_limit_value_eq_cluster_value.{u} :
    ∀ {p : ℕ} {Ei : Fin p → Type u}
      [inst : (i : Fin p) → PseudoMetricSpace (Ei i)]
      (F : ((i : Fin p) → Ei i) → EReal) (x : ℕ → (i : Fin p) → Ei i),
      ContinuousOn F (effective_domain F) →
        is_alternating_minimization_trajectory F x →
          ∀ {ψ : ℕ → ℕ},
            StrictMono ψ →
              ∀ (i : Fin p) {xBar y : (j : Fin p) → Ei j},
                xBar ∈ effective_domain F →
                  Filter.Tendsto (fun m => x (ψ m)) Filter.atTop (nhds xBar) →
                    Filter.Tendsto
                        (fun m => alternating_minimization_prefix_state x (ψ m) ↑i)
                        Filter.atTop (nhds xBar) →
                      Filter.Tendsto
                          (fun m => alternating_minimization_prefix_state x (ψ m) (↑i + 1))
                          Filter.atTop (nhds y) →
                        Inseparable y (Function.update xBar i (y i)) →
                          y i ∈ alternating_minimization_argmin F xBar i →
                            F (Function.update xBar i (y i)) = F xBar := by
  intro p Ei _ F x hcont htraj ψ hψ i xBar y hxBar hiter hstage hnext hyUpdate hyArgmin
  have hupdate_dom :
      Function.update xBar i (y i) ∈ effective_domain F :=
    alternating_minimization_argmin_update_mem_effective_domain_of_base_mem
      F i hxBar hyArgmin
  have hstage_dom :
      ∀ m, alternating_minimization_prefix_state x (ψ m) i.1 ∈ effective_domain F := by
    intro m
    exact (alternating_minimization_prefix_state_mem_effective_domain_and_le
      F x htraj (ψ m)
      (alternating_minimization_iterate_mem_effective_domain F x htraj (ψ m))
      i.1 (Nat.le_of_lt i.is_lt)).1
  have hnext_dom :
      ∀ m, alternating_minimization_prefix_state x (ψ m) (i.1 + 1) ∈ effective_domain F := by
    intro m
    exact (alternating_minimization_prefix_state_mem_effective_domain_and_le
      F x htraj (ψ m)
      (alternating_minimization_iterate_mem_effective_domain F x htraj (ψ m))
      (i.1 + 1) (Nat.succ_le_of_lt i.is_lt)).1
  have hFiter :
      Filter.Tendsto (fun m ↦ F (x (ψ m))) Filter.atTop (nhds (F xBar)) := by
    -- Continuity on the effective domain identifies the objective limit along the converging
    -- subsequence of outer iterates.
    exact alternating_minimization_tendsto_objective_of_tendsto
      F hcont hxBar hiter
      (fun m ↦ alternating_minimization_iterate_mem_effective_domain F x htraj (ψ m))
  have hFshift :
      Filter.Tendsto (fun m ↦ F (x (ψ m + 1))) Filter.atTop (nhds (F xBar)) := by
    -- The outer-iterate objective is antitone, so the shifted subsequence has the same limit.
    exact alternating_minimization_shifted_objective_tendsto F x htraj hψ hFiter
  have hFstage :
      Filter.Tendsto
          (fun m ↦ F (alternating_minimization_prefix_state x (ψ m) i.1))
          Filter.atTop
          (nhds (F xBar)) := by
    -- The stage-`i` prefix states converge to the same cluster point inside the effective domain.
    exact alternating_minimization_tendsto_objective_of_tendsto
      F hcont hxBar hstage hstage_dom
  have hFnext_xBar :
      Filter.Tendsto
          (fun m ↦ F (alternating_minimization_prefix_state x (ψ m) (i.1 + 1)))
          Filter.atTop
          (nhds (F xBar)) := by
    -- The stage-`i+1` objective is squeezed between the shifted outer iterate and the stage-`i`
    -- prefix objective, so it converges to the same value.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hFshift hFstage ?_ ?_
    · intro m
      exact alternating_minimization_next_iterate_objective_le_prefix_state
        F x htraj (ψ m) (i.1 + 1)
    · intro m
      exact alternating_minimization_prefix_state_succ_objective_le
        F x htraj (ψ m) i.1 i.is_lt
  have hnext_update :
      Filter.Tendsto
          (fun m ↦ alternating_minimization_prefix_state x (ψ m) (i.1 + 1))
          Filter.atTop
          (nhds (Function.update xBar i (y i))) := by
    -- The stage-`i+1` limit and the updated cluster point are topologically indistinguishable.
    simpa [hyUpdate.nhds_eq] using hnext
  have hFnext_update :
      Filter.Tendsto
          (fun m ↦ F (alternating_minimization_prefix_state x (ψ m) (i.1 + 1)))
          Filter.atTop
          (nhds (F (Function.update xBar i (y i)))) := by
    -- Continuity transports that updated-state convergence to the objective values.
    exact alternating_minimization_tendsto_objective_of_tendsto
      F hcont hupdate_dom hnext_update hnext_dom
  -- Uniqueness of limits identifies the updated-state objective with the cluster-point value.
  exact tendsto_nhds_unique hFnext_update hFnext_xBar

/-- Helper for Theorem 14.3: the stage-`i+1` limit package recovers both the fixed-base argmin
fact and the value identity once strict competitors admit the local recovery premise. -/
theorem alternating_minimization_prefix_state_limit_update_argmin_and_value_of_strictRecovery.{u} :
    ∀ {p : ℕ} {Ei : Fin p → Type u}
      [inst : (i : Fin p) → PseudoMetricSpace (Ei i)] [ProperSpace ((i : Fin p) → Ei i)]
      (F : ((i : Fin p) → Ei i) → EReal) (x : ℕ → (i : Fin p) → Ei i),
      LowerSemicontinuous F →
        ContinuousOn F (effective_domain F) →
          is_alternating_minimization_trajectory F x →
            ∀ {ψ : ℕ → ℕ},
              StrictMono ψ →
                ∀ (i : Fin p) {xBar y : (j : Fin p) → Ei j},
                  xBar ∈ effective_domain F →
                    Filter.Tendsto (fun m => x (ψ m)) Filter.atTop (nhds xBar) →
                      Filter.Tendsto
                          (fun m => alternating_minimization_prefix_state x (ψ m) ↑i)
                          Filter.atTop (nhds xBar) →
                        Filter.Tendsto
                            (fun m => alternating_minimization_prefix_state x (ψ m) (↑i + 1))
                            Filter.atTop (nhds y) →
                          (∀ ⦃zi : Ei i⦄,
                              Function.update xBar i zi ∈ effective_domain F →
                                F (Function.update xBar i zi) < F xBar →
                                  ∀ s ∈ nhds zi,
                                    {xBase |
                                        ∃ zi' ∈ s,
                                          Function.update xBase i zi' ∈ effective_domain F ∧
                                            F (Function.update xBase i zi') < F xBar} ∈
                                      nhds xBar) →
                            Inseparable y (Function.update xBar i (y i)) ∧
                              y i ∈ alternating_minimization_argmin F xBar i ∧
                                F (Function.update xBar i (y i)) = F xBar := by
  intro p Ei _ _ F x hclosed hcont htraj ψ hψ i xBar y hxBar hiter hstage hnext hrecover
  have hyUpdate :
      Inseparable y (Function.update xBar i (y i)) :=
    alternating_minimization_prefix_state_limit_inseparable_update x ψ i hstage hnext
  have hFnext :
      Filter.Tendsto
          (fun m ↦ F (alternating_minimization_prefix_state x (ψ m) (i.1 + 1)))
          Filter.atTop (nhds (F xBar)) := by
    -- Reuse the same stage-`i+1` objective squeeze after threading the strict-recovery premise.
    exact alternating_minimization_prefix_state_stage_succ_objective_tendsto
      F x hcont htraj hψ i hxBar hiter hstage
  have hyArgmin :
      y i ∈ alternating_minimization_argmin F xBar i := by
    -- Route correction: use the recovery-threaded owner instead of the blocked no-recovery API.
    exact alternating_minimization_limit_block_argmin_of_strictRecovery
      F x hclosed hcont htraj xBar y i hxBar hyUpdate hstage hnext hFnext hrecover
  have hvalue :
      F (Function.update xBar i (y i)) = F xBar := by
    -- Once the block argmin fact is available, continuity identifies the updated-state value.
    exact alternating_minimization_prefix_state_limit_value_eq_cluster_value
      F x hcont htraj hψ i hxBar hiter hstage hnext hyUpdate hyArgmin
  exact ⟨hyUpdate, hyArgmin, hvalue⟩

theorem alternating_minimization_prefix_state_limit_update_argmin_and_value.{u} :
    ∀ {p : ℕ} {Ei : Fin p → Type u}
      [inst : (i : Fin p) → PseudoMetricSpace (Ei i)] [ProperSpace ((i : Fin p) → Ei i)]
      (F : ((i : Fin p) → Ei i) → EReal) (x : ℕ → (i : Fin p) → Ei i),
      LowerSemicontinuous F →
        ContinuousOn F (effective_domain F) →
          (∀ (α : ℝ), Bornology.IsBounded {x | F x ≤ ↑α}) →
            is_alternating_minimization_trajectory F x →
              ∀ {ψ : ℕ → ℕ},
                StrictMono ψ →
                  ∀ (i : Fin p) {xBar y : (j : Fin p) → Ei j},
                    xBar ∈ effective_domain F →
                      Filter.Tendsto (fun m => x (ψ m)) Filter.atTop (nhds xBar) →
                        Filter.Tendsto
                            (fun m => alternating_minimization_prefix_state x (ψ m) ↑i)
                            Filter.atTop (nhds xBar) →
                          Filter.Tendsto
                              (fun m => alternating_minimization_prefix_state x (ψ m) (↑i + 1))
                              Filter.atTop (nhds y) →
                            (∀ ⦃zi : Ei i⦄,
                                Function.update xBar i zi ∈ effective_domain F →
                                  F (Function.update xBar i zi) < F xBar →
                                    ∀ s ∈ nhds zi,
                                      {xBase |
                                          ∃ zi' ∈ s,
                                            Function.update xBase i zi' ∈ effective_domain F ∧
                                              F (Function.update xBase i zi') < F xBar} ∈
                                        nhds xBar) →
                              Inseparable y (Function.update xBar i (y i)) ∧
                                y i ∈ alternating_minimization_argmin F xBar i ∧
                                  F (Function.update xBar i (y i)) = F xBar := by
  intro p Ei _ _ F x hclosed hcont hlevels htraj ψ hψ i xBar y hxBar hiter hstage hnext
    hrecover
  -- Route correction: package the stage-`i+1` limit facts by delegating to the proved
  -- recovery-threaded variant, while retaining the bounded-sublevel parameter for compatibility.
  simpa using
    alternating_minimization_prefix_state_limit_update_argmin_and_value_of_strictRecovery
      F x hclosed hcont htraj hψ i hxBar hiter hstage hnext hrecover

/-- Helper for `alternatingMinimizationRecoverLimitArgminAlongPrefixState`: if the stage-`n`
cluster point admits strict competitor recovery, then a refined stage-`n+1` subsequence
converges back to the same cluster point and forces the `n`th coordinate into the fixed-base
block argmin. -/
theorem alternating_minimization_prefix_state_stage_succ_refine_to_cluster_point_of_strictRecovery.{u} :
    ∀ {p : ℕ} {Ei : Fin p → Type u}
      [inst : (i : Fin p) → PseudoMetricSpace (Ei i)] [ProperSpace ((i : Fin p) → Ei i)]
      (F : ((i : Fin p) → Ei i) → EReal) (x : ℕ → (i : Fin p) → Ei i),
      LowerSemicontinuous F →
        ContinuousOn F (effective_domain F) →
          (∀ xBar ∈ effective_domain F, ∀ (i : Fin p),
            (alternating_minimization_argmin F xBar i).Subsingleton) →
            (∀ (α : ℝ), Bornology.IsBounded {x | F x ≤ ↑α}) →
              is_alternating_minimization_trajectory F x →
                ∀ {xBar : (i : Fin p) → Ei i},
                  MapClusterPt xBar Filter.atTop x →
                    ∀ {ψ : ℕ → ℕ},
                      StrictMono ψ →
                        ∀ {n : ℕ} (hn : n < p),
                          Filter.Tendsto (fun m => x (ψ m)) Filter.atTop (nhds xBar) →
                            Filter.Tendsto
                                (fun m => alternating_minimization_prefix_state x (ψ m) n)
                                Filter.atTop (nhds xBar) →
                              (∀ ⦃zi : Ei ⟨n, hn⟩⦄,
                                  Function.update xBar ⟨n, hn⟩ zi ∈ effective_domain F →
                                    F (Function.update xBar ⟨n, hn⟩ zi) < F xBar →
                                      ∀ s ∈ nhds zi,
                                        {xBase |
                                            ∃ zi' ∈ s,
                                              Function.update xBase ⟨n, hn⟩ zi' ∈
                                                effective_domain F ∧
                                                F (Function.update xBase ⟨n, hn⟩ zi') <
                                                  F xBar} ∈
                                          nhds xBar) →
                                ∃ ψ' : ℕ → ℕ,
                                  StrictMono ψ' ∧
                                    Filter.Tendsto (fun m => x (ψ' m)) Filter.atTop
                                      (nhds xBar) ∧
                                      Filter.Tendsto
                                          (fun m =>
                                            alternating_minimization_prefix_state x (ψ' m)
                                              (n + 1))
                                          Filter.atTop
                                          (nhds xBar) ∧
                                        xBar ⟨n, hn⟩ ∈
                                          alternating_minimization_argmin F xBar ⟨n, hn⟩ := by
  intro p Ei _ _ F x hclosed hcont hunique hlevels htraj xBar hxBar ψ hψ n hn hiter hstage
    hrecover
  let i : Fin p := ⟨n, hn⟩
  have hxBar_dom :
      xBar ∈ effective_domain F :=
    AlternatingMinimization.ClusterPoint.mem_effective_domain_of_initial_sublevel
      F x hclosed htraj hxBar
  rcases alternating_minimization_stage_succ_refinement_as_recovered_updates
      F x hclosed hlevels htraj i (ψ := ψ) with
    ⟨φ, hφ, y, hnext, -, _⟩
  let ψ' : ℕ → ℕ := ψ ∘ φ
  have hψ' : StrictMono ψ' := hψ.comp hφ
  have hiter' :
      Filter.Tendsto (fun m ↦ x (ψ' m)) Filter.atTop (nhds xBar) := by
    -- Refining the original subsequence preserves convergence to the cluster point.
    simpa [ψ'] using hiter.comp hφ.tendsto_atTop
  have hstage' :
      Filter.Tendsto
          (fun m ↦ alternating_minimization_prefix_state x (ψ' m) n)
          Filter.atTop
          (nhds xBar) := by
    -- The stage-`n` prefix-state convergence survives the same refinement.
    simpa [ψ'] using hstage.comp hφ.tendsto_atTop
  have hnext' :
      Filter.Tendsto
          (fun m ↦ alternating_minimization_prefix_state x (ψ' m) (n + 1))
          Filter.atTop
          (nhds y) := by
    -- The recovered stage-`n+1` limit is exactly the refined stage-`n+1` prefix sequence.
    simpa [ψ', i] using hnext
  rcases alternating_minimization_prefix_state_limit_update_argmin_and_value_of_strictRecovery
      F x hclosed hcont htraj hψ' i hxBar_dom hiter' hstage' hnext' (by simpa [i] using hrecover)
      with ⟨hyUpdate, hyArgmin, hvalue⟩
  have hxBarArgmin :
      xBar i ∈ alternating_minimization_argmin F xBar i :=
    alternating_minimization_base_coordinate_mem_argmin_of_limit
      F xBar y i hyArgmin hvalue
  have hyCluster :
      Inseparable y xBar := by
    -- Route correction: the recovery-threaded argmin package replaces the blocked no-recovery
    -- owner before uniqueness collapses the updated limit back to `xBar`.
    exact alternating_minimization_limit_block_inseparable_cluster_point
      F xBar y i hxBar_dom hyUpdate hyArgmin hvalue hunique
  have hnext_xBar :
      Filter.Tendsto
          (fun m ↦ alternating_minimization_prefix_state x (ψ' m) (n + 1))
          Filter.atTop
          (nhds xBar) := by
    -- The refined stage-`n+1` prefix states converge to `xBar` after transporting through
    -- inseparability.
    simpa [hyCluster.nhds_eq] using hnext'
  exact ⟨ψ', hψ', hiter', hnext_xBar, by simpa [i] using hxBarArgmin⟩

theorem alternating_minimization_prefix_state_stage_succ_refine_to_cluster_point.{u} :
    ∀ {p : ℕ} {Ei : Fin p → Type u}
      [inst : (i : Fin p) → PseudoMetricSpace (Ei i)] [ProperSpace ((i : Fin p) → Ei i)]
      (F : ((i : Fin p) → Ei i) → EReal) (x : ℕ → (i : Fin p) → Ei i),
      LowerSemicontinuous F →
        ContinuousOn F (effective_domain F) →
          (∀ xBar ∈ effective_domain F, ∀ (i : Fin p),
            (alternating_minimization_argmin F xBar i).Subsingleton) →
            (∀ (α : ℝ), Bornology.IsBounded {x | F x ≤ ↑α}) →
              is_alternating_minimization_trajectory F x →
                ∀ {xBar : (i : Fin p) → Ei i},
                  MapClusterPt xBar Filter.atTop x →
                    ∀ {ψ : ℕ → ℕ},
                      StrictMono ψ →
                        ∀ {n : ℕ} (hn : n < p),
                          Filter.Tendsto (fun m => x (ψ m)) Filter.atTop (nhds xBar) →
                            Filter.Tendsto
                                (fun m => alternating_minimization_prefix_state x (ψ m) n)
                                Filter.atTop (nhds xBar) →
                              (∀ ⦃zi : Ei ⟨n, hn⟩⦄,
                                  Function.update xBar ⟨n, hn⟩ zi ∈ effective_domain F →
                                    F (Function.update xBar ⟨n, hn⟩ zi) < F xBar →
                                      ∀ s ∈ nhds zi,
                                        {xBase |
                                            ∃ zi' ∈ s,
                                              Function.update xBase ⟨n, hn⟩ zi' ∈
                                                effective_domain F ∧
                                                F (Function.update xBase ⟨n, hn⟩ zi') <
                                                  F xBar} ∈
                                          nhds xBar) →
                                ∃ ψ' : ℕ → ℕ,
                                  StrictMono ψ' ∧
                                    Filter.Tendsto (fun m => x (ψ' m)) Filter.atTop (nhds xBar) ∧
                                      Filter.Tendsto
                                          (fun m =>
                                            alternating_minimization_prefix_state x (ψ' m)
                                              (n + 1))
                                          Filter.atTop (nhds xBar) ∧
                                        xBar ⟨n, hn⟩ ∈
                                          alternating_minimization_argmin F xBar ⟨n, hn⟩ := by
  intro p Ei _ _ F x hclosed hcont hunique hlevels htraj xBar hxBar ψ hψ n hn hiter hstage
    hrecover
  -- Route correction: the stage-succ packaging now reuses the proved strict-recovery theorem
  -- rather than rebuilding the fixed-competitor branch from the weaker premise-free surface.
  simpa using
    alternating_minimization_prefix_state_stage_succ_refine_to_cluster_point_of_strictRecovery
      F x hclosed hcont hunique hlevels htraj hxBar hψ hn hiter hstage hrecover

theorem alternating_minimization_prefix_state_stage_induction_invariant.{u} :
    ∀ {p : ℕ} {Ei : Fin p → Type u}
      [inst : (i : Fin p) → PseudoMetricSpace (Ei i)] [ProperSpace ((i : Fin p) → Ei i)]
      (F : ((i : Fin p) → Ei i) → EReal) (x : ℕ → (i : Fin p) → Ei i),
      LowerSemicontinuous F →
        ContinuousOn F (effective_domain F) →
          (∀ xBar ∈ effective_domain F, ∀ (i : Fin p),
            (alternating_minimization_argmin F xBar i).Subsingleton) →
            (∀ (α : ℝ), Bornology.IsBounded {x | F x ≤ ↑α}) →
              is_alternating_minimization_trajectory F x →
                (∀ {xBar : (i : Fin p) → Ei i},
                    xBar ∈ effective_domain F →
                      ∀ (i : Fin p) ⦃zi : Ei i⦄,
                        Function.update xBar i zi ∈ effective_domain F →
                          F (Function.update xBar i zi) < F xBar →
                            ∀ s ∈ nhds zi,
                              {xBase |
                                  ∃ zi' ∈ s,
                                    Function.update xBase i zi' ∈ effective_domain F ∧
                                      F (Function.update xBase i zi') < F xBar} ∈
                                nhds xBar) →
                ∀ {xBar : (i : Fin p) → Ei i},
                  MapClusterPt xBar Filter.atTop x →
                    ∀ n : ℕ, n ≤ p →
                      ∃ ψ : ℕ → ℕ,
                        StrictMono ψ ∧
                          Filter.Tendsto (fun m => x (ψ m)) Filter.atTop (nhds xBar) ∧
                                Filter.Tendsto
                                    (fun m => alternating_minimization_prefix_state x (ψ m) n)
                                    Filter.atTop (nhds xBar) ∧
                                  ∀ (j : Fin p),
                                    ↑j < n → xBar j ∈ alternating_minimization_argmin F xBar j := by
  intro p Ei _ _ F x hclosed hcont hunique hlevels htraj hrecover xBar hxBar n hn
  have haux :
      ∀ n : ℕ, n ≤ p →
        ∀ {xBar : (i : Fin p) → Ei i},
          MapClusterPt xBar Filter.atTop x →
            ∃ ψ : ℕ → ℕ,
              StrictMono ψ ∧
                Filter.Tendsto (fun m ↦ x (ψ m)) Filter.atTop (nhds xBar) ∧
                  Filter.Tendsto
                      (fun m ↦ alternating_minimization_prefix_state x (ψ m) n)
                      Filter.atTop
                      (nhds xBar) ∧
                    ∀ (j : Fin p),
                      ↑j < n → xBar j ∈ alternating_minimization_argmin F xBar j := by
    intro n
    induction n with
    | zero =>
        intro hn xBar hxBar
        rcases MapClusterPt.tendsto_subseq hxBar with ⟨ψ, hψ, hiter⟩
        refine ⟨ψ, hψ, hiter, ?_, ?_⟩
        · -- The stage-`0` prefix state is just the current iterate.
          simpa using hiter
        · intro j hj
          exact (Nat.not_lt_zero _ hj).elim
    | succ n ihn =>
        intro hn xBar hxBar
        have hn_le : n ≤ p := Nat.le_of_succ_le hn
        rcases ihn hn_le hxBar with ⟨ψ, hψ, hiter, hstage, hblocks⟩
        have hn_lt : n < p := Nat.lt_of_succ_le hn
        have hxBar_dom :
            xBar ∈ effective_domain F :=
          AlternatingMinimization.ClusterPoint.mem_effective_domain_of_initial_sublevel
            F x hclosed htraj hxBar
        rcases alternating_minimization_prefix_state_stage_succ_refine_to_cluster_point
            F x hclosed hcont hunique hlevels htraj hxBar hψ hn_lt hiter hstage
            (by simpa using hrecover hxBar_dom ⟨n, hn_lt⟩) with
          ⟨ψ', hψ', hiter', hstage', hiArgmin⟩
        refine ⟨ψ', hψ', hiter', hstage', ?_⟩
        intro j hj
        by_cases hji : j = ⟨n, hn_lt⟩
        · subst hji
          simpa using hiArgmin
        · have hj_lt_n : ↑j < n := by
            have hj_le_n : ↑j ≤ n := Nat.lt_succ_iff.mp hj
            have hj_ne_n : ↑j ≠ n := by
              intro hj_eq
              apply hji
              exact Fin.ext hj_eq
            exact lt_of_le_of_ne hj_le_n hj_ne_n
          exact hblocks j hj_lt_n
  exact haux n hn hxBar
