/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u

variable {X : Type u} [MetricSpace X]

/-- Helper for Theorem 1.49: disjoint compact and closed sets have a positive `infDist` gap. -/
private lemma exists_positive_infDist_lower_bound_of_disjoint {A B : Set X} (hA : IsCompact A)
    (hBclosed : IsClosed B) (hBne : B.Nonempty) (hAB : Disjoint A B) :
    ∃ δ > 0, ∀ a ∈ A, δ ≤ Metric.infDist a B := by
  rw [Set.disjoint_left] at hAB
  -- Every point of `A` stays at positive distance from the closed set `B`.
  have hpos : ∀ a ∈ A, 0 < Metric.infDist a B := by
    intro a ha
    have hnotmem : a ∉ B := fun hb ↦ hAB ha hb
    have hnotclosure : a ∉ closure B := by
      simpa [hBclosed.closure_eq] using hnotmem
    exact (Metric.infDist_pos_iff_notMem_closure hBne).mp hnotclosure
  -- Compactness upgrades pointwise positivity to a uniform positive lower bound.
  obtain ⟨δ, hδ, hδlower⟩ :=
    hA.exists_forall_le' ((Metric.continuous_infDist_pt B).continuousOn) hpos
  exact ⟨δ, hδ, hδlower⟩

/-- Helper for Theorem 1.49: a cluster point in `A` forces arbitrarily late visits arbitrarily
close to `A`. -/
private lemma exists_ge_infDist_lt_of_mem_mapClusterPt {A : Set X} {a : X} {u : ℕ → X}
    (haA : a ∈ A)
    (ha : MapClusterPt a atTop u) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n ≥ N, Metric.infDist (u n) A < ε := by
  -- The cluster-point condition gives arbitrarily late terms inside every ball around `a`.
  have hfreq : ∃ᶠ n in atTop, u n ∈ Metric.ball a ε :=
    (mapClusterPt_iff_frequently.mp ha) (Metric.ball a ε) (Metric.ball_mem_nhds a hε)
  rw [Filter.frequently_atTop] at hfreq
  obtain ⟨n, hnN, hnball⟩ := hfreq N
  refine ⟨n, hnN, lt_of_le_of_lt (Metric.infDist_le_dist_of_mem haA) ?_⟩
  simpa [Metric.mem_ball, dist_comm] using hnball

/-- Helper for Theorem 1.49: being within `δ / 3` of the left piece forces distance greater than
`2 * δ / 3` from the right piece. -/
private lemma two_thirds_gap_of_one_third_near_left {A B : Set X} (hAne : A.Nonempty) {δ : ℝ}
    (hlower : ∀ a ∈ A, δ ≤ Metric.infDist a B) {x : X} (hx : Metric.infDist x A < δ / 3) :
    2 * δ / 3 < Metric.infDist x B := by
  -- Pick a point of `A` close to `x` and compare distances through the Lipschitz control of `infDist`.
  obtain ⟨a, haA, hxa⟩ := (Metric.infDist_lt_iff hAne).mp hx
  have hδle : δ ≤ Metric.infDist x B + dist x a := by
    calc
      δ ≤ Metric.infDist a B := hlower a haA
      _ ≤ Metric.infDist x B + dist a x :=
        by
          simpa using
            (show Metric.infDist a B ≤ Metric.infDist x B + dist a x from
              Metric.infDist_le_infDist_add_dist)
      _ = Metric.infDist x B + dist x a := by rw [dist_comm]
  linarith

/- Proof sketch: argue by contradiction, separating the cluster-point set into two disjoint closed
pieces with positive distance; then use `dist (u n) (u (n + 1)) → 0` and compactness to extract
a new cluster point whose distance to one piece lies strictly between `δ / 3` and `2 * δ / 3`,
contradicting the separation. -/
/-- Theorem 1.49: (Ostrowski) in a metric space, if `C` is compact, a sequence `u` takes values in
`C`, and `dist (u n) (u (n + 1)) → 0`, then the cluster-point set of `u` is connected. Under the
hypothesis `u n ∈ C`, every cluster point already lies in `C`, so this is equivalent to the
textbook formulation with `C ∩ {x | MapClusterPt x atTop u}`. -/
theorem isConnected_clusterPoints_of_tendsto_dist_succ_eq_zero
    {C : Set X} {u : ℕ → X} (hC : IsCompact C) (huC : ∀ n, u n ∈ C)
    (hstep : Tendsto (fun n ↦ dist (u n) (u (n + 1))) atTop (𝓝 0)) :
    IsConnected {x | MapClusterPt x atTop u} := by
  classical
  let S : Set X := {x | MapClusterPt x atTop u}
  -- Compactness of `C` supplies at least one cluster point.
  have hSnonempty : S.Nonempty := by
    obtain ⟨x, -, hxcluster⟩ :=
      hC.isCountablyCompact.seq_clusterPt u (Filter.Eventually.of_forall huC)
    exact ⟨x, hxcluster⟩
  -- The cluster-point set is closed, hence compact inside `C`.
  have hSclosed : IsClosed S := by
    simpa [S, MapClusterPt] using
      (isClosed_setOf_clusterPt : IsClosed {x | ClusterPt x (map u atTop)})
  have hSsubsetC : S ⊆ C := by
    intro x hx
    exact IsClosed.mem_of_mapClusterPt hC.isClosed hx (Filter.Eventually.of_forall huC)
  have hScompact : IsCompact S := hC.of_isClosed_subset hSclosed hSsubsetC
  change IsConnected S
  refine ⟨hSnonempty, ?_⟩
  by_contra hSnotpre
  -- A failure of preconnectedness yields a separation by closed sets.
  have hsep : ∃ U V, IsClosed U ∧ IsClosed V ∧ S ⊆ U ∪ V ∧ Disjoint U V ∧ ¬ S ⊆ U ∧ ¬ S ⊆ V := by
    rw [isPreconnected_iff_subset_of_fully_disjoint_closed hSclosed] at hSnotpre
    push Not at hSnotpre
    exact hSnotpre
  obtain ⟨U, V, hUclosed, hVclosed, hSUV, hUV, hSnotU, hSnotV⟩ := hsep
  let A : Set X := S ∩ U
  let B : Set X := S ∩ V
  have hUV' : ∀ ⦃x⦄, x ∈ U → x ∈ V → False := by
    rw [Set.disjoint_left] at hUV
    exact hUV
  have hAclosed : IsClosed A := hSclosed.inter hUclosed
  have hBclosed : IsClosed B := hSclosed.inter hVclosed
  have hAne : A.Nonempty := by
    obtain ⟨a, haS, haVnot⟩ := Set.not_subset.1 hSnotV
    have haU : a ∈ U := by
      rcases hSUV haS with haU | haV
      · exact haU
      · exact (haVnot haV).elim
    exact ⟨a, ⟨haS, haU⟩⟩
  have hBne : B.Nonempty := by
    obtain ⟨b, hbS, hbUnot⟩ := Set.not_subset.1 hSnotU
    have hbV : b ∈ V := by
      rcases hSUV hbS with hbU | hbV
      · exact (hbUnot hbU).elim
      · exact hbV
    exact ⟨b, ⟨hbS, hbV⟩⟩
  have hAdisjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact hUV' hxA.2 hxB.2
  have hAcompact : IsCompact A := hScompact.of_isClosed_subset hAclosed (by
    intro x hx
    exact hx.1)
  have hAne_keep : A.Nonempty := hAne
  have hBne_keep : B.Nonempty := hBne
  obtain ⟨a₀, ha₀A⟩ := hAne
  obtain ⟨b₀, hb₀B⟩ := hBne
  have ha₀cluster : MapClusterPt a₀ atTop u := ha₀A.1
  have hb₀cluster : MapClusterPt b₀ atTop u := hb₀B.1
  -- The two closed pieces are separated by a uniform positive gap in `infDist`.
  obtain ⟨δ, hδpos, hδlower⟩ :=
    exists_positive_infDist_lower_bound_of_disjoint hAcompact hBclosed hBne_keep hAdisjoint
  have hδthird : 0 < δ / 3 := by linarith
  have hδtwo : δ / 3 < 2 * δ / 3 := by linarith
  -- For every late threshold `N`, one can find a first crossing index into the `2δ / 3`-neighborhood
  -- of `B`, while still staying outside the `δ / 3`-neighborhood of `B`.
  have hcross :
      ∀ N, ∃ n ≥ N, δ / 3 < Metric.infDist (u n) B ∧ Metric.infDist (u n) B < 2 * δ / 3 := by
    intro N
    obtain ⟨M, hMraw⟩ := Metric.tendsto_atTop.1 hstep (δ / 3) hδthird
    have hM : ∀ n ≥ M, dist (u n) (u (n + 1)) < δ / 3 := by
      intro n hn
      have hsmall := hMraw n hn
      simpa [Real.dist_eq, abs_of_nonneg (dist_nonneg : 0 ≤ dist (u n) (u (n + 1)))] using hsmall
    obtain ⟨k, hk_ge, hkAnear⟩ :=
      exists_ge_infDist_lt_of_mem_mapClusterPt ha₀A ha₀cluster hδthird (max N M)
    have hkN : k ≥ N := le_trans (le_max_left N M) hk_ge
    have hkM : k ≥ M := le_trans (le_max_right N M) hk_ge
    have hkBfar : 2 * δ / 3 < Metric.infDist (u k) B :=
      two_thirds_gap_of_one_third_near_left hAne_keep hδlower hkAnear
    obtain ⟨j, hj_ge, hjBnear⟩ :=
      exists_ge_infDist_lt_of_mem_mapClusterPt hb₀B hb₀cluster hδthird (max (k + 1) M)
    have hjk : k < j := by
      exact lt_of_lt_of_le (Nat.lt_succ_self k) (le_trans (le_max_left (k + 1) M) hj_ge)
    let Q : ℕ → Prop := fun n ↦ k < n ∧ n ≤ j ∧ Metric.infDist (u n) B < 2 * δ / 3
    have hQj : Q j := by
      refine ⟨hjk, le_rfl, lt_trans hjBnear hδtwo⟩
    let l : ℕ := Nat.find ⟨j, hQj⟩
    have hlQ : Q l := Nat.find_spec ⟨j, hQj⟩
    have hkl : k < l := hlQ.1
    have hlj : l ≤ j := hlQ.2.1
    have hlupper : Metric.infDist (u l) B < 2 * δ / 3 := hlQ.2.2
    have hlpos : 0 < l := lt_of_le_of_lt (Nat.zero_le k) hkl
    have hpred_ge_M : l - 1 ≥ M := by
      omega
    have hstep_small : dist (u (l - 1)) (u l) < δ / 3 := by
      have hstep_small' := hM (l - 1) hpred_ge_M
      have hlpred : l - 1 + 1 = l := Nat.sub_add_cancel (Nat.succ_le_of_lt hlpos)
      simpa [hlpred] using hstep_small'
    have hpred_far : 2 * δ / 3 ≤ Metric.infDist (u (l - 1)) B := by
      by_cases hl_eq : l = k + 1
      · have hl_sub : l - 1 = k := by
          omega
        simpa [hl_sub] using hkBfar.le
      · have hk_pred : k < l - 1 := by
          omega
        have hpred_lt : l - 1 < l := Nat.pred_lt hlpos.ne'
        have hnotQpred : ¬ Q (l - 1) := Nat.find_min ⟨j, hQj⟩ hpred_lt
        have hpred_le_j : l - 1 ≤ j := by
          omega
        have hpred_not_lt : ¬ Metric.infDist (u (l - 1)) B < 2 * δ / 3 := by
          intro hlt
          exact hnotQpred ⟨hk_pred, hpred_le_j, hlt⟩
        exact le_of_not_gt hpred_not_lt
    have hllower : δ / 3 < Metric.infDist (u l) B := by
      have hcompare : 2 * δ / 3 ≤ Metric.infDist (u l) B + dist (u (l - 1)) (u l) := by
        calc
          2 * δ / 3 ≤ Metric.infDist (u (l - 1)) B := hpred_far
          _ ≤ Metric.infDist (u l) B + dist (u (l - 1)) (u l) :=
            by
              simpa using
                (show
                  Metric.infDist (u (l - 1)) B ≤
                    Metric.infDist (u l) B + dist (u (l - 1)) (u l) from
                  Metric.infDist_le_infDist_add_dist)
      linarith
    exact ⟨l, le_trans hkN hkl.le, hllower, hlupper⟩
  -- These intermediate-distance indices produce a cluster point inside the closed middle band.
  have hfreq :
      ∃ᶠ n in atTop,
        δ / 3 < Metric.infDist (u n) B ∧ Metric.infDist (u n) B < 2 * δ / 3 := by
    rw [Filter.frequently_atTop]
    exact hcross
  let D : Set X := {x | x ∈ C ∧ δ / 3 ≤ Metric.infDist x B ∧ Metric.infDist x B ≤ 2 * δ / 3}
  have hDclosed : IsClosed D := by
    refine hC.isClosed.inter ?_
    exact (isClosed_le continuous_const (Metric.continuous_infDist_pt B)).inter
      (isClosed_le (Metric.continuous_infDist_pt B) continuous_const)
  have hDcompact : IsCompact D := hC.of_isClosed_subset hDclosed (by
    intro x hx
    exact hx.1)
  have hfreqD : ∃ᶠ n in atTop, u n ∈ D := by
    refine hfreq.mono ?_
    intro n hn
    exact ⟨huC n, le_of_lt hn.1, le_of_lt hn.2⟩
  obtain ⟨z, hzD, hzcluster⟩ := hDcompact.exists_mapClusterPt_of_frequently hfreqD
  have hzS : z ∈ S := hzcluster
  have hznotV : z ∉ V := by
    intro hzV
    have hznotB : z ∉ B := by
      have hposB : 0 < Metric.infDist z B := by
        linarith [hzD.2.1]
      exact ((hBclosed.notMem_iff_infDist_pos hBne_keep).2 hposB)
    exact hznotB ⟨hzS, hzV⟩
  have hzA : z ∈ A := by
    have hzU : z ∈ U := by
      rcases hSUV hzS with hzU | hzV
      · exact hzU
      · exact (hznotV hzV).elim
    exact ⟨hzS, hzU⟩
  have hz_gap : δ ≤ Metric.infDist z B := hδlower z hzA
  have hz_upper : Metric.infDist z B ≤ 2 * δ / 3 := hzD.2.2
  linarith

/-- Theorem 1.49 in textbook form: under the same hypotheses, the cluster points of `u` lying in
`C` form a connected set. This is a one-step restatement of
`isConnected_clusterPoints_of_tendsto_dist_succ_eq_zero`. -/
theorem isConnected_clusterPointsIn_compact_of_tendsto_dist_succ_eq_zero
    {C : Set X} {u : ℕ → X} (hC : IsCompact C) (huC : ∀ n, u n ∈ C)
    (hstep : Tendsto (fun n ↦ dist (u n) (u (n + 1))) atTop (𝓝 0)) :
    IsConnected {x | x ∈ C ∧ MapClusterPt x atTop u} := by
  have hcluster :
      {x | x ∈ C ∧ MapClusterPt x atTop u} = {x | MapClusterPt x atTop u} := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨IsClosed.mem_of_mapClusterPt hC.isClosed hx (Filter.Eventually.of_forall huC), hx⟩
  simpa [hcluster] using isConnected_clusterPoints_of_tendsto_dist_succ_eq_zero hC huC hstep
