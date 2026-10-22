/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part2

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise

/-- Helper for Theorem 35.3: full continuity in `t` on `C × D` implies joint continuity on
`C × D × T`. -/
lemma helperForTheorem_35_3_fullContinuityImplication
    {m n : ℕ} {T : Type*} [TopologicalSpace T] [LocallyCompactSpace T]
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {K : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → T → ℝ}
    (hC : IsRelativelyOpenConvex C) (hD : IsRelativelyOpenConvex D)
    (hK : ∀ t, IsRealConcaveConvexOn C D (fun u v => K u v t))
    (hCont : ∀ u ∈ C, ∀ v ∈ D, Continuous fun t => K u v t) :
    ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) × T =>
        K p.1 p.2.1 p.2.2)
      (C ×ˢ (D ×ˢ (Set.univ : Set T))) := by
  classical
  -- Work on the associated product `((u, v), t)` so the spatial variable is a single metric term.
  have hAssoc :
      ContinuousOn
        (fun p : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) × T =>
          K p.1.1 p.1.2 p.2)
        ((C ×ˢ D) ×ˢ (Set.univ : Set T)) := by
    intro p hp
    rcases p with ⟨q0, t0⟩
    rcases q0 with ⟨u0, v0⟩
    have hu0 : u0 ∈ C := hp.1.1
    have hv0 : v0 ∈ D := hp.1.2
    -- Fix a compact neighborhood in the parameter space and a closed bounded neighborhood in space.
    rw [ContinuousWithinAt, Metric.tendsto_nhds]
    intro ε hε
    rcases exists_compact_mem_nhds t0 with ⟨K0, hK0comp, hK0nhds⟩
    have ht0K0 : t0 ∈ K0 := mem_of_mem_nhds hK0nhds
    rcases
        helperForTheorem_35_1_existsClosedBoundedNeighborhood_subset_relativelyOpenConvex
          (hs := hC) hu0 with
      ⟨TC, hu0TC, hTCsub, hTCclosed, hTCbdd, hTCnhds⟩
    rcases
        helperForTheorem_35_1_existsClosedBoundedNeighborhood_subset_relativelyOpenConvex
          (hs := hD) hv0 with
      ⟨TD, hv0TD, hTDsub, hTDclosed, hTDbdd, hTDnhds⟩
    let S : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) := TC ×ˢ TD
    have hSsub : S ⊆ C ×ˢ D := by
      intro q hq
      exact ⟨hTCsub hq.1, hTDsub hq.2⟩
    have hSclosed : IsClosed S := hTCclosed.prod hTDclosed
    have hSbdd : Bornology.IsBounded S := hTCbdd.prod hTDbdd
    have hHull :
        C ×ˢ D ⊆ convexHull ℝ (closure (C ×ˢ D)) := by
      intro q hq
      exact subset_convexHull ℝ (closure (C ×ˢ D)) (subset_closure hq)
    have hFamily :=
      helperForTheorem_35_3_compactIndexed_family_uniformlyBoundedAndEquiLipschitz
        (hC := hC) (hD := hD) (hK := hK)
        (K0 := K0) hK0comp
        (hCwsub := subset_rfl) (hDwsub := subset_rfl)
        hHull hCont hSsub hSclosed hSbdd
    rcases hFamily.2 with ⟨L, hL⟩
    have hL1pos : 0 < ((L : ℝ) + 1) := by
      have hLnonneg : 0 ≤ (L : ℝ) := by exact_mod_cast L.2
      linarith
    have hL1ne : ((L : ℝ) + 1) ≠ 0 := ne_of_gt hL1pos
    -- Extract an ambient product ball around `(u0, v0)` that stays in the closed bounded set `S`.
    have hSnhds : S ∈ nhdsWithin (u0, v0) (C ×ˢ D) := by
      simpa [S, nhdsWithin_prod_eq] using Filter.prod_mem_prod hTCnhds hTDnhds
    rcases Metric.mem_nhdsWithin_iff.mp hSnhds with ⟨r0, hr0pos, hr0sub⟩
    -- Continuity at the base point handles the parameter variable.
    have hcont_t :
        Filter.Tendsto (fun t : T => K u0 v0 t) (nhds t0) (nhds (K u0 v0 t0)) :=
      (hCont u0 hu0 v0 hv0).tendsto t0
    have hV' : ∀ᶠ t in nhds t0, dist (K u0 v0 t) (K u0 v0 t0) < ε / 2 :=
      (Metric.tendsto_nhds.1 hcont_t) (ε / 2) (by linarith)
    let V : Set T := {t : T | dist (K u0 v0 t) (K u0 v0 t0) < ε / 2} ∩ K0
    have hV : V ∈ nhds t0 := Filter.inter_mem hV' hK0nhds
    -- Use the common Lipschitz constant on a smaller product ball.
    let δq : ℝ := (ε / 2) / ((L : ℝ) + 1)
    have hδqpos : 0 < δq := div_pos (by linarith) hL1pos
    let U : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :=
      Metric.ball (u0, v0) (min r0 δq) ∩ (C ×ˢ D)
    have hU : U ∈ nhdsWithin (u0, v0) (C ×ˢ D) := by
      rw [Metric.mem_nhdsWithin_iff]
      refine ⟨min r0 δq, lt_min hr0pos hδqpos, ?_⟩
      intro q hq
      exact hq
    -- Assemble neighborhoods in the product filter.
    have hEq :
        nhdsWithin ((u0, v0), t0) ((C ×ˢ D) ×ˢ (Set.univ : Set T)) =
          (nhdsWithin (u0, v0) (C ×ˢ D)) ×ˢ nhds t0 := by
      simpa [nhdsWithin_univ] using
        (nhdsWithin_prod_eq (u0, v0) t0 (C ×ˢ D) (Set.univ : Set T))
    have hUV' : U ×ˢ V ∈ (nhdsWithin (u0, v0) (C ×ˢ D)) ×ˢ nhds t0 :=
      Filter.prod_mem_prod hU hV
    have hUV : U ×ˢ V ∈ nhdsWithin ((u0, v0), t0) ((C ×ˢ D) ×ˢ (Set.univ : Set T)) := by
      simpa [hEq] using hUV'
    refine Filter.mem_of_superset hUV ?_
    rintro ⟨q, t⟩ hqt
    rcases hqt with ⟨hqU, htV⟩
    have hqBall : q ∈ Metric.ball (u0, v0) (min r0 δq) := hqU.1
    have hqCD : q ∈ C ×ˢ D := hqU.2
    have hqBall0 : q ∈ Metric.ball (u0, v0) r0 := by
      have hqdist' : dist q (u0, v0) < min r0 δq := by
        simpa [U, Metric.mem_ball] using hqBall
      have : dist q (u0, v0) < r0 := lt_of_lt_of_le hqdist' (min_le_left _ _)
      simpa [Metric.mem_ball] using this
    have hqS : q ∈ S := hr0sub ⟨hqBall0, hqCD⟩
    have hq0S : (u0, v0) ∈ S := ⟨hu0TC, hv0TD⟩
    have htK0 : t ∈ K0 := htV.2
    have htcont : dist (K u0 v0 t) (K u0 v0 t0) < ε / 2 := htV.1
    have hqdist : dist q (u0, v0) < δq := by
      have hqdist' : dist q (u0, v0) < min r0 δq := by
        simpa [U, Metric.mem_ball] using hqBall
      exact lt_of_lt_of_le hqdist' (min_le_right _ _)
    let τ : {t : T // t ∈ K0} := ⟨t, htK0⟩
    have hdist_le :
        dist (K q.1 q.2 t) (K u0 v0 t) ≤ (L : ℝ) * dist q (u0, v0) := by
      simpa [S, Function.uncurry] using (hL τ).dist_le_mul q hqS (u0, v0) hq0S
    have hmul_lt : ((L : ℝ) + 1) * dist q (u0, v0) < ε / 2 := by
      have :
          ((L : ℝ) + 1) * dist q (u0, v0) < ((L : ℝ) + 1) * δq :=
        mul_lt_mul_of_pos_left hqdist hL1pos
      have hmul : ((L : ℝ) + 1) * δq = ε / 2 := by
        simpa [δq] using (mul_div_cancel₀ (a := ε / 2) (b := (L : ℝ) + 1) hL1ne)
      simpa [hmul] using this
    have hle_mul :
        (L : ℝ) * dist q (u0, v0) ≤ ((L : ℝ) + 1) * dist q (u0, v0) := by
      have hLle : (L : ℝ) ≤ (L : ℝ) + 1 := by linarith
      exact mul_le_mul_of_nonneg_right hLle dist_nonneg
    have hqcont : dist (K q.1 q.2 t) (K u0 v0 t) < ε / 2 :=
      lt_of_le_of_lt (le_trans hdist_le hle_mul) hmul_lt
    -- Finish with the standard two-term triangle estimate.
    have htri :
        dist (K q.1 q.2 t) (K u0 v0 t0) ≤
          dist (K q.1 q.2 t) (K u0 v0 t) + dist (K u0 v0 t) (K u0 v0 t0) :=
      dist_triangle (K q.1 q.2 t) (K u0 v0 t) (K u0 v0 t0)
    have :
        dist (K q.1 q.2 t) (K u0 v0 t0) < ε / 2 + ε / 2 :=
      lt_of_le_of_lt htri (add_lt_add hqcont htcont)
    simpa [add_halves] using this
  -- Transfer the continuity statement back to the textbook product association.
  exact helperForTheorem_35_3_rightAssociatedContinuousOn hAssoc

/-- Helper for Theorem 35.3: continuity in `t` on a dense witness product still implies joint
continuity on `C × D × T`. -/
lemma helperForTheorem_35_3_denseContinuityImplication
    {m n : ℕ} {T : Type*} [TopologicalSpace T] [LocallyCompactSpace T]
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {C' : Set (EuclideanSpace ℝ (Fin m))} {D' : Set (EuclideanSpace ℝ (Fin n))}
    {K : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → T → ℝ}
    (hC : IsRelativelyOpenConvex C) (hD : IsRelativelyOpenConvex D)
    (hK : ∀ t, IsRealConcaveConvexOn C D (fun u v => K u v t))
    (hC'sub : C' ⊆ C) (hD'sub : D' ⊆ D)
    (hCclosure : C ⊆ closure C') (hDclosure : D ⊆ closure D')
    (hCont : ∀ u ∈ C', ∀ v ∈ D', Continuous fun t => K u v t) :
    ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) × T =>
        K p.1 p.2.1 p.2.2)
      (C ×ˢ (D ×ˢ (Set.univ : Set T))) := by
  classical
  -- Work on the associated product `((u, v), t)` to mirror the dense variant of Theorem 10.7.
  have hAssoc :
      ContinuousOn
        (fun p : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) × T =>
          K p.1.1 p.1.2 p.2)
        ((C ×ˢ D) ×ˢ (Set.univ : Set T)) := by
    intro p hp
    rcases p with ⟨q0, t0⟩
    rcases q0 with ⟨u0, v0⟩
    have hu0 : u0 ∈ C := hp.1.1
    have hv0 : v0 ∈ D := hp.1.2
    -- Localize both the spatial and parameter variables.
    rw [ContinuousWithinAt, Metric.tendsto_nhds]
    intro ε hε
    rcases exists_compact_mem_nhds t0 with ⟨K0, hK0comp, hK0nhds⟩
    have ht0K0 : t0 ∈ K0 := mem_of_mem_nhds hK0nhds
    rcases
        helperForTheorem_35_1_existsClosedBoundedNeighborhood_subset_relativelyOpenConvex
          (hs := hC) hu0 with
      ⟨TC, hu0TC, hTCsub, hTCclosed, hTCbdd, hTCnhds⟩
    rcases
        helperForTheorem_35_1_existsClosedBoundedNeighborhood_subset_relativelyOpenConvex
          (hs := hD) hv0 with
      ⟨TD, hv0TD, hTDsub, hTDclosed, hTDbdd, hTDnhds⟩
    let S : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) := TC ×ˢ TD
    have hSsub : S ⊆ C ×ˢ D := by
      intro q hq
      exact ⟨hTCsub hq.1, hTDsub hq.2⟩
    have hSclosed : IsClosed S := hTCclosed.prod hTDclosed
    have hSbdd : Bornology.IsBounded S := hTCbdd.prod hTDbdd
    have hHull :=
      helperForTheorem_35_3_productHull_of_factorClosures
        (C := C) (D := D) (C' := C') (D' := D') hCclosure hDclosure
    have hFamily :=
      helperForTheorem_35_3_compactIndexed_family_uniformlyBoundedAndEquiLipschitz
        (hC := hC) (hD := hD) (hK := hK)
        (K0 := K0) hK0comp
        hC'sub hD'sub hHull hCont hSsub hSclosed hSbdd
    rcases hFamily.2 with ⟨L, hL⟩
    have hL1pos : 0 < ((L : ℝ) + 1) := by
      have hLnonneg : 0 ≤ (L : ℝ) := by exact_mod_cast L.2
      linarith
    have hL1ne : ((L : ℝ) + 1) ≠ 0 := ne_of_gt hL1pos
    have hSnhds : S ∈ nhdsWithin (u0, v0) (C ×ˢ D) := by
      simpa [S, nhdsWithin_prod_eq] using Filter.prod_mem_prod hTCnhds hTDnhds
    rcases Metric.mem_nhdsWithin_iff.mp hSnhds with ⟨r0, hr0pos, hr0sub⟩
    rcases Metric.mem_nhdsWithin_iff.mp hTCnhds with ⟨rC, hrCpos, hrCsub⟩
    rcases Metric.mem_nhdsWithin_iff.mp hTDnhds with ⟨rD, hrDpos, hrDsub⟩
    -- Pick a nearby dense witness pair inside the closed bounded neighborhood.
    have hu0Cl : u0 ∈ closure C' := hCclosure hu0
    have hv0Cl : v0 ∈ closure D' := hDclosure hv0
    have hε8 : 0 < ε / 8 := by linarith
    let δ1 : ℝ := min rC (min rD ((ε / 8) / ((L : ℝ) + 1)))
    have hδ1pos : 0 < δ1 := by
      refine lt_min hrCpos ?_
      exact lt_min hrDpos (div_pos hε8 hL1pos)
    rcases (Metric.mem_closure_iff.1 hu0Cl) δ1 hδ1pos with ⟨u1, hu1C', hu1dist⟩
    rcases (Metric.mem_closure_iff.1 hv0Cl) δ1 hδ1pos with ⟨v1, hv1D', hv1dist⟩
    have hu1C : u1 ∈ C := hC'sub hu1C'
    have hv1D : v1 ∈ D := hD'sub hv1D'
    have hu1dist' : dist u1 u0 < δ1 := by simpa [dist_comm] using hu1dist
    have hv1dist' : dist v1 v0 < δ1 := by simpa [dist_comm] using hv1dist
    have hu1TC : u1 ∈ TC := by
      apply hrCsub
      refine ⟨?_, hu1C⟩
      have : dist u1 u0 < rC := lt_of_lt_of_le hu1dist' (min_le_left _ _)
      simpa [Metric.mem_ball, dist_comm] using this
    have hv1TD : v1 ∈ TD := by
      apply hrDsub
      refine ⟨?_, hv1D⟩
      have : dist v1 v0 < rD := lt_of_lt_of_le hv1dist' (le_trans (min_le_right _ _) (min_le_left _ _))
      simpa [Metric.mem_ball, dist_comm] using this
    have hq1S : (u1, v1) ∈ S := ⟨hu1TC, hv1TD⟩
    have hq0S : (u0, v0) ∈ S := ⟨hu0TC, hv0TD⟩
    have hq01 : dist (u0, v0) (u1, v1) < δ1 := by
      rw [Prod.dist_eq]
      exact max_lt_iff.mpr ⟨by simpa [dist_comm] using hu1dist', by simpa [dist_comm] using hv1dist'⟩
    have hWitnessCont :
        Filter.Tendsto (fun t : T => K u1 v1 t) (nhds t0) (nhds (K u1 v1 t0)) :=
      (hCont u1 hu1C' v1 hv1D').tendsto t0
    have hV' : ∀ᶠ t in nhds t0, dist (K u1 v1 t) (K u1 v1 t0) < ε / 4 :=
      (Metric.tendsto_nhds.1 hWitnessCont) (ε / 4) (by linarith)
    let V : Set T := {t : T | dist (K u1 v1 t) (K u1 v1 t0) < ε / 4} ∩ K0
    have hV : V ∈ nhds t0 := Filter.inter_mem hV' hK0nhds
    let δq : ℝ := (ε / 2) / ((L : ℝ) + 1)
    have hδqpos : 0 < δq := div_pos (by linarith) hL1pos
    let U : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :=
      Metric.ball (u0, v0) (min r0 δq) ∩ (C ×ˢ D)
    have hU : U ∈ nhdsWithin (u0, v0) (C ×ˢ D) := by
      rw [Metric.mem_nhdsWithin_iff]
      refine ⟨min r0 δq, lt_min hr0pos hδqpos, ?_⟩
      intro q hq
      exact hq
    have hEq :
        nhdsWithin ((u0, v0), t0) ((C ×ˢ D) ×ˢ (Set.univ : Set T)) =
          (nhdsWithin (u0, v0) (C ×ˢ D)) ×ˢ nhds t0 := by
      simpa [nhdsWithin_univ] using
        (nhdsWithin_prod_eq (u0, v0) t0 (C ×ˢ D) (Set.univ : Set T))
    have hUV' : U ×ˢ V ∈ (nhdsWithin (u0, v0) (C ×ˢ D)) ×ˢ nhds t0 :=
      Filter.prod_mem_prod hU hV
    have hUV : U ×ˢ V ∈ nhdsWithin ((u0, v0), t0) ((C ×ˢ D) ×ˢ (Set.univ : Set T)) := by
      simpa [hEq] using hUV'
    refine Filter.mem_of_superset hUV ?_
    rintro ⟨q, t⟩ hqt
    rcases hqt with ⟨hqU, htV⟩
    have hqBall : q ∈ Metric.ball (u0, v0) (min r0 δq) := hqU.1
    have hqCD : q ∈ C ×ˢ D := hqU.2
    have hqBall0 : q ∈ Metric.ball (u0, v0) r0 := by
      have hqdist' : dist q (u0, v0) < min r0 δq := by
        simpa [U, Metric.mem_ball] using hqBall
      have : dist q (u0, v0) < r0 := lt_of_lt_of_le hqdist' (min_le_left _ _)
      simpa [Metric.mem_ball] using this
    have hqS : q ∈ S := hr0sub ⟨hqBall0, hqCD⟩
    have htK0 : t ∈ K0 := htV.2
    have htcont1 : dist (K u1 v1 t) (K u1 v1 t0) < ε / 4 := htV.1
    have hqdist : dist q (u0, v0) < δq := by
      have hqdist' : dist q (u0, v0) < min r0 δq := by
        simpa [U, Metric.mem_ball] using hqBall
      exact lt_of_lt_of_le hqdist' (min_le_right _ _)
    let τ : {t : T // t ∈ K0} := ⟨t, htK0⟩
    have hdist_le :
        dist (K q.1 q.2 t) (K u0 v0 t) ≤ (L : ℝ) * dist q (u0, v0) := by
      simpa [S, Function.uncurry] using (hL τ).dist_le_mul q hqS (u0, v0) hq0S
    have hmul_lt : ((L : ℝ) + 1) * dist q (u0, v0) < ε / 2 := by
      have :
          ((L : ℝ) + 1) * dist q (u0, v0) < ((L : ℝ) + 1) * δq :=
        mul_lt_mul_of_pos_left hqdist hL1pos
      have hmul : ((L : ℝ) + 1) * δq = ε / 2 := by
        simpa [δq] using (mul_div_cancel₀ (a := ε / 2) (b := (L : ℝ) + 1) hL1ne)
      simpa [hmul] using this
    have hle_mul :
        (L : ℝ) * dist q (u0, v0) ≤ ((L : ℝ) + 1) * dist q (u0, v0) := by
      have hLle : (L : ℝ) ≤ (L : ℝ) + 1 := by linarith
      exact mul_le_mul_of_nonneg_right hLle dist_nonneg
    have hqcont : dist (K q.1 q.2 t) (K u0 v0 t) < ε / 2 :=
      lt_of_le_of_lt (le_trans hdist_le hle_mul) hmul_lt
    have hδ1small : δ1 ≤ (ε / 8) / ((L : ℝ) + 1) := by
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hmul_q01 :
        ((L : ℝ) + 1) * dist (u0, v0) (u1, v1) < ε / 8 := by
      have hq01' : dist (u0, v0) (u1, v1) < (ε / 8) / ((L : ℝ) + 1) :=
        lt_of_lt_of_le hq01 hδ1small
      have :
          ((L : ℝ) + 1) * dist (u0, v0) (u1, v1) <
            ((L : ℝ) + 1) * ((ε / 8) / ((L : ℝ) + 1)) :=
        mul_lt_mul_of_pos_left hq01' hL1pos
      have hmul :
          ((L : ℝ) + 1) * ((ε / 8) / ((L : ℝ) + 1)) = ε / 8 := by
        simp [mul_div_cancel₀, hL1ne]
      simpa [hmul] using this
    have hLq01 : (L : ℝ) * dist (u0, v0) (u1, v1) < ε / 8 := by
      have hle :
          (L : ℝ) * dist (u0, v0) (u1, v1) ≤
            ((L : ℝ) + 1) * dist (u0, v0) (u1, v1) := by
        have hLle : (L : ℝ) ≤ (L : ℝ) + 1 := by linarith
        exact mul_le_mul_of_nonneg_right hLle dist_nonneg
      exact lt_of_le_of_lt hle hmul_q01
    have htcont0 : dist (K u0 v0 t) (K u0 v0 t0) < ε / 2 := by
      let τ0 : {t : T // t ∈ K0} := ⟨t0, ht0K0⟩
      have hdist_xt :
          dist (K u0 v0 t) (K u1 v1 t) ≤ (L : ℝ) * dist (u0, v0) (u1, v1) := by
        simpa [S, Function.uncurry] using (hL τ).dist_le_mul (u0, v0) hq0S (u1, v1) hq1S
      have hdist_x0t0 :
          dist (K u1 v1 t0) (K u0 v0 t0) ≤ (L : ℝ) * dist (u0, v0) (u1, v1) := by
        have :
            dist (K u0 v0 t0) (K u1 v1 t0) ≤ (L : ℝ) * dist (u0, v0) (u1, v1) := by
          simpa [S, Function.uncurry] using (hL τ0).dist_le_mul (u0, v0) hq0S (u1, v1) hq1S
        simpa [dist_comm] using this
      have htri1 :
          dist (K u0 v0 t) (K u0 v0 t0) ≤
            dist (K u0 v0 t) (K u1 v1 t) +
              dist (K u1 v1 t) (K u1 v1 t0) +
                dist (K u1 v1 t0) (K u0 v0 t0) := by
        calc
          dist (K u0 v0 t) (K u0 v0 t0) ≤
              dist (K u0 v0 t) (K u1 v1 t) + dist (K u1 v1 t) (K u0 v0 t0) :=
            dist_triangle (K u0 v0 t) (K u1 v1 t) (K u0 v0 t0)
          _ ≤ dist (K u0 v0 t) (K u1 v1 t) +
                (dist (K u1 v1 t) (K u1 v1 t0) + dist (K u1 v1 t0) (K u0 v0 t0)) := by
            gcongr
            exact dist_triangle (K u1 v1 t) (K u1 v1 t0) (K u0 v0 t0)
          _ = _ := by simp [add_assoc]
      have hle' :
          dist (K u0 v0 t) (K u0 v0 t0) ≤
            (L : ℝ) * dist (u0, v0) (u1, v1) + ε / 4 +
              (L : ℝ) * dist (u0, v0) (u1, v1) := by
        refine le_trans htri1 ?_
        have hmid : dist (K u1 v1 t) (K u1 v1 t0) ≤ ε / 4 := le_of_lt htcont1
        have hleft :
            dist (K u0 v0 t) (K u1 v1 t) + dist (K u1 v1 t) (K u1 v1 t0) ≤
              (L : ℝ) * dist (u0, v0) (u1, v1) + ε / 4 :=
          add_le_add hdist_xt hmid
        have htotal :
            (dist (K u0 v0 t) (K u1 v1 t) + dist (K u1 v1 t) (K u1 v1 t0)) +
                dist (K u1 v1 t0) (K u0 v0 t0) ≤
              ((L : ℝ) * dist (u0, v0) (u1, v1) + ε / 4) +
                (L : ℝ) * dist (u0, v0) (u1, v1) :=
          add_le_add hleft hdist_x0t0
        simpa [add_assoc] using htotal
      have hfinal :
          (L : ℝ) * dist (u0, v0) (u1, v1) + ε / 4 +
            (L : ℝ) * dist (u0, v0) (u1, v1) < ε / 2 := by
        linarith [hLq01]
      exact lt_of_le_of_lt hle' hfinal
    -- The witness-point estimate and the local Lipschitz estimate finish the dense argument.
    have htri :
        dist (K q.1 q.2 t) (K u0 v0 t0) ≤
          dist (K q.1 q.2 t) (K u0 v0 t) + dist (K u0 v0 t) (K u0 v0 t0) :=
      dist_triangle (K q.1 q.2 t) (K u0 v0 t) (K u0 v0 t0)
    have :
        dist (K q.1 q.2 t) (K u0 v0 t0) < ε / 2 + ε / 2 :=
      lt_of_le_of_lt htri (add_lt_add hqcont htcont0)
    simpa [add_halves] using this
  -- Transfer the continuity statement back to the textbook product association.
  exact helperForTheorem_35_3_rightAssociatedContinuousOn hAssoc

end Section35
end Chap07
