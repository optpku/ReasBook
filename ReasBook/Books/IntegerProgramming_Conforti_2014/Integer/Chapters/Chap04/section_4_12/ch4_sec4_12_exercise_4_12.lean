/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3.ch4_sec4_3_definition_4_3_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_1.ch4_sec4_3_1_definition_4_3_1_extra_1
import Mathlib

-- This file reuses the chapter owners `digraph_incidence_matrix` and
-- `arc_induced_digraph`, together with mathlib's `Digraph.toSimpleGraphInclusive`,
-- `SimpleGraph.Walk.IsCycle`, and `Matrix.rank` APIs directly.

namespace Digraph

variable {V : Type} (D : Digraph V)

/-- The arcs of a digraph, represented as ordered adjacent vertex pairs. -/
abbrev Arc :=
  { e : V × V // D.Adj e.1 e.2 }

/-- The tail of an arc of `D`. -/
abbrev Arc.tail (e : D.Arc) : V :=
  e.1.1

/-- The head of an arc of `D`. -/
abbrev Arc.head (e : D.Arc) : V :=
  e.1.2

/-- The oriented incidence matrix of a digraph over `ℚ`, with one column for each arc. Its
entries are `1` at the head, `-1` at the tail, and `0` elsewhere. -/
noncomputable abbrev incidenceMatrix : Matrix V D.Arc ℚ :=
  let tail : D.Arc → V := fun e ↦ e.tail
  let head : D.Arc → V := fun e ↦ e.head
  let M : Matrix V D.Arc ℚ := digraph_incidence_matrix ℚ tail head
  M

/-- The undirected support graph of a finite set of arcs, obtained by forgetting orientations. -/
abbrev supportGraph (F : Finset D.Arc) : SimpleGraph V :=
  (arc_induced_digraph (fun e : D.Arc ↦ e.tail) (fun e ↦ e.head) F).toSimpleGraphInclusive

/-- A finite set of arcs contains a cycle when its orientation-forgetting support graph contains a
simple cycle. -/
def HasUndirectedCycle (F : Finset D.Arc) : Prop :=
  ∃ u : V, ∃ p : (D.supportGraph F).Walk u u, p.IsCycle

/-- Helper for Exercise 4.12: a finite arc family has an undirected cycle exactly when its
support graph is not acyclic. -/
lemma hasUndirectedCycle_iff_not_isAcyclic (F : Finset D.Arc) :
    D.HasUndirectedCycle F ↔ ¬ (D.supportGraph F).IsAcyclic := by
  -- This just unfolds the local definitions of "undirected cycle" and "acyclic".
  simp [HasUndirectedCycle, SimpleGraph.IsAcyclic]

/-- Helper for Exercise 4.12: every undirected support edge comes from a unique arc of `F`.
The asymmetry hypothesis rules out having both orientations of the same undirected edge. -/
lemma supportGraph_adj_iff_exists_unique_arc
    (hasymm : Std.Asymm D.Adj) {F : Finset D.Arc} {u v : V} :
    (D.supportGraph F).Adj u v ↔
      u ≠ v ∧ ∃! e : D.Arc,
        e ∈ F ∧ ((e.tail = u ∧ e.head = v) ∨ (e.tail = v ∧ e.head = u)) := by
  constructor
  · intro huv
    simp [supportGraph, Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj] at huv
    rcases huv with ⟨huv_ne, huv | huv⟩
    · rw [arc_induced_digraph_adj_iff (fun e : D.Arc ↦ e.tail) (fun e ↦ e.head) F u v] at huv
      rcases huv with ⟨e, heF, htail, hhead⟩
      refine ⟨huv_ne, ⟨e, ⟨heF, Or.inl ⟨htail, hhead⟩⟩, ?_⟩⟩
      intro e' he'
      rcases he' with ⟨he'F, (⟨htail', hhead'⟩ | ⟨htail', hhead'⟩)⟩
      · -- Matching the same orientation fixes the arc uniquely by its endpoint pair.
        apply Subtype.ext
        exact Prod.ext (htail'.trans htail.symm) (hhead'.trans hhead.symm)
      · -- The opposite orientation would contradict asymmetry of `D.Adj`.
        have huv' : D.Adj u v := by
          simpa [htail, hhead] using e.2
        have hvu' : D.Adj v u := by
          simpa [htail', hhead'] using e'.2
        exact False.elim ((hasymm.asymm u v huv') hvu')
    · rw [arc_induced_digraph_adj_iff (fun e : D.Arc ↦ e.tail) (fun e ↦ e.head) F v u] at huv
      rcases huv with ⟨e, heF, htail, hhead⟩
      refine ⟨huv_ne, ⟨e, ⟨heF, Or.inr ⟨htail, hhead⟩⟩, ?_⟩⟩
      intro e' he'
      rcases he' with ⟨he'F, (⟨htail', hhead'⟩ | ⟨htail', hhead'⟩)⟩
      · -- The opposite orientation again contradicts asymmetry.
        have hvu' : D.Adj v u := by
          simpa [htail, hhead] using e.2
        have huv' : D.Adj u v := by
          simpa [htail', hhead'] using e'.2
        exact False.elim ((hasymm.asymm v u hvu') huv')
      · -- Matching the stored reversed orientation fixes the arc uniquely.
        apply Subtype.ext
        exact Prod.ext (htail'.trans htail.symm) (hhead'.trans hhead.symm)
  · rintro ⟨huv_ne, ⟨e, ⟨heF, hends⟩, _⟩⟩
    simp [supportGraph, Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj]
    refine ⟨huv_ne, ?_⟩
    rcases hends with ⟨htail, hhead⟩ | ⟨htail, hhead⟩
    · left
      rw [arc_induced_digraph_adj_iff (fun e : D.Arc ↦ e.tail) (fun e ↦ e.head) F u v]
      exact ⟨e, heF, htail, hhead⟩
    · right
      rw [arc_induced_digraph_adj_iff (fun e : D.Arc ↦ e.tail) (fun e ↦ e.head) F v u]
      exact ⟨e, heF, htail, hhead⟩

/-- Helper for Exercise 4.12: erasing one arc can only delete support-graph edges, never create
new ones. This is the monotonicity input needed to pass acyclicity to `F.erase e`. -/
lemma supportGraph_erase_le [DecidableEq D.Arc] {F : Finset D.Arc} {e : D.Arc} :
    D.supportGraph (F.erase e) ≤ D.supportGraph F := by
  intro u v huv
  -- Unfold the support-graph adjacency and keep the same witnessing arc after forgetting `erase`.
  simp [supportGraph, Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj] at huv ⊢
  rcases huv with ⟨huv_ne, huv | huv⟩
  · refine ⟨huv_ne, Or.inl ?_⟩
    rw [arc_induced_digraph_adj_iff (fun a : D.Arc ↦ a.tail) (fun a ↦ a.head) (F.erase e) u v] at huv
    rw [arc_induced_digraph_adj_iff (fun a : D.Arc ↦ a.tail) (fun a ↦ a.head) F u v]
    rcases huv with ⟨a, ha, htail, hhead⟩
    exact ⟨a, Finset.mem_of_mem_erase ha, htail, hhead⟩
  · refine ⟨huv_ne, Or.inr ?_⟩
    rw [arc_induced_digraph_adj_iff (fun a : D.Arc ↦ a.tail) (fun a ↦ a.head) (F.erase e) v u] at huv
    rw [arc_induced_digraph_adj_iff (fun a : D.Arc ↦ a.tail) (fun a ↦ a.head) F v u]
    rcases huv with ⟨a, ha, htail, hhead⟩
    exact ⟨a, Finset.mem_of_mem_erase ha, htail, hhead⟩

/-- Helper for Exercise 4.12: acyclicity survives erasing an arc from the support set. -/
lemma supportGraph_isAcyclic_of_erase [DecidableEq D.Arc]
    {F : Finset D.Arc} {e : D.Arc} (hacyc : (D.supportGraph F).IsAcyclic) :
    (D.supportGraph (F.erase e)).IsAcyclic := by
  -- Pass acyclicity through the support-graph inclusion from `F.erase e` into `F`.
  exact hacyc.anti (D.supportGraph_erase_le (F := F) (e := e))

/-- Helper for Exercise 4.12: if a vanishing relation among the restricted incidence columns is
supported at the row `v` by exactly one non-loop arc `e`, then the coefficient of `e` is zero. -/
lemma leaf_row_isolates_arc_coefficient
    {F : Finset D.Arc} {c : ↥F → ℚ} {e : D.Arc} (heF : e ∈ F) {v : V}
    (hincident : e.tail = v ∨ e.head = v) (hne : e.tail ≠ e.head)
    (hunique :
      ∀ a : D.Arc, a ∈ F → a ≠ e → a.tail ≠ v ∧ a.head ≠ v)
    (hrel :
      ∑ a : ↥F, c a • (fun w : V ↦ D.incidenceMatrix w (a : D.Arc)) = 0) :
    c ⟨e, heF⟩ = 0 := by
  classical
  have hv :
      ∑ a : ↥F, c a * D.incidenceMatrix v (a : D.Arc) = 0 := by
    -- Evaluating the column relation at the leaf row turns it into a scalar equation.
    simpa [Pi.smul_apply, smul_eq_mul] using congrFun hrel v
  have hsum_single :
      ∑ a : ↥F, c a * D.incidenceMatrix v (a : D.Arc) =
        c ⟨e, heF⟩ * D.incidenceMatrix v e := by
    refine Finset.sum_eq_single (a := (⟨e, heF⟩ : ↥F)) ?_ ?_
    · intro a _ hane
      have hane' : (a : D.Arc) ≠ e := by
        intro hae
        apply hane
        exact Subtype.ext hae
      have htail : (a : D.Arc).tail ≠ v := (hunique (a : D.Arc) a.2 hane').1
      have hhead : (a : D.Arc).head ≠ v := (hunique (a : D.Arc) a.2 hane').2
      have hzero : D.incidenceMatrix v (a : D.Arc) = 0 := by
        simpa [Digraph.incidenceMatrix] using
          (digraph_incidence_matrix_eq_zero_of_ne_endpoints
            ℚ (fun e : D.Arc ↦ e.tail) (fun e ↦ e.head) (w := v) (e := (a : D.Arc))
            htail.symm hhead.symm)
      simp [hzero]
    · intro hmem
      exact False.elim (hmem (Finset.mem_univ _))
  rw [hsum_single] at hv
  rcases hincident with htail | hhead
  · -- At the tail row, the lone surviving incidence entry is `-1`.
    have hentry : D.incidenceMatrix v e = -1 := by
      simpa [Digraph.incidenceMatrix, htail] using
        (digraph_incidence_matrix_tail
          ℚ (fun e : D.Arc ↦ e.tail) (fun e ↦ e.head) e hne)
    rw [hentry] at hv
    linarith
  · -- At the head row, the lone surviving incidence entry is `1`.
    have hentry : D.incidenceMatrix v e = 1 := by
      simpa [Digraph.incidenceMatrix, hhead] using
        (digraph_incidence_matrix_head
          ℚ (fun e : D.Arc ↦ e.tail) (fun e ↦ e.head) e hne)
    rw [hentry] at hv
    linarith

/-- Helper for Exercise 4.12: adding a single coefficient at `e` adds exactly the corresponding
incidence column to the restricted linear combination. -/
lemma add_single_coefficient_sum
    [DecidableEq V] {F : Finset D.Arc} (σ : ↥F → ℚ) (e : ↥F) (r : ℚ) :
    (∑ a : ↥F, (σ a + if a = e then r else 0) •
        (fun w : V ↦ D.incidenceMatrix w (a : D.Arc))) =
      (∑ a : ↥F, σ a • (fun w : V ↦ D.incidenceMatrix w (a : D.Arc))) +
        r • (fun w : V ↦ D.incidenceMatrix w (e : D.Arc)) := by
  -- Rewrite each updated coefficient as an old term plus a singleton contribution.
  simp_rw [add_smul]
  rw [Finset.sum_add_distrib]
  simp

/-- Helper for Exercise 4.12: traversing a support edge contributes the endpoint-delta vector,
with sign determined by whether the stored arc orientation agrees with the traversal. -/
lemma signed_incidence_column_eq_endpoint_delta
    [DecidableEq V]
    {e : D.Arc} {u v : V} (hne : u ≠ v)
    (hends : (e.tail = u ∧ e.head = v) ∨ (e.tail = v ∧ e.head = u)) :
    let sign : ℚ := if e.tail = u ∧ e.head = v then 1 else -1
    sign • (fun w : V ↦ D.incidenceMatrix w e) =
      fun w : V ↦ (if w = v then (1 : ℚ) else 0) - (if w = u then 1 else 0) :=
  by
    classical
    rcases hends with hforward | hreverse
    · -- In the forward orientation, the column is already the endpoint-delta vector.
      have htail_ne_head : e.tail ≠ e.head := by
        simpa [hforward.1, hforward.2] using hne
      have hsign : (if e.tail = u ∧ e.head = v then (1 : ℚ) else -1) = 1 := by
        simp [hforward]
      ext w
      by_cases hwv : w = v
      · have hentry : D.incidenceMatrix w e = 1 := by
          have hw_head : w = e.head := by
            simpa [hforward.2] using hwv
          simpa [hw_head, Digraph.incidenceMatrix] using
            (digraph_incidence_matrix_head
              ℚ (fun e : D.Arc ↦ e.tail) (fun e ↦ e.head) e htail_ne_head)
        rw [Pi.smul_apply, hsign, hentry]
        have hvu : v ≠ u := hne.symm
        simp [hwv, hvu]
      · by_cases hwu : w = u
        · have hentry : D.incidenceMatrix w e = -1 := by
            have hw_tail : w = e.tail := by
              simpa [hforward.1] using hwu
            simpa [hw_tail, Digraph.incidenceMatrix] using
              (digraph_incidence_matrix_tail
                ℚ (fun e : D.Arc ↦ e.tail) (fun e ↦ e.head) e htail_ne_head)
          rw [Pi.smul_apply, hsign, hentry]
          have huv : u ≠ v := hne
          simp [hwu, huv]
        · have hzero : D.incidenceMatrix w e = 0 := by
            have hw_tail : w ≠ e.tail := by simpa [hforward.1] using hwu
            have hw_head : w ≠ e.head := by simpa [hforward.2] using hwv
            simpa [Digraph.incidenceMatrix] using
              (digraph_incidence_matrix_eq_zero_of_ne_endpoints
                ℚ (fun e : D.Arc ↦ e.tail) (fun e ↦ e.head) hw_tail hw_head)
          rw [Pi.smul_apply, hsign, hzero]
          simp [hwv, hwu]
    · -- Route correction: when the traversal opposes the stored orientation, multiply by `-1`.
      have htail_ne_head : e.tail ≠ e.head := by
        simpa [hreverse.1, hreverse.2] using hne.symm
      have hnot_forward : ¬ (e.tail = u ∧ e.head = v) := by
        intro hforward
        exact hne (hforward.1.symm.trans hreverse.1)
      have hsign : (if e.tail = u ∧ e.head = v then (1 : ℚ) else -1) = -1 := by
        simp [hnot_forward]
      ext w
      by_cases hwv : w = v
      · have hentry : D.incidenceMatrix w e = -1 := by
          have hw_tail : w = e.tail := by
            simpa [hreverse.1] using hwv
          simpa [hw_tail, Digraph.incidenceMatrix] using
            (digraph_incidence_matrix_tail
              ℚ (fun e : D.Arc ↦ e.tail) (fun e ↦ e.head) e htail_ne_head)
        rw [Pi.smul_apply, hsign, hentry]
        have hvu : v ≠ u := hne.symm
        simp [hwv, hvu]
      · by_cases hwu : w = u
        · have hentry : D.incidenceMatrix w e = 1 := by
            have hw_head : w = e.head := by
              simpa [hreverse.2] using hwu
            simpa [hw_head, Digraph.incidenceMatrix] using
              (digraph_incidence_matrix_head
                ℚ (fun e : D.Arc ↦ e.tail) (fun e ↦ e.head) e htail_ne_head)
          rw [Pi.smul_apply, hsign, hentry]
          have huv : u ≠ v := hne
          simp [hwu, huv]
        · have hzero : D.incidenceMatrix w e = 0 := by
            have hw_tail : w ≠ e.tail := by simpa [hreverse.1] using hwv
            have hw_head : w ≠ e.head := by simpa [hreverse.2] using hwu
            simpa [Digraph.incidenceMatrix] using
              (digraph_incidence_matrix_eq_zero_of_ne_endpoints
                ℚ (fun e : D.Arc ↦ e.tail) (fun e ↦ e.head) hw_tail hw_head)
          rw [Pi.smul_apply, hsign, hzero]
          simp [hwv, hwu]

/-- Helper for Exercise 4.12: a walk in the support graph yields a signed restricted incidence
relation that telescopes to the difference of the endpoint delta vectors, and any nonzero
coefficient comes from an undirected edge traversed by the walk. -/
lemma support_walk_incidence_telescopes
    [DecidableEq V] (hasymm : Std.Asymm D.Adj) {F : Finset D.Arc} {u v : V}
    (p : (D.supportGraph F).Walk u v) :
    ∃ σ : ↥F → ℚ,
      ((∑ a : ↥F, σ a • (fun w : V ↦ D.incidenceMatrix w (a : D.Arc))) =
        (fun w : V ↦ (if w = v then (1 : ℚ) else 0) - (if w = u then 1 else 0))) ∧
      (∀ a : ↥F, σ a ≠ 0 → s((a : D.Arc).tail, (a : D.Arc).head) ∈ p.edges) := by
  classical
  -- Route correction: the previous statement tried to force a nonzero coefficient on the first
  -- edge for every nonempty walk, but backtracking walks such as `u-x-u` make that impossible.
  -- The source-faithful telescoping relation is true for arbitrary walks, and the nontriviality
  -- witness is recovered later only for cycles, where the first edge does not reappear.
  induction p with
  | nil =>
      refine ⟨fun _ ↦ 0, ?_, ?_⟩
      · -- The empty walk telescopes to the zero endpoint-delta relation.
        ext w
        simp
      · intro a hσ
        exact False.elim (hσ rfl)
  | @cons u x v h p ih =>
      rcases ih with ⟨σ, hσsum, hσsupp⟩
      rcases (D.supportGraph_adj_iff_exists_unique_arc hasymm).1 h with
        ⟨hux_ne, ⟨e, ⟨heF, hends⟩, _⟩⟩
      let eF : ↥F := ⟨e, heF⟩
      let sign : ℚ := if e.tail = u ∧ e.head = x then 1 else -1
      have hedge :
          s(((eF : D.Arc).tail), ((eF : D.Arc).head)) = s(u, x) := by
        rcases hends with ⟨htail, hhead⟩ | ⟨htail, hhead⟩
        · simpa [eF, htail, hhead]
        · simpa [eF, htail, hhead]
      have hcol :
          sign • (fun w : V ↦ D.incidenceMatrix w (eF : D.Arc)) =
            (fun w : V ↦ (if w = x then (1 : ℚ) else 0) - (if w = u then 1 else 0)) := by
        simpa [sign, eF] using
          (D.signed_incidence_column_eq_endpoint_delta (e := e) (u := u) (v := x) hux_ne hends)
      have hdelta :
          (fun w : V ↦
            ((if w = v then (1 : ℚ) else 0) - (if w = x then 1 else 0)) +
              ((if w = x then (1 : ℚ) else 0) - (if w = u then 1 else 0))) =
            (fun w : V ↦ (if w = v then (1 : ℚ) else 0) - (if w = u then 1 else 0)) := by
        ext w
        ring
      refine ⟨fun a ↦ σ a + if a = eF then sign else 0, ?_, ?_⟩
      · -- Add the new support edge column to the suffix relation and let the endpoint deltas telescope.
        calc
          (∑ a : ↥F,
              (σ a + if a = eF then sign else 0) •
                (fun w : V ↦ D.incidenceMatrix w (a : D.Arc))) =
              (∑ a : ↥F, σ a • (fun w : V ↦ D.incidenceMatrix w (a : D.Arc))) +
                sign • (fun w : V ↦ D.incidenceMatrix w (eF : D.Arc)) := by
                  simpa [eF, sign] using D.add_single_coefficient_sum σ eF sign
          _ =
              (fun w : V ↦ (if w = v then (1 : ℚ) else 0) - (if w = x then 1 else 0)) +
                (fun w : V ↦ (if w = x then (1 : ℚ) else 0) - (if w = u then 1 else 0)) := by
                  rw [hσsum, hcol]
          _ = (fun w : V ↦ (if w = v then (1 : ℚ) else 0) - (if w = u then 1 else 0)) := hdelta
      · intro a hσa
        by_cases hae : a = eF
        · -- The freshly added coefficient is supported on the new head edge.
          subst hae
          simpa [SimpleGraph.Walk.edges_cons, hedge]
        · -- Any other nonzero coefficient already comes from the suffix walk.
          have hσa_old : σ a ≠ 0 := by
            intro hzero
            apply hσa
            simp [hae, hzero]
          have hmem : s((a : D.Arc).tail, (a : D.Arc).head) ∈ p.edges := hσsupp a hσa_old
          simpa [SimpleGraph.Walk.edges_cons, hmem]

/-- Helper for Exercise 4.12: an undirected cycle in the support graph gives a nontrivial linear
dependence among the restricted incidence columns. -/
lemma incidence_columns_not_linearIndependent_of_hasUndirectedCycle
    (hasymm : Std.Asymm D.Adj) {F : Finset D.Arc} (hcycle : D.HasUndirectedCycle F) :
    ¬ LinearIndependent ℚ
      (fun e : ↥F ↦ fun v : V ↦ D.incidenceMatrix v (e : D.Arc)) :=
by
  classical
  rcases hcycle with ⟨u, p, hpcycle⟩
  rcases SimpleGraph.Walk.not_nil_iff.mp hpcycle.not_nil with ⟨x, hux, q, hpcons⟩
  have hpcycle' : (SimpleGraph.Walk.cons hux q).IsCycle := by
    simpa [hpcons] using hpcycle
  have hqinfo := (SimpleGraph.Walk.cons_isCycle_iff q hux).1 hpcycle'
  rcases hqinfo with ⟨_, hfirst_not_mem⟩
  rcases (D.supportGraph_adj_iff_exists_unique_arc hasymm).1 hux with
    ⟨hux_ne, ⟨e, ⟨heF, hends⟩, _⟩⟩
  let eF : ↥F := ⟨e, heF⟩
  let sign : ℚ := if e.tail = u ∧ e.head = x then 1 else -1
  rcases D.support_walk_incidence_telescopes hasymm q with ⟨σ, hσsum, hσsupp⟩
  have hedge :
      s(((eF : D.Arc).tail), ((eF : D.Arc).head)) = s(u, x) := by
    rcases hends with ⟨htail, hhead⟩ | ⟨htail, hhead⟩
    · simpa [eF, htail, hhead]
    · simpa [eF, htail, hhead]
  have hσe_zero : σ eF = 0 := by
    by_contra hσe
    have hmem : s(((eF : D.Arc).tail), ((eF : D.Arc).head)) ∈ q.edges := hσsupp eF hσe
    exact hfirst_not_mem (hedge ▸ hmem)
  have hcol :
      sign • (fun w : V ↦ D.incidenceMatrix w (eF : D.Arc)) =
        (fun w : V ↦ (if w = x then (1 : ℚ) else 0) - (if w = u then 1 else 0)) := by
    simpa [sign, eF] using
      (D.signed_incidence_column_eq_endpoint_delta (e := e) (u := u) (v := x) hux_ne hends)
  have hzero :
      (fun w : V ↦
        ((if w = u then (1 : ℚ) else 0) - (if w = x then 1 else 0)) +
          ((if w = x then (1 : ℚ) else 0) - (if w = u then 1 else 0))) = 0 := by
    ext w
    simp
  rw [Fintype.not_linearIndependent_iff]
  refine ⟨fun a ↦ σ a + if a = eF then sign else 0, ?_, ?_⟩
  · -- The suffix gives `δ_u - δ_x`; adding the first edge contributes `δ_x - δ_u`.
    calc
      (∑ a : ↥F,
          (σ a + if a = eF then sign else 0) •
            (fun w : V ↦ D.incidenceMatrix w (a : D.Arc))) =
          (∑ a : ↥F, σ a • (fun w : V ↦ D.incidenceMatrix w (a : D.Arc))) +
            sign • (fun w : V ↦ D.incidenceMatrix w (eF : D.Arc)) := by
              simpa [eF, sign] using D.add_single_coefficient_sum σ eF sign
      _ =
          (fun w : V ↦ (if w = u then (1 : ℚ) else 0) - (if w = x then 1 else 0)) +
            (fun w : V ↦ (if w = x then (1 : ℚ) else 0) - (if w = u then 1 else 0)) := by
              rw [hσsum, hcol]
      _ = 0 := hzero
  · -- The first traversed support edge carries a nonzero coefficient, so the relation is nontrivial.
    refine ⟨eF, ?_⟩
    by_cases hforward : e.tail = u ∧ e.head = x
    · simpa [eF, sign, hσe_zero, hforward]
    · simpa [eF, sign, hσe_zero, hforward]

/-- Helper for Exercise 4.12: enlarging the chosen arc family can only enlarge the undirected
support graph. -/
lemma supportGraph_mono {F G : Finset D.Arc} (hFG : F ⊆ G) :
    D.supportGraph F ≤ D.supportGraph G := by
  intro u v huv
  -- Forgetting orientations commutes with passing to a larger arc witness set.
  simp [supportGraph, Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj] at huv ⊢
  rcases huv with ⟨huv_ne, huv | huv⟩
  · refine ⟨huv_ne, Or.inl ?_⟩
    rw [arc_induced_digraph_adj_iff (fun a : D.Arc ↦ a.tail) (fun a ↦ a.head) F u v] at huv
    rw [arc_induced_digraph_adj_iff (fun a : D.Arc ↦ a.tail) (fun a ↦ a.head) G u v]
    rcases huv with ⟨a, haF, htail, hhead⟩
    exact ⟨a, hFG haF, htail, hhead⟩
  · refine ⟨huv_ne, Or.inr ?_⟩
    rw [arc_induced_digraph_adj_iff (fun a : D.Arc ↦ a.tail) (fun a ↦ a.head) F v u] at huv
    rw [arc_induced_digraph_adj_iff (fun a : D.Arc ↦ a.tail) (fun a ↦ a.head) G v u]
    rcases huv with ⟨a, haF, htail, hhead⟩
    exact ⟨a, hFG haF, htail, hhead⟩

/-- Helper for Exercise 4.12: every arc of `F` contributes its endpoint pair as an edge of the
support graph. -/
lemma supportGraph_adj_of_mem
    (hasymm : Std.Asymm D.Adj) {F : Finset D.Arc} {e : D.Arc} (heF : e ∈ F) :
    (D.supportGraph F).Adj e.tail e.head := by
  have hne : e.tail ≠ e.head := by
    intro htail_head
    have hforward : D.Adj e.tail e.head := by
      simpa using e.2
    have hreverse : D.Adj e.head e.tail := by
      simpa [htail_head] using e.2
    exact (hasymm.asymm _ _ hforward) hreverse
  -- The chosen arc itself witnesses the corresponding undirected support edge.
  refine (D.supportGraph_adj_iff_exists_unique_arc hasymm).2 ?_
  refine ⟨hne, ⟨e, ⟨heF, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩⟩
  intro a ha
  rcases ha with ⟨haF, (⟨htail, hhead⟩ | ⟨htail, hhead⟩)⟩
  · apply Subtype.ext
    exact Prod.ext htail hhead
  · have hforward : D.Adj e.tail e.head := by
      simpa using e.2
    have hreverse : D.Adj e.head e.tail := by
      simpa [htail, hhead] using a.2
    exact False.elim ((hasymm.asymm _ _ hforward) hreverse)

/-- Helper for Exercise 4.12: removing the zero coefficients from a vanishing incidence relation
does not change the resulting sum. -/
lemma restrict_zero_relation_to_nonzeroSupport
    {F : Finset D.Arc} (σ : D.Arc → ℚ)
    (hrel :
      ∑ a : ↥F, σ (a : D.Arc) • (fun w : V ↦ D.incidenceMatrix w (a : D.Arc)) = 0) :
    let S := F.filter fun e ↦ σ e ≠ 0
    ∑ a : ↥S, σ (a : D.Arc) • (fun w : V ↦ D.incidenceMatrix w (a : D.Arc)) = 0 := by
  classical
  let t : Finset ↥F := Finset.univ.filter fun a : ↥F ↦ σ (a : D.Arc) ≠ 0
  have hsum :
      Finset.sum t (fun a ↦ σ (a : D.Arc) • (fun w : V ↦ D.incidenceMatrix w (a : D.Arc))) =
        Finset.sum (Finset.univ : Finset ↥F)
          (fun a ↦ σ (a : D.Arc) • (fun w : V ↦ D.incidenceMatrix w (a : D.Arc))) := by
    -- On the subtype index family, filtering out zero coefficients does not change the sum.
    rw [show t = Finset.univ.filter fun a : ↥F ↦ σ (a : D.Arc) ≠ 0 by rfl]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro a ha
    by_cases hσ : σ (a : D.Arc) ≠ 0
    · simp [hσ]
    · have hσ' : σ (a : D.Arc) = 0 := by simpa using hσ
      simp [hσ']
  have hfiltered :
      Finset.sum t (fun a ↦ σ (a : D.Arc) • (fun w : V ↦ D.incidenceMatrix w (a : D.Arc))) = 0 := by
    rw [hsum, hrel]
  have ht :
      t =
        (F.filter fun e ↦ σ e ≠ 0).attach.map
          ((Function.Embedding.refl _).subtypeMap Finset.mem_of_mem_filter) := by
    simpa [t, Finset.univ_eq_attach] using
      (Finset.filter_attach (p := fun e : D.Arc ↦ σ e ≠ 0) F)
  rw [ht, Finset.sum_map] at hfiltered
  simpa [Finset.sum_attach] using hfiltered

/-- Helper for Exercise 4.12: a nonempty acyclic support graph contains an arc incident to a leaf
vertex, so every other chosen arc avoids that vertex. -/
lemma exists_leaf_arc_of_supportGraph_isAcyclic
    (hasymm : Std.Asymm D.Adj) {F : Finset D.Arc}
    (hacyc : (D.supportGraph F).IsAcyclic) (hF : F.Nonempty) :
    ∃ e ∈ F, ∃ v, (e.tail = v ∨ e.head = v) ∧ e.tail ≠ e.head ∧
      (∀ a : D.Arc, a ∈ F → a ≠ e → a.tail ≠ v ∧ a.head ≠ v) := by
  classical
  rcases hF with ⟨e, heF⟩
  have hne : e.tail ≠ e.head := by
    intro htail_head
    have hforward : D.Adj e.tail e.head := by
      simpa using e.2
    have hreverse : D.Adj e.head e.tail := by
      simpa [htail_head] using e.2
    exact (hasymm.asymm _ _ hforward) hreverse
  let T : Finset V := circuit_vertices (fun a : D.Arc ↦ a.tail) (fun a ↦ a.head) F
  let H : SimpleGraph ↥T := (D.supportGraph F).induce (↑T : Set V)
  have htailT : e.tail ∈ T := by
    exact (mem_circuit_vertices_iff (fun a : D.Arc ↦ a.tail) (fun a ↦ a.head) F e.tail).2
      ⟨e, heF, Or.inl rfl⟩
  have hheadT : e.head ∈ T := by
    exact (mem_circuit_vertices_iff (fun a : D.Arc ↦ a.tail) (fun a ↦ a.head) F e.head).2
      ⟨e, heF, Or.inr rfl⟩
  have hacycH : H.IsAcyclic := by
    -- Restrict to the finitely many vertices touched by `F` so the tree leaf theorem applies.
    simpa [H] using hacyc.induce (↑T : Set V)
  have hadjH : H.Adj ⟨e.tail, htailT⟩ ⟨e.head, hheadT⟩ := by
    simpa [H] using D.supportGraph_adj_of_mem hasymm (F := F) heF
  let c : H.ConnectedComponent := H.connectedComponentMk ⟨e.tail, htailT⟩
  have htailC : (⟨e.tail, htailT⟩ : ↥T) ∈ c.supp := by
    simpa [c] using (SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      (G := H) (v := ⟨e.tail, htailT⟩))
  have hheadC : (⟨e.head, hheadT⟩ : ↥T) ∈ c.supp := by
    exact SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp c htailC hadjH
  have hnontrivial : Nontrivial c.supp := by
    -- The chosen arc gives two distinct vertices in the same connected component.
    refine ⟨⟨⟨e.tail, htailT⟩, htailC⟩, ⟨⟨e.head, hheadT⟩, hheadC⟩, ?_⟩
    intro hEq
    apply hne
    exact congrArg Subtype.val (congrArg Subtype.val hEq)
  have htree : c.toSimpleGraph.IsTree := hacycH.isTree_connectedComponent c
  obtain ⟨v, hvdeg⟩ := htree.exists_vert_degree_one_of_nontrivial
  obtain ⟨w, hvw, huniqueNeighbor⟩ :=
    (SimpleGraph.degree_eq_one_iff_existsUnique_adj (G := c.toSimpleGraph) (v := v)).1 hvdeg
  have hvwG : (D.supportGraph F).Adj v.1.1 w.1.1 := by
    -- Move the leaf-edge adjacency back through the connected-component and induced-graph layers.
    simpa [H] using hvw
  rcases (D.supportGraph_adj_iff_exists_unique_arc hasymm (F := F) (u := v.1.1) (v := w.1.1)).1
      hvwG with ⟨_, ⟨eLeaf, ⟨heLeafF, hleafEnds⟩, hleafUnique⟩⟩
  have hleafNe : eLeaf.tail ≠ eLeaf.head := by
    intro htail_head
    have hforward : D.Adj eLeaf.tail eLeaf.head := by
      simpa using eLeaf.2
    have hreverse : D.Adj eLeaf.head eLeaf.tail := by
      simpa [htail_head] using eLeaf.2
    exact (hasymm.asymm _ _ hforward) hreverse
  have hincidentUnique :
      ∀ a : D.Arc, a ∈ F → (a.tail = v.1.1 ∨ a.head = v.1.1) → a = eLeaf := by
    intro a haF haIncident
    rcases haIncident with hatail | hahead
    · have hheadT' : a.head ∈ T := by
        exact (mem_circuit_vertices_iff (fun b : D.Arc ↦ b.tail) (fun b ↦ b.head) F a.head).2
          ⟨a, haF, Or.inr rfl⟩
      have hadjH' : H.Adj v.1 ⟨a.head, hheadT'⟩ := by
        simpa [H, hatail] using D.supportGraph_adj_of_mem hasymm (F := F) haF
      have hheadC' : (⟨a.head, hheadT'⟩ : ↥T) ∈ c.supp := by
        exact SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp c v.2 hadjH'
      let aHeadC : c.supp := ⟨⟨a.head, hheadT'⟩, hheadC'⟩
      have haHeadEq : aHeadC = w := huniqueNeighbor aHeadC (by simpa using hadjH')
      have hheadEq : a.head = w.1.1 := by
        exact congrArg (fun z : c.supp ↦ z.1.1) haHeadEq
      exact hleafUnique a ⟨haF, Or.inl ⟨hatail, hheadEq⟩⟩
    · have htailT' : a.tail ∈ T := by
        exact (mem_circuit_vertices_iff (fun b : D.Arc ↦ b.tail) (fun b ↦ b.head) F a.tail).2
          ⟨a, haF, Or.inl rfl⟩
      have hadjH' : H.Adj v.1 ⟨a.tail, htailT'⟩ := by
        simpa [H, hahead] using (D.supportGraph_adj_of_mem hasymm (F := F) haF).symm
      have htailC' : (⟨a.tail, htailT'⟩ : ↥T) ∈ c.supp := by
        exact SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp c v.2 hadjH'
      let aTailC : c.supp := ⟨⟨a.tail, htailT'⟩, htailC'⟩
      have haTailEq : aTailC = w := huniqueNeighbor aTailC (by simpa using hadjH')
      have htailEq : a.tail = w.1.1 := by
        exact congrArg (fun z : c.supp ↦ z.1.1) haTailEq
      exact hleafUnique a ⟨haF, Or.inr ⟨htailEq, hahead⟩⟩
  refine ⟨eLeaf, heLeafF, v.1.1, ?_, hleafNe, ?_⟩
  · rcases hleafEnds with ⟨htail, _⟩ | ⟨_, hhead⟩
    · exact Or.inl htail
    · exact Or.inr hhead
  · intro a haF haNe
    constructor
    · intro hatail
      exact haNe (hincidentUnique a haF (Or.inl hatail))
    · intro hahead
      exact haNe (hincidentUnique a haF (Or.inr hahead))

/-- Exercise 4.12 (1). For a finite set of arcs `F`, the columns of the incidence matrix indexed
by `F` are linearly independent if and only if `F` contains no cycle in the underlying undirected
graph. The asymmetry assumption formalizes the textbook convention that opposite orientations of
the same undirected edge are not both present as arcs. -/
theorem incidenceMatrix_columns_linearIndependent_iff_no_cycle
    (hasymm : Std.Asymm D.Adj) (F : Finset D.Arc) :
    LinearIndependent ℚ
      (fun e : ↥F ↦ fun v : V ↦ D.incidenceMatrix v (e : D.Arc)) ↔
      ¬ D.HasUndirectedCycle F := by
  classical
  constructor
  · intro hli hcycle
    -- A cycle gives a signed telescoping relation, so linear independence rules cycles out.
    exact D.incidence_columns_not_linearIndependent_of_hasUndirectedCycle hasymm hcycle hli
  · intro hnoCycle
    -- Rewrite "no undirected cycle" as support-graph acyclicity, then eliminate any nonzero
    -- coefficient by restricting to its nonzero support and using a leaf row of that forest.
    rw [Fintype.linearIndependent_iff]
    intro c hrel i
    let σ : D.Arc → ℚ := fun e ↦ if heF : e ∈ F then c ⟨e, heF⟩ else 0
    let S : Finset D.Arc := F.filter fun e ↦ σ e ≠ 0
    have hacycF : (D.supportGraph F).IsAcyclic := by
      rw [D.hasUndirectedCycle_iff_not_isAcyclic] at hnoCycle
      exact not_not.mp hnoCycle
    have hrelS :
        ∑ a : ↥S, σ (a : D.Arc) • (fun w : V ↦ D.incidenceMatrix w (a : D.Arc)) = 0 := by
      -- The original relation is unchanged after removing all zero coefficients.
      have hrelσ :
          ∑ a : ↥F, σ (a : D.Arc) • (fun w : V ↦ D.incidenceMatrix w (a : D.Arc)) = 0 := by
        simpa [σ] using hrel
      simpa [S] using D.restrict_zero_relation_to_nonzeroSupport (F := F) σ hrelσ
    have hSF : S ⊆ F := by
      intro e heS
      exact (Finset.mem_filter.1 heS).1
    have hSempty : S = ∅ := by
      by_contra hS_ne
      have hSnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_ne
      have hacycS : (D.supportGraph S).IsAcyclic := by
        exact hacycF.anti (D.supportGraph_mono (F := S) (G := F) hSF)
      rcases D.exists_leaf_arc_of_supportGraph_isAcyclic hasymm hacycS hSnonempty with
        ⟨e, heS, v, hincident, hne, hunique⟩
      have hσe_zero : σ e = 0 := by
        -- At a leaf vertex only one nonzero-support arc contributes, so its coefficient vanishes.
        exact D.leaf_row_isolates_arc_coefficient
          (F := S) (c := fun a : ↥S ↦ σ (a : D.Arc)) heS hincident hne hunique hrelS
      exact (Finset.mem_filter.1 heS).2 hσe_zero
    have hi_not_mem : i.1 ∉ S := by
      simpa [hSempty]
    by_cases hσi : σ i.1 = 0
    · simpa [σ, i.2] using hσi
    · exact False.elim (hi_not_mem (by simp [S, hσi]))

/-- Helper for Exercise 4.12: evaluating `((D.incidenceMatrix)ᵀ *ᵥ x)` on an arc subtracts the
tail value from the head value. -/
lemma incidenceMatrix_transpose_mulVec_apply [Fintype V] (x : V → ℚ) (e : D.Arc) :
    Matrix.mulVec (Matrix.transpose D.incidenceMatrix) x e = x e.head - x e.tail := by
  classical
  -- Expand the transpose-mulVec entry and separate the head and tail indicator sums.
  rw [Matrix.mulVec, dotProduct]
  change
    (∑ a,
        (digraph_incidence_matrix ℚ (fun e : D.Arc ↦ e.tail) (fun e ↦ e.head) a e) * x a) =
      x e.head - x e.tail
  unfold digraph_incidence_matrix
  have hsplit :
      ∀ a : V,
        (((if a = e.head then (1 : ℚ) else 0) - (if a = e.tail then 1 else 0)) * x a) =
          (if a = e.head then x a else 0) - (if a = e.tail then x a else 0) := by
    intro a
    by_cases hhead : a = e.head
    · by_cases htail : a = e.tail
      · have hloop : e.head = e.tail := hhead.symm.trans htail
        simp [hhead, htail, hloop]
      · by_cases hloop : e.head = e.tail
        · exact False.elim (htail (hhead.trans hloop))
        · simp [hhead, htail, hloop]
    · by_cases htail : a = e.tail
      · by_cases hloop : e.head = e.tail
        · exact False.elim (hhead (htail.trans hloop.symm))
        · have hloop' : e.tail ≠ e.head := by
            exact mt Eq.symm hloop
          simp [hhead, htail, hloop, hloop']
      · by_cases hloop : e.head = e.tail
        · simp [hhead, htail, hloop]
        · simp [hhead, htail, hloop]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib]
  have hhead : ∑ a, (if a = e.head then x a else 0) = x e.head := by
    simp
  have htail : ∑ a, (if a = e.tail then x a else 0) = x e.tail := by
    simp
  rw [hhead, htail]

/-- Helper for Exercise 4.12: the transpose-incidence kernel consists exactly of the vertex
functions that are constant on connected components of `D.toSimpleGraphInclusive`. -/
lemma incidenceMatrix_transpose_mulVec_eq_zero_iff_forall_reachable
    [Fintype V] {x : V → ℚ} :
    Matrix.mulVec (Matrix.transpose D.incidenceMatrix) x = 0 ↔
      ∀ i j : V, D.toSimpleGraphInclusive.Reachable i j → x i = x j := by
  classical
  constructor
  · intro hx i j hij
    have hconst_adj :
        ∀ ⦃u v : V⦄, D.toSimpleGraphInclusive.Adj u v → x u = x v := by
      intro u v huv
      rw [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj] at huv
      rcases huv.2 with huv | hvu
      · let e : D.Arc := ⟨(u, v), huv⟩
        have he : Matrix.mulVec (Matrix.transpose D.incidenceMatrix) x e = 0 := by
          simp [hx] at *
        rw [D.incidenceMatrix_transpose_mulVec_apply x e] at he
        linarith
      · let e : D.Arc := ⟨(v, u), hvu⟩
        have he : Matrix.mulVec (Matrix.transpose D.incidenceMatrix) x e = 0 := by
          simp [hx] at *
        rw [D.incidenceMatrix_transpose_mulVec_apply x e] at he
        linarith
    rcases hij with ⟨p⟩
    -- Walk induction propagates equality across every undirected support edge.
    induction p with
    | nil =>
        rfl
    | @cons a b c hab p ih =>
        exact (hconst_adj hab).trans ih
  · intro hx
    ext e
    by_cases hloop : e.tail = e.head
    · rw [D.incidenceMatrix_transpose_mulVec_apply x e]
      simp [hloop]
    · have hadj : D.toSimpleGraphInclusive.Adj e.tail e.head := by
        rw [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj]
        exact ⟨hloop, Or.inl e.2⟩
      have heq : x e.tail = x e.head := hx e.tail e.head hadj.reachable
      rw [D.incidenceMatrix_transpose_mulVec_apply x e]
      simpa [sub_eq_zero] using heq.symm

/-- Helper for Exercise 4.12: the indicator of a connected component lies in the kernel of the
transpose incidence map. -/
lemma mem_ker_toLin'_incidenceMatrix_transpose_of_connectedComponent [Fintype V] [DecidableEq V]
    [DecidableEq D.toSimpleGraphInclusive.ConnectedComponent]
    (c : D.toSimpleGraphInclusive.ConnectedComponent) :
    (fun i ↦ if D.toSimpleGraphInclusive.connectedComponentMk i = c then 1 else 0) ∈
      LinearMap.ker (Matrix.toLin' (Matrix.transpose D.incidenceMatrix)) := by
  -- Rewrite kernel membership into the connected-component constancy criterion.
  rw [LinearMap.mem_ker, Matrix.toLin'_apply]
  rw [D.incidenceMatrix_transpose_mulVec_eq_zero_iff_forall_reachable]
  intro i j hij
  have hcc :
      D.toSimpleGraphInclusive.connectedComponentMk i =
        D.toSimpleGraphInclusive.connectedComponentMk j :=
    SimpleGraph.ConnectedComponent.sound hij
  by_cases hi : D.toSimpleGraphInclusive.connectedComponentMk i = c
  · have hj : D.toSimpleGraphInclusive.connectedComponentMk j = c := by
      calc
        D.toSimpleGraphInclusive.connectedComponentMk j
          = D.toSimpleGraphInclusive.connectedComponentMk i := hcc.symm
        _ = c := hi
    simp [hi, hj]
  · have hj : D.toSimpleGraphInclusive.connectedComponentMk j ≠ c := by
      intro hj
      exact hi (hcc.trans hj)
    simp [hi, hj]

/-- Helper for Exercise 4.12: the connected-component indicator corresponding to `c`, viewed as an
element of the transpose-incidence kernel. -/
def incidenceMatrix_transpose_ker_basis_aux [Fintype V] [DecidableEq V]
    [DecidableEq D.toSimpleGraphInclusive.ConnectedComponent]
    (c : D.toSimpleGraphInclusive.ConnectedComponent) :
    LinearMap.ker (Matrix.toLin' (Matrix.transpose D.incidenceMatrix)) :=
  ⟨fun i ↦ if D.toSimpleGraphInclusive.connectedComponentMk i = c then (1 : ℚ) else 0,
    D.mem_ker_toLin'_incidenceMatrix_transpose_of_connectedComponent c⟩

/-- Helper for Exercise 4.12: the connected-component indicator family in the transpose kernel is
linearly independent. -/
lemma linearIndependent_incidenceMatrix_transpose_ker_basis_aux [Fintype V] [DecidableEq V]
    [DecidableEq D.toSimpleGraphInclusive.ConnectedComponent] :
    LinearIndependent ℚ (D.incidenceMatrix_transpose_ker_basis_aux) := by
  classical
  let _ : Fintype D.toSimpleGraphInclusive.ConnectedComponent := Fintype.ofFinite _
  rw [Fintype.linearIndependent_iff]
  intro g hg c₀
  rw [Subtype.ext_iff] at hg
  have hEval :
      (∑ c : D.toSimpleGraphInclusive.ConnectedComponent,
          g c *
            (if D.toSimpleGraphInclusive.connectedComponentMk c₀.out = c then (1 : ℚ) else 0)) = 0 := by
    simpa [incidenceMatrix_transpose_ker_basis_aux] using congrFun hg c₀.out
  -- Evaluate at the representative of `c₀` to isolate the `c₀`-coefficient.
  have hsingle' :
      (∑ c : D.toSimpleGraphInclusive.ConnectedComponent,
          g c *
            (if D.toSimpleGraphInclusive.connectedComponentMk c₀.out = c then (1 : ℚ) else 0)) =
        g c₀ *
          (if D.toSimpleGraphInclusive.connectedComponentMk c₀.out = c₀ then (1 : ℚ) else 0) := by
    refine Finset.sum_eq_single c₀ ?_ ?_
    · intro c _ hcc
      have hout_not_mem : c₀.out ∉ c.supp := by
        intro hmem
        exact hcc (SimpleGraph.ConnectedComponent.eq_of_common_vertex hmem c₀.out_eq)
      have hneq : D.toSimpleGraphInclusive.connectedComponentMk c₀.out ≠ c := by
        simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hout_not_mem
      simp [hneq]
    · intro hc₀
      exact False.elim (hc₀ (Finset.mem_univ _))
  have hsingle :
      (∑ c : D.toSimpleGraphInclusive.ConnectedComponent,
          g c *
            (if D.toSimpleGraphInclusive.connectedComponentMk c₀.out = c then (1 : ℚ) else 0)) =
        g c₀ := by
    calc
      (∑ c : D.toSimpleGraphInclusive.ConnectedComponent,
          g c *
            (if D.toSimpleGraphInclusive.connectedComponentMk c₀.out = c then (1 : ℚ) else 0)) =
        g c₀ *
          (if D.toSimpleGraphInclusive.connectedComponentMk c₀.out = c₀ then (1 : ℚ) else 0) :=
            hsingle'
      _ = g c₀ * (1 : ℚ) := by
            have hcc : D.toSimpleGraphInclusive.connectedComponentMk c₀.out = c₀ := c₀.out_eq
            have hif :
                (if D.toSimpleGraphInclusive.connectedComponentMk c₀.out = c₀ then (1 : ℚ) else 0) =
                  1 := by
              simp [hcc]
            rw [hif]
      _ = g c₀ := by ring
  calc
    g c₀ = (∑ c : D.toSimpleGraphInclusive.ConnectedComponent,
        g c *
          (if D.toSimpleGraphInclusive.connectedComponentMk c₀.out = c then (1 : ℚ) else 0)) := by
            symm
            exact hsingle
    _ = 0 := hEval

/-- Helper for Exercise 4.12: the connected-component indicator family spans the whole transpose
kernel. -/
lemma top_le_span_range_incidenceMatrix_transpose_ker_basis_aux [Fintype V] [DecidableEq V]
    [DecidableEq D.toSimpleGraphInclusive.ConnectedComponent] :
    ⊤ ≤ Submodule.span ℚ (Set.range (D.incidenceMatrix_transpose_ker_basis_aux)) := by
  classical
  let _ : Fintype D.toSimpleGraphInclusive.ConnectedComponent := Fintype.ofFinite _
  intro x _
  rw [Submodule.mem_span_range_iff_exists_fun]
  use fun c ↦ x.val c.out
  have hx :
      ∀ i j : V, D.toSimpleGraphInclusive.Reachable i j → x.val i = x.val j := by
    have hxker : Matrix.mulVec (Matrix.transpose D.incidenceMatrix) x.val = 0 := by
      exact x.2
    exact (D.incidenceMatrix_transpose_mulVec_eq_zero_iff_forall_reachable).1 hxker
  -- Evaluating at a vertex collapses the component-indicator sum to its own component.
  ext v
  rw [AddSubmonoid.coe_finsetSum]
  simp only [incidenceMatrix_transpose_ker_basis_aux, SetLike.mk_smul_mk, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  let c : D.toSimpleGraphInclusive.ConnectedComponent := D.toSimpleGraphInclusive.connectedComponentMk v
  have hsingle' :
      (∑ d : D.toSimpleGraphInclusive.ConnectedComponent,
          x.val d.out *
            (if D.toSimpleGraphInclusive.connectedComponentMk v = d then (1 : ℚ) else 0)) =
        x.val c.out *
          (if D.toSimpleGraphInclusive.connectedComponentMk v = c then (1 : ℚ) else 0) := by
    refine Finset.sum_eq_single c ?_ ?_
    · intro d _ hdc
      have hneq : D.toSimpleGraphInclusive.connectedComponentMk v ≠ d := by
        intro hEq
        exact hdc hEq.symm
      simp [hneq]
    · intro hc
      exact False.elim (hc (Finset.mem_univ _))
  have hsingle :
      (∑ d : D.toSimpleGraphInclusive.ConnectedComponent,
          x.val d.out *
            (if D.toSimpleGraphInclusive.connectedComponentMk v = d then (1 : ℚ) else 0)) =
        x.val c.out := by
    simpa only [c, if_true, mul_one] using hsingle'
  rw [hsingle]
  have hv_mem : v ∈ c.supp := by
    simpa [c] using (SimpleGraph.ConnectedComponent.mem_supp_iff c v).2 rfl
  have hreach : D.toSimpleGraphInclusive.Reachable c.out v :=
    c.reachable_of_mem_supp c.out_eq hv_mem
  simpa using hx c.out v hreach

/-- Helper for Exercise 4.12: a basis of the transpose-incidence kernel indexed by connected
components of `D.toSimpleGraphInclusive`. -/
noncomputable def incidenceMatrix_transpose_ker_basis [Fintype V] [DecidableEq V]
    [DecidableEq D.toSimpleGraphInclusive.ConnectedComponent] :
    Module.Basis D.toSimpleGraphInclusive.ConnectedComponent ℚ
      (LinearMap.ker (Matrix.toLin' (Matrix.transpose D.incidenceMatrix))) :=
  Module.Basis.mk D.linearIndependent_incidenceMatrix_transpose_ker_basis_aux
    D.top_le_span_range_incidenceMatrix_transpose_ker_basis_aux

/-- Helper for Exercise 4.12: the transpose-incidence kernel has dimension equal to the number of
connected components of the underlying undirected graph. -/
theorem card_connectedComponent_eq_finrank_ker_toLin'_incidenceMatrix_transpose
    [Fintype V] [DecidableEq V] :
    Nat.card D.toSimpleGraphInclusive.ConnectedComponent =
      Module.finrank ℚ (Matrix.toLin' (Matrix.transpose D.incidenceMatrix)).ker := by
  classical
  let _ : Fintype D.toSimpleGraphInclusive.ConnectedComponent := Fintype.ofFinite _
  -- The basis above identifies the kernel dimension with the finite number of components.
  rw [Nat.card_eq_fintype_card, Module.finrank_eq_card_basis
    (D.incidenceMatrix_transpose_ker_basis)]

/-- Exercise 4.12 (2). The rank of the incidence matrix equals the number of vertices minus the
number of connected components of the underlying undirected graph. -/
theorem incidenceMatrix_rank_eq_card_vertices_sub_card_connectedComponents
    [Fintype V] [DecidableRel D.Adj] :
    (D.incidenceMatrix).rank =
      Fintype.card V - Fintype.card D.toSimpleGraphInclusive.ConnectedComponent := by
  classical
  have hker :
      Module.finrank ℚ (Matrix.toLin' (Matrix.transpose D.incidenceMatrix)).ker =
        Nat.card D.toSimpleGraphInclusive.ConnectedComponent := by
    -- The previously constructed kernel basis identifies the kernel dimension with the component
    -- count, stated with `Nat.card` to avoid competing `Fintype` instances.
    simpa using
      (D.card_connectedComponent_eq_finrank_ker_toLin'_incidenceMatrix_transpose).symm
  have hsum :
      (Matrix.transpose D.incidenceMatrix).rank +
          Nat.card D.toSimpleGraphInclusive.ConnectedComponent =
        Fintype.card V := by
    -- Apply rank-nullity to the transpose, whose ambient codomain is the vertex function space.
    simpa [Matrix.rank, hker, Module.finrank_pi] using
      (LinearMap.finrank_range_add_finrank_ker
        (Matrix.toLin' (Matrix.transpose D.incidenceMatrix)))
  have hsum' :
      (D.incidenceMatrix).rank +
          Nat.card D.toSimpleGraphInclusive.ConnectedComponent =
        Fintype.card V := by
    -- `rank A = rank Aᵀ`, so the transpose identity is already the desired cardinality equation.
    calc
      (D.incidenceMatrix).rank +
          Nat.card D.toSimpleGraphInclusive.ConnectedComponent =
            (Matrix.transpose D.incidenceMatrix).rank +
              Nat.card D.toSimpleGraphInclusive.ConnectedComponent := by
                rw [Matrix.rank_transpose]
      _ = Fintype.card V := hsum
  have hcomp :
      Nat.card D.toSimpleGraphInclusive.ConnectedComponent =
        @Fintype.card D.toSimpleGraphInclusive.ConnectedComponent SetLike.instFintype := by
    exact
      @Nat.card_eq_fintype_card D.toSimpleGraphInclusive.ConnectedComponent SetLike.instFintype
  have hrank_nat :
      (D.incidenceMatrix).rank =
        Fintype.card V - Nat.card D.toSimpleGraphInclusive.ConnectedComponent := by
    exact Nat.eq_sub_of_add_eq hsum'
  -- Solve the resulting additive cardinality identity for the rank term.
  exact hrank_nat.trans (congrArg (fun n ↦ Fintype.card V - n) hcomp)

end Digraph
