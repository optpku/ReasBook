/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_4.ch7_sec7_4_theorem_7_19
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_4.ch7_sec7_4_2_proposition_7_20

open SimpleGraph
open scoped BigOperators Matrix

attribute [local instance] Classical.propDecidable

noncomputable section

section Exercise718

variable {n k : ℕ}

/-- The `complete_graph_edges n` coordinates incident to the vertex `v`. This is the local
filter-view of the shared graph-level owner from Section 7.4. -/
private def completeGraphIncidentEdgeFinset (n : ℕ) (v : Fin n) :
    Finset (complete_graph_edges n) :=
  Finset.univ.filter fun e ↦ v ∈ (e : Sym2 (Fin n))

/-- The local filter-view of the complete-graph incident edges agrees with the reindexed
graph-level owner from Section 7.4. -/
private theorem completeGraphIncidentEdgeFinset_eq
    (n : ℕ) (v : Fin n) :
    completeGraphIncidentEdgeFinset n v =
      (incidentEdgeFinset (completeGraph (Fin n)) v).map
        completeGraphEdgeEquiv.symm.toEmbedding := by
    ext e
    simpa [completeGraphIncidentEdgeFinset] using
    (mem_completeGraph_incidentEdgeFinset_iff (i := v) (e := e)).symm

/-- Membership in the local complete-graph incident-edge finset means that `v` is an endpoint of
the edge coordinate. -/
private theorem mem_completeGraphIncidentEdgeFinset_iff
    {n : ℕ} {v : Fin n} {e : complete_graph_edges n} :
    e ∈ completeGraphIncidentEdgeFinset n v ↔ v ∈ (e : Sym2 (Fin n)) := by
  simp [completeGraphIncidentEdgeFinset]

/-- Helper for Exercise 7.18: the family `S₀, …, S_k` attached to a comb, with `S₀ = handle`
and `S_{i+1} = teeth i`. -/
def comb_sets (handle : Finset (Fin n)) (teeth : Fin k → Finset (Fin n)) :
    Fin (k + 1) → Finset (Fin n) :=
  Fin.cases handle teeth

/-- Helper for Exercise 7.18: the internal edges of the complete graph induced by `S`, recorded
in the `complete_graph_edges n` coordinates. -/
def induced_edge_finset {n : ℕ} (S : Finset (Fin n)) : Finset (complete_graph_edges n) :=
  Finset.univ.filter fun e ↦ completeGraphEdge e ∈ E[completeGraph (Fin n)] (S : Set (Fin n))

/-- Summing `subtour_elimination_value` over `comb_sets handle teeth` splits into the handle cut
and the tooth cuts. -/
theorem sum_subtour_elimination_value_comb_sets_eq
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (x : complete_graph_edges n → ℝ) :
    (∑ i : Fin (k + 1), subtour_elimination_value (comb_sets handle teeth i) x) =
      subtour_elimination_value handle x + ∑ i : Fin k, subtour_elimination_value (teeth i) x :=
  by
    -- Split the `Fin (k + 1)` sum into the `0` term and the successor terms.
    simpa [comb_sets, Fin.sum_univ_succ, add_comm, add_left_comm,
      add_assoc]

/-- Helper for Exercise 7.18: a complete-graph sum with an indicator `if` rewrites to the sum
over the filtered edge finset. -/
lemma complete_graph_sum_ite_eq_sum_filter
    (p : complete_graph_edges n → Prop) [DecidablePred p]
    (f : complete_graph_edges n → ℝ) :
    (∑ e : complete_graph_edges n, (if p e then f e else 0)) = (Finset.univ.filter p).sum f := by
  -- Rewrite the filtered sum into the corresponding `if`-sum over `Finset.univ`.
  rw [Finset.sum_filter]

/-- Helper for Exercise 7.18: evaluating the comb coefficient against `x` splits into the
induced-edge sum on the handle plus the induced-edge sums on the teeth. -/
lemma comb_coefficient_dot_eq_handle_teeth_induced_edge_sums
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (x : complete_graph_edges n → ℝ) :
    comb_coefficient handle teeth ⬝ᵥ x =
      Finset.sum (induced_edge_finset handle) x +
        ∑ i : Fin k, Finset.sum (induced_edge_finset (teeth i)) x := by
  -- Expand the dot product and separate the handle contribution from the tooth contributions.
  calc
    comb_coefficient handle teeth ⬝ᵥ x =
        (∑ e : complete_graph_edges n,
          if e ∈ induced_edge_finset handle then x e else 0) +
          ∑ i : Fin k, ∑ e : complete_graph_edges n,
            if e ∈ induced_edge_finset (teeth i) then x e else 0 := by
          simp_rw [dotProduct, comb_coefficient, add_mul, Finset.sum_add_distrib, Finset.sum_mul,
            ite_mul, one_mul, zero_mul, induced_edge_finset, Finset.mem_filter, Finset.mem_univ,
            true_and]
          rw [Finset.sum_comm]
    _ = Finset.sum (induced_edge_finset handle) x +
          ∑ i : Fin k, Finset.sum (induced_edge_finset (teeth i)) x := by
          congr 1
          · simpa using
              (complete_graph_sum_ite_eq_sum_filter
                (p := fun e : complete_graph_edges n ↦ e ∈ induced_edge_finset handle)
                (f := x))
          · refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using
              (complete_graph_sum_ite_eq_sum_filter
                (p := fun e : complete_graph_edges n ↦ e ∈ induced_edge_finset (teeth i))
                (f := x))

/-- Helper for Exercise 7.18: filtering the vertices of `S` that lie on an edge agrees with
filtering the edge-endpoint finset by membership in `S`. -/
lemma complete_graph_edge_filter_eq_endpoint_filter
    (S : Finset (Fin n))
    (e : complete_graph_edges n) :
    S.filter (fun v ↦ v ∈ (e : Sym2 (Fin n))) =
      ((e : Sym2 (Fin n)).toFinset.filter fun v ↦ v ∈ (S : Set (Fin n))) := by
  -- Both filters record the same condition: `v` is both in `S` and an endpoint of `e`.
  ext v
  simp [Sym2.mem_toFinset, and_comm]

/-- Helper for Exercise 7.18: membership in `induced_edge_finset S` is exactly the condition that
both concrete endpoints of `e` lie in `S`. -/
lemma mem_induced_edge_finset_iff
    (S : Finset (Fin n))
    (e : complete_graph_edges n) :
    e ∈ induced_edge_finset S ↔
      e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S := by
  have hneq : e.1.out.1 ≠ e.1.out.2 := by
    intro hout_eq
    apply e.2
    rw [← e.1.out_eq, Sym2.mk_isDiag_iff]
    exact hout_eq
  rw [induced_edge_finset, Finset.mem_filter]
  constructor
  · intro he
    rw [SimpleGraph.mem_inducedEdgeFinset_iff, completeGraphEdge_coe, ← e.1.out_eq,
      SimpleGraph.Subgraph.mem_edgeSet] at he
    simpa [SimpleGraph.Subgraph.induce, hneq] using he.2
  · intro he
    refine ⟨by simp, ?_⟩
    rw [SimpleGraph.mem_inducedEdgeFinset_iff, completeGraphEdge_coe, ← e.1.out_eq,
      SimpleGraph.Subgraph.mem_edgeSet]
    simpa [SimpleGraph.Subgraph.induce, hneq] using he

/-- Helper for Exercise 7.18: an edge induced by `S` cannot simultaneously belong to `δ(S)`. -/
lemma not_mem_edge_boundary_finset_of_mem_induced
    (S : Finset (Fin n))
    (e : complete_graph_edges n)
    (he : e ∈ induced_edge_finset S) :
    e ∉ δ(S) := by
  -- The cut `δ(S)` requires exactly one endpoint in `S`, while an induced edge has both endpoints
  -- in `S`.
  rw [mem_induced_edge_finset_iff] at he
  intro hcut
  rcases (mem_edge_boundary_finset_iff_out_endpoints S e).1 hcut with
    (⟨_, h₂⟩ | ⟨_, h₁⟩)
  · exact h₂ he.2
  · exact h₁ he.1

/-- Helper for Exercise 7.18: filtering the two endpoints `{a, b}` by membership in `S` has
cardinality `2`, `1`, or `0` according to how many endpoints lie in `S`. -/
lemma exercise_7_18_pair_filter_card_of_ne
    (a b : Fin n)
    (hab : a ≠ b)
    (S : Finset (Fin n)) :
    (((({a, b} : Finset (Fin n)).filter fun v ↦ v ∈ (S : Set (Fin n))).card : ℕ) : ℝ) =
      if a ∈ (S : Set (Fin n)) ∧ b ∈ (S : Set (Fin n)) then 2
      else if a ∈ (S : Set (Fin n)) ∨ b ∈ (S : Set (Fin n)) then 1 else 0 := by
  -- Compute the filtered two-point finset by the four endpoint-membership cases.
  by_cases ha : a ∈ (S : Set (Fin n))
  · by_cases hb : b ∈ (S : Set (Fin n))
    · have hfilter :
          ({a, b} : Finset (Fin n)).filter (fun v ↦ v ∈ (S : Set (Fin n))) = {a, b} := by
        -- When both endpoints lie in `S`, the filter keeps the whole two-point finset.
        ext v
        constructor
        · intro hv
          exact (Finset.mem_filter.mp hv).1
        · intro hv
          refine Finset.mem_filter.mpr ⟨hv, ?_⟩
          rcases Finset.mem_insert.mp hv with rfl | hv'
          · simpa [ha]
          · rw [Finset.mem_singleton.mp hv']
            simpa [hb]
      rw [hfilter]
      simp [ha, hb, hab]
    · have hfilter :
          ({a, b} : Finset (Fin n)).filter (fun v ↦ v ∈ (S : Set (Fin n))) = {a} := by
        -- When only `a` lies in `S`, the filter keeps exactly the singleton `{a}`.
        ext v
        constructor
        · intro hv
          rcases Finset.mem_filter.mp hv with ⟨hv, hvS⟩
          rcases Finset.mem_insert.mp hv with rfl | hv'
          · simp
          · exfalso
            rw [Finset.mem_singleton.mp hv'] at hvS
            exact hb hvS
        · intro hv
          rcases Finset.mem_singleton.mp hv with rfl
          refine Finset.mem_filter.mpr ⟨?_, ?_⟩
          · simp
          · simpa using ha
      rw [hfilter]
      simp [ha, hb]
  · by_cases hb : b ∈ (S : Set (Fin n))
    · have hfilter :
          ({a, b} : Finset (Fin n)).filter (fun v ↦ v ∈ (S : Set (Fin n))) = {b} := by
        -- When only `b` lies in `S`, the filter keeps exactly the singleton `{b}`.
        ext v
        constructor
        · intro hv
          rcases Finset.mem_filter.mp hv with ⟨hv, hvS⟩
          rcases Finset.mem_insert.mp hv with hv' | hvb
          · exfalso
            exact ha (hv' ▸ hvS)
          · simpa using hvb
        · intro hv
          rcases Finset.mem_singleton.mp hv with rfl
          refine Finset.mem_filter.mpr ⟨?_, ?_⟩
          · simp [hab]
          · simpa using hb
      rw [hfilter]
      simp [ha, hb]
    · have hfilter :
          ({a, b} : Finset (Fin n)).filter (fun v ↦ v ∈ (S : Set (Fin n))) = ∅ := by
        -- When neither endpoint lies in `S`, the filtered endpoint set is empty.
        ext v
        constructor
        · intro hv
          rcases Finset.mem_filter.mp hv with ⟨hv, hvS⟩
          rcases Finset.mem_insert.mp hv with rfl | hv'
          · exact (ha hvS).elim
          · exact (hb (by rw [Finset.mem_singleton.mp hv'] at hvS; exact hvS)).elim
        · intro hv
          simpa using hv
      rw [hfilter]
      simp [ha, hb]

/-- Helper for Exercise 7.18: the endpoint finset of a complete-graph edge is the unordered pair
of its two `Sym2.out` endpoints. -/
lemma complete_graph_edge_toFinset_eq_pair
    (e : complete_graph_edges n) :
    ((e : Sym2 (Fin n)).toFinset) = {e.1.out.1, e.1.out.2} := by
  -- Rewrite the underlying `Sym2` edge by its canonical `out` representative.
  calc
    ((e : Sym2 (Fin n)).toFinset) = (s(e.1.out.1, e.1.out.2)).toFinset := by
      simpa [e.1.out_eq]
    _ = {e.1.out.1, e.1.out.2} := Sym2.toFinset_mk_eq

/-- Helper for Exercise 7.18: the filtered endpoint finset of an edge has cardinality `2` for an
induced edge, `1` for a cut edge, and `0` otherwise. -/
lemma endpoint_filter_card_eq_induced_or_cut
    (S : Finset (Fin n))
    (e : complete_graph_edges n) :
    (((e : Sym2 (Fin n)).toFinset.filter fun v ↦ v ∈ (S : Set (Fin n))).card : ℝ) =
      if e ∈ induced_edge_finset S then 2
      else if e ∈ δ(S) then 1 else 0 := by
  -- Route correction: first compute the filtered two-endpoint card, then translate the endpoint
  -- membership cases into the induced-versus-cut trichotomy.
  have hout_ne : e.1.out.1 ≠ e.1.out.2 := by
    -- A complete-graph edge is non-diagonal, so its extracted endpoints are distinct.
    intro hout_eq
    apply e.2
    rw [← e.1.out_eq, Sym2.mk_isDiag_iff]
    exact hout_eq
  rw [complete_graph_edge_toFinset_eq_pair]
  rw [exercise_7_18_pair_filter_card_of_ne (a := e.1.out.1) (b := e.1.out.2) (hab := hout_ne)
    (S := S)]
  -- Finish by the four endpoint-membership cases for the concrete `Sym2.out` endpoints.
  by_cases hfst : e.1.out.1 ∈ S
  · by_cases hsnd : e.1.out.2 ∈ S
    · have hind : e ∈ induced_edge_finset S := (mem_induced_edge_finset_iff S e).2 ⟨hfst, hsnd⟩
      have hnotcut : e ∉ δ(S) := not_mem_edge_boundary_finset_of_mem_induced S e hind
      simp [hfst, hsnd, hind, hnotcut]
    · have hnotind : e ∉ induced_edge_finset S := by
        intro hind
        exact hsnd ((mem_induced_edge_finset_iff S e).1 hind).2
      have hcut : e ∈ δ(S) := by
        exact (mem_edge_boundary_finset_iff_out_endpoints S e).2 (Or.inl ⟨hfst, hsnd⟩)
      simp [hfst, hsnd, hnotind, hcut]
  · by_cases hsnd : e.1.out.2 ∈ S
    · have hnotind : e ∉ induced_edge_finset S := by
        intro hind
        exact hfst ((mem_induced_edge_finset_iff S e).1 hind).1
      have hcut : e ∈ δ(S) := by
        exact (mem_edge_boundary_finset_iff_out_endpoints S e).2 (Or.inr ⟨hsnd, hfst⟩)
      simp [hfst, hsnd, hnotind, hcut]
    · have hnotind : e ∉ induced_edge_finset S := by
        intro hind
        exact hfst ((mem_induced_edge_finset_iff S e).1 hind).1
      have hnotcut : e ∉ δ(S) := by
        intro hcut
        rcases (mem_edge_boundary_finset_iff_out_endpoints S e).1 hcut with
          (⟨h₁, _⟩ | ⟨h₂, _⟩)
        · exact hfst h₁
        · exact hsnd h₂
      simp [hfst, hsnd, hnotind, hnotcut]

/-- Helper for Exercise 7.18: the contribution of one edge to the summed degree equations on `S`
is `2 x_e` for an induced edge, `x_e` for a cut edge, and `0` otherwise. -/
lemma endpoint_contribution_eq_induced_and_cut
    (S : Finset (Fin n))
    (e : complete_graph_edges n)
    (x : complete_graph_edges n → ℝ) :
    Finset.sum S (fun v ↦ if v ∈ (e : Sym2 (Fin n)) then x e else 0) =
      (if e ∈ induced_edge_finset S then 2 * x e else 0) +
        if e ∈ δ(S) then x e else 0 := by
  -- Rewrite the vertex sum as a constant sum over the filtered endpoint finset of `e`.
  calc
    Finset.sum S (fun v ↦ if v ∈ (e : Sym2 (Fin n)) then x e else 0) =
        Finset.sum (S.filter fun v ↦ v ∈ (e : Sym2 (Fin n))) (fun _ ↦ x e) := by
          rw [Finset.sum_filter]
    _ = Finset.sum (((e : Sym2 (Fin n)).toFinset.filter fun v ↦ v ∈ (S : Set (Fin n))))
          (fun _ ↦ x e) := by
            rw [complete_graph_edge_filter_eq_endpoint_filter]
    _ = ((((e : Sym2 (Fin n)).toFinset.filter fun v ↦ v ∈ (S : Set (Fin n))).card : ℝ) * x e) := by
          simp [Finset.sum_const, mul_comm, mul_left_comm, mul_assoc]
    _ = (if e ∈ induced_edge_finset S then 2 * x e else 0) +
          if e ∈ δ(S) then x e else 0 := by
            rw [endpoint_filter_card_eq_induced_or_cut]
            by_cases hind : e ∈ induced_edge_finset S
            · have hnotcut : e ∉ δ(S) := not_mem_edge_boundary_finset_of_mem_induced S e hind
              simp [hind, hnotcut]
            · by_cases hcut : e ∈ δ(S)
              · simp [hind, hcut]
              · simp [hind, hcut]

/-- Helper for Exercise 7.18: summing the degree equations on a vertex set counts each induced
edge twice and each cut edge once. -/
private lemma sum_incident_edges_on_set_eq_twice_induced_edges_add_subtour
    (S : Finset (Fin n))
    (x : complete_graph_edges n → ℝ) :
    Finset.sum S (fun v ↦ (completeGraphIncidentEdgeFinset n v).sum x) =
      2 * Finset.sum (induced_edge_finset S) x +
        subtour_elimination_value S x := by
  -- Rewrite each degree sum as a complete-graph `if`-sum, then swap the vertex and edge sums.
  calc
    Finset.sum S (fun v ↦ (completeGraphIncidentEdgeFinset n v).sum x) =
        Finset.sum S (fun v ↦
          (Finset.univ : Finset (complete_graph_edges n)).sum
            (fun e ↦ if v ∈ (e : Sym2 (Fin n)) then x e else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro v hv
          calc
            (completeGraphIncidentEdgeFinset n v).sum x =
                (Finset.univ : Finset (complete_graph_edges n)).sum
                  (fun e ↦ if e ∈ completeGraphIncidentEdgeFinset n v then x e else 0) := by
                  simpa using
                    (complete_graph_sum_ite_eq_sum_filter
                      (p := fun e : complete_graph_edges n ↦
                        e ∈ completeGraphIncidentEdgeFinset n v)
                      (f := x)).symm
            _ = (Finset.univ : Finset (complete_graph_edges n)).sum
                  (fun e ↦ if v ∈ (e : Sym2 (Fin n)) then x e else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro e he
                  by_cases h : e ∈ completeGraphIncidentEdgeFinset n v
                  · have hv : v ∈ (e : Sym2 (Fin n)) :=
                      (mem_completeGraphIncidentEdgeFinset_iff (v := v) (e := e)).1 h
                    simp [h, hv]
                  · have hv : v ∉ (e : Sym2 (Fin n)) := by
                      intro hv
                      exact h ((mem_completeGraphIncidentEdgeFinset_iff (v := v) (e := e)).2 hv)
                    simp [h, hv]
    _ = (Finset.univ : Finset (complete_graph_edges n)).sum
          (fun e ↦ Finset.sum S (fun v ↦ if v ∈ (e : Sym2 (Fin n)) then x e else 0)) := by
          -- Swap the vertex and edge sums before classifying each edge contribution.
          rw [Finset.sum_comm]
    _ = ∑ e : complete_graph_edges n,
          ((if e ∈ induced_edge_finset S then 2 * x e else 0) + if e ∈ δ(S) then x e else 0) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          simpa using endpoint_contribution_eq_induced_and_cut (S := S) (e := e) (x := x)
    _ = (Finset.univ.filter fun e : complete_graph_edges n ↦ e ∈ induced_edge_finset S).sum
          (fun e ↦ 2 * x e) +
          (Finset.univ.filter fun e : complete_graph_edges n ↦ e ∈ δ(S)).sum x := by
          rw [Finset.sum_add_distrib]
          congr 1
          · exact complete_graph_sum_ite_eq_sum_filter
              (p := fun e : complete_graph_edges n ↦ e ∈ induced_edge_finset S)
              (f := fun e ↦ 2 * x e)
          · exact complete_graph_sum_ite_eq_sum_filter
              (p := fun e : complete_graph_edges n ↦ e ∈ δ(S))
              (f := x)
    _ = (induced_edge_finset S).sum (fun e ↦ 2 * x e) +
          (δ(S)).sum x := by
          simp [induced_edge_finset]
    _ = 2 * Finset.sum (induced_edge_finset S) x +
          subtour_elimination_value S x := by
          rw [← Finset.mul_sum, subtour_elimination_value_eq]

/-- Helper for Exercise 7.18: the degree equations rewrite the induced-edge sum on a set as its
cardinality minus one half of the cut-value. -/
private lemma induced_edge_sum_eq_card_sub_half_subtour
    (S : Finset (Fin n))
    {x : complete_graph_edges n → ℝ}
    (hx_degree : x ∈ travelingSalesmanDegreeConstraintSet n) :
    Finset.sum (induced_edge_finset S) x =
      (S.card : ℝ) - subtour_elimination_value S x / 2 := by
  -- Sum the degree equations over `S`, rewrite the left-hand side by double counting, and solve
  -- the resulting linear identity for the induced-edge sum.
  have hx_degree' := mem_travelingSalesmanDegreeConstraintSet_iff.mp hx_degree
  have hdegree_sum :
      Finset.sum S (fun v ↦ (completeGraphIncidentEdgeFinset n v).sum x) = 2 * (S.card : ℝ) := by
    calc
      Finset.sum S (fun v ↦ (completeGraphIncidentEdgeFinset n v).sum x) = ∑ v ∈ S, (2 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simpa [completeGraphIncidentEdgeFinset_eq] using hx_degree' v
      _ = 2 * (S.card : ℝ) := by
            simp [two_mul, mul_comm, mul_left_comm, mul_assoc]
  have hcount := sum_incident_edges_on_set_eq_twice_induced_edges_add_subtour (S := S) (x := x)
  linarith

/-- Exercise 7.18. For edge-vectors satisfying the traveling-salesman degree equations and an odd
number of teeth, the comb inequality (7.23) is equivalent to the cut-sum form
`∑_{i=0}^k ∑_{e ∈ δ(S_i)} x_e ≥ 3k + 1`, where `S₀ = handle` and `S_{i+1} = teeth i`. -/
theorem exercise_7_18_comb_inequality_iff_cut_sum_form
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (hk : Odd k)
    {x : complete_graph_edges n → ℝ}
    (hx_degree : x ∈ travelingSalesmanDegreeConstraintSet n) :
    comb_coefficient handle teeth ⬝ᵥ x ≤ comb_rhs handle teeth ↔
      ∑ i : Fin (k + 1), subtour_elimination_value (comb_sets handle teeth i) x ≥
        (3 * k + 1 : ℝ) := by
  -- Rewrite the comb coefficient into induced-edge sums, then use the source-facing Chapter 7.19
  -- cut owner `δ(S)` and `subtour_elimination_value`.
  have hhandle :
      Finset.sum (induced_edge_finset handle) x =
        (handle.card : ℝ) - subtour_elimination_value handle x / 2 :=
    induced_edge_sum_eq_card_sub_half_subtour handle hx_degree
  have hteeth :
      ∀ i : Fin k,
        Finset.sum (induced_edge_finset (teeth i)) x =
          ((teeth i).card : ℝ) - subtour_elimination_value (teeth i) x / 2 := by
    intro i
    exact induced_edge_sum_eq_card_sub_half_subtour (teeth i) hx_degree
  have hsum_teeth :
      (∑ i : Fin k, Finset.sum (induced_edge_finset (teeth i)) x) =
        (∑ i : Fin k, ((teeth i).card : ℝ)) -
          ∑ i : Fin k, subtour_elimination_value (teeth i) x / 2 := by
    -- Rewrite each tooth contribution and then separate the card and cut sums.
    calc
      (∑ i : Fin k, Finset.sum (induced_edge_finset (teeth i)) x) =
          ∑ i : Fin k, (((teeth i).card : ℝ) - subtour_elimination_value (teeth i) x / 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using hteeth i
      _ = (∑ i : Fin k, ((teeth i).card : ℝ)) -
            ∑ i : Fin k, subtour_elimination_value (teeth i) x / 2 := by
            rw [Finset.sum_sub_distrib]
  have hcuts :
      subtour_elimination_value handle x + ∑ i : Fin k, subtour_elimination_value (teeth i) x =
        ∑ i : Fin (k + 1), subtour_elimination_value (comb_sets handle teeth i) x := by
    simpa using (sum_subtour_elimination_value_comb_sets_eq handle teeth x).symm
  have hhalf_sum :
      subtour_elimination_value handle x / 2 +
          ∑ i : Fin k, subtour_elimination_value (teeth i) x / 2 =
        (subtour_elimination_value handle x +
            ∑ i : Fin k, subtour_elimination_value (teeth i) x) / 2 := by
    -- Pull the common factor `1 / 2` out of the handle term and the tooth sum.
    have htooth_half :
        (∑ i : Fin k, subtour_elimination_value (teeth i) x / 2) =
          (∑ i : Fin k, subtour_elimination_value (teeth i) x) / 2 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]
    rw [htooth_half]
    ring
  have hk_even : Even (3 * k + 1) := by
    rcases hk with ⟨m, hm⟩
    refine ⟨3 * m + 2, ?_⟩
    omega
  have hhalf_rhs :
      (((((3 : ℕ) * k + 1) / 2 : ℕ) : ℝ)) = (3 * k + 1 : ℝ) / 2 := by
    rcases hk_even with ⟨m, hm⟩
    have hdiv : (((3 : ℕ) * k + 1) / 2 : ℕ) = m := by
      omega
    calc
      (((((3 : ℕ) * k + 1) / 2 : ℕ) : ℝ)) = (m : ℝ) := by
        exact_mod_cast hdiv
      _ = (3 * k + 1 : ℝ) / 2 := by
        have hm_real : (3 * k + 1 : ℝ) = m + m := by
          exact_mod_cast hm
        linarith
  have hrewritten :
      comb_coefficient handle teeth ⬝ᵥ x =
        (handle.card : ℝ) + (∑ i : Fin k, ((teeth i).card : ℝ)) -
          (subtour_elimination_value handle x +
            ∑ i : Fin k, subtour_elimination_value (teeth i) x) / 2 := by
    -- Rewrite the comb coefficient into induced-edge sums, then replace those sums by the degree
    -- equation formula on the handle and each tooth.
    calc
      comb_coefficient handle teeth ⬝ᵥ x =
          Finset.sum (induced_edge_finset handle) x +
            ∑ i : Fin k, Finset.sum (induced_edge_finset (teeth i)) x := by
              simpa using comb_coefficient_dot_eq_handle_teeth_induced_edge_sums handle teeth x
      _ = ((handle.card : ℝ) - subtour_elimination_value handle x / 2) +
            ((∑ i : Fin k, ((teeth i).card : ℝ)) -
              ∑ i : Fin k, subtour_elimination_value (teeth i) x / 2) := by
              rw [hhandle, hsum_teeth]
      _ = (handle.card : ℝ) + (∑ i : Fin k, ((teeth i).card : ℝ)) -
            (subtour_elimination_value handle x +
              ∑ i : Fin k, subtour_elimination_value (teeth i) x) / 2 := by
              linarith [hhalf_sum]
  -- Both inequalities are now the same linear inequality after collecting the cut terms.
  constructor
  · intro hineq
    rw [hrewritten, comb_rhs] at hineq
    have htarget :
        ∑ i : Fin (k + 1), subtour_elimination_value (comb_sets handle teeth i) x ≥
          (3 * k + 1 : ℝ) := by
      rw [← hcuts]
      linarith [hineq, hhalf_rhs]
    exact htarget
  · intro hcut
    rw [hrewritten, comb_rhs]
    rw [← hcuts] at hcut
    linarith [hcut, hhalf_rhs]

end Exercise718

end
