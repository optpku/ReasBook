/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_theorem_2_3.LinearFunctional
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_example_3_36
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4.ch4_sec4_4_corollary_4_19
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_4.ch7_sec7_4_theorem_7_18

open SimpleGraph
open scoped BigOperators Matrix

noncomputable section

attribute [local instance] Classical.propDecidable

-- This file keeps only the comb-specific source-facing layer, reusing the Chapter 3 owner
-- `is_valid_inequality`, the Chapter 4 complete-graph induced-edge owner `E[G]`, and the
-- Section 7.4 traveling-salesman owners.

section Proposition720

variable {n k : ℕ}

/-- `IsComb handle teeth` records the standard comb hypotheses for the handle `handle` and the
teeth `teeth 0, ..., teeth (k - 1)`. -/
@[mk_iff isComb_iff]
class IsComb (handle : Finset (Fin n)) (teeth : Fin k → Finset (Fin n)) : Prop where
  /-- A comb has an odd number of teeth. -/
  odd_card : Odd k
  /-- A comb has at least three teeth. -/
  three_le_card : 3 ≤ k
  /-- Distinct teeth are disjoint. -/
  pairwise_disjoint : Pairwise fun i j ↦ Disjoint (teeth i) (teeth j)
  /-- Each tooth meets the handle. -/
  inter_nonempty : ∀ i : Fin k, (teeth i ∩ handle).Nonempty
  /-- Each tooth also has a vertex outside the handle. -/
  diff_nonempty : ∀ i : Fin k, (teeth i \ handle).Nonempty

/-- The coefficient of the comb inequality on the edge `e`: one copy for the handle and one copy
for each tooth whose induced subgraph in the complete graph contains `e`. -/
def comb_coefficient (handle : Finset (Fin n)) (teeth : Fin k → Finset (Fin n)) :
    complete_graph_edges n → ℝ :=
  fun e ↦
    (if completeGraphEdge e ∈ E[completeGraph (Fin n)] (handle : Set (Fin n)) then (1 : ℝ)
      else 0) +
      ∑ i : Fin k,
        if completeGraphEdge e ∈ E[completeGraph (Fin n)] (teeth i : Set (Fin n)) then (1 : ℝ)
        else 0

/-- Evaluating the comb coefficient at `e` gives one copy from the handle and one copy from each
tooth that induces `e`. -/
theorem comb_coefficient_apply
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (e : complete_graph_edges n) :
    comb_coefficient handle teeth e =
      (if completeGraphEdge e ∈ E[completeGraph (Fin n)] (handle : Set (Fin n)) then (1 : ℝ)
        else 0) +
        ∑ i : Fin k,
          if completeGraphEdge e ∈ E[completeGraph (Fin n)] (teeth i : Set (Fin n))
          then (1 : ℝ) else 0 := by
  rfl

/-- The right-hand side of the comb inequality (7.23). -/
def comb_rhs (handle : Finset (Fin n)) (teeth : Fin k → Finset (Fin n)) : ℝ :=
  (handle.card : ℝ) + ∑ i : Fin k, ((teeth i).card : ℝ) -
    ((((3 : ℕ) * k + 1) / 2 : ℕ) : ℝ)

/-- Helper for Proposition 7.20: the complete-graph boundary owner `δ(S)` on the
`complete_graph_edges n` coordinates. -/
private abbrev edge_boundary_finset {n : ℕ} (S : Finset (Fin n)) :
    Finset (complete_graph_edges n) :=
  Finset.univ.filter
    fun e ↦ completeGraphEdge e ∈ δ[completeGraph (Fin n)] (S : Set (Fin n))

local notation "δ(" S ")" => edge_boundary_finset S

/-- Helper for Proposition 7.20: the local cut owner `δ(S)` is the complete-graph cut-edge
finset specialized to `Fin n`. -/
private theorem mem_edge_boundary_finset_iff_mem_cutEdgeFinset
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    e ∈ δ(S) ↔ completeGraphEdge e ∈ δ[completeGraph (Fin n)] (S : Set (Fin n)) := by
  -- This is exactly the defining filter condition for the local boundary owner.
  simp [edge_boundary_finset]

/-- Helper for Proposition 7.20: membership in `δ(S)` means that one endpoint lies in `S` and the
other lies outside `S`. -/
private theorem mem_edge_boundary_finset_iff_mixed_endpoints
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    e ∈ δ(S) ↔ ∃ u ∈ S, ∃ v ∉ S, s(u, v) = e.1 := by
  -- Reuse the complete-graph cut-edge characterization and rewrite the local edge coordinate.
  simpa [completeGraphEdge] using
    (mem_cutEdgeFinset_iff (completeGraph (Fin n)) :
      completeGraphEdge e ∈ δ[completeGraph (Fin n)] (S : Set (Fin n)) ↔
        ∃ u ∈ (S : Set (Fin n)), ∃ v ∉ (S : Set (Fin n)), s(u, v) = completeGraphEdge e)

/-- Helper for Proposition 7.20: membership in `δ(S)` is equivalent to the two canonical
`Sym2.out` endpoints of `e` lying on opposite sides of the cut. -/
private theorem mem_edge_boundary_finset_iff_out_endpoints
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    e ∈ δ(S) ↔
      (e.1.out.1 ∈ S ∧ e.1.out.2 ∉ S) ∨ (e.1.out.2 ∈ S ∧ e.1.out.1 ∉ S) := by
  constructor
  · intro he
    rcases (mem_edge_boundary_finset_iff_mixed_endpoints S e).1 he with ⟨u, hu, v, hv, huv⟩
    rw [← e.1.out_eq] at huv
    rw [Sym2.eq_iff] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hu, hv⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact (mem_edge_boundary_finset_iff_mixed_endpoints S e).2
        ⟨e.1.out.1, h₁, e.1.out.2, h₂, e.1.out_eq⟩
    · exact (mem_edge_boundary_finset_iff_mixed_endpoints S e).2
        ⟨e.1.out.2, h₁, e.1.out.1, h₂, Sym2.eq_swap.trans e.1.out_eq⟩

/-- Helper for Proposition 7.20: the cut-incidence vector of `S` is the indicator of `δ(S)`. -/
private theorem mem_edge_boundary_finset_iff
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    e ∈ δ(S) ↔ cutIncidenceVector S e = 1 := by
  rw [mem_edge_boundary_finset_iff_out_endpoints]
  have hpair :
      cutIncidenceVector S e =
        if (e.1.out.1 ∈ S) = (e.1.out.2 ∈ S) then 0 else 1 := by
    simpa [e.1.out_eq] using
      (cutIncidenceVector_apply_pair S e.1.out.1 e.1.out.2 (by simpa [e.1.out_eq] using e.2))
  rw [hpair]
  by_cases h₁ : e.1.out.1 ∈ S
  · by_cases h₂ : e.1.out.2 ∈ S
    · simp [h₁, h₂]
    · simp [h₁, h₂]
  · by_cases h₂ : e.1.out.2 ∈ S
    · simp [h₁, h₂]
    · simp [h₁, h₂]

/-- Helper for Proposition 7.20: the subtour-elimination left-hand side attached to `S`. -/
private def subtour_elimination_value
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) : ℝ :=
  Finset.sum (δ(S)) x

/-- Helper for Proposition 7.20: every cut-incidence coordinate is either `0` or `1`. -/
private theorem cutIncidenceVector_eq_zero_or_one
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    cutIncidenceVector S e = 0 ∨ cutIncidenceVector S e = 1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h u v =>
      rw [cutIncidenceVector_apply_pair S u v he]
      by_cases huv : (u ∈ S) = (v ∈ S) <;> simp [huv]

/-- Helper for Proposition 7.20: the cut-incidence vector is the indicator of the local boundary
owner `δ(S)`. -/
private theorem cutIncidenceVector_eq_indicator_edge_boundary
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    cutIncidenceVector S e = if e ∈ δ(S) then 1 else 0 := by
  by_cases he : e ∈ δ(S)
  · simpa [he] using (mem_edge_boundary_finset_iff S e).mp he
  · rcases cutIncidenceVector_eq_zero_or_one S e with hzero | hone
    · simp [he, hzero]
    · exfalso
      exact he ((mem_edge_boundary_finset_iff S e).2 hone)

/-- Helper for Proposition 7.20: `subtour_elimination_value S x` is the sum of the coordinates of
`x` over the cut owner `δ(S)`. -/
private theorem subtour_elimination_value_eq
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) :
    subtour_elimination_value S x = Finset.sum (δ(S)) x :=
  rfl

/-- Helper for Proposition 7.20: the subtour-elimination sum is the dot product with the
cut-incidence vector of `S`. -/
private theorem subtour_elimination_value_eq_dotProduct
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) :
    subtour_elimination_value S x = cutIncidenceVector S ⬝ᵥ x := by
  symm
  calc
    cutIncidenceVector S ⬝ᵥ x
        = ∑ e : complete_graph_edges n, (if e ∈ δ(S) then 1 else 0) * x e := by
            simp [dotProduct, cutIncidenceVector_eq_indicator_edge_boundary]
    _ = Finset.sum (δ(S)) x := by
          calc
            ∑ e : complete_graph_edges n, (if e ∈ δ(S) then 1 else 0) * x e
                = ∑ e : complete_graph_edges n, if e ∈ δ(S) then x e else 0 := by
                    refine Finset.sum_congr rfl ?_
                    intro e he
                    by_cases hmem : e ∈ δ(S) <;> simp [hmem]
            _ = Finset.sum (δ(S)) x := by
                  have hfilter :
                      Finset.univ.filter
                          (fun e : complete_graph_edges n ↦ e ∈ δ(S)) = δ(S) := by
                    ext e
                    simp [edge_boundary_finset]
                  rw [← hfilter, Finset.sum_filter]
                  simp
    _ = subtour_elimination_value S x := by
          rw [subtour_elimination_value]

/-- Helper for Proposition 7.20: the complete-graph coordinates incident to `v`. -/
private def completeGraphIncidentEdgeFinset {n : ℕ} (v : Fin n) :
    Finset (complete_graph_edges n) :=
  Finset.univ.filter fun e ↦ v ∈ (e : Sym2 (Fin n))

/-- Helper for Proposition 7.20: the local incident-edge filter agrees with the shared
reindexed graph-level incident-edge owner. -/
private theorem completeGraphIncidentEdgeFinset_eq
    {n : ℕ} (v : Fin n) :
    completeGraphIncidentEdgeFinset v =
      (incidentEdgeFinset (completeGraph (Fin n)) v).map
        completeGraphEdgeEquiv.symm.toEmbedding := by
  -- Both finsets record exactly the complete-graph edge coordinates whose unordered pair contains
  -- `v`.
  ext e
  simpa [completeGraphIncidentEdgeFinset] using
    (mem_completeGraph_incidentEdgeFinset_iff (i := v) (e := e)).symm

/-- Helper for Proposition 7.20: membership in the local incident-edge owner means that `v`
is one endpoint of `e`. -/
private theorem mem_completeGraphIncidentEdgeFinset_iff
    {n : ℕ} {v : Fin n} {e : complete_graph_edges n} :
    e ∈ completeGraphIncidentEdgeFinset v ↔ v ∈ (e : Sym2 (Fin n)) := by
  -- This is just the defining filter condition.
  simp [completeGraphIncidentEdgeFinset]

/-- Helper for Proposition 7.20: the complete-graph edges induced by `S`, recorded in the
`complete_graph_edges n` coordinates. -/
private def induced_edge_finset {n : ℕ} (S : Finset (Fin n)) :
    Finset (complete_graph_edges n) :=
  Finset.univ.filter fun e ↦ completeGraphEdge e ∈ E[completeGraph (Fin n)] (S : Set (Fin n))

/-- Helper for Proposition 7.20: a complete-graph `if`-sum rewrites to the sum over the filtered
edge finset. -/
private theorem complete_graph_sum_ite_eq_sum_filter
    {n : ℕ}
    (p : complete_graph_edges n → Prop) [DecidablePred p]
    (f : complete_graph_edges n → ℝ) :
    (∑ e : complete_graph_edges n, if p e then f e else 0) = (Finset.univ.filter p).sum f := by
  -- This is the standard `Finset.sum_filter` normalization for the complete-graph coordinate
  -- universe.
  rw [Finset.sum_filter]

/-- Helper for Proposition 7.20: evaluating the comb coefficient against `x` splits into the
induced-edge sum on the handle plus the induced-edge sums on the teeth. -/
private theorem comb_coefficient_dot_eq_handle_teeth_induced_edge_sums
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (x : complete_graph_edges n → ℝ) :
    comb_coefficient handle teeth ⬝ᵥ x =
      Finset.sum (induced_edge_finset handle) x +
        ∑ i : Fin k, Finset.sum (induced_edge_finset (teeth i)) x := by
  -- Expand the dot product, then separate the handle contribution from the tooth contributions.
  calc
    comb_coefficient handle teeth ⬝ᵥ x =
        (∑ e : complete_graph_edges n, if e ∈ induced_edge_finset handle then x e else 0) +
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

/-- Helper for Proposition 7.20: membership in `induced_edge_finset S` means that both canonical
endpoints of `e` lie in `S`. -/
private theorem mem_induced_edge_finset_iff
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    e ∈ induced_edge_finset S ↔ e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S := by
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

/-- Helper for Proposition 7.20: an edge induced by `S` cannot lie in the cut `δ(S)`. -/
private theorem not_mem_edge_boundary_finset_of_mem_induced
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n)
    (he : e ∈ induced_edge_finset S) :
    e ∉ δ(S) := by
  -- A cut edge has exactly one endpoint in `S`, whereas an induced edge has both endpoints in `S`.
  rw [mem_induced_edge_finset_iff] at he
  intro hcut
  rcases (mem_edge_boundary_finset_iff_out_endpoints S e).1 hcut with
    (⟨_, h₂⟩ | ⟨_, h₁⟩)
  · exact h₂ he.2
  · exact h₁ he.1

/-- Helper for Proposition 7.20: filtering the vertices of `S` that lie on `e` agrees with
filtering the endpoint finset of `e` by membership in `S`. -/
private theorem complete_graph_edge_filter_eq_endpoint_filter
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    S.filter (fun v ↦ v ∈ (e : Sym2 (Fin n))) =
      ((e : Sym2 (Fin n)).toFinset.filter fun v ↦ v ∈ (S : Set (Fin n))) := by
  -- Both filters encode the same conjunction: `v` lies in `S` and is an endpoint of `e`.
  ext v
  simp [Sym2.mem_toFinset, and_comm]

/-- Helper for Proposition 7.20: filtering the unordered pair `{a, b}` by membership in `S`
has cardinality `2`, `1`, or `0` according to how many endpoints lie in `S`. -/
private theorem pair_filter_card_of_ne
    {n : ℕ}
    (a b : Fin n) (hab : a ≠ b)
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
        -- When only `a` lies in `S`, the filter keeps exactly `{a}`.
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
        -- When only `b` lies in `S`, the filter keeps exactly `{b}`.
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

/-- Helper for Proposition 7.20: the endpoint finset of `e` is the unordered pair of its
canonical `Sym2.out` endpoints. -/
private theorem complete_graph_edge_toFinset_eq_pair
    {n : ℕ} (e : complete_graph_edges n) :
    ((e : Sym2 (Fin n)).toFinset) = {e.1.out.1, e.1.out.2} := by
  -- Rewrite the underlying `Sym2` edge by its canonical `out` representative.
  calc
    ((e : Sym2 (Fin n)).toFinset) = (s(e.1.out.1, e.1.out.2)).toFinset := by
      simpa [e.1.out_eq]
    _ = {e.1.out.1, e.1.out.2} := Sym2.toFinset_mk_eq

/-- Helper for Proposition 7.20: the filtered endpoint finset of an edge has cardinality `2` for
an induced edge, `1` for a cut edge, and `0` otherwise. -/
private theorem endpoint_filter_card_eq_induced_or_cut
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    (((e : Sym2 (Fin n)).toFinset.filter fun v ↦ v ∈ (S : Set (Fin n))).card : ℝ) =
      if e ∈ induced_edge_finset S then 2
      else if e ∈ δ(S) then 1 else 0 := by
  -- Route correction: first compute the filtered two-endpoint cardinality, then translate the
  -- endpoint-membership cases into the induced-versus-cut trichotomy.
  have hout_ne : e.1.out.1 ≠ e.1.out.2 := by
    intro hout_eq
    apply e.2
    rw [← e.1.out_eq, Sym2.mk_isDiag_iff]
    exact hout_eq
  rw [complete_graph_edge_toFinset_eq_pair]
  rw [pair_filter_card_of_ne (a := e.1.out.1) (b := e.1.out.2) (hab := hout_ne) (S := S)]
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

/-- Helper for Proposition 7.20: the contribution of one edge to the summed degree equations on
`S` is `2 x_e` for an induced edge, `x_e` for a cut edge, and `0` otherwise. -/
private theorem endpoint_contribution_eq_induced_and_cut
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n)
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

/-- Helper for Proposition 7.20: summing the degree equations on a vertex set counts each induced
edge twice and each cut edge once. -/
private theorem sumIncidentEdgesOnSet_eq_twiceInducedEdges_add_subtour
    {n : ℕ} (S : Finset (Fin n))
    (x : complete_graph_edges n → ℝ) :
    Finset.sum S (fun v ↦ (completeGraphIncidentEdgeFinset v).sum x) =
      2 * Finset.sum (induced_edge_finset S) x + subtour_elimination_value S x := by
  -- Rewrite each degree sum as an `if`-sum over the complete-graph universe, then swap the
  -- vertex and edge sums.
  calc
    Finset.sum S (fun v ↦ (completeGraphIncidentEdgeFinset v).sum x) =
        Finset.sum S (fun v ↦
          (Finset.univ : Finset (complete_graph_edges n)).sum
            (fun e ↦ if v ∈ (e : Sym2 (Fin n)) then x e else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro v hv
          calc
            (completeGraphIncidentEdgeFinset v).sum x =
                (Finset.univ : Finset (complete_graph_edges n)).sum
                  (fun e ↦ if e ∈ completeGraphIncidentEdgeFinset v then x e else 0) := by
                  simpa using
                    (complete_graph_sum_ite_eq_sum_filter
                      (p := fun e : complete_graph_edges n ↦ e ∈ completeGraphIncidentEdgeFinset v)
                      (f := x)).symm
            _ = (Finset.univ : Finset (complete_graph_edges n)).sum
                  (fun e ↦ if v ∈ (e : Sym2 (Fin n)) then x e else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro e he
                  by_cases h : e ∈ completeGraphIncidentEdgeFinset v
                  · have hv' : v ∈ (e : Sym2 (Fin n)) :=
                      (mem_completeGraphIncidentEdgeFinset_iff (v := v) (e := e)).1 h
                    simp [h, hv']
                  · have hv' : v ∉ (e : Sym2 (Fin n)) := by
                      intro hv'
                      exact h ((mem_completeGraphIncidentEdgeFinset_iff (v := v) (e := e)).2 hv')
                    simp [h, hv']
    _ = (Finset.univ : Finset (complete_graph_edges n)).sum
          (fun e ↦ Finset.sum S (fun v ↦ if v ∈ (e : Sym2 (Fin n)) then x e else 0)) := by
          -- Swapping the vertex and edge sums isolates each edge contribution.
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
    _ = (induced_edge_finset S).sum (fun e ↦ 2 * x e) + (δ(S)).sum x := by
          simp [induced_edge_finset]
    _ = 2 * Finset.sum (induced_edge_finset S) x + subtour_elimination_value S x := by
          rw [← Finset.mul_sum, subtour_elimination_value_eq]

/-- Helper for Proposition 7.20: on the traveling-salesman degree slice, the induced-edge sum on
`S` is its cardinality minus one half of the cut value. -/
private theorem inducedEdgeSum_eq_card_sub_half_subtour
    {n : ℕ} (S : Finset (Fin n))
    {x : complete_graph_edges n → ℝ}
    (hx_degree : x ∈ travelingSalesmanDegreeConstraintSet n) :
    Finset.sum (induced_edge_finset S) x =
      (S.card : ℝ) - subtour_elimination_value S x / 2 := by
  -- Sum the degree equations over `S`, rewrite the left-hand side by double counting, and solve
  -- the resulting linear identity for the induced-edge sum.
  have hx_degree' := mem_travelingSalesmanDegreeConstraintSet_iff.mp hx_degree
  have hdegree_sum :
      Finset.sum S (fun v ↦ (completeGraphIncidentEdgeFinset v).sum x) = 2 * (S.card : ℝ) := by
    calc
      Finset.sum S (fun v ↦ (completeGraphIncidentEdgeFinset v).sum x) = ∑ v ∈ S, (2 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simpa [completeGraphIncidentEdgeFinset_eq] using hx_degree' v
      _ = 2 * (S.card : ℝ) := by
            simp [two_mul, mul_comm, mul_left_comm, mul_assoc]
  have hcount := sumIncidentEdgesOnSet_eq_twiceInducedEdges_add_subtour (S := S) (x := x)
  linarith

/-- Helper for Proposition 7.20: summing the Hamiltonian-tour indicator over any edge finset
counts exactly the tour edges lying in that finset. -/
private theorem edgeIndicatorSum_eq_card_inter_of_tour
    {n : ℕ} (T : Finset (complete_graph_edges n))
    (σ : Equiv.Perm (Fin n)) :
    T.sum (hamiltonian_tour_incidence_vector σ) =
      (((T ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) := by
  -- Rewrite the `0/1` tour indicator as the cardinality of the matching intersection.
  calc
    T.sum (hamiltonian_tour_incidence_vector σ) =
        T.sum (fun e ↦ if e ∈ hamiltonian_tour_edge_finset σ then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          simp [hamiltonian_tour_incidence_vector, is_hamiltonian_tour_edge]
    _ = (((T.filter fun e ↦ e ∈ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) := by
          rw [Finset.sum_boole]
    _ = (((T ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) := by
          have hfilter :
              T.filter (fun e ↦ e ∈ hamiltonian_tour_edge_finset σ) = T ∩ hamiltonian_tour_edge_finset σ := by
            ext e
            simp [Finset.mem_inter]
          rw [hfilter]

/-- Helper for Proposition 7.20: every Hamiltonian-tour vertex with `n ≥ 3` lies in the
traveling-salesman degree slice. -/
private theorem hamiltonianTourIncidenceVector_mem_degreeConstraintSet
    {n : ℕ} (hn : 3 ≤ n)
    (σ : Equiv.Perm (Fin n)) :
    hamiltonian_tour_incidence_vector σ ∈ travelingSalesmanDegreeConstraintSet n := by
  -- Move the Hamiltonian-tour vertex into the affine hull, then use the affine-span description
  -- from Section 7.18.
  have hx_poly :
      hamiltonian_tour_incidence_vector σ ∈ travelingSalesmanPolytope n := by
    rw [travelingSalesmanPolytope_eq_convexHull]
    exact subset_convexHull ℝ _ (Set.mem_range_self σ)
  have hx_aff :
      hamiltonian_tour_incidence_vector σ ∈ affineSpan ℝ (travelingSalesmanPolytope n) := by
    exact subset_affineSpan ℝ _ hx_poly
  have hspan :
      (affineSpan ℝ (travelingSalesmanPolytope n) : Set (complete_graph_edges n → ℝ)) =
        travelingSalesmanDegreeConstraintSet n := by
    simpa using affineSpan_travelingSalesmanPolytope_eq_degreeConstraintSet n hn
  rw [← hspan]
  exact hx_aff

/-- Helper for Proposition 7.20: on a Hamiltonian-tour vertex, the subtour value counts the
tour edges crossing `δ(S)`. -/
private theorem subtourEliminationValue_eq_cutCard
    {n : ℕ} (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) :
    subtour_elimination_value S (hamiltonian_tour_incidence_vector σ) =
      (((δ(S) ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) := by
  -- The generic tour-indicator/cardinality adapter closes the cut-count rewrite in one step.
  simpa [subtour_elimination_value_eq] using edgeIndicatorSum_eq_card_inter_of_tour (δ(S)) σ

/-- Helper for Proposition 7.20: on a Hamiltonian-tour vertex, the induced-edge sum counts the
tour edges whose endpoints both lie in `S`. -/
private theorem inducedEdgeSum_eq_inducedCard
    {n : ℕ} (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) :
    Finset.sum (induced_edge_finset S) (hamiltonian_tour_incidence_vector σ) =
      (((induced_edge_finset S ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) := by
  -- The same tour-indicator/cardinality adapter also rewrites the induced-edge sum directly.
  simpa using edgeIndicatorSum_eq_card_inter_of_tour (induced_edge_finset S) σ

/-- Helper for Proposition 7.20: every Hamiltonian-path edge also belongs to the corresponding
Hamiltonian tour once `n ≥ 2`. -/
private theorem hamiltonianPathEdge_mem_hamiltonianTourEdgeFinset
    {n : ℕ} (hn : 2 ≤ n)
    (σ : Equiv.Perm (Fin n))
    {e : complete_graph_edges n}
    (he : e ∈ hamiltonian_path_edge_finset σ) :
    e ∈ hamiltonian_tour_edge_finset σ := by
  -- For `n ≥ 2`, the Hamiltonian tour is the Hamiltonian path together with one closing edge.
  classical
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  have hm' : n = m + 2 := by omega
  rw [hm'] at he ⊢
  have he' :
      e ∈ (insert (hamiltonian_tour_closing_edge σ) (hamiltonian_path_edge_finset σ) :
        Finset (complete_graph_edges (m + 2))) :=
    Finset.mem_insert_of_mem he
  simpa [hamiltonian_tour_edge_finset] using he'

/-- Helper for Proposition 7.20: if a consecutive Hamiltonian-path edge does not cross `δ(S)`,
then its two endpoints lie on the same side of the cut. -/
private theorem pathEdgeOfIndex_not_mem_boundary_iff_same_side
    {n : ℕ} (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n))
    (k : Fin (n - 1))
    (hnot : path_edge_of_index σ k ∉ δ(S)) :
    σ ⟨k.1, by
        have hk : k.1 < n - 1 := k.2
        omega⟩ ∈ S ↔
      σ ⟨k.1 + 1, by
        have hk : k.1 < n - 1 := k.2
        omega⟩ ∈ S := by
  constructor
  · intro hleft
    by_contra hright
    exact hnot ((mem_edge_boundary_finset_iff_mixed_endpoints S (path_edge_of_index σ k)).2
      ⟨σ ⟨k.1, by
          have hk : k.1 < n - 1 := k.2
          omega⟩,
        hleft,
        σ ⟨k.1 + 1, by
            have hk : k.1 < n - 1 := k.2
            omega⟩,
        hright,
        rfl⟩)
  · intro hright
    by_contra hleft
    exact hnot ((mem_edge_boundary_finset_iff_mixed_endpoints S (path_edge_of_index σ k)).2
      ⟨σ ⟨k.1 + 1, by
            have hk : k.1 < n - 1 := k.2
            omega⟩,
        hright,
        σ ⟨k.1, by
            have hk : k.1 < n - 1 := k.2
            omega⟩,
        hleft,
        Sym2.eq_swap.trans rfl⟩)

/-- Helper for Proposition 7.20: a nonempty proper vertex set meets at least one Hamiltonian-tour
edge, so the tour cut count is positive. -/
private theorem hamiltonianTourCutCard_pos
    {n : ℕ} (hn : 2 ≤ n)
    (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n))
    (hS_nonempty : S.Nonempty)
    (hS_proper : S.card < n) :
    0 < (δ(S) ∩ hamiltonian_tour_edge_finset σ).card := by
  by_contra hzero
  have hzero' : (δ(S) ∩ hamiltonian_tour_edge_finset σ).card = 0 := Nat.eq_zero_of_not_pos hzero
  have hempty : δ(S) ∩ hamiltonian_tour_edge_finset σ = ∅ := Finset.card_eq_zero.mp hzero'
  let zero : Fin n := ⟨0, by omega⟩
  have hno_cut : ∀ k : Fin (n - 1), path_edge_of_index σ k ∉ δ(S) := by
    intro k hkcut
    have hpath :
        path_edge_of_index σ k ∈ hamiltonian_path_edge_finset σ := by
      simpa [is_hamiltonian_path_edge] using
        ((is_hamiltonian_path_edge_iff_exists_index σ (path_edge_of_index σ k)).2 ⟨k, rfl⟩)
    have htour :
        path_edge_of_index σ k ∈ hamiltonian_tour_edge_finset σ :=
      hamiltonianPathEdge_mem_hamiltonianTourEdgeFinset hn σ hpath
    have hmem :
        path_edge_of_index σ k ∈ δ(S) ∩ hamiltonian_tour_edge_finset σ := by
      simp [hkcut, htour]
    have : path_edge_of_index σ k ∈ (∅ : Finset (complete_graph_edges n)) := by
      simpa [hempty] using hmem
    simpa using this
  have hsame :
      ∀ m : ℕ, ∀ hm : m < n, σ ⟨m, hm⟩ ∈ S ↔ σ zero ∈ S := by
    intro m
    induction m with
    | zero =>
        intro hm
        simp [zero]
    | succ m ih =>
        intro hm
        have hm' : m < n := by omega
        let k : Fin (n - 1) := ⟨m, by omega⟩
        have hstep :
            σ ⟨m, hm'⟩ ∈ S ↔ σ ⟨m + 1, hm⟩ ∈ S :=
          pathEdgeOfIndex_not_mem_boundary_iff_same_side S σ k (hno_cut k)
        exact hstep.symm.trans (ih hm')
  rcases hS_nonempty with ⟨u, hu⟩
  have houtside : ∃ v : Fin n, v ∉ S := by
    by_contra houtside
    push_neg at houtside
    have hEq : S = Finset.univ := by
      ext v
      simp [houtside v]
    have hcard : S.card = n := by
      simpa [hEq]
    exact (Nat.ne_of_lt hS_proper) hcard
  rcases houtside with ⟨v, hv⟩
  have hzero_mem : σ zero ∈ S := by
    have hu' : σ ⟨(σ.symm u).1, (σ.symm u).2⟩ ∈ S := by simpa using hu
    exact (hsame (σ.symm u).1 (σ.symm u).2).mp hu'
  have hv' : σ ⟨(σ.symm v).1, (σ.symm v).2⟩ ∈ S := by
    exact (hsame (σ.symm v).1 (σ.symm v).2).mpr hzero_mem
  exact hv (by simpa using hv')

/-- Helper for Proposition 7.20: every Hamiltonian tour crosses the cut of a nonempty proper set
at least twice. -/
private theorem hamiltonianTourSubtourElimination_ge_two
    {n : ℕ} (hn : 3 ≤ n)
    (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n))
    (hS_nonempty : S.Nonempty)
    (hS_proper : S.card < n) :
    2 ≤ subtour_elimination_value S (hamiltonian_tour_incidence_vector σ) := by
  -- Rewrite the degree equations on `S`, then use the positive cut count to force at least two
  -- crossing tour edges.
  have hx_degree :
      hamiltonian_tour_incidence_vector σ ∈ travelingSalesmanDegreeConstraintSet n :=
    hamiltonianTourIncidenceVector_mem_degreeConstraintSet hn σ
  have hx_degree' := mem_travelingSalesmanDegreeConstraintSet_iff.mp hx_degree
  have hdegree_sum :
      Finset.sum S
          (fun v ↦
            (completeGraphIncidentEdgeFinset v).sum
              (hamiltonian_tour_incidence_vector σ)) =
        2 * (S.card : ℝ) := by
    calc
      Finset.sum S
          (fun v ↦
            (completeGraphIncidentEdgeFinset v).sum
              (hamiltonian_tour_incidence_vector σ)) =
          ∑ v ∈ S, (2 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simpa [completeGraphIncidentEdgeFinset_eq] using hx_degree' v
      _ = 2 * (S.card : ℝ) := by
            simp [two_mul, mul_comm, mul_left_comm, mul_assoc]
  have hcount :=
    sumIncidentEdgesOnSet_eq_twiceInducedEdges_add_subtour
      (S := S) (x := hamiltonian_tour_incidence_vector σ)
  rw [inducedEdgeSum_eq_inducedCard, subtourEliminationValue_eq_cutCard] at hcount
  have hcountCard :
      2 * (((induced_edge_finset S ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) +
          (((δ(S) ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) =
        2 * (S.card : ℝ) := by
    linarith
  have hcountNat :
      2 * (induced_edge_finset S ∩ hamiltonian_tour_edge_finset σ).card +
          (δ(S) ∩ hamiltonian_tour_edge_finset σ).card =
        2 * S.card := by
    exact_mod_cast hcountCard
  have hcutPos :
      0 < (δ(S) ∩ hamiltonian_tour_edge_finset σ).card :=
    hamiltonianTourCutCard_pos (hn := by omega) S σ hS_nonempty hS_proper
  have hcutTwo :
      2 ≤ (δ(S) ∩ hamiltonian_tour_edge_finset σ).card := by
    omega
  calc
    2 ≤ (((δ(S) ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) := by
          exact_mod_cast hcutTwo
    _ = subtour_elimination_value S (hamiltonian_tour_incidence_vector σ) := by
          symm
          exact subtourEliminationValue_eq_cutCard S σ

/-- Helper for Proposition 7.20: on a Hamiltonian tour, the induced-edge sum of any nonempty
proper set is at most `|S| - 1`. -/
private theorem hamiltonianTourInducedEdgeSum_le_card_sub_one
    {n : ℕ} (hn : 3 ≤ n)
    (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n))
    (hS_nonempty : S.Nonempty)
    (hS_proper : S.card < n) :
    Finset.sum (induced_edge_finset S) (hamiltonian_tour_incidence_vector σ) ≤
      (S.card : ℝ) - 1 := by
  -- Route correction: use the degree-slice identity plus the lower bound `subtour(S) ≥ 2`
  -- instead of reviving the old nat-cast rounding route.
  have hx_degree :
      hamiltonian_tour_incidence_vector σ ∈ travelingSalesmanDegreeConstraintSet n :=
    hamiltonianTourIncidenceVector_mem_degreeConstraintSet hn σ
  have hsubtour :
      2 ≤ subtour_elimination_value S (hamiltonian_tour_incidence_vector σ) :=
    hamiltonianTourSubtourElimination_ge_two hn S σ hS_nonempty hS_proper
  have hinduced :
      Finset.sum (induced_edge_finset S) (hamiltonian_tour_incidence_vector σ) =
        (S.card : ℝ) -
          subtour_elimination_value S (hamiltonian_tour_incidence_vector σ) / 2 :=
    inducedEdgeSum_eq_card_sub_half_subtour S hx_degree
  linarith

/-- Helper for Proposition 7.20: the cross edges of tooth `i` connect `teeth i \ handle` to
`teeth i ∩ handle`. -/
private def toothCrossEdgeFinset
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (i : Fin k) :
    Finset (complete_graph_edges n) :=
  Finset.univ.filter fun e ↦
    (e.1.out.1 ∈ teeth i \ handle ∧ e.1.out.2 ∈ teeth i ∩ handle) ∨
      (e.1.out.2 ∈ teeth i \ handle ∧ e.1.out.1 ∈ teeth i ∩ handle)

/-- Helper for Proposition 7.20: membership in the tooth cross-edge owner is exactly the endpoint
predicate used to define it. -/
private theorem mem_toothCrossEdgeFinset_iff
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (i : Fin k)
    (e : complete_graph_edges n) :
    e ∈ toothCrossEdgeFinset handle teeth i ↔
      (e.1.out.1 ∈ teeth i \ handle ∧ e.1.out.2 ∈ teeth i ∩ handle) ∨
        (e.1.out.2 ∈ teeth i \ handle ∧ e.1.out.1 ∈ teeth i ∩ handle) := by
  -- This is just the defining filter condition.
  simp [toothCrossEdgeFinset]

/-- Helper for Proposition 7.20: membership in the cross-edge finset spells out the endpoint
conditions on the tooth and the handle. -/
private theorem mem_toothCrossEdgeFinset_iff_endpoints
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (i : Fin k)
    (e : complete_graph_edges n) :
    e ∈ toothCrossEdgeFinset handle teeth i ↔
      (e.1.out.1 ∈ teeth i ∧ e.1.out.1 ∉ handle ∧
          e.1.out.2 ∈ teeth i ∧ e.1.out.2 ∈ handle) ∨
        (e.1.out.2 ∈ teeth i ∧ e.1.out.2 ∉ handle ∧
          e.1.out.1 ∈ teeth i ∧ e.1.out.1 ∈ handle) := by
  rw [mem_toothCrossEdgeFinset_iff]
  simp only [Finset.mem_sdiff, Finset.mem_inter, and_assoc]

/-- Helper for Proposition 7.20: membership in `induced_edge_finset (S \ T)` means both endpoints
lie in `S` and outside `T`. -/
private theorem mem_induced_edge_finset_sdiff_iff
    {n : ℕ} (S T : Finset (Fin n)) (e : complete_graph_edges n) :
    e ∈ induced_edge_finset (S \ T) ↔
      e.1.out.1 ∈ S ∧ e.1.out.1 ∉ T ∧ e.1.out.2 ∈ S ∧ e.1.out.2 ∉ T := by
  rw [mem_induced_edge_finset_iff]
  simp only [Finset.mem_sdiff, and_assoc]

/-- Helper for Proposition 7.20: membership in `induced_edge_finset (S ∩ T)` means both endpoints
lie in both `S` and `T`. -/
private theorem mem_induced_edge_finset_inter_iff
    {n : ℕ} (S T : Finset (Fin n)) (e : complete_graph_edges n) :
    e ∈ induced_edge_finset (S ∩ T) ↔
      e.1.out.1 ∈ S ∧ e.1.out.1 ∈ T ∧ e.1.out.2 ∈ S ∧ e.1.out.2 ∈ T := by
  rw [mem_induced_edge_finset_iff]
  simp only [Finset.mem_inter, and_assoc]

/-- Helper for Proposition 7.20: every tooth cross edge is also induced by the tooth itself. -/
private theorem mem_induced_edge_finset_of_mem_toothCrossEdge
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (i : Fin k)
    (e : complete_graph_edges n)
    (he : e ∈ toothCrossEdgeFinset handle teeth i) :
    e ∈ induced_edge_finset (teeth i) := by
  -- Both endpoints of a tooth cross edge lie in the same tooth by construction.
  rw [mem_induced_edge_finset_iff]
  rcases (mem_toothCrossEdgeFinset_iff_endpoints handle teeth i e).1 he with h | h
  · exact ⟨h.1, h.2.2.1⟩
  · exact ⟨h.2.2.1, h.1⟩

/-- Helper for Proposition 7.20: every tooth cross edge lies in the handle cut `δ(handle)`. -/
private theorem mem_edge_boundary_finset_of_mem_toothCrossEdge
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (i : Fin k)
    (e : complete_graph_edges n)
    (he : e ∈ toothCrossEdgeFinset handle teeth i) :
    e ∈ δ(handle) := by
  -- A tooth cross edge has one endpoint in `handle` and the other outside `handle`.
  rcases (mem_toothCrossEdgeFinset_iff_endpoints handle teeth i e).1 he with h | h
  · exact (mem_edge_boundary_finset_iff_out_endpoints handle e).2
      (Or.inr ⟨h.2.2.2, h.2.1⟩)
  · exact (mem_edge_boundary_finset_iff_out_endpoints handle e).2
      (Or.inl ⟨h.2.2.2, h.2.1⟩)

/-- Helper for Proposition 7.20: if the same edge is a tooth cross edge for two different teeth,
then those tooth indices are equal. -/
private theorem toothCrossEdgeFinset_index_unique
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (hcomb : IsComb handle teeth)
    {i j : Fin k}
    (hij : i ≠ j)
    {e : complete_graph_edges n}
    (hi : e ∈ toothCrossEdgeFinset handle teeth i)
    (hj : e ∈ toothCrossEdgeFinset handle teeth j) :
    False := by
  have hleft_i : e.1.out.1 ∈ teeth i := by
    rcases (mem_toothCrossEdgeFinset_iff_endpoints handle teeth i e).1 hi with h | h
    · exact h.1
    · exact h.2.2.1
  have hleft_j : e.1.out.1 ∈ teeth j := by
    rcases (mem_toothCrossEdgeFinset_iff_endpoints handle teeth j e).1 hj with h | h
    · exact h.1
    · exact h.2.2.1
  exact (Finset.disjoint_left.mp (hcomb.pairwise_disjoint hij) hleft_i hleft_j).elim

/-- Helper for Proposition 7.20: the tooth induced-edge sum splits into the outside-handle part,
the inside-handle part, and the cross edges between them. -/
private theorem toothInducedEdgeSum_eq_diff_add_inter_add_cross
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (i : Fin k)
    (x : complete_graph_edges n → ℝ) :
    Finset.sum (induced_edge_finset (teeth i)) x =
      Finset.sum (induced_edge_finset (teeth i \ handle)) x +
        Finset.sum (induced_edge_finset (teeth i ∩ handle)) x +
          Finset.sum (toothCrossEdgeFinset handle teeth i) x := by
  -- Route correction: classify each tooth edge by whether its endpoints lie outside the handle,
  -- inside the handle, or on opposite sides.
  calc
    Finset.sum (induced_edge_finset (teeth i)) x =
        ∑ e : complete_graph_edges n, if e ∈ induced_edge_finset (teeth i) then x e else 0 := by
          simpa using
            (complete_graph_sum_ite_eq_sum_filter
              (p := fun e : complete_graph_edges n ↦ e ∈ induced_edge_finset (teeth i))
              (f := x)).symm
    _ = ∑ e : complete_graph_edges n,
          ((if e ∈ induced_edge_finset (teeth i \ handle) then x e else 0) +
            (if e ∈ induced_edge_finset (teeth i ∩ handle) then x e else 0) +
              (if e ∈ toothCrossEdgeFinset handle teeth i then x e else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases hind : e ∈ induced_edge_finset (teeth i)
          · rcases (mem_induced_edge_finset_iff (teeth i) e).1 hind with ⟨h₁, h₂⟩
            by_cases hh₁ : e.1.out.1 ∈ handle
            · by_cases hh₂ : e.1.out.2 ∈ handle
              · have hinter : e ∈ induced_edge_finset (teeth i ∩ handle) := by
                  rw [mem_induced_edge_finset_inter_iff]
                  exact ⟨h₁, hh₁, h₂, hh₂⟩
                have hnotdiff : e ∉ induced_edge_finset (teeth i \ handle) := by
                  intro hdiff
                  exact (((mem_induced_edge_finset_sdiff_iff (teeth i) handle e).1 hdiff).2.1) hh₁
                have hnotcross : e ∉ toothCrossEdgeFinset handle teeth i := by
                  intro hcross
                  rcases (mem_toothCrossEdgeFinset_iff_endpoints handle teeth i e).1 hcross with h | h
                  · exact h.2.1 hh₁
                  · exact h.2.1 hh₂
                simp [hind, hinter, hnotdiff, hnotcross]
              · have hcross : e ∈ toothCrossEdgeFinset handle teeth i := by
                  exact (mem_toothCrossEdgeFinset_iff_endpoints handle teeth i e).2
                    (Or.inr ⟨h₂, hh₂, h₁, hh₁⟩)
                have hnotdiff : e ∉ induced_edge_finset (teeth i \ handle) := by
                  intro hdiff
                  exact (((mem_induced_edge_finset_sdiff_iff (teeth i) handle e).1 hdiff).2.1) hh₁
                have hnotinter : e ∉ induced_edge_finset (teeth i ∩ handle) := by
                  intro hinter
                  exact hh₂ (((mem_induced_edge_finset_inter_iff (teeth i) handle e).1 hinter).2.2.2)
                simp [hind, hcross, hnotdiff, hnotinter]
            · by_cases hh₂ : e.1.out.2 ∈ handle
              · have hcross : e ∈ toothCrossEdgeFinset handle teeth i := by
                  exact (mem_toothCrossEdgeFinset_iff_endpoints handle teeth i e).2
                    (Or.inl ⟨h₁, hh₁, h₂, hh₂⟩)
                have hnotdiff : e ∉ induced_edge_finset (teeth i \ handle) := by
                  intro hdiff
                  exact (((mem_induced_edge_finset_sdiff_iff (teeth i) handle e).1 hdiff).2.2.2) hh₂
                have hnotinter : e ∉ induced_edge_finset (teeth i ∩ handle) := by
                  intro hinter
                  exact hh₁ (((mem_induced_edge_finset_inter_iff (teeth i) handle e).1 hinter).2.1)
                simp [hind, hcross, hnotdiff, hnotinter]
              · have hdiff : e ∈ induced_edge_finset (teeth i \ handle) := by
                  rw [mem_induced_edge_finset_sdiff_iff]
                  exact ⟨h₁, hh₁, h₂, hh₂⟩
                have hnotinter : e ∉ induced_edge_finset (teeth i ∩ handle) := by
                  intro hinter
                  exact hh₁ (((mem_induced_edge_finset_inter_iff (teeth i) handle e).1 hinter).2.1)
                have hnotcross : e ∉ toothCrossEdgeFinset handle teeth i := by
                  intro hcross
                  rcases (mem_toothCrossEdgeFinset_iff_endpoints handle teeth i e).1 hcross with h | h
                  · exact hh₂ h.2.2.2
                  · exact hh₁ h.2.2.2
                simp [hind, hdiff, hnotinter, hnotcross]
          · have hnotdiff : e ∉ induced_edge_finset (teeth i \ handle) := by
              intro hdiff
              exact hind ((mem_induced_edge_finset_iff (teeth i) e).2
                ⟨((mem_induced_edge_finset_sdiff_iff (teeth i) handle e).1 hdiff).1,
                  ((mem_induced_edge_finset_sdiff_iff (teeth i) handle e).1 hdiff).2.2.1⟩)
            have hnotinter : e ∉ induced_edge_finset (teeth i ∩ handle) := by
              intro hinter
              exact hind ((mem_induced_edge_finset_iff (teeth i) e).2
                ⟨((mem_induced_edge_finset_inter_iff (teeth i) handle e).1 hinter).1,
                  ((mem_induced_edge_finset_inter_iff (teeth i) handle e).1 hinter).2.2.1⟩)
            have hnotcross : e ∉ toothCrossEdgeFinset handle teeth i := by
              intro hcross
              exact hind (mem_induced_edge_finset_of_mem_toothCrossEdge handle teeth i e hcross)
            simp [hind, hnotdiff, hnotinter, hnotcross]
    _ =
        Finset.sum (induced_edge_finset (teeth i \ handle)) x +
          Finset.sum (induced_edge_finset (teeth i ∩ handle)) x +
            Finset.sum (toothCrossEdgeFinset handle teeth i) x := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          rw [complete_graph_sum_ite_eq_sum_filter, complete_graph_sum_ite_eq_sum_filter,
            complete_graph_sum_ite_eq_sum_filter]
          simp

/-- Helper for Proposition 7.20: the total tour sum on the tooth cross edges is controlled by the
handle cut because each such edge is a unique handle-crossing tour edge. -/
private theorem crossEdgeSum_le_handleSubtourOnTour
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (hcomb : IsComb handle teeth)
    (σ : Equiv.Perm (Fin n)) :
    ∑ i : Fin k,
        Finset.sum (toothCrossEdgeFinset handle teeth i) (hamiltonian_tour_incidence_vector σ) ≤
      subtour_elimination_value handle (hamiltonian_tour_incidence_vector σ) := by
  classical
  -- Rewrite the tooth cross-edge sums as a single sum over `δ(handle)`, then use the uniqueness
  -- of the tooth index attached to each cross edge.
  have hrewrite :
      ∑ i : Fin k,
          Finset.sum (toothCrossEdgeFinset handle teeth i) (hamiltonian_tour_incidence_vector σ) =
        Finset.sum (δ(handle)) (fun e ↦
          ∑ i : Fin k,
            if e ∈ toothCrossEdgeFinset handle teeth i then hamiltonian_tour_incidence_vector σ e
            else 0) := by
    calc
      ∑ i : Fin k,
          Finset.sum (toothCrossEdgeFinset handle teeth i) (hamiltonian_tour_incidence_vector σ) =
          ∑ i : Fin k,
            Finset.sum (δ(handle))
              (fun e ↦
                if e ∈ toothCrossEdgeFinset handle teeth i then hamiltonian_tour_incidence_vector σ e
                else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            calc
              Finset.sum (toothCrossEdgeFinset handle teeth i) (hamiltonian_tour_incidence_vector σ) =
                  ∑ e : complete_graph_edges n,
                    if e ∈ toothCrossEdgeFinset handle teeth i then hamiltonian_tour_incidence_vector σ e
                    else 0 := by
                      simpa using
                        (complete_graph_sum_ite_eq_sum_filter
                          (p := fun e : complete_graph_edges n ↦ e ∈ toothCrossEdgeFinset handle teeth i)
                          (f := hamiltonian_tour_incidence_vector σ)).symm
              _ =
                  Finset.sum (δ(handle))
                    (fun e ↦
                      if e ∈ toothCrossEdgeFinset handle teeth i then hamiltonian_tour_incidence_vector σ e
                      else 0) := by
                    have hfilter :
                        Finset.univ.filter
                            (fun e : complete_graph_edges n ↦ e ∈ toothCrossEdgeFinset handle teeth i) =
                          (δ(handle)).filter
                            (fun e : complete_graph_edges n ↦ e ∈ toothCrossEdgeFinset handle teeth i) := by
                      ext e
                      constructor
                      · intro he
                        rw [Finset.mem_filter] at he ⊢
                        refine ⟨?_, ?_⟩
                        · simpa using mem_edge_boundary_finset_of_mem_toothCrossEdge handle teeth i e he.2
                        · exact he.2
                      · intro he
                        rw [Finset.mem_filter] at he ⊢
                        exact ⟨by simp, he.2⟩
                    calc
                      (∑ e : complete_graph_edges n,
                          if e ∈ toothCrossEdgeFinset handle teeth i then hamiltonian_tour_incidence_vector σ e
                          else 0) =
                          (Finset.univ.filter
                              (fun e : complete_graph_edges n ↦ e ∈ toothCrossEdgeFinset handle teeth i)).sum
                            (hamiltonian_tour_incidence_vector σ) := by
                              simpa using
                                (complete_graph_sum_ite_eq_sum_filter
                                  (p := fun e : complete_graph_edges n ↦
                                    e ∈ toothCrossEdgeFinset handle teeth i)
                                  (f := hamiltonian_tour_incidence_vector σ))
                      _ =
                          ((δ(handle)).filter
                              (fun e : complete_graph_edges n ↦ e ∈ toothCrossEdgeFinset handle teeth i)).sum
                            (hamiltonian_tour_incidence_vector σ) := by
                              rw [hfilter]
                      _ =
                          Finset.sum (δ(handle))
                            (fun e ↦
                              if e ∈ toothCrossEdgeFinset handle teeth i then hamiltonian_tour_incidence_vector σ e
                              else 0) := by
                              rw [Finset.sum_filter]
      _ = Finset.sum (δ(handle)) (fun e ↦
            ∑ i : Fin k,
              if e ∈ toothCrossEdgeFinset handle teeth i then hamiltonian_tour_incidence_vector σ e
              else 0) := by
            rw [Finset.sum_comm]
  have hpointwise :
      ∀ e ∈ δ(handle),
        (∑ i : Fin k,
            if e ∈ toothCrossEdgeFinset handle teeth i then hamiltonian_tour_incidence_vector σ e
            else 0) ≤
          hamiltonian_tour_incidence_vector σ e := by
    intro e he
    by_cases hex : ∃ i : Fin k, e ∈ toothCrossEdgeFinset handle teeth i
    · rcases hex with ⟨i, hi⟩
      have hunique : ∀ j : Fin k, e ∈ toothCrossEdgeFinset handle teeth j → j = i := by
        intro j hj
        by_contra hji
        exact toothCrossEdgeFinset_index_unique handle teeth hcomb
          (fun hij => hji hij.symm) hi hj
      have hsum :
          (∑ i' : Fin k,
              if e ∈ toothCrossEdgeFinset handle teeth i' then hamiltonian_tour_incidence_vector σ e
              else 0) =
            hamiltonian_tour_incidence_vector σ e := by
        rw [Finset.sum_eq_single i]
        · simp [hi]
        · intro j _ hji
          have hnot : e ∉ toothCrossEdgeFinset handle teeth j := by
            intro hj'
            exact hji (hunique j hj')
          simp [hnot]
        · intro hiuniv
          exact False.elim (hiuniv (Finset.mem_univ i))
      simpa [hsum]
    · have hnone : ∀ i : Fin k, e ∉ toothCrossEdgeFinset handle teeth i := by
        intro i
        intro hi
        exact hex ⟨i, hi⟩
      by_cases htour : e ∈ hamiltonian_tour_edge_finset σ
      · simp [hnone, hamiltonian_tour_incidence_vector, is_hamiltonian_tour_edge, htour]
      · simp [hnone, hamiltonian_tour_incidence_vector, is_hamiltonian_tour_edge, htour]
  calc
    ∑ i : Fin k,
        Finset.sum (toothCrossEdgeFinset handle teeth i) (hamiltonian_tour_incidence_vector σ) =
        Finset.sum (δ(handle)) (fun e ↦
          ∑ i : Fin k,
            if e ∈ toothCrossEdgeFinset handle teeth i then hamiltonian_tour_incidence_vector σ e
            else 0) := hrewrite
    _ ≤ Finset.sum (δ(handle)) (hamiltonian_tour_incidence_vector σ) := by
          exact Finset.sum_le_sum hpointwise
    _ = subtour_elimination_value handle (hamiltonian_tour_incidence_vector σ) := by
          rw [subtour_elimination_value_eq]

/-- Helper for Proposition 7.20: a comb has at least three vertices. -/
private theorem comb_three_le_n
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (hcomb : IsComb handle teeth) :
    3 ≤ n := by
  have hk : 3 ≤ k := hcomb.three_le_card
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  let i2 : Fin k := ⟨2, by omega⟩
  rcases hcomb.inter_nonempty i0 with ⟨v0, hv0⟩
  rcases hcomb.inter_nonempty i1 with ⟨v1, hv1⟩
  rcases hcomb.inter_nonempty i2 with ⟨v2, hv2⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i0, i1] at hval
  have hi02 : i0 ≠ i2 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i0, i2] at hval
  have hi12 : i1 ≠ i2 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i1, i2] at hval
  have hv01 : v0 ≠ v1 := by
    intro h
    exact (Finset.disjoint_left.mp (hcomb.pairwise_disjoint hi01)
      (Finset.mem_inter.mp hv0).1 (h ▸ (Finset.mem_inter.mp hv1).1)).elim
  have hv02 : v0 ≠ v2 := by
    intro h
    exact (Finset.disjoint_left.mp (hcomb.pairwise_disjoint hi02)
      (Finset.mem_inter.mp hv0).1 (h ▸ (Finset.mem_inter.mp hv2).1)).elim
  have hv12 : v1 ≠ v2 := by
    intro h
    exact (Finset.disjoint_left.mp (hcomb.pairwise_disjoint hi12)
      (Finset.mem_inter.mp hv1).1 (h ▸ (Finset.mem_inter.mp hv2).1)).elim
  have hcard : ({v0, v1, v2} : Finset (Fin n)).card = 3 := by
    simp [hv01, hv02, hv12]
  have hle :
      3 ≤ (Finset.univ : Finset (Fin n)).card := by
    rw [← hcard]
    exact Finset.card_le_card (by simp)
  simpa using hle

/-- Helper for Proposition 7.20: every tooth index has a different companion tooth index because
a comb has at least three teeth. -/
private theorem comb_exists_other_tooth
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (hcomb : IsComb handle teeth)
    (i : Fin k) :
    ∃ j : Fin k, j ≠ i := by
  have hk : 3 ≤ k := hcomb.three_le_card
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  have hi10 : i1 ≠ i0 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i0, i1] at hval
  by_cases hi0 : i = i0
  · refine ⟨i1, ?_⟩
    intro h
    exact hi10 (h.trans hi0)
  · exact ⟨i0, fun h ↦ hi0 h.symm⟩

/-- Helper for Proposition 7.20: every tooth is a proper subset of the full vertex set. -/
private theorem tooth_card_lt_n
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (hcomb : IsComb handle teeth)
    (i : Fin k) :
    (teeth i).card < n := by
  rcases comb_exists_other_tooth (handle := handle) (teeth := teeth) hcomb i with ⟨j, hj⟩
  rcases hcomb.inter_nonempty j with ⟨v, hvj⟩
  have hvj_tooth : v ∈ teeth j := (Finset.mem_inter.mp hvj).1
  have hv_not_mem : v ∉ teeth i := by
    intro hvi
    exact (Finset.disjoint_left.mp (hcomb.pairwise_disjoint hj) hvj_tooth hvi).elim
  simpa using Finset.card_lt_univ_of_notMem (s := teeth i) hv_not_mem

/-- Helper for Proposition 7.20: the handle part of a tooth is also a proper subset of `Fin n`. -/
private theorem tooth_inter_card_lt_n
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (hcomb : IsComb handle teeth)
    (i : Fin k) :
    (teeth i ∩ handle).card < n := by
  exact lt_of_le_of_lt (Finset.card_le_card Finset.inter_subset_left)
    (tooth_card_lt_n handle teeth hcomb i)

/-- Helper for Proposition 7.20: the outside-handle part of a tooth is also a proper subset of
`Fin n`. -/
private theorem tooth_diff_card_lt_n
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (hcomb : IsComb handle teeth)
    (i : Fin k) :
    (teeth i \ handle).card < n := by
  exact lt_of_le_of_lt (Finset.card_le_card Finset.sdiff_subset)
    (tooth_card_lt_n handle teeth hcomb i)

/-- Helper for Proposition 7.20: on a Hamiltonian tour, the induced-edge sum of one tooth is at
most `|tooth| - 3/2` plus half of its tooth-cross contribution. -/
private theorem toothInducedEdge_sub_halfCross_le_card_sub_threeHalves_onTour
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (hcomb : IsComb handle teeth)
    (hn : 3 ≤ n)
    (σ : Equiv.Perm (Fin n))
    (i : Fin k) :
    Finset.sum (induced_edge_finset (teeth i)) (hamiltonian_tour_incidence_vector σ) -
        Finset.sum (toothCrossEdgeFinset handle teeth i) (hamiltonian_tour_incidence_vector σ) / 2 ≤
      ((teeth i).card : ℝ) - (3 : ℝ) / 2 := by
  -- Apply the generic `|S| - 1` bound to the whole tooth, its outside-handle part, and its
  -- inside-handle part, then combine them with the tooth-edge decomposition.
  have htooth_nonempty : (teeth i).Nonempty := by
    rcases hcomb.inter_nonempty i with ⟨v, hv⟩
    exact ⟨v, (Finset.mem_inter.mp hv).1⟩
  have htooth :
      Finset.sum (induced_edge_finset (teeth i)) (hamiltonian_tour_incidence_vector σ) ≤
        ((teeth i).card : ℝ) - 1 :=
    hamiltonianTourInducedEdgeSum_le_card_sub_one hn (teeth i) σ htooth_nonempty
      (tooth_card_lt_n handle teeth hcomb i)
  have hdiff :
      Finset.sum (induced_edge_finset (teeth i \ handle)) (hamiltonian_tour_incidence_vector σ) ≤
        ((teeth i \ handle).card : ℝ) - 1 :=
    hamiltonianTourInducedEdgeSum_le_card_sub_one hn (teeth i \ handle) σ (hcomb.diff_nonempty i)
      (tooth_diff_card_lt_n handle teeth hcomb i)
  have hinter :
      Finset.sum (induced_edge_finset (teeth i ∩ handle)) (hamiltonian_tour_incidence_vector σ) ≤
        ((teeth i ∩ handle).card : ℝ) - 1 :=
    hamiltonianTourInducedEdgeSum_le_card_sub_one hn (teeth i ∩ handle) σ (hcomb.inter_nonempty i)
      (tooth_inter_card_lt_n handle teeth hcomb i)
  have hdecomp :=
    toothInducedEdgeSum_eq_diff_add_inter_add_cross handle teeth i (hamiltonian_tour_incidence_vector σ)
  have hcardsplit :
      ((teeth i \ handle).card : ℝ) + ((teeth i ∩ handle).card : ℝ) = ((teeth i).card : ℝ) := by
    exact_mod_cast (Finset.card_sdiff_add_card_inter (teeth i) handle)
  linarith

/-- Helper for Proposition 7.20: the comb inequality holds directly on each Hamiltonian-tour
generator. -/
private theorem combGeneratorBoundOnTour
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (hcomb : IsComb handle teeth)
    (σ : Equiv.Perm (Fin n)) :
    comb_coefficient handle teeth ⬝ᵥ hamiltonian_tour_incidence_vector σ ≤
      comb_rhs handle teeth := by
  -- Route correction: abandon the old nat-cast rounding witness and assemble the source proof
  -- directly from the degree-slice identity, the tooth diff/inter decomposition, and the handle
  -- cut control of the tooth cross edges.
  have hn : 3 ≤ n := comb_three_le_n handle teeth hcomb
  have hx_degree :
      hamiltonian_tour_incidence_vector σ ∈ travelingSalesmanDegreeConstraintSet n :=
    hamiltonianTourIncidenceVector_mem_degreeConstraintSet hn σ
  have hhandle :
      Finset.sum (induced_edge_finset handle) (hamiltonian_tour_incidence_vector σ) =
        (handle.card : ℝ) -
          subtour_elimination_value handle (hamiltonian_tour_incidence_vector σ) / 2 :=
    inducedEdgeSum_eq_card_sub_half_subtour handle hx_degree
  have htooth :
      ∀ i : Fin k,
        Finset.sum (induced_edge_finset (teeth i)) (hamiltonian_tour_incidence_vector σ) -
            Finset.sum (toothCrossEdgeFinset handle teeth i) (hamiltonian_tour_incidence_vector σ) / 2 ≤
          ((teeth i).card : ℝ) - (3 : ℝ) / 2 := by
    intro i
    exact toothInducedEdge_sub_halfCross_le_card_sub_threeHalves_onTour handle teeth hcomb hn σ i
  have hcross :
      ∑ i : Fin k,
          Finset.sum (toothCrossEdgeFinset handle teeth i) (hamiltonian_tour_incidence_vector σ) / 2 ≤
        subtour_elimination_value handle (hamiltonian_tour_incidence_vector σ) / 2 := by
    simpa [div_eq_mul_inv, Finset.sum_mul] using
      (div_le_div_of_nonneg_right
        (crossEdgeSum_le_handleSubtourOnTour handle teeth hcomb σ) (by norm_num : (0 : ℝ) ≤ 2))
  have hsum_teeth :
      ∑ i : Fin k, Finset.sum (induced_edge_finset (teeth i)) (hamiltonian_tour_incidence_vector σ) ≤
        ∑ i : Fin k, ((teeth i).card : ℝ) - (3 : ℝ) * k / 2 +
          subtour_elimination_value handle (hamiltonian_tour_incidence_vector σ) / 2 := by
    have hpre :
        ∑ i : Fin k, Finset.sum (induced_edge_finset (teeth i)) (hamiltonian_tour_incidence_vector σ) ≤
          ∑ i : Fin k,
            (((teeth i).card : ℝ) - (3 : ℝ) / 2 +
              Finset.sum (toothCrossEdgeFinset handle teeth i) (hamiltonian_tour_incidence_vector σ) / 2) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      linarith [htooth i]
    have hsplit :
        (∑ i : Fin k,
            (((teeth i).card : ℝ) - (3 : ℝ) / 2 +
              Finset.sum (toothCrossEdgeFinset handle teeth i) (hamiltonian_tour_incidence_vector σ) / 2)) =
          ∑ i : Fin k, ((teeth i).card : ℝ) - (3 : ℝ) * k / 2 +
            ∑ i : Fin k,
              Finset.sum (toothCrossEdgeFinset handle teeth i) (hamiltonian_tour_incidence_vector σ) / 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have hconst : (∑ _i : Fin k, ((3 : ℝ) / 2)) = (3 : ℝ) * k / 2 := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
      linarith
    linarith
  have hcombDot :
      comb_coefficient handle teeth ⬝ᵥ hamiltonian_tour_incidence_vector σ =
        Finset.sum (induced_edge_finset handle) (hamiltonian_tour_incidence_vector σ) +
          ∑ i : Fin k,
            Finset.sum (induced_edge_finset (teeth i)) (hamiltonian_tour_incidence_vector σ) :=
    comb_coefficient_dot_eq_handle_teeth_induced_edge_sums handle teeth
      (hamiltonian_tour_incidence_vector σ)
  let totalCard : ℕ := handle.card + ∑ i : Fin k, (teeth i).card
  have hbound :
      comb_coefficient handle teeth ⬝ᵥ hamiltonian_tour_incidence_vector σ ≤
        (totalCard : ℝ) - (3 : ℝ) * k / 2 := by
    dsimp [totalCard]
    calc
      comb_coefficient handle teeth ⬝ᵥ hamiltonian_tour_incidence_vector σ =
          Finset.sum (induced_edge_finset handle) (hamiltonian_tour_incidence_vector σ) +
            ∑ i : Fin k,
              Finset.sum (induced_edge_finset (teeth i)) (hamiltonian_tour_incidence_vector σ) := hcombDot
      _ ≤
          ((handle.card : ℝ) -
              subtour_elimination_value handle (hamiltonian_tour_incidence_vector σ) / 2) +
            (∑ i : Fin k, ((teeth i).card : ℝ) - (3 : ℝ) * k / 2 +
              subtour_elimination_value handle (hamiltonian_tour_incidence_vector σ) / 2) := by
            gcongr
      _ = (handle.card : ℝ) + ∑ i : Fin k, ((teeth i).card : ℝ) - (3 : ℝ) * k / 2 := by
            ring
  have hcombDotNat :
      ∃ m : ℕ,
        comb_coefficient handle teeth ⬝ᵥ hamiltonian_tour_incidence_vector σ = (m : ℝ) := by
    refine ⟨(induced_edge_finset handle ∩ hamiltonian_tour_edge_finset σ).card +
        ∑ i : Fin k, (induced_edge_finset (teeth i) ∩ hamiltonian_tour_edge_finset σ).card, ?_⟩
    rw [hcombDot, inducedEdgeSum_eq_inducedCard handle σ]
    simp_rw [inducedEdgeSum_eq_inducedCard]
    norm_num [Nat.cast_add, Nat.cast_sum]
  rcases hcomb.odd_card with ⟨t, rfl⟩
  rcases hcombDotNat with ⟨m, hm⟩
  have hbound' :
      (m : ℝ) ≤ (totalCard : ℝ) - (3 : ℝ) * (2 * t + 1) / 2 := by
    simpa [hm] using hbound
  have htotal_ge : 3 * t + 2 ≤ totalCard := by
    have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
    by_contra hlt
    have hlt' : (totalCard : ℝ) < 3 * t + 2 := by
      exact_mod_cast hlt
    nlinarith [hbound', hm_nonneg]
  have hm_nat :
      m ≤ totalCard - (3 * t + 2) := by
    by_contra hm_nat
    have hm_lt : totalCard - (3 * t + 2) < m := Nat.lt_of_not_ge hm_nat
    have hm_succ : totalCard - (3 * t + 1) ≤ m := by
      omega
    have hm_succ' : (totalCard : ℝ) - (3 * t + 1 : ℕ) ≤ (m : ℝ) := by
      have hA1 : 3 * t + 1 ≤ totalCard := by omega
      have hm_succ_nat : (((totalCard - (3 * t + 1) : ℕ) : ℕ) : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast hm_succ
      simpa [Nat.cast_sub hA1] using hm_succ_nat
    nlinarith [hbound', hm_succ']
  rw [hm, comb_rhs]
  have hrhs :
      (((3 : ℕ) * (2 * t + 1) + 1) / 2 : ℕ) = 3 * t + 2 := by
    ring_nf
  rw [hrhs]
  have hm_nat' : (m : ℝ) ≤ (((totalCard - (3 * t + 2) : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast hm_nat
  simpa [totalCard, Nat.cast_sub htotal_ge, Nat.cast_add, Nat.cast_sum] using hm_nat'

/-- Helper for Proposition 7.20: the direct Hamiltonian-tour comb bound is the final generator
inequality, so no separate nat-cast rounding witness is needed. -/
private lemma combGeneratorRoundedBound
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (hcomb : IsComb handle teeth)
    (σ : Equiv.Perm (Fin n)) :
    comb_coefficient handle teeth ⬝ᵥ hamiltonian_tour_incidence_vector σ ≤
      comb_rhs handle teeth := by
  -- The new route closes the generator inequality directly on the Hamiltonian-tour vertex.
  simpa using combGeneratorBoundOnTour handle teeth hcomb σ

/-- Helper for Proposition 7.20: every Hamiltonian-tour generator lies in the final comb
halfspace. -/
private lemma generator_mem_combHalfspace
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (hcomb : IsComb handle teeth)
    (σ : Equiv.Perm (Fin n)) :
    hamiltonian_tour_incidence_vector σ ∈
      {x : complete_graph_edges n → ℝ |
        comb_coefficient handle teeth ⬝ᵥ x ≤ comb_rhs handle teeth} := by
  -- The generator membership statement is exactly the rounded generator inequality.
  simpa using combGeneratorRoundedBound handle teeth hcomb σ

/-- Helper for Proposition 7.20: the comb halfspace is the preimage of `Set.Iic` under the
dot-product functional defined by `comb_coefficient handle teeth`. -/
private lemma combHalfspace_eq_linearPreimage
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n)) :
    ({x : complete_graph_edges n → ℝ |
        comb_coefficient handle teeth ⬝ᵥ x ≤ comb_rhs handle teeth} :
        Set (complete_graph_edges n → ℝ)) =
      dotProductLinearMap (comb_coefficient handle teeth) ⁻¹' Set.Iic (comb_rhs handle teeth) := by
  -- This is the canonical dot-product halfspace rewrite.
  ext x
  simp

/-- Proposition 7.20. If `handle` and `teeth` form a comb, then the comb inequality (7.23),
written as `comb_coefficient handle teeth ⬝ᵥ x ≤ comb_rhs handle teeth`, is valid for the
traveling salesman polytope. -/
theorem comb_inequality_valid_for_traveling_salesman_polytope
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (hcomb : IsComb handle teeth) :
    is_valid_inequality
      (travelingSalesmanPolytope n)
      (comb_coefficient handle teeth)
      (comb_rhs handle teeth) := by
  classical
  -- Route correction: reduce validity to the Hamiltonian-tour generators of
  -- `travelingSalesmanPolytope n`, prove the source weighted bound there using the helper
  -- `|S| - 1` inequalities on the teeth and their handle/nonhandle parts, round the half-integer
  -- right-hand side down using integrality of the tour incidence vector, and then lift the final
  -- halfspace from the generators to the convex hull.
  rw [is_valid_inequality_iff]
  intro x hx
  let halfspace : Set (complete_graph_edges n → ℝ) :=
    {y | comb_coefficient handle teeth ⬝ᵥ y ≤ comb_rhs handle teeth}
  have hhalfspace_eq :
      halfspace = dotProductLinearMap (comb_coefficient handle teeth) ⁻¹' Set.Iic (comb_rhs handle teeth) := by
    -- Use the canonical linear-halfspace presentation of the comb inequality.
    simpa [halfspace] using combHalfspace_eq_linearPreimage handle teeth
  have hhalfspace_convex : Convex ℝ halfspace := by
    -- Convexity follows by pulling back the convex ray `Set.Iic` along the dot-product map.
    rw [hhalfspace_eq]
    exact (convex_Iic (comb_rhs handle teeth)).linear_preimage _
  have hpoly_subset : travelingSalesmanPolytope n ⊆ halfspace := by
    -- It is enough to verify the inequality on the Hamiltonian-tour generators of the polytope.
    rw [travelingSalesmanPolytope_eq_convexHull]
    refine convexHull_min ?_ hhalfspace_convex
    rintro y ⟨σ, rfl⟩
    simpa [halfspace] using generator_mem_combHalfspace handle teeth hcomb σ
  exact hpoly_subset hx

end Proposition720
