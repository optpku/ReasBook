import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4.ch4_sec4_4_corollary_4_19
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4_4.ch4_sec4_4_4_theorem_4_24

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open SimpleGraph
open scoped BigOperators

attribute [local instance] Classical.propDecidable

-- Semantic search note: `lean_leansearch` was unavailable in this session, so this file reuses
-- the chapter-level owner vocabulary `perfectMatchingPolytope`, `perfectMatchingConstraintSet`,
-- and the odd-cut notation `δ[G] S` from Corollary 4.19 together with mathlib's
-- `SimpleGraph.IsBridge` and `SimpleGraph.IsRegularOfDegree` APIs.

universe u

section Exercise_4_28

variable {V : Type u}
variable (G : SimpleGraph V)

section OddCutSystem

variable [Fintype V] [DecidableEq V]
variable [DecidableRel G.Adj]

/-- The odd-cut/nonnegativity/total-edge-sum view of `perfectMatchingConstraintSet G` used in
Exercise 4.28. This is a bridge/view, not a second owner for the perfect-matching constraints. -/
def perfectMatchingOddCutSystem : Set (G.edgeSet → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧
      (∑ e, x e = (Fintype.card V : ℝ) / 2) ∧
      ∀ S : Set V, Odd S.ncard → 1 ≤ (δ[G] S).sum x}

/-- Helper for Exercise 4.28: the cut of a singleton vertex set is exactly the incidence finset of
that vertex. -/
lemma cut_singleton_eq_incidence_filter (v : V) :
    δ[G] ({v} : Set V) =
      Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v := by
  ext e
  have hmem : (∃ w : V, w ≠ v ∧ s(v, w) = (e : Sym2 V)) ↔ v ∈ (e : Sym2 V) := by
    constructor
    · intro h
      rcases h with ⟨w, hw, hEq⟩
      -- Rewrite the cut edge as the unordered pair `s(v, w)` to read off the endpoint `v`.
      rw [← hEq]
      simp
    · intro he
      -- Conversely, use the other endpoint of the edge to build the singleton cut witness.
      refine ⟨Sym2.Mem.other he, Sym2.other_ne (G.not_isDiag_of_mem_edgeSet e.2) he, ?_⟩
      exact Sym2.other_spec he
  -- The singleton-cut membership condition reduces to the edge containing `v`.
  simp [SimpleGraph.mem_cutEdgeFinset_iff, SimpleGraph.mem_incidenceFinset,
    SimpleGraph.edge_mem_incidenceSet_iff, hmem]

/-- Helper for Exercise 4.28: summing the incidence weights over all vertices counts every edge
twice. -/
lemma sum_incidence_weights_eq_twice_edge_sum (x : G.edgeSet → ℝ) :
    ∑ v : V, (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x =
      2 * ∑ e, x e := by
  classical
  -- Swap the vertex-edge summation order so each edge can be counted by its endpoints.
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp_rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  calc
    ∑ e : G.edgeSet, ∑ v : V, (if v ∈ (e : Sym2 V) then x e else 0)
        = ∑ e : G.edgeSet,
            Finset.sum (Finset.univ.filter (fun v : V ↦ v ∈ (e : Sym2 V))) (fun _ : V ↦ x e) := by
            refine Finset.sum_congr rfl ?_
            intro e he
            rw [← Finset.sum_filter]
    _ = ∑ e : G.edgeSet, Finset.sum ((e : Sym2 V).toFinset) (fun _ : V ↦ x e) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          have hfilter :
              Finset.univ.filter (fun v : V ↦ v ∈ (e : Sym2 V)) = (e : Sym2 V).toFinset := by
            ext v
            simp [Sym2.mem_toFinset]
          rw [hfilter]
    _ = ∑ e : G.edgeSet, (((e : Sym2 V).toFinset.card : ℝ) * x e) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ e : G.edgeSet, 2 * x e := by
          refine Finset.sum_congr rfl ?_
          intro e he
          rw [Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet e.2)]
          norm_num
    _ = 2 * ∑ e, x e := by
          rw [Finset.mul_sum]

/-- Helper for Exercise 4.28: if every vertex-incidence sum is at least `1` and the total edge
sum is `|V| / 2`, then each vertex-incidence sum is exactly `1`. -/
lemma incidence_eq_one_of_total_edge_sum_and_lower_bounds {x : G.edgeSet → ℝ}
    (hsum : ∑ e, x e = (Fintype.card V : ℝ) / 2)
    (hlb : ∀ v : V,
      1 ≤ (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) :
    ∀ v : V,
      (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x = 1 := by
  classical
  let degsum : V → ℝ := fun v ↦
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x
  have htotal : ∑ v : V, degsum v = (Fintype.card V : ℝ) := by
    -- The weighted handshaking identity converts the global edge sum into the total incidence sum.
    calc
      ∑ v : V, degsum v = 2 * ∑ e, x e := sum_incidence_weights_eq_twice_edge_sum (G := G) x
      _ = 2 * ((Fintype.card V : ℝ) / 2) := by rw [hsum]
      _ = (Fintype.card V : ℝ) := by ring
  have hsub_nonneg : ∀ v : V, 0 ≤ degsum v - 1 := by
    intro v
    linarith [hlb v]
  have hsum_zero : ∑ v : V, (degsum v - 1) = 0 := by
    -- Subtracting the all-ones vector leaves a nonnegative vector with total sum zero.
    calc
      ∑ v : V, (degsum v - 1) = (∑ v : V, degsum v) - ∑ v : V, (1 : ℝ) := by
        rw [Finset.sum_sub_distrib]
      _ = (Fintype.card V : ℝ) - ∑ v : V, (1 : ℝ) := by rw [htotal]
      _ = 0 := by simp
  have hzero : ∀ v : V, degsum v - 1 = 0 := by
    intro v
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _hi ↦ hsub_nonneg i)).1 hsum_zero v
      (Finset.mem_univ v)
  intro v
  linarith [hzero v]

/-- Helper for Exercise 4.28: the owner file's edge-coordinate enumeration of `G.edgeSet`
coincides with the ambient one. -/
lemma edge_univ_eq_of_decidableRel :
    (letI : DecidableEq V := SimpleGraph.instDecidableEq_integer
     letI : DecidableRel G.Adj := SimpleGraph.instDecidableRelAdj_integer G
     (Finset.univ : Finset G.edgeSet)) = Finset.univ := by
  -- Both `Finset.univ` terms enumerate the same subtype `G.edgeSet`; only the proof-level
  -- decidability data changes, so extensional finset membership is unchanged.
  ext e
  simp

/-- Helper for Exercise 4.28: the incidence-filter sum is unchanged when the Chapter 4 owner
switches to its canonical classical decision procedures. -/
lemma incidence_filter_sum_eq_of_decidableRel (x : G.edgeSet → ℝ) (v : V) :
    (letI : DecidableEq V := SimpleGraph.instDecidableEq_integer
     letI : DecidableRel G.Adj := SimpleGraph.instDecidableRelAdj_integer G
     (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
      (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x := by
  -- Rewrite the owner-side filtered finset by extensionality; the predicate is the same edge-
  -- incidence condition once `mem_incidenceFinset` is unfolded.
  refine congrArg (fun s : Finset G.edgeSet => s.sum x) ?_
  ext e
  simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]

/-- Helper for Exercise 4.28: summing over `G.edgeSet` is independent of the Chapter 4 owner's
canonical classical decision procedures. -/
lemma edge_sum_eq_owner_instances (x : G.edgeSet → ℝ) :
    (letI : DecidableEq V := SimpleGraph.instDecidableEq_integer
     letI : DecidableRel G.Adj := SimpleGraph.instDecidableRelAdj_integer G
     ∑ e, x e) = ∑ e, x e := by
  -- Rewrite the owner-side sum through the common `Finset.univ` enumeration of the edge subtype.
  simpa using congrArg (fun s : Finset G.edgeSet => s.sum x)
    (edge_univ_eq_of_decidableRel (G := G))

/-- Helper for Exercise 4.28: a feasible point of `perfectMatchingConstraintSet G` has ambient
incidence sum `1` at every vertex. -/
private lemma incidence_sum_eq_one_of_mem_perfectMatchingConstraintSet {x : G.edgeSet → ℝ}
    (hx : x ∈ perfectMatchingConstraintSet G) (v : V) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x = 1 := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨-, hx_deg, -⟩
  -- Transport the owner-side degree equality back to the ambient incidence filter.
  exact (incidence_filter_sum_eq_of_decidableRel (G := G) x v).symm.trans (hx_deg v)

/-- Helper for Exercise 4.28: the Chapter 4 owner constraints imply the odd-cut/nonnegativity/
total-edge-sum formulation. -/
lemma mem_perfectMatchingOddCutSystem_of_mem_perfectMatchingConstraintSet {x : G.edgeSet → ℝ}
    (hx : x ∈ perfectMatchingConstraintSet G) :
    x ∈ perfectMatchingOddCutSystem G := by
  rw [SimpleGraph.mem_perfectMatchingConstraintSet_iff] at hx
  rcases hx with ⟨hx_nonneg, hx_deg, hx_cut⟩
  refine ⟨hx_nonneg, ?_, ?_⟩
  · -- Transport the owner-side degree equations first, then derive the global edge sum.
    have hx_constraint : x ∈ perfectMatchingConstraintSet G := by
      rw [SimpleGraph.mem_perfectMatchingConstraintSet_iff]
      exact ⟨hx_nonneg, hx_deg, hx_cut⟩
    have htwice :
        2 * ∑ e, x e = (Fintype.card V : ℝ) := by
      calc
        2 * ∑ e, x e
            = ∑ v : V,
                (Finset.univ.filter
                  fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x := by
                symm
                exact sum_incidence_weights_eq_twice_edge_sum (G := G) x
        _ = ∑ v : V, (1 : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro v hv
              exact incidence_sum_eq_one_of_mem_perfectMatchingConstraintSet
                (G := G) hx_constraint v
        _ = (Fintype.card V : ℝ) := by simp
    linarith
  · -- The odd-cut inequalities are already part of the owner formulation.
    simpa using hx_cut

/-- Helper for Exercise 4.28: the odd-cut/nonnegativity/total-edge-sum formulation recovers the
owner-side degree equations from singleton cuts. -/
lemma mem_perfectMatchingConstraintSet_of_mem_perfectMatchingOddCutSystem {x : G.edgeSet → ℝ}
    (hx : x ∈ perfectMatchingOddCutSystem G) :
    x ∈ perfectMatchingConstraintSet G := by
  rcases hx with ⟨hx_nonneg, hx_sum, hx_cut⟩
  rw [SimpleGraph.mem_perfectMatchingConstraintSet_iff]
  refine ⟨hx_nonneg, ?_, ?_⟩
  · -- Singleton odd cuts give lower bounds on every incidence sum.
    have hlb :
        ∀ v : V,
          1 ≤ (Finset.univ.filter
            fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x := by
      intro v
      have hsingleton_odd : Odd ({v} : Set V).ncard := by
        simp
      simpa [cut_singleton_eq_incidence_filter (G := G) v] using
        hx_cut ({v} : Set V) hsingleton_odd
    -- The total edge sum then forces all of those lower bounds to be equalities.
    have hdeg_ambient :
        ∀ v : V,
          (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x = 1 :=
      incidence_eq_one_of_total_edge_sum_and_lower_bounds (G := G) hx_sum hlb
    intro v
    exact (incidence_filter_sum_eq_of_decidableRel (G := G) x v).trans (hdeg_ambient v)
  · -- Route correction: keep the odd-cut clause unchanged and transport only the degree sums.
    simpa using hx_cut

/-- The Chapter 4.23 perfect-matching constraint system is exactly the odd-cut/nonnegativity/
total-edge-sum view `perfectMatchingOddCutSystem G`. -/
theorem perfectMatchingConstraintSet_eq_oddCutSystem
    : perfectMatchingConstraintSet G = perfectMatchingOddCutSystem G := by
  -- Route correction: the stable route is two directed membership lemmas, transporting only the
  -- vertex-incidence equations and deriving the total edge sum afterwards.
  ext x
  constructor
  · exact mem_perfectMatchingOddCutSystem_of_mem_perfectMatchingConstraintSet (G := G)
  · exact mem_perfectMatchingConstraintSet_of_mem_perfectMatchingOddCutSystem (G := G)

/-- Helper for Exercise 4.28: membership in the local odd-cut presentation is equivalent to
membership in the Chapter 4.23 owner constraint system. -/
lemma mem_perfectMatchingConstraintSet_iff_mem_perfectMatchingOddCutSystem
    {x : G.edgeSet → ℝ} :
    x ∈ perfectMatchingConstraintSet G ↔ x ∈ perfectMatchingOddCutSystem G := by
  -- Package the owner-to-local identification as a rewrite-friendly membership equivalence.
  rw [perfectMatchingConstraintSet_eq_oddCutSystem (G := G)]

/-- Helper for Exercise 4.28: evaluating a finite weighted sum of edge-vectors at one edge turns
the functional convex-combination identity into an ordinary scalar identity. -/
lemma weighted_sum_apply {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → G.edgeSet → ℝ)
    {x : G.edgeSet → ℝ} (hx : ∑ i, w i • z i = x) (e : G.edgeSet) :
    ∑ i, w i * z i e = x e := by
  -- Apply the vector identity at the single coordinate `e`.
  simpa [Pi.smul_apply, smul_eq_mul] using congrFun hx e

/-- Helper for Exercise 4.28: the edges with at least one endpoint in `S`, regarded as a finset
of edge coordinates of `G`. -/
private def oddSetIncidentEdgeFinset (S : Finset V) : Finset G.edgeSet :=
  Finset.univ.filter fun e : G.edgeSet ↦ ∃ v ∈ S, (e : Sym2 V) ∈ G.incidenceFinset v

/-- Helper for Exercise 4.28: summing over `G.edgeSet` with an indicator `if` rewrites to the
corresponding filtered edge sum. -/
private lemma edgeSet_sum_ite_eq_sum_filter
    (p : G.edgeSet → Prop) [DecidablePred p] (f : G.edgeSet → ℝ) :
    (∑ e : G.edgeSet, if p e then f e else 0) = (Finset.univ.filter p).sum f := by
  -- This is the edge-coordinate version of `Finset.sum_filter`.
  rw [Finset.sum_filter]

/-- Helper for Exercise 4.28: the endpoint finset of an edge-coordinate is its unordered pair of
canonical `Sym2.out` endpoints. -/
private lemma edge_toFinset_eq_pair_finset (e : G.edgeSet) :
    ((e : Sym2 V).toFinset) = {e.1.out.1, e.1.out.2} := by
  -- Rewrite the edge through its canonical `Sym2.out` endpoints.
  calc
    ((e : Sym2 V).toFinset) = (s(e.1.out.1, e.1.out.2)).toFinset := by
      simpa [e.1.out_eq]
    _ = {e.1.out.1, e.1.out.2} := Sym2.toFinset_mk_eq

/-- Helper for Exercise 4.28: filtering the two-point endpoint finset `{a, b}` by membership in
`S` has cardinality `2`, `1`, or `0` according as both, one, or none of the endpoints lie in
`S`. -/
private lemma pair_filter_card_of_ne_finset
    (a b : V) (hab : a ≠ b) (S : Finset V) :
    (((({a, b} : Finset V).filter fun v ↦ v ∈ (S : Set V)).card : ℕ) : ℝ) =
      if a ∈ (S : Set V) ∧ b ∈ (S : Set V) then 2
      else if a ∈ (S : Set V) ∨ b ∈ (S : Set V) then 1 else 0 := by
  -- Split into the four endpoint-membership cases and let `simp` normalize the filtered pair.
  by_cases ha : a ∈ (S : Set V)
  · by_cases hb : b ∈ (S : Set V)
    · have hfilter :
          (({a, b} : Finset V).filter fun v ↦ v ∈ (S : Set V)) = ({a, b} : Finset V) := by
          ext v
          constructor
          · intro hv
            simpa using (Finset.mem_filter.mp hv).1
          · intro hv
            refine Finset.mem_filter.mpr ⟨hv, ?_⟩
            rcases Finset.mem_insert.mp hv with rfl | hvb
            · simpa using ha
            · have hvb' : v = b := by simpa using hvb
              subst hvb'
              simpa using hb
      rw [hfilter]
      simp [ha, hb, hab]
    · have hfilter :
          (({a, b} : Finset V).filter fun v ↦ v ∈ (S : Set V)) = ({a} : Finset V) := by
          ext v
          constructor
          · intro hv
            rcases Finset.mem_filter.mp hv with ⟨hvpair, hvS⟩
            rw [Finset.mem_singleton]
            rcases Finset.mem_insert.mp hvpair with rfl | hvb
            · rfl
            · have hvb' : v = b := by simpa using hvb
              subst hvb'
              exact (hb (by simpa using hvS)).elim
          · intro hv
            have hv' : v = a := by simpa using hv
            subst hv'
            refine Finset.mem_filter.mpr ⟨?_, ?_⟩
            · simp
            · simpa using ha
      rw [hfilter]
      simp [ha, hb]
  · by_cases hb : b ∈ (S : Set V)
    · have hfilter :
          (({a, b} : Finset V).filter fun v ↦ v ∈ (S : Set V)) = ({b} : Finset V) := by
          ext v
          constructor
          · intro hv
            rcases Finset.mem_filter.mp hv with ⟨hvpair, hvS⟩
            rw [Finset.mem_singleton]
            rcases Finset.mem_insert.mp hvpair with hva | hvb
            · subst hva
              exact (ha (by simpa using hvS)).elim
            · simpa using hvb
          · intro hv
            have hv' : v = b := by simpa using hv
            subst hv'
            refine Finset.mem_filter.mpr ⟨?_, ?_⟩
            · simp [hab]
            · simpa using hb
      rw [hfilter]
      simp [ha, hb]
    · have hfilter :
          (({a, b} : Finset V).filter fun v ↦ v ∈ (S : Set V)) = (∅ : Finset V) := by
          ext v
          constructor
          · intro hv
            rcases Finset.mem_filter.mp hv with ⟨hvpair, hvS⟩
            rcases Finset.mem_insert.mp hvpair with hva | hvb
            · subst hva
              exact (ha (by simpa using hvS)).elim
            · have hvb' : v = b := by simpa using hvb
              subst hvb'
              exact (hb (by simpa using hvS)).elim
          · intro hv
            simpa using hv
      rw [hfilter]
      simp [ha, hb]

/-- Helper for Exercise 4.28: an induced edge is characterized by both canonical endpoints lying
in the chosen vertex set. -/
private lemma mem_inducedEdgeFinset_endpoints_iff_finset
    (S : Set V) (e : G.edgeSet) :
    e ∈ E[G] S ↔ e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S := by
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    have he : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
      simpa [e.1.out_eq] using e.prop
    exact (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 he
  -- Rewrite induced-edge membership through the canonical endpoint presentation of `e`.
  rw [mem_inducedEdgeFinset_iff, ← e.1.out_eq, SimpleGraph.Subgraph.mem_edgeSet]
  simp [SimpleGraph.Subgraph.induce, hadj]

/-- Helper for Exercise 4.28: a cut edge is characterized by the two canonical endpoints lying on
opposite sides of the chosen vertex set. -/
private lemma mem_cutEdgeFinset_endpoints_iff_finset
    (S : Set V) (e : G.edgeSet) :
    e ∈ δ[G] S ↔
      (e.1.out.1 ∈ S ∧ e.1.out.2 ∉ S) ∨ (e.1.out.2 ∈ S ∧ e.1.out.1 ∉ S) := by
  constructor
  · intro he
    rcases (mem_cutEdgeFinset_iff (G := G) (S := S) (e := e)).1 he with ⟨u, hu, v, hv, huv⟩
    -- Normalize the witness edge equality to the canonical endpoints of `e`.
    rw [← e.1.out_eq] at huv
    rw [Sym2.eq_iff] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hu, hv⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact (mem_cutEdgeFinset_iff (G := G) (S := S) (e := e)).2
        ⟨e.1.out.1, h₁, e.1.out.2, h₂, e.1.out_eq⟩
    · exact (mem_cutEdgeFinset_iff (G := G) (S := S) (e := e)).2
        ⟨e.1.out.2, h₁, e.1.out.1, h₂, Sym2.eq_swap.trans e.1.out_eq⟩

/-- Helper for Exercise 4.28: an induced edge cannot simultaneously lie in the cut of the same
vertex set. -/
private lemma not_mem_cutEdgeFinset_of_mem_inducedEdgeFinset_finset
    {S : Set V} {e : G.edgeSet} (he : e ∈ E[G] S) :
    e ∉ δ[G] S := by
  rcases (mem_inducedEdgeFinset_endpoints_iff_finset (G := G) S e).1 he with ⟨h₁, h₂⟩
  intro hcut
  rcases (mem_cutEdgeFinset_endpoints_iff_finset (G := G) S e).1 hcut with
    (⟨_, h₂'⟩ | ⟨_, h₁'⟩)
  · exact h₂' h₂
  · exact h₁' h₁

/-- Helper for Exercise 4.28: an edge belongs to `oddSetIncidentEdgeFinset S` exactly when one of
its two concrete endpoints lies in `S`. -/
private lemma mem_oddSetIncidentEdgeFinset_iff
    (S : Finset V) (e : G.edgeSet) :
    e ∈ oddSetIncidentEdgeFinset (G := G) S ↔
      e.1.out.1 ∈ (S : Set V) ∨ e.1.out.2 ∈ (S : Set V) := by
  rw [oddSetIncidentEdgeFinset, Finset.mem_filter]
  constructor
  · rintro ⟨_, v, hvS, hvInc⟩
    have hvMem : v ∈ (e : Sym2 V) := by
      exact
        (G.edge_mem_incidenceSet_iff (a := v) (e := e)).1
          ((G.mem_incidenceFinset (v := v) (e := (e : Sym2 V))).1 hvInc)
    rw [← e.1.out_eq] at hvMem
    rw [Sym2.mem_iff] at hvMem
    rcases hvMem with rfl | rfl
    · exact Or.inl (by simpa using hvS)
    · exact Or.inr (by simpa using hvS)
  · intro h
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases h with h₁ | h₂
    · refine ⟨e.1.out.1, by simpa using h₁, ?_⟩
      exact
        (G.mem_incidenceFinset (v := e.1.out.1) (e := (e : Sym2 V))).2
          ((G.edge_mem_incidenceSet_iff (a := e.1.out.1) (e := e)).2 (Sym2.out_fst_mem _))
    · refine ⟨e.1.out.2, by simpa using h₂, ?_⟩
      exact
        (G.mem_incidenceFinset (v := e.1.out.2) (e := (e : Sym2 V))).2
          ((G.edge_mem_incidenceSet_iff (a := e.1.out.2) (e := e)).2 (Sym2.out_snd_mem _))

/-- Helper for Exercise 4.28: an edge incident to `S` is either internal to `S` or crosses the
cut of `S`. -/
private lemma mem_oddSetIncidentEdgeFinset_iff_mem_induced_or_cut
    (S : Finset V) (e : G.edgeSet) :
    e ∈ oddSetIncidentEdgeFinset (G := G) S ↔
      e ∈ E[G] (S : Set V) ∨ e ∈ δ[G] (S : Set V) := by
  constructor
  · intro he
    rcases (mem_oddSetIncidentEdgeFinset_iff (G := G) S e).1 he with h₁ | h₂
    · by_cases h₂S : e.1.out.2 ∈ (S : Set V)
      · exact Or.inl <|
          (mem_inducedEdgeFinset_endpoints_iff_finset (G := G) (S : Set V) e).2 ⟨h₁, h₂S⟩
      · exact Or.inr <|
          (mem_cutEdgeFinset_endpoints_iff_finset (G := G) (S : Set V) e).2 (Or.inl ⟨h₁, h₂S⟩)
    · by_cases h₁S : e.1.out.1 ∈ (S : Set V)
      · exact Or.inl <|
          (mem_inducedEdgeFinset_endpoints_iff_finset (G := G) (S : Set V) e).2 ⟨h₁S, h₂⟩
      · exact Or.inr <|
          (mem_cutEdgeFinset_endpoints_iff_finset (G := G) (S : Set V) e).2 (Or.inr ⟨h₂, h₁S⟩)
  · intro he
    rcases he with hind | hcut
    · exact
        (mem_oddSetIncidentEdgeFinset_iff (G := G) S e).2
          (Or.inl ((mem_inducedEdgeFinset_endpoints_iff_finset (G := G) (S : Set V) e).1 hind).1)
    · rcases (mem_cutEdgeFinset_endpoints_iff_finset (G := G) (S : Set V) e).1 hcut with
        (⟨h₁, _⟩ | ⟨h₂, _⟩)
      · exact (mem_oddSetIncidentEdgeFinset_iff (G := G) S e).2 (Or.inl h₁)
      · exact (mem_oddSetIncidentEdgeFinset_iff (G := G) S e).2 (Or.inr h₂)

/-- Helper for Exercise 4.28: the edges incident to `S` split disjointly into the edges induced
by `S` and the cut edges of `S`. -/
private lemma oddSetIncidentEdgeFinset_sum_eq_induced_add_cut
    (S : Finset V) (x : G.edgeSet → ℝ) :
    (oddSetIncidentEdgeFinset (G := G) S).sum x =
      (E[G] (S : Set V)).sum x + (δ[G] (S : Set V)).sum x := by
  have hUnion :
      oddSetIncidentEdgeFinset (G := G) S = E[G] (S : Set V) ∪ δ[G] (S : Set V) := by
    ext e
    simp [mem_oddSetIncidentEdgeFinset_iff_mem_induced_or_cut]
  have hDisj : Disjoint (E[G] (S : Set V)) (δ[G] (S : Set V)) := by
    rw [Finset.disjoint_left]
    intro e he hind
    exact not_mem_cutEdgeFinset_of_mem_inducedEdgeFinset_finset (G := G) he hind
  -- Split the incident-edge sum along the disjoint induced/cut partition.
  rw [hUnion, Finset.sum_union hDisj]

/-- Helper for Exercise 4.28: filtering the vertices of `S` that lie on an edge agrees with
filtering the endpoint finset of that edge by membership in `S`. -/
private lemma edge_filter_eq_endpoint_filter
    (S : Finset V) (e : G.edgeSet) :
    S.filter (fun v ↦ v ∈ (e : Sym2 V)) =
      ((e : Sym2 V).toFinset.filter fun v ↦ v ∈ (S : Set V)) := by
  -- Both sides describe the finite intersection `S ∩ ((e : Sym2 V).toFinset)`.
  ext v
  simpa [Finset.mem_filter, and_comm] using
    (show v ∈ S.filter (fun w ↦ w ∈ (e : Sym2 V)) ↔
      v ∈ ((e : Sym2 V).toFinset.filter fun w ↦ w ∈ (S : Set V)) by
        simp [Finset.mem_filter, Sym2.mem_toFinset])

/-- Helper for Exercise 4.28: the filtered endpoint cardinality of an edge is the sum of the
incident-edge indicator and the induced-edge indicator. -/
private lemma endpoint_filter_card_eq_incident_add_induced
    (S : Finset V) (e : G.edgeSet) :
    ((((e : Sym2 V).toFinset.filter fun v : V ↦ v ∈ (S : Set V)).card : ℕ) : ℝ) =
      (if e ∈ oddSetIncidentEdgeFinset (G := G) S then 1 else 0) +
        if e ∈ E[G] (S : Set V) then 1 else 0 := by
  have hne : e.1.out.1 ≠ e.1.out.2 := by
    have hadj : G.Adj e.1.out.1 e.1.out.2 := by
      have he : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
        simpa [e.1.out_eq] using e.prop
      exact (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 he
    exact G.ne_of_adj hadj
  -- Compute the filtered endpoint cardinality by case-splitting on the two endpoints.
  rw [edge_toFinset_eq_pair_finset (G := G) e, pair_filter_card_of_ne_finset _ _ hne]
  by_cases h₁ : e.1.out.1 ∈ (S : Set V)
  · by_cases h₂ : e.1.out.2 ∈ (S : Set V)
    · norm_num [h₁, h₂, mem_oddSetIncidentEdgeFinset_iff,
        mem_inducedEdgeFinset_endpoints_iff_finset]
    · norm_num [h₁, h₂, mem_oddSetIncidentEdgeFinset_iff,
        mem_inducedEdgeFinset_endpoints_iff_finset]
  · by_cases h₂ : e.1.out.2 ∈ (S : Set V)
    · norm_num [h₁, h₂, mem_oddSetIncidentEdgeFinset_iff,
        mem_inducedEdgeFinset_endpoints_iff_finset]
    · norm_num [h₁, h₂, mem_oddSetIncidentEdgeFinset_iff,
        mem_inducedEdgeFinset_endpoints_iff_finset]

/-- Helper for Exercise 4.28: summing the vertex-incidence equations on `S` counts each edge
incident to `S` once, plus one extra copy for each edge internal to `S`. -/
private lemma sumIncidenceOnFinset_eq_oddSetIncident_add_induced
    (S : Finset V) (x : G.edgeSet → ℝ) :
    Finset.sum S
      (fun v ↦ (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
      (oddSetIncidentEdgeFinset (G := G) S).sum x + (E[G] (S : Set V)).sum x := by
  calc
    Finset.sum S
        (fun v ↦ (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
        Finset.sum S
          (fun v ↦ ∑ e : G.edgeSet, if (e : Sym2 V) ∈ G.incidenceFinset v then x e else 0) := by
            -- Rewrite each incidence-filter sum as a full edge-set sum with an indicator.
            refine Finset.sum_congr rfl ?_
            intro v hv
            rw [Finset.sum_filter]
    _ = Finset.sum Finset.univ
          (fun e : G.edgeSet ↦
            Finset.sum S (fun v ↦ if (e : Sym2 V) ∈ G.incidenceFinset v then x e else 0)) := by
          -- Swap the vertex and edge summations.
          rw [Finset.sum_comm]
    _ = ∑ e : G.edgeSet,
          (S.filter fun v ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum (fun _ ↦ x e) := by
          -- Repackage the inner indicator sum as a filtered sum over the chosen vertices.
          refine Finset.sum_congr rfl ?_
          intro e he
          rw [Finset.sum_filter]
    _ = ∑ e : G.edgeSet,
          ((((e : Sym2 V).toFinset.filter fun v : V ↦ v ∈ (S : Set V)).card : ℕ) : ℝ) * x e := by
          -- The filtered vertex set is exactly the filtered endpoint set of `e`.
          refine Finset.sum_congr rfl ?_
          intro e he
          have hfilter :
              S.filter (fun v ↦ (e : Sym2 V) ∈ G.incidenceFinset v) =
                S.filter (fun v ↦ v ∈ (e : Sym2 V)) := by
            ext v
            simp [G.edge_mem_incidenceSet_iff]
          rw [hfilter, edge_filter_eq_endpoint_filter (G := G) S e, Finset.sum_const]
          simp [nsmul_eq_mul]
    _ = ∑ e : G.edgeSet,
          (((if e ∈ oddSetIncidentEdgeFinset (G := G) S then 1 else 0) +
              if e ∈ E[G] (S : Set V) then 1 else 0) * x e) := by
          -- Replace the endpoint multiplicity by the incident-plus-induced decomposition.
          refine Finset.sum_congr rfl ?_
          intro e he
          rw [endpoint_filter_card_eq_incident_add_induced (G := G) S e]
    _ = ∑ e : G.edgeSet,
          ((if e ∈ oddSetIncidentEdgeFinset (G := G) S then x e else 0) +
            if e ∈ E[G] (S : Set V) then x e else 0) := by
          -- Each `0/1` coefficient turns into the corresponding indicator term.
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases hOdd : e ∈ oddSetIncidentEdgeFinset (G := G) S <;>
            by_cases hInd : e ∈ E[G] (S : Set V) <;>
            simp [hOdd, hInd, add_mul]
    _ = (Finset.univ.filter fun e : G.edgeSet ↦ e ∈ oddSetIncidentEdgeFinset (G := G) S).sum x +
          (Finset.univ.filter fun e : G.edgeSet ↦ e ∈ E[G] (S : Set V)).sum x := by
          rw [Finset.sum_add_distrib]
          congr 1
          · exact edgeSet_sum_ite_eq_sum_filter
              (G := G) (p := fun e : G.edgeSet ↦ e ∈ oddSetIncidentEdgeFinset (G := G) S) x
          · exact edgeSet_sum_ite_eq_sum_filter
              (G := G) (p := fun e : G.edgeSet ↦ e ∈ E[G] (S : Set V)) x
    _ = (oddSetIncidentEdgeFinset (G := G) S).sum x + (E[G] (S : Set V)).sum x := by
          simp

/-- Helper for Exercise 4.28: summing the incidence equations on `S` counts each internal edge
twice and each cut edge once. -/
lemma sumIncidenceOn_eq_twice_inducedEdgeSum_addCutSum
    (S : Set V) (x : G.edgeSet → ℝ) :
    Finset.sum S.toFinset
      (fun v ↦ (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
      2 * (E[G] S).sum x + (δ[G] S).sum x := by
  calc
    Finset.sum S.toFinset
        (fun v ↦ (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
        (oddSetIncidentEdgeFinset (G := G) S.toFinset).sum x + (E[G] S).sum x := by
          simpa using sumIncidenceOnFinset_eq_oddSetIncident_add_induced (G := G) S.toFinset x
    _ = ((E[G] (S.toFinset : Set V)).sum x + (δ[G] (S.toFinset : Set V)).sum x) + (E[G] S).sum x := by
          rw [oddSetIncidentEdgeFinset_sum_eq_induced_add_cut (G := G) S.toFinset x]
    _ = ((E[G] S).sum x + (δ[G] S).sum x) + (E[G] S).sum x := by
          simp
    _ = 2 * (E[G] S).sum x + (δ[G] S).sum x := by
          ring

/-- Helper for Exercise 4.28: every point of the perfect-matching constraint system satisfies the
matching constraint system. -/
lemma mem_matchingConstraintSet_of_mem_perfectMatchingConstraintSet {x : G.edgeSet → ℝ}
    (hx : x ∈ perfectMatchingConstraintSet G) :
    x ∈ matchingConstraintSet G := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, hx_deg, hx_cut⟩
  rw [SimpleGraph.mem_matchingConstraintSet_iff]
  refine ⟨hx_nonneg, ?_, ?_⟩
  · intro v
    linarith [hx_deg v]
  · intro S hS
    have hdegree_sum :
        Finset.sum S.toFinite.toFinset
          (fun v ↦
            (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
          (S.ncard : ℝ) := by
      calc
        Finset.sum S.toFinite.toFinset
            (fun v ↦
              (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
            Finset.sum S.toFinite.toFinset (fun _ : V ↦ (1 : ℝ)) := by
                refine Finset.sum_congr rfl ?_
                intro v hv
                exact incidence_sum_eq_one_of_mem_perfectMatchingConstraintSet (G := G) hx v
        _ = (S.toFinite.toFinset.card : ℝ) := by
              simp
        _ = (S.ncard : ℝ) := by
              have hcard : S.toFinite.toFinset.card = S.ncard := by
                simpa [Set.toFinite_toFinset] using (Set.ncard_eq_toFinset_card' S).symm
              exact_mod_cast hcard
    have hsplit :
        Finset.sum S.toFinite.toFinset
          (fun v ↦
            (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
          2 * (E[G] S).sum x + (δ[G] S).sum x := by
      simpa using sumIncidenceOn_eq_twice_inducedEdgeSum_addCutSum (G := G) S x
    have hcut_lb : 1 ≤ (δ[G] S).sum x := hx_cut S hS
    linarith

/-- Helper for Exercise 4.28: incidence vectors of subgraphs have nonnegative edge coordinates. -/
lemma subgraphIncidenceVector_nonneg (M : G.Subgraph) :
    ∀ e : G.edgeSet, 0 ≤ G.subgraphIncidenceVector ℝ M e := by
  intro e
  -- Each coordinate is an indicator value, so it is either `0` or `1`.
  by_cases h : e.1 ∈ M.edgeSet
  · simp [SimpleGraph.subgraphIncidenceVector, h]
  · simp [SimpleGraph.subgraphIncidenceVector, h]

/-- Helper for Exercise 4.28: if a vertex is not covered by a subgraph, then its incidence sum in
the subgraph incidence vector is `0`. -/
lemma subgraphIncidenceSum_eq_zero_of_notMem_verts {M : G.Subgraph} {v : V}
    (hv : v ∉ M.verts) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = 0 := by
  -- Any incident edge with positive coordinate would place `v` in `M.verts`, contradicting `hv`.
  refine Finset.sum_eq_zero ?_
  intro e he
  have hv_mem : v ∈ (e : Sym2 V) := by
    have he_inc : (e : Sym2 V) ∈ G.incidenceFinset v := (Finset.mem_filter.mp he).2
    simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff] using he_inc
  by_cases heM : e.1 ∈ M.edgeSet
  · exact (hv (Subgraph.mem_verts_of_mem_edge heM hv_mem)).elim
  · simp [SimpleGraph.subgraphIncidenceVector, heM]

/-- Helper for Exercise 4.28: at a covered vertex of a matching, the matching incidence sum is
exactly `1`. -/
lemma matchingIncidenceSum_eq_one_of_mem_verts {M : G.Subgraph} (hM : M.IsMatching)
    {v : V} (hv : v ∈ M.verts) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = 1 := by
  obtain ⟨w, hvw, huniq⟩ := hM hv
  let e₀ : G.edgeSet := ⟨s(v, w), M.adj_sub hvw⟩
  have he₀_mem :
      e₀ ∈ Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v := by
    -- The unique matching edge at `v` belongs to the incidence filter.
    simp [e₀, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  have he₀_val : G.subgraphIncidenceVector ℝ M e₀ = 1 := by
    have he₀_edge : e₀.1 ∈ M.edgeSet := Subgraph.mem_edgeSet.2 hvw
    simp [SimpleGraph.subgraphIncidenceVector, he₀_edge]
  calc
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = G.subgraphIncidenceVector ℝ M e₀ := by
          refine Finset.sum_eq_single_of_mem e₀ he₀_mem ?_
          intro e he he_ne
          by_cases heM : e.1 ∈ M.edgeSet
          · have hv_e : v ∈ (e : Sym2 V) := by
              have he_inc : (e : Sym2 V) ∈ G.incidenceFinset v := (Finset.mem_filter.mp he).2
              simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
                using he_inc
            have hAdj_e : M.Adj v (Sym2.Mem.other hv_e) := by
              exact Subgraph.mem_edgeSet.1 (by simpa [Sym2.other_spec hv_e] using heM)
            have he_eq : e.1 = e₀.1 := by
              calc
                e.1 = s(v, Sym2.Mem.other hv_e) := by symm; exact Sym2.other_spec hv_e
                _ = s(v, w) := by rw [huniq _ hAdj_e]
                _ = e₀.1 := rfl
            exact (he_ne (Subtype.ext he_eq)).elim
          · simp [SimpleGraph.subgraphIncidenceVector, heM]
    _ = 1 := he₀_val

/-- Helper for Exercise 4.28: every matching incidence sum at a vertex is bounded by `1`. -/
lemma matchingIncidenceSum_le_one {M : G.Subgraph} (hM : M.IsMatching) (v : V) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) ≤ 1 := by
  -- A matching contributes `1` on covered vertices and `0` on uncovered ones.
  by_cases hv : v ∈ M.verts
  · have hsum_eq_one := matchingIncidenceSum_eq_one_of_mem_verts (G := G) hM hv
    linarith
  · rw [subgraphIncidenceSum_eq_zero_of_notMem_verts (G := G) hv]
    norm_num

/-- Helper for Exercise 4.28: a perfect matching contributes exactly one incident edge at every
vertex. -/
lemma perfectMatchingIncidenceSum_eq_one {M : G.Subgraph} (hM : M.IsPerfectMatching) (v : V) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = 1 := by
  -- Perfect matchings are matchings that cover every vertex.
  simpa using matchingIncidenceSum_eq_one_of_mem_verts (G := G) hM.1 (hM.2 v)

/-- Helper for Exercise 4.28: every odd cut contains at least one edge of a perfect matching. -/
lemma perfectMatchingCutLowerBound {M : G.Subgraph} (hM : M.IsPerfectMatching)
    {S : Set V} (hS : Odd S.ncard) :
    1 ≤ (δ[G] S).sum (G.subgraphIncidenceVector ℝ M) := by
  classical
  by_contra hcut
  have hcut_lt : (δ[G] S).sum (G.subgraphIncidenceVector ℝ M) < 1 := by
    linarith
  have hno_cut :
      ∀ {e : G.edgeSet}, e.1 ∈ M.edgeSet → e ∉ δ[G] S := by
    intro e heM heCut
    -- Any matching edge in the cut already contributes `1` to the cut sum.
    have hsum_ge :
        1 ≤ (δ[G] S).sum (G.subgraphIncidenceVector ℝ M) := by
      calc
        1 = G.subgraphIncidenceVector ℝ M e := by
              simp [SimpleGraph.subgraphIncidenceVector, heM]
        _ ≤ (δ[G] S).sum (G.subgraphIncidenceVector ℝ M) := by
              exact Finset.single_le_sum
                (fun e' _ ↦ subgraphIncidenceVector_nonneg (G := G) M e') heCut
    linarith
  have hinduced_match : (M.induce S).IsMatching := by
    intro v hv
    have hvS : v ∈ S := by
      simpa [Subgraph.induce_verts, hM.2.verts_eq_univ] using hv
    obtain ⟨w, hvw, huniq⟩ := (Subgraph.isPerfectMatching_iff.mp hM) v
    have hwS : w ∈ S := by
      by_contra hwS
      let e : G.edgeSet := ⟨s(v, w), M.adj_sub hvw⟩
      have heCut : e ∈ δ[G] S := by
        exact (SimpleGraph.mem_cutEdgeFinset_iff (G := G)).2 ⟨v, hvS, w, hwS, rfl⟩
      have heM : e.1 ∈ M.edgeSet := Subgraph.mem_edgeSet.2 hvw
      exact hno_cut heM heCut
    -- Once no matching edge crosses the cut, the matched neighbor stays inside `S`.
    refine ⟨w, ?_, ?_⟩
    · exact ⟨hvS, hwS, hvw⟩
    · intro x hx
      exact huniq x hx.2.2
  letI : Fintype ↑((M.induce S).verts) := Fintype.ofFinite _
  have hEven : Even S.ncard := by
    -- The induced matching covers exactly `S`, so `S` has even cardinality.
    simpa [Subgraph.induce_verts, hM.2.verts_eq_univ, Set.inter_univ,
      Set.ncard_eq_toFinset_card'] using hinduced_match.even_card
  exact (Nat.not_even_iff_odd.mpr hS) hEven

/-- Helper for Exercise 4.28: every perfect-matching incidence vector satisfies the Chapter 4.19
constraint system. -/
lemma subgraphIncidenceVector_mem_perfectMatchingConstraintSet {M : G.Subgraph}
    (hM : M.IsPerfectMatching) :
    G.subgraphIncidenceVector ℝ M ∈ perfectMatchingConstraintSet G := by
  rw [SimpleGraph.mem_perfectMatchingConstraintSet_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact subgraphIncidenceVector_nonneg (G := G) M
  · intro v
    exact (incidence_filter_sum_eq_of_decidableRel (G := G) (G.subgraphIncidenceVector ℝ M) v).trans
      (perfectMatchingIncidenceSum_eq_one (G := G) hM v)
  · intro S hS
    exact perfectMatchingCutLowerBound (G := G) hM hS

/-- Helper for Exercise 4.28: in a weighted average of numbers in `[0, 1]` with total weight `1`,
every positive-weight support term must already equal `1` if the average is `1`. -/
lemma eq_one_of_weightedAverage_eq_one {ι : Type*} [Fintype ι] {w a : ι → ℝ}
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (ha_le_one : ∀ i, a i ≤ 1)
    (hw_sum : ∑ i, w i = 1)
    (havg : ∑ i, w i * a i = 1) :
    ∀ i, w i ≠ 0 → a i = 1 := by
  have hterm_nonneg : ∀ i, 0 ≤ w i * (1 - a i) := by
    intro i
    exact mul_nonneg (hw_nonneg i) (sub_nonneg.mpr (ha_le_one i))
  have hterm_sum : ∑ i, w i * (1 - a i) = 0 := by
    calc
      ∑ i, w i * (1 - a i) = ∑ i, (w i - w i * a i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
      _ = (∑ i, w i) - ∑ i, w i * a i := by
            rw [Finset.sum_sub_distrib]
      _ = 0 := by
            nlinarith [hw_sum, havg]
  have hzero : ∀ i, w i * (1 - a i) = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _hj ↦ hterm_nonneg j)).1 hterm_sum i
      (Finset.mem_univ i)
  intro i hwi
  have hwi_pos : 0 < w i := lt_of_le_of_ne (hw_nonneg i) (Ne.symm hwi)
  have hslack_nonneg : 0 ≤ 1 - a i := sub_nonneg.mpr (ha_le_one i)
  have hslack_zero : 1 - a i = 0 := by
    nlinarith [hzero i, hwi_pos, hslack_nonneg]
  nlinarith [hslack_zero]

/-- Helper for Exercise 4.28: a convex decomposition by matchings upgrades to one by perfect
matchings once the barycenter already satisfies the perfect-matching degree equations. -/
lemma perfectMatchingPolytope_of_mem_matchingPolytope_of_mem_perfectMatchingConstraintSet
    {x : G.edgeSet → ℝ}
    (hx_matchingPolytope : x ∈ matchingPolytope G)
    (hxPerfect : x ∈ perfectMatchingConstraintSet G) :
    x ∈ perfectMatchingPolytope G := by
  rw [SimpleGraph.matchingPolytope, mem_convexHull_iff_exists_fintype] at hx_matchingPolytope
  rcases hx_matchingPolytope with ⟨ι, _, w, z, hw_nonneg, hw_sum, hz, hx_sum⟩
  have hz' : ∀ i, ∃ M : G.Subgraph, M.IsMatching ∧ z i = G.subgraphIncidenceVector ℝ M := by
    intro i
    simpa using hz i
  choose M hMatch hVec using hz'
  have hx_sum_match :
      ∑ i, w i • G.subgraphIncidenceVector ℝ (M i) = x := by
    calc
      ∑ i, w i • G.subgraphIncidenceVector ℝ (M i) = ∑ i, w i • z i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hVec i]
      _ = x := hx_sum
  have hsupport_perfect :
      ∀ i, w i ≠ 0 → (M i).IsPerfectMatching :=
    by
      rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hxPerfect with
        ⟨-, hx_deg, -⟩
      intro i hwi
      refine ⟨hMatch i, ?_⟩
      intro v
      let I : Finset G.edgeSet :=
        Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v
      have hterm :
          ∀ j, w j * I.sum (G.subgraphIncidenceVector ℝ (M j)) =
            Finset.sum I (fun e ↦ w j * G.subgraphIncidenceVector ℝ (M j) e) := by
        intro j
        rw [Finset.mul_sum]
      have havg :
          ∑ j, w j * I.sum (G.subgraphIncidenceVector ℝ (M j)) = 1 := by
        calc
          ∑ j, w j * I.sum (G.subgraphIncidenceVector ℝ (M j)) =
              ∑ j, Finset.sum I (fun e ↦ w j * G.subgraphIncidenceVector ℝ (M j) e) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                exact hterm j
          _ = Finset.sum I (fun e ↦ ∑ j, w j * G.subgraphIncidenceVector ℝ (M j) e) := by
                rw [Finset.sum_comm]
          _ = Finset.sum I x := by
                refine Finset.sum_congr rfl ?_
                intro e he
                simpa using
                  weighted_sum_apply (G := G) w (fun j ↦ G.subgraphIncidenceVector ℝ (M j))
                    hx_sum_match e
          _ = 1 := by
                exact incidence_sum_eq_one_of_mem_perfectMatchingConstraintSet
                  (G := G) hxPerfect v
      have hle :
          ∀ j, I.sum (G.subgraphIncidenceVector ℝ (M j)) ≤ 1 := by
        intro j
        simpa [I] using matchingIncidenceSum_le_one (G := G) (hMatch j) v
      have hi_sum_eq_one :
          I.sum (G.subgraphIncidenceVector ℝ (M i)) = 1 :=
        eq_one_of_weightedAverage_eq_one hw_nonneg hle hw_sum havg i hwi
      by_contra hv
      have hi_sum_eq_zero :
          I.sum (G.subgraphIncidenceVector ℝ (M i)) = 0 := by
        simpa [I] using subgraphIncidenceSum_eq_zero_of_notMem_verts (G := G) (M := M i) hv
      linarith
  have hweight_nonzero : ∑ i, w i ≠ 0 := by
    rw [hw_sum]
    norm_num
  obtain ⟨i₀, -, hi₀_nonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero hweight_nonzero
  have hM₀_perfect : (M i₀).IsPerfectMatching := hsupport_perfect i₀ hi₀_nonzero
  let zPerfect : ι → G.edgeSet → ℝ :=
    fun i ↦ if hwi : w i = 0 then G.subgraphIncidenceVector ℝ (M i₀) else z i
  have hzPerfect :
      ∀ i, ∃ N : G.Subgraph, N.IsPerfectMatching ∧ zPerfect i = G.subgraphIncidenceVector ℝ N := by
    intro i
    by_cases hwi : w i = 0
    · exact ⟨M i₀, hM₀_perfect, by simp [zPerfect, hwi]⟩
    · exact ⟨M i, hsupport_perfect i hwi, by simp [zPerfect, hwi, hVec i]⟩
  have hx_sum_perfect : ∑ i, w i • zPerfect i = x := by
    calc
      ∑ i, w i • zPerfect i = ∑ i, w i • z i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hwi : w i = 0
        · ext e
          simp [zPerfect, hwi]
        · ext e
          simp [zPerfect, hwi]
      _ = x := hx_sum
  rw [SimpleGraph.perfectMatchingPolytope, mem_convexHull_iff_exists_fintype]
  refine ⟨ι, inferInstance, w, zPerfect, hw_nonneg, hw_sum, ?_, hx_sum_perfect⟩
  intro i
  rcases hzPerfect i with ⟨N, hN, hzN⟩
  exact ⟨N, hN, hzN⟩

/-- Helper for Exercise 4.28: the Chapter 4.19 perfect-matching constraint system is convex. -/
lemma convex_perfectMatchingConstraintSet :
    Convex ℝ (perfectMatchingConstraintSet G) := by
  rw [perfectMatchingConstraintSet_eq_oddCutSystem (G := G)]
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx_nonneg, hx_sum, hx_cut⟩
  rcases hy with ⟨hy_nonneg, hy_sum, hy_cut⟩
  refine ⟨?_, ?_, ?_⟩
  · intro e
    have hcoord : (a • x + b • y) e = a * x e + b * y e := by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hcoord]
    nlinarith [hx_nonneg e, hy_nonneg e, ha, hb]
  · calc
      ∑ e, (a • x + b • y) e = a * ∑ e, x e + b * ∑ e, y e := by
          simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]
      _ = a * ((Fintype.card V : ℝ) / 2) + b * ((Fintype.card V : ℝ) / 2) := by
            rw [hx_sum, hy_sum]
      _ = (a + b) * ((Fintype.card V : ℝ) / 2) := by ring
      _ = (Fintype.card V : ℝ) / 2 := by rw [hab, one_mul]
  · intro S hS
    calc
      1 = a * 1 + b * 1 := by nlinarith
      _ ≤ a * (δ[G] S).sum x + b * (δ[G] S).sum y := by
            nlinarith [hx_cut S hS, hy_cut S hS, ha, hb]
      _ = (δ[G] S).sum (a • x + b • y) := by
            simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]

/-- Exercise 4.28 (1). The perfect matching polytope is exactly the
odd-cut/nonnegativity/total-edge-sum view `perfectMatchingOddCutSystem G`. This is the general
reformulation of Theorem 4.23 used in the first part of the exercise. -/
theorem perfectMatchingPolytope_eq_oddCutSystem
    : perfectMatchingPolytope G = perfectMatchingOddCutSystem G := by
  have hConstraint : perfectMatchingPolytope G = perfectMatchingConstraintSet G := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [SimpleGraph.perfectMatchingPolytope] at hx
      refine convexHull_min ?_ (convex_perfectMatchingConstraintSet (G := G)) hx
      intro y hy
      rcases hy with ⟨M, hM, rfl⟩
      exact subgraphIncidenceVector_mem_perfectMatchingConstraintSet (G := G) hM
    · intro x hx
      have hx_matching : x ∈ matchingPolytope G := by
        rw [matchingPolytope_eq_matchingConstraintSet (G := G)]
        exact mem_matchingConstraintSet_of_mem_perfectMatchingConstraintSet (G := G) hx
      exact perfectMatchingPolytope_of_mem_matchingPolytope_of_mem_perfectMatchingConstraintSet
        (G := G) hx_matching hx
  calc
    perfectMatchingPolytope G = perfectMatchingConstraintSet G := hConstraint
    _ = perfectMatchingOddCutSystem G := perfectMatchingConstraintSet_eq_oddCutSystem (G := G)

end OddCutSystem

section CubicGraph

variable [Fintype V] [DecidableRel G.Adj]

local instance : DecidableEq V := Classical.decEq V

/-- Helper for Exercise 4.28: in a perfect matching, two matched edges incident to the same vertex
must coincide. -/
lemma edge_eq_of_incident_in_perfectMatching {M : G.Subgraph} (hM : M.IsPerfectMatching)
    {e f : G.edgeSet} {u : V} (heM : e.1 ∈ M.edgeSet) (hfM : f.1 ∈ M.edgeSet)
    (hu_e : u ∈ (e : Sym2 V)) (hu_f : u ∈ (f : Sym2 V)) :
    e.1 = f.1 := by
  obtain ⟨w, huw, huniq⟩ := (Subgraph.isPerfectMatching_iff.mp hM) u
  have hAdj_e : M.Adj u (Sym2.Mem.other hu_e) := by
    -- Rewrite the stored edge as `s(u, other)` to read it as an adjacency in the subgraph.
    exact Subgraph.mem_edgeSet.1 (by simpa [Sym2.other_spec hu_e] using heM)
  have hAdj_f : M.Adj u (Sym2.Mem.other hu_f) := by
    -- The same endpoint-rewrite turns the second incident edge into another matched neighbor.
    exact Subgraph.mem_edgeSet.1 (by simpa [Sym2.other_spec hu_f] using hfM)
  have he_other : Sym2.Mem.other hu_e = w := huniq _ hAdj_e
  have hf_other : Sym2.Mem.other hu_f = w := huniq _ hAdj_f
  -- Unique matched neighbors force the two edge coordinates to agree.
  calc
    e.1 = s(u, Sym2.Mem.other hu_e) := by symm; exact Sym2.other_spec hu_e
    _ = s(u, w) := by rw [he_other]
    _ = s(u, Sym2.Mem.other hu_f) := by rw [hf_other]
    _ = f.1 := Sym2.other_spec hu_f

/-- Helper for Exercise 4.28: if a perfect matching omits an edge `e`, then at each endpoint of
`e` the matching uses a different incident edge. -/
lemma exists_matched_edge_at_endpoint_of_absent_edge {M : G.Subgraph} (hM : M.IsPerfectMatching)
    {e : G.edgeSet} {u : V} (_hu : u ∈ (e : Sym2 V)) (heM : e.1 ∉ M.edgeSet) :
    ∃ f : G.edgeSet, f.1 ∈ M.edgeSet ∧ u ∈ (f : Sym2 V) ∧ f.1 ≠ e.1 := by
  obtain ⟨w, huw, -⟩ := (Subgraph.isPerfectMatching_iff.mp hM) u
  let f : G.edgeSet := ⟨s(u, w), M.adj_sub huw⟩
  refine ⟨f, Subgraph.mem_edgeSet.2 huw, ?_, ?_⟩
  · -- The constructed matching edge was chosen to be incident to the endpoint `u`.
    change u ∈ s(u, w)
    simp
  · -- If this were the same edge as `e`, then `e` would belong to the matching after all.
    intro hfe
    exact heM (hfe ▸ Subgraph.mem_edgeSet.2 huw)

/-- Helper for Exercise 4.28: once the textbook `1 / 3` point lies in the perfect matching
polytope, some perfect matching must contain any chosen edge. -/
lemma exists_perfectMatching_containing_edge_of_constant_one_third_mem_polytope
    (hconst : (fun _ : G.edgeSet ↦ (1 / 3 : ℝ)) ∈ perfectMatchingPolytope G)
    (e : G.edgeSet) :
    ∃ M : G.Subgraph, M.IsPerfectMatching ∧ e.1 ∈ M.edgeSet := by
  classical
  rw [SimpleGraph.perfectMatchingPolytope, mem_convexHull_iff_exists_fintype] at hconst
  rcases hconst with ⟨ι, _, w, z, hw_nonneg, hw_sum, hz, hx⟩
  have hz' : ∀ i, ∃ M : G.Subgraph, M.IsPerfectMatching ∧ z i = G.subgraphIncidenceVector ℝ M := by
    intro i
    simpa using hz i
  choose M hMperf hVec using hz'
  have hcoord_e : ∑ i, w i * z i e = (1 / 3 : ℝ) := by
    -- Evaluate the barycentric equality at the coordinate of the chosen edge.
    simpa using weighted_sum_apply (G := G) w z hx e
  by_contra hnone
  have hz_zero : ∀ i, z i e = 0 := by
    intro i
    rw [hVec i]
    -- If every support perfect matching omits `e`, its incidence vector has zero `e`-coordinate.
    have he_absent : e.1 ∉ (M i).edgeSet := by
      intro he_mem
      exact hnone ⟨M i, hMperf i, he_mem⟩
    simp [SimpleGraph.subgraphIncidenceVector, he_absent]
  have hsum_zero : ∑ i, w i * z i e = 0 := by
    -- All summands vanish because all support matchings omit `e`.
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp [hz_zero i]
  linarith

/-- Helper for Exercise 4.28: once the textbook `1 / 3` point lies in the perfect matching
polytope, every edge has two distinct avoiding perfect matchings. -/
lemma exists_two_distinct_perfectMatchings_avoiding_edge_of_constant_one_third_mem_polytope
    (hconst : (fun _ : G.edgeSet ↦ (1 / 3 : ℝ)) ∈ perfectMatchingPolytope G)
    (e : G.edgeSet) :
    ∃ M₁ M₂ : G.Subgraph,
      M₁.IsPerfectMatching ∧
        M₂.IsPerfectMatching ∧ M₁ ≠ M₂ ∧ e.1 ∉ M₁.edgeSet ∧ e.1 ∉ M₂.edgeSet := by
  classical
  rw [SimpleGraph.perfectMatchingPolytope, mem_convexHull_iff_exists_fintype] at hconst
  rcases hconst with ⟨ι, _, w, z, hw_nonneg, hw_sum, hz, hx⟩
  have hz' : ∀ i, ∃ M : G.Subgraph, M.IsPerfectMatching ∧ z i = G.subgraphIncidenceVector ℝ M := by
    intro i
    simpa using hz i
  choose M hMperf hVec using hz'
  have hcoord_e : ∑ i, w i * z i e = (1 / 3 : ℝ) := by
    -- The constant point has value `1 / 3` at every edge coordinate.
    simpa using weighted_sum_apply (G := G) w z hx e
  have hex_avoid : ∃ M : G.Subgraph, M.IsPerfectMatching ∧ e.1 ∉ M.edgeSet := by
    by_contra hnone
    have hz_one : ∀ i, z i e = 1 := by
      intro i
      rw [hVec i]
      -- If no perfect matching avoids `e`, every support perfect matching contains it.
      have he_mem : e.1 ∈ (M i).edgeSet := by
        by_contra he_absent
        exact hnone ⟨M i, hMperf i, he_absent⟩
      simp [SimpleGraph.subgraphIncidenceVector, he_mem]
    have hsum_one : ∑ i, w i * z i e = 1 := by
      calc
        ∑ i, w i * z i e = ∑ i, w i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [hz_one i]
        _ = 1 := hw_sum
    linarith
  obtain ⟨M₀, hM₀perf, hM₀avoid⟩ := hex_avoid
  by_contra hnot
  have huniq_avoider :
      ∀ M : G.Subgraph, M.IsPerfectMatching → e.1 ∉ M.edgeSet → M = M₀ := by
    intro M hM havoid
    by_contra hneq
    exact hnot ⟨M₀, M, hM₀perf, hM, by simpa [ne_comm] using hneq, hM₀avoid, havoid⟩
  let u : V := e.1.out.1
  have hu : u ∈ (e : Sym2 V) := by
    -- Use one explicit endpoint of the edge `e`.
    simpa [u] using Sym2.out_fst_mem e.1
  obtain ⟨f, hfmem, huf, hfe_ne⟩ :=
    exists_matched_edge_at_endpoint_of_absent_edge (G := G) hM₀perf hu hM₀avoid
  have hcoord_f : ∑ i, w i * z i f = (1 / 3 : ℝ) := by
    -- The same constant point has value `1 / 3` at the auxiliary edge `f`.
    simpa using weighted_sum_apply (G := G) w z hx f
  have hpointwise :
      ∀ i, w i * z i f = w i - w i * z i e := by
    intro i
    by_cases he_mem : e.1 ∈ (M i).edgeSet
    · have hf_absent : f.1 ∉ (M i).edgeSet := by
        intro hf_mem
        exact hfe_ne
          (edge_eq_of_incident_in_perfectMatching (G := G) (M := M i) (hMperf i)
            he_mem hf_mem hu huf).symm
      rw [hVec i]
      -- A perfect matching containing `e` must omit the distinct edge `f` through the same vertex.
      simp [SimpleGraph.subgraphIncidenceVector, he_mem, hf_absent]
    · have hMi_eq : M i = M₀ := huniq_avoider (M i) (hMperf i) he_mem
      have hf_mem : f.1 ∈ (M i).edgeSet := by simpa [hMi_eq] using hfmem
      rw [hVec i]
      -- Any support perfect matching avoiding `e` is forced to be `M₀`, hence it contains `f`.
      simp [SimpleGraph.subgraphIncidenceVector, he_mem, hf_mem]
  have hsum_f : ∑ i, w i * z i f = (2 / 3 : ℝ) := by
    -- Summing the pointwise identity shows that the `f`-coordinate must be `2 / 3`.
    calc
      ∑ i, w i * z i f = ∑ i, (w i - w i * z i e) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact hpointwise i
      _ = ∑ i, w i - ∑ i, w i * z i e := by
        rw [Finset.sum_sub_distrib]
      _ = (1 : ℝ) - (1 / 3 : ℝ) := by rw [hw_sum, hcoord_e]
      _ = (2 / 3 : ℝ) := by norm_num
  linarith

/-- Helper for Exercise 4.28: the edge-set incidence filter over `G.edgeSet` has cardinality
`degree v`. -/
lemma card_incident_edge_filter_eq_degree (v : V) :
    (Finset.univ.filter fun e : G.edgeSet ↦ v ∈ (e : Sym2 V)).card = G.degree v := by
  classical
  let incidentEquiv : {e : G.edgeSet // v ∈ (e : Sym2 V)} ≃ G.incidenceSet v :=
    { toFun := fun e ↦ ⟨e.1, ⟨e.1.2, e.2⟩⟩
      invFun := fun e ↦ ⟨⟨e.1, e.2.1⟩, e.2.2⟩
      left_inv := fun e ↦ by cases e; rfl
      right_inv := fun e ↦ by cases e; rfl }
  -- Reinterpret the filtered finset as the subtype of incident edge-coordinates.
  calc
    (Finset.univ.filter fun e : G.edgeSet ↦ v ∈ (e : Sym2 V)).card
        = Fintype.card {e : G.edgeSet // v ∈ (e : Sym2 V)} := by
            symm
            exact Fintype.card_subtype (fun e : G.edgeSet ↦ v ∈ (e : Sym2 V))
    _ = Fintype.card (G.incidenceSet v) := Fintype.card_congr incidentEquiv
    _ = G.degree v := G.card_incidenceSet_eq_degree v

/-- Helper for Exercise 4.28: an edge lies in the induced edge finset on `S` exactly when both of
its endpoints lie in `S`. -/
lemma mem_inducedEdgeFinset_endpoints_iff (S : Set V) (e : G.edgeSet) :
    e ∈ E[G] S ↔ e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S := by
  -- Route correction: read induced-edge membership directly at the concrete endpoints from
  -- `e.1.out`, avoiding the unstable `Sym2.eq_iff` transport route.
  rw [mem_inducedEdgeFinset_iff]
  constructor
  · intro he
    -- Rewrite the edge coordinate by `e.1.out_eq` and then unfold induced-subgraph membership.
    rw [← e.1.out_eq, Subgraph.mem_edgeSet] at he
    exact ⟨he.1, he.2.1⟩
  · rintro ⟨hu, hv⟩
    rw [← e.1.out_eq, Subgraph.mem_edgeSet]
    -- The ambient adjacency comes from the fact that `e` is already an edge of `G`.
    have hmem : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
      simpa [e.1.out_eq] using e.2
    have hadj : G.Adj e.1.out.1 e.1.out.2 := G.mem_edgeSet.mp hmem
    exact ⟨hu, hv, by simpa using hadj⟩

/-- Helper for Exercise 4.28: an edge lies in the cut finset on `S` exactly when its endpoints are
separated by `S`. -/
lemma mem_cutEdgeFinset_endpoints_iff (S : Set V) (e : G.edgeSet) :
    e ∈ δ[G] S ↔
      (e.1.out.1 ∈ S ∧ e.1.out.2 ∉ S) ∨ (e.1.out.2 ∈ S ∧ e.1.out.1 ∉ S) := by
  constructor
  · intro he
    rcases (mem_cutEdgeFinset_iff G).1 he with ⟨u, huS, v, hvS, huv⟩
    have huv' : s(u, v) = s(e.1.out.1, e.1.out.2) := huv.trans e.1.out_eq.symm
    rw [Sym2.eq_iff] at huv'
    rcases huv' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨huS, hvS⟩
    · exact Or.inr ⟨huS, hvS⟩
  · intro he
    rcases he with ⟨huS, hvS⟩ | ⟨hvS, huS⟩
    · exact (mem_cutEdgeFinset_iff G).2 ⟨e.1.out.1, huS, e.1.out.2, hvS, e.1.out_eq⟩
    · refine (mem_cutEdgeFinset_iff G).2 ?_
      exact ⟨e.1.out.2, hvS, e.1.out.1, huS, Sym2.eq_swap.trans e.1.out_eq⟩

/-- Helper for Exercise 4.28: an induced edge cannot simultaneously be a cut edge. -/
lemma not_mem_cutEdgeFinset_of_mem_inducedEdgeFinset {S : Set V} {e : G.edgeSet}
    (he : e ∈ E[G] S) : e ∉ δ[G] S := by
  intro hcut
  -- The induced-edge and cut-edge endpoint characterizations are incompatible.
  rcases (mem_inducedEdgeFinset_endpoints_iff (G := G) S e).1 he with ⟨hu, hv⟩
  rcases (mem_cutEdgeFinset_endpoints_iff (G := G) S e).1 hcut with hsep | hsep
  · exact hsep.2 hv
  · exact hsep.2 hu

/-- Helper for Exercise 4.28: the endpoint finset of an edge-coordinate is the unordered pair of
its canonical `Sym2.out` endpoints. -/
lemma edge_toFinset_eq_pair (e : G.edgeSet) :
    (((e : Sym2 V).toFinset : Finset V)) =
      ({(e : Sym2 V).out.1, (e : Sym2 V).out.2} : Finset V) := by
  -- Rewrite the edge by its canonical `out` representative before taking `toFinset`.
  calc
    ((e : Sym2 V).toFinset : Finset V) = s((e : Sym2 V).out.1, (e : Sym2 V).out.2).toFinset := by
      exact congrArg Sym2.toFinset ((e : Sym2 V).out_eq).symm
    _ = ({(e : Sym2 V).out.1, (e : Sym2 V).out.2} : Finset V) := by
      exact Sym2.toFinset_mk_eq

/-- Helper for Exercise 4.28: filtering a two-point endpoint finset by membership in `S` has
cardinality `2`, `1`, or `0` according as both, one, or none of the endpoints lie in `S`. -/
lemma pair_filter_card_of_ne (a b : V) (hab : a ≠ b) (S : Set V) :
    ((({a, b} : Finset V).filter fun v ↦ v ∈ S).card : ℕ) =
      if a ∈ S ∧ b ∈ S then 2 else if a ∈ S ∨ b ∈ S then 1 else 0 := by
  classical
  -- Compute the filtered pair directly by the four endpoint-membership cases.
  by_cases ha : a ∈ S
  · by_cases hb : b ∈ S
    · have hfilter :
          ({a, b} : Finset V).filter (fun v ↦ v ∈ S) = {a, b} := by
        -- When both endpoints lie in `S`, the filter keeps the whole pair.
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
          ({a, b} : Finset V).filter (fun v ↦ v ∈ S) = {a} := by
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
          exact Finset.mem_filter.mpr ⟨by simp, ha⟩
      rw [hfilter]
      simp [ha, hb]
  · by_cases hb : b ∈ S
    · have hfilter :
          ({a, b} : Finset V).filter (fun v ↦ v ∈ S) = {b} := by
        -- When only `b` lies in `S`, the filter keeps exactly `{b}`.
        ext v
        constructor
        · intro hv
          rcases Finset.mem_filter.mp hv with ⟨hv, hvS⟩
          rcases Finset.mem_insert.mp hv with hv' | hv'
          · exfalso
            exact ha (hv' ▸ hvS)
          · have hvb : v = b := by simpa using hv'
            subst hvb
            simp
        · intro hv
          rcases Finset.mem_singleton.mp hv with rfl
          exact Finset.mem_filter.mpr ⟨by simp [hab], hb⟩
      rw [hfilter]
      simp [ha, hb]
    · have hfilter :
          ({a, b} : Finset V).filter (fun v ↦ v ∈ S) = ∅ := by
        -- When neither endpoint lies in `S`, the filtered endpoint set is empty.
        ext v
        constructor
        · intro hv
          rcases Finset.mem_filter.mp hv with ⟨hv, hvS⟩
          rcases Finset.mem_insert.mp hv with rfl | hv'
          · exact (ha hvS).elim
          · exact (hb (by rw [Finset.mem_singleton.mp hv'] at hvS; exact hvS)).elim
        · intro hv
          exact False.elim (Finset.notMem_empty v hv)
      rw [hfilter]
      simp [ha, hb]

/-- Helper for Exercise 4.28: each edge contributes `2`, `1`, or `0` to the endpoint count on
`S` according as it lies inside `S`, crosses the cut, or misses `S`. -/
lemma endpoint_count_eq_two_or_one_or_zero (S : Set V) (e : G.edgeSet) :
    ((e : Sym2 V).toFinset.filter fun v : V ↦ v ∈ S).card =
      if e ∈ E[G] S then 2 else if e ∈ δ[G] S then 1 else 0 := by
  classical
  have hout_ne : e.1.out.1 ≠ e.1.out.2 := by
    -- Edge coordinates of `G` are non-diagonal, so their canonical endpoints are distinct.
    intro hout_eq
    have hdiag : e.1.IsDiag := by
      rw [← e.1.out_eq, Sym2.mk_isDiag_iff]
      exact hout_eq
    exact (G.not_isDiag_of_mem_edgeSet e.2) hdiag
  rw [edge_toFinset_eq_pair (G := G) e]
  rw [pair_filter_card_of_ne (a := (e : Sym2 V).out.1) (b := (e : Sym2 V).out.2)
    (by simpa using hout_ne) (S := S)]
  -- Translate the four endpoint-membership cases into induced-edge versus cut-edge membership.
  by_cases hfst : (e : Sym2 V).out.1 ∈ S
  · by_cases hsnd : (e : Sym2 V).out.2 ∈ S
    · have hfst' : e.1.out.1 ∈ S := by simpa using hfst
      have hsnd' : e.1.out.2 ∈ S := by simpa using hsnd
      simp [mem_inducedEdgeFinset_endpoints_iff, mem_cutEdgeFinset_endpoints_iff, hfst, hsnd,
        hfst', hsnd']
    · have hfst' : e.1.out.1 ∈ S := by simpa using hfst
      have hsnd' : e.1.out.2 ∉ S := by simpa using hsnd
      simp [mem_inducedEdgeFinset_endpoints_iff, mem_cutEdgeFinset_endpoints_iff, hfst, hsnd,
        hfst', hsnd']
  · by_cases hsnd : (e : Sym2 V).out.2 ∈ S
    · have hfst' : e.1.out.1 ∉ S := by simpa using hfst
      have hsnd' : e.1.out.2 ∈ S := by simpa using hsnd
      simp [mem_inducedEdgeFinset_endpoints_iff, mem_cutEdgeFinset_endpoints_iff, hfst, hsnd,
        hfst', hsnd']
    · have hfst' : e.1.out.1 ∉ S := by simpa using hfst
      have hsnd' : e.1.out.2 ∉ S := by simpa using hsnd
      simp [mem_inducedEdgeFinset_endpoints_iff, mem_cutEdgeFinset_endpoints_iff, hfst, hsnd,
        hfst', hsnd']

/-- Helper for Exercise 4.28: summing the degrees on a vertex subset counts each internal edge
twice and each cut edge once. -/
lemma sum_degrees_on_set_eq_twice_induced_edges_add_cut_card (S : Set V) :
    Finset.sum S.toFinset (fun v ↦ G.degree v) = 2 * (E[G] S).card + (δ[G] S).card := by
  classical
  calc
    Finset.sum S.toFinset (fun v ↦ G.degree v)
        = Finset.sum S.toFinset
            (fun v ↦ (Finset.univ.filter fun e : G.edgeSet ↦ v ∈ (e : Sym2 V)).card) := by
            -- Rewrite each degree as the number of incident edge-coordinates.
            refine Finset.sum_congr rfl ?_
            intro v hv
            symm
            exact card_incident_edge_filter_eq_degree (G := G) v
    _ = Finset.sum S.toFinset
          (fun v ↦ Finset.sum Finset.univ fun e : G.edgeSet ↦ if v ∈ (e : Sym2 V) then 1 else 0) := by
          -- Expand each filtered cardinality as a sum of endpoint indicators.
          refine Finset.sum_congr rfl ?_
          intro v hv
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = Finset.sum Finset.univ
          (fun e : G.edgeSet ↦ Finset.sum S.toFinset fun v ↦ if v ∈ (e : Sym2 V) then 1 else 0) := by
          -- Commute the vertex-edge double sum so we can count each edge once.
          rw [Finset.sum_comm]
    _ = Finset.sum Finset.univ
          (fun e : G.edgeSet ↦ ((e : Sym2 V).toFinset.filter fun v : V ↦ v ∈ S).card) := by
          -- For a fixed edge, the surviving vertex indicators are exactly its endpoints lying in `S`.
          refine Finset.sum_congr rfl ?_
          intro e he
          calc
            Finset.sum S.toFinset (fun v ↦ if v ∈ (e : Sym2 V) then 1 else 0)
                = (S.toFinset.filter fun v : V ↦ v ∈ (e : Sym2 V)).card := by
                    rw [← Finset.sum_filter, Finset.card_eq_sum_ones]
            _ = ((e : Sym2 V).toFinset.filter fun v : V ↦ v ∈ S).card := by
                  have hfilter :
                      S.toFinset.filter (fun v : V ↦ v ∈ (e : Sym2 V)) =
                        (e : Sym2 V).toFinset.filter (fun v : V ↦ v ∈ S) := by
                    ext v
                    simp [Sym2.mem_toFinset, and_left_comm, and_assoc, and_comm]
                  rw [hfilter]
    _ = Finset.sum Finset.univ
          (fun e : G.edgeSet ↦ if e ∈ E[G] S then 2 else if e ∈ δ[G] S then 1 else 0) := by
          -- The endpoint-count lemma classifies each edge by inside/cut/outside.
          refine Finset.sum_congr rfl ?_
          intro e he
          exact endpoint_count_eq_two_or_one_or_zero (G := G) S e
    _ = Finset.sum Finset.univ
          (fun e : G.edgeSet ↦ (if e ∈ E[G] S then 2 else 0) + (if e ∈ δ[G] S then 1 else 0)) := by
          -- Internal and cut edges are disjoint, so the nested `if` splits into two indicators.
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases hind : e ∈ E[G] S
          · have hnotCut : e ∉ δ[G] S :=
              not_mem_cutEdgeFinset_of_mem_inducedEdgeFinset (G := G) hind
            simp [hind, hnotCut]
          · by_cases hcut : e ∈ δ[G] S
            · simp [hind, hcut]
            · simp [hind, hcut]
    _ = Finset.sum Finset.univ (fun e : G.edgeSet ↦ if e ∈ E[G] S then 2 else 0) +
          Finset.sum Finset.univ (fun e : G.edgeSet ↦ if e ∈ δ[G] S then 1 else 0) := by
            rw [Finset.sum_add_distrib]
    _ = 2 * (E[G] S).card + (δ[G] S).card := by
          have hInduced :
              Finset.sum Finset.univ (fun e : G.edgeSet ↦ if e ∈ E[G] S then 2 else 0) =
                2 * (E[G] S).card := by
            have hfilterE :
                Finset.univ.filter (fun e : G.edgeSet ↦ e ∈ E[G] S) = E[G] S := by
              ext e
              simp
            calc
              Finset.sum Finset.univ (fun e : G.edgeSet ↦ if e ∈ E[G] S then 2 else 0) =
                  Finset.sum (Finset.univ.filter fun e : G.edgeSet ↦ e ∈ E[G] S)
                    (fun _ : G.edgeSet ↦ (2 : ℕ)) := by
                rw [← Finset.sum_filter]
              _ = Finset.sum (E[G] S) (fun _ : G.edgeSet ↦ (2 : ℕ)) := by
                rw [hfilterE]
              _ = (E[G] S).card * 2 := by simp
              _ = 2 * (E[G] S).card := by rw [Nat.mul_comm]
          have hCut :
              Finset.sum Finset.univ (fun e : G.edgeSet ↦ if e ∈ δ[G] S then 1 else 0) =
                (δ[G] S).card := by
            have hfilterCut :
                Finset.univ.filter (fun e : G.edgeSet ↦ e ∈ δ[G] S) = δ[G] S := by
              ext e
              simp
            calc
              Finset.sum Finset.univ (fun e : G.edgeSet ↦ if e ∈ δ[G] S then 1 else 0) =
                  Finset.sum (Finset.univ.filter fun e : G.edgeSet ↦ e ∈ δ[G] S)
                    (fun _ : G.edgeSet ↦ (1 : ℕ)) := by
                rw [← Finset.sum_filter]
              _ = Finset.sum (δ[G] S) (fun _ : G.edgeSet ↦ (1 : ℕ)) := by
                rw [hfilterCut]
              _ = (δ[G] S).card := by simp
          simpa [hInduced, hCut]

/-- Helper for Exercise 4.28: in a cubic graph, every odd vertex subset has an odd cut. -/
lemma odd_cut_card_odd_of_cubic (hcubic : G.IsRegularOfDegree 3) (S : Set V) :
    Odd S.ncard → Odd (δ[G] S).card := by
  intro hOddS
  rw [Set.ncard_eq_toFinset_card'] at hOddS
  have hDegreeSum :
      Finset.sum S.toFinset (fun v ↦ G.degree v) = 3 * S.toFinset.card := by
    -- Regularity turns the left-hand side into a constant sum over `S`.
    calc
      Finset.sum S.toFinset (fun v ↦ G.degree v)
          = Finset.sum S.toFinset (fun _ : V ↦ 3) := by
              refine Finset.sum_congr rfl ?_
              intro v hv
              rw [hcubic.degree_eq]
      _ = S.toFinset.card * 3 := by simp
      _ = 3 * S.toFinset.card := by rw [Nat.mul_comm]
  have hParity :
      3 * S.toFinset.card = 2 * (E[G] S).card + (δ[G] S).card := by
    calc
      3 * S.toFinset.card = Finset.sum S.toFinset (fun v ↦ G.degree v) := by
            symm
            exact hDegreeSum
      _ = 2 * (E[G] S).card + (δ[G] S).card :=
            sum_degrees_on_set_eq_twice_induced_edges_add_cut_card (G := G) S
  have hOddCard : (δ[G] S).card % 2 = 1 := by
    have hSetOdd : S.toFinset.card % 2 = 1 := Nat.odd_iff.mp hOddS
    omega
  exact Nat.odd_iff.mpr hOddCard

/-- Helper for Exercise 4.28: a walk from `S` to its complement must use a cut edge. -/
lemma walk_meets_cut_of_endpoints_separated {S : Set V} {u v : V} (p : G.Walk u v)
    (huS : u ∈ S) (hvS : v ∉ S) :
    ∃ f : G.edgeSet, f ∈ δ[G] S ∧ (f : Sym2 V) ∈ p.edges := by
  induction p with
  | nil =>
      exact (hvS huS).elim
  | @cons u w v huw p ih =>
      by_cases hwS : w ∈ S
      · -- If the first step stays inside `S`, the crossing must occur later in the walk.
        rcases ih hwS hvS with ⟨f, hfCut, hfEdges⟩
        exact ⟨f, hfCut, by simp [hfEdges]⟩
      · -- Otherwise the first edge already crosses the cut.
        let f : G.edgeSet := ⟨s(u, w), huw⟩
        refine ⟨f, ?_, ?_⟩
        · exact (mem_cutEdgeFinset_iff G).2 ⟨u, huS, w, hwS, rfl⟩
        · simp [f]

/-- Helper for Exercise 4.28: a singleton cut edge is a bridge. -/
lemma isBridge_of_cutEdgeFinset_eq_singleton {S : Set V} {e : G.edgeSet}
    (hcut : δ[G] S = {e}) : G.IsBridge e.1 := by
  have hbridge_oriented {u v : V}
      (huS : u ∈ S) (hvS : v ∉ S) (huv : s(u, v) = e.1) : G.IsBridge e.1 := by
    rw [← huv, SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges]
    refine ⟨?_, ?_⟩
    · -- The singleton cut edge is already an ambient edge of `G`.
      exact G.mem_edgeSet.mp (by simpa [huv] using e.2)
    · intro p
      -- Any walk between the separated endpoints meets the cut, hence it uses the unique cut edge.
      rcases walk_meets_cut_of_endpoints_separated (G := G) p huS hvS with ⟨f, hfCut, hfEdges⟩
      have hfEq : f = e := by
        simpa [hcut] using hfCut
      simpa [huv] using hfEq ▸ hfEdges
  have heCut : e ∈ δ[G] S := by
    simpa [hcut]
  rcases (mem_cutEdgeFinset_endpoints_iff (G := G) S e).1 heCut with hsep | hsep
  · -- Use the endpoint order matching the side of the cut.
    exact hbridge_oriented hsep.1 hsep.2 e.1.out_eq
  · -- Swap the endpoints to fit the walk characterization of bridges.
    exact hbridge_oriented hsep.1 hsep.2 (Sym2.eq_swap.trans e.1.out_eq)

/-- Helper for Exercise 4.28: every odd cut in a bridgeless cubic graph has size at least `3`. -/
lemma odd_cut_card_ge_three_of_bridgeless_cubic
    (hbridgeless : ∀ e : G.edgeSet, ¬ G.IsBridge e.1) (hcubic : G.IsRegularOfDegree 3)
    (S : Set V) : Odd S.ncard → 3 ≤ (δ[G] S).card := by
  intro hoddS
  have hoddCut : Odd (δ[G] S).card :=
    odd_cut_card_odd_of_cubic (G := G) hcubic S hoddS
  have hneZero : (δ[G] S).card ≠ 0 := by
    intro hzero
    simpa [hzero] using hoddCut
  have hneOne : (δ[G] S).card ≠ 1 := by
    intro hone
    rcases Finset.card_eq_one.mp hone with ⟨e, he⟩
    exact hbridgeless e (isBridge_of_cutEdgeFinset_eq_singleton (G := G) (S := S) (e := e) he)
  have hcutMod : (δ[G] S).card % 2 = 1 := Nat.odd_iff.mp hoddCut
  have honeLt : 1 < (δ[G] S).card :=
    Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hneZero, hneOne⟩
  -- An odd natural number strictly larger than `1` is at least `3`.
  omega

/-- Helper for Exercise 4.28: a finite cubic graph satisfies `2 * |E(G)| = 3 * |V|`. -/
lemma two_mul_card_edgeSet_eq_three_mul_card_vertices_of_cubic
    (hcubic : G.IsRegularOfDegree 3) :
    2 * Fintype.card G.edgeSet = 3 * Fintype.card V := by
  -- Global handshaking turns the degree-`3` hypothesis into the standard edge-count identity.
  calc
    2 * Fintype.card G.edgeSet = 2 * G.edgeFinset.card := by
          rw [SimpleGraph.card_edgeSet]
    _ = ∑ v : V, G.degree v := by
          symm
          exact G.sum_degrees_eq_twice_card_edges
    _ = ∑ v : V, 3 := by
          refine Finset.sum_congr rfl ?_
          intro v hv
          rw [hcubic.degree_eq]
    _ = 3 * Fintype.card V := by
          simp [mul_comm]

/-- Helper for Exercise 4.28: the constant `1 / 3` edge-vector satisfies the odd-cut,
nonnegativity, and total-edge-sum constraints of a bridgeless cubic graph. -/
lemma constant_one_third_mem_perfectMatchingOddCutSystem_of_bridgeless_cubic
    (hbridgeless : ∀ e : G.edgeSet, ¬ G.IsBridge e.1) (hcubic : G.IsRegularOfDegree 3) :
    (fun _ : G.edgeSet ↦ (1 / 3 : ℝ)) ∈ perfectMatchingOddCutSystem G := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    -- Every coordinate of the constant point is nonnegative.
    norm_num
  · have hcardEdges : 2 * Fintype.card G.edgeSet = 3 * Fintype.card V := by
      -- Reuse the cubic handshaking identity before solving the real-valued total-sum equation.
      exact two_mul_card_edgeSet_eq_three_mul_card_vertices_of_cubic (G := G) hcubic
    have hcardEdgesReal : (2 : ℝ) * Fintype.card G.edgeSet = 3 * Fintype.card V := by
      exact_mod_cast hcardEdges
    -- Evaluate the constant edge-sum and solve the resulting linear identity over `ℝ`.
    have hsumConst :
        (∑ e : G.edgeSet, (1 / 3 : ℝ)) = (Fintype.card G.edgeSet : ℝ) * (1 / 3 : ℝ) := by
      simp
    rw [hsumConst]
    linarith
  · intro S hoddS
    have hcutGe :
        3 ≤ (δ[G] S).card :=
      odd_cut_card_ge_three_of_bridgeless_cubic (G := G) hbridgeless hcubic S hoddS
    have hcutGeReal : (3 : ℝ) ≤ (δ[G] S).card := by
      exact_mod_cast hcutGe
    have hsumCut :
        Finset.sum (δ[G] S) (fun _ : G.edgeSet ↦ (1 / 3 : ℝ)) =
          ((δ[G] S).card : ℝ) * (1 / 3 : ℝ) := by
      simp
    -- The odd-cut lower bound `|δ(S)| ≥ 3` certifies the constant `1 / 3` point.
    rw [hsumCut]
    nlinarith

/-- Helper for Exercise 4.28: the textbook `1 / 3` point belongs to the perfect matching
polytope of a bridgeless cubic graph. -/
lemma constant_one_third_mem_perfectMatchingPolytope_of_bridgeless_cubic
    (hbridgeless : ∀ e : G.edgeSet, ¬ G.IsBridge e.1) (hcubic : G.IsRegularOfDegree 3) :
    (fun _ : G.edgeSet ↦ (1 / 3 : ℝ)) ∈ perfectMatchingPolytope G := by
  classical
  -- Route correction: the remaining source-faithful gap is exactly the graph-theoretic bridge
  -- `subset handshaking -> odd cuts have size at least 3 -> the constant 1/3 point is feasible`.
  rw [perfectMatchingPolytope_eq_oddCutSystem (G := G)]
  exact constant_one_third_mem_perfectMatchingOddCutSystem_of_bridgeless_cubic (G := G)
    hbridgeless hcubic

/-- Part (2) of Exercise 4.28. In a finite bridgeless cubic graph, every edge belongs to some
perfect matching. -/
theorem exists_perfectMatching_containing_edge
    (hbridgeless : ∀ e : G.edgeSet, ¬ G.IsBridge e.1) (hcubic : G.IsRegularOfDegree 3)
    (e : G.edgeSet) :
    ∃ M : G.Subgraph, M.IsPerfectMatching ∧ e.1 ∈ M.edgeSet := by
  classical
  -- Use the textbook `1 / 3` point and then read off the `e`-coordinate in a convex decomposition.
  exact exists_perfectMatching_containing_edge_of_constant_one_third_mem_polytope (G := G)
    (constant_one_third_mem_perfectMatchingPolytope_of_bridgeless_cubic (G := G)
      hbridgeless hcubic) e

/-- Part (3) of Exercise 4.28. In a finite bridgeless cubic graph, every edge is omitted by two
distinct perfect matchings. -/
theorem exists_two_distinct_perfectMatchings_avoiding_edge
    (hbridgeless : ∀ e : G.edgeSet, ¬ G.IsBridge e.1) (hcubic : G.IsRegularOfDegree 3)
    (e : G.edgeSet) :
    ∃ M₁ M₂ : G.Subgraph,
      M₁.IsPerfectMatching ∧
        M₂.IsPerfectMatching ∧ M₁ ≠ M₂ ∧ e.1 ∉ M₁.edgeSet ∧ e.1 ∉ M₂.edgeSet := by
  classical
  -- The second coordinate contradiction is the source endgame once the `1 / 3` point is available.
  exact exists_two_distinct_perfectMatchings_avoiding_edge_of_constant_one_third_mem_polytope
    (G := G)
    (constant_one_third_mem_perfectMatchingPolytope_of_bridgeless_cubic (G := G)
      hbridgeless hcubic) e

end CubicGraph

end Exercise_4_28
