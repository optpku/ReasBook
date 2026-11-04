/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_theorem_3_24
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_9.ch3_sec3_9_theorem_3_27
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_proposition_2_12
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4.ch4_sec4_4_corollary_4_19
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4_4.ch4_sec4_4_4_theorem_4_24
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_12.ch4_sec4_12_exercise_4_28
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_12.ch4_sec4_12_exercise_4_38.FacetTransport
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.incident_edge_finset

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Matrix

attribute [local instance] Classical.propDecidable

section Exercise74

open SimpleGraph

variable {V : Type} [Fintype V]
variable (G : SimpleGraph V)

noncomputable local instance : DecidableEq V := Classical.decEq V
noncomputable local instance : DecidableRel G.Adj := Classical.decRel G.Adj

/-- The degree-system relaxation
`{x ∈ ℝ^E | ∑_{e ∈ δ(v)} x_e ≤ 1 for all v, x ≥ 0}` of the matching polytope. -/
def matching_degree_constraint_set : Set (G.edgeSet → ℝ) :=
  {x |
    (∀ v : V, (incidentEdgeFinset G v).sum x ≤ 1) ∧
      ∀ e, 0 ≤ x e}

/-- Membership in `matching_degree_constraint_set G` means satisfying the degree inequalities and
the nonnegativity constraints. -/
theorem mem_matching_degree_constraint_set_iff
    {x : G.edgeSet → ℝ} :
    x ∈ matching_degree_constraint_set G ↔
      (∀ v : V, (incidentEdgeFinset G v).sum x ≤ 1) ∧
        ∀ e, 0 ≤ x e := Iff.rfl

/-- The coefficient vector of the blossom inequality attached to the odd vertex set `U`. -/
def blossom_vector (U : Set V) : G.edgeSet → ℝ :=
  fun e ↦ if e ∈ E[G] U then 1 else 0

/-- `blossom_vector G U` is `1` on the induced-edge coordinates `E[G] U` and `0` elsewhere. -/
theorem blossom_vector_apply
    (U : Set V) (e : G.edgeSet) :
    blossom_vector G U e = if e ∈ E[G] U then 1 else 0 := by
  rfl

/-- The right-hand side of the blossom inequality attached to the odd vertex set `U`. -/
def blossom_rhs (U : Set V) : ℝ :=
  ((U.ncard : ℝ) - 1) / 2

/-- The equality face of the blossom inequality on the matching polytope. -/
def blossom_face (U : Set V) : Set (G.edgeSet → ℝ) :=
  G.matchingPolytope ∩ {x : G.edgeSet → ℝ | blossom_vector G U ⬝ᵥ x = blossom_rhs U}

/-- Membership in `blossom_face G U` means belonging to the matching polytope and meeting the
blossom inequality at equality. -/
theorem mem_blossom_face_iff
    {U : Set V} {x : G.edgeSet → ℝ} :
    x ∈ blossom_face G U ↔
      x ∈ G.matchingPolytope ∧ blossom_vector G U ⬝ᵥ x = blossom_rhs U := by
  simp [blossom_face]

/-- Helper for Exercise 7.4: the blossom coefficient vector defines a continuous linear functional
on the ambient edge-coordinate space. -/
private noncomputable def blossomStrongDual
    (U : Set V) : StrongDual ℝ (G.edgeSet → ℝ) :=
  ∑ e, blossom_vector G U e • ContinuousLinearMap.proj e

/-- Helper for Exercise 7.4: the strong-dual functional attached to `blossom_vector G U`
evaluates as the corresponding dot product. -/
private lemma blossomStrongDual_apply
    (U : Set V) (x : G.edgeSet → ℝ) :
    blossomStrongDual G U x = blossom_vector G U ⬝ᵥ x := by
  -- Expand the coordinate projections and collect the finite sum into the dot product.
  simp [blossomStrongDual, dotProduct]

/-- The aggregated left-hand-side coefficient of an edge under row multipliers `u` on the degree
constraints and slack multipliers `v` on the nonnegativity constraints. -/
private def matching_degree_chvatal_coeff
    (u : V → ℝ) (v : G.edgeSet → ℝ) : G.edgeSet → ℝ :=
  fun e ↦
    (Finset.univ.filter fun w : V ↦ e ∈ incidentEdgeFinset G w).sum u - v e

/-- A Chvátal inequality for the matching degree system is obtained from nonnegative row
multipliers on the degree inequalities together with nonnegative slack multipliers on the
nonnegativity constraints, with integral aggregate edge coefficients. -/
def IsMatchingDegreeSystemChvatalInequality
    (c : G.edgeSet → ℝ) (β : ℝ) : Prop :=
  ∃ u : V → ℝ, ∃ v : G.edgeSet → ℝ,
    (∀ w, 0 ≤ u w) ∧
      (∀ e, 0 ≤ v e) ∧
        (∀ e, ∃ z : ℤ, matching_degree_chvatal_coeff G u v e = (z : ℝ)) ∧
          c = matching_degree_chvatal_coeff G u v ∧
            β = (Int.floor (∑ w, u w) : ℝ)

/-- `IsMatchingDegreeSystemChvatalInequality G c β` unfolds to existence of nonnegative row and
slack multipliers whose aggregate coefficients are integral and equal to `c`, with right-hand side
`β`. -/
theorem isMatchingDegreeSystemChvatalInequality_iff
    (c : G.edgeSet → ℝ) (β : ℝ) :
    IsMatchingDegreeSystemChvatalInequality G c β ↔
      ∃ u : V → ℝ, ∃ v : G.edgeSet → ℝ,
        (∀ w, 0 ≤ u w) ∧
          (∀ e, 0 ≤ v e) ∧
            (∀ e, ∃ z : ℤ,
              (Finset.univ.filter fun w : V ↦ e ∈ incidentEdgeFinset G w).sum u - v e = (z : ℝ)) ∧
              (∀ e,
                c e =
                  (Finset.univ.filter fun w : V ↦ e ∈ incidentEdgeFinset G w).sum u - v e) ∧
                β = (Int.floor (∑ w, u w) : ℝ) := by
  constructor
  · rintro ⟨u, v, hu, hv, hint, hc, hβ⟩
    refine ⟨u, v, hu, hv, ?_, ?_, hβ⟩
    · intro e
      rcases hint e with ⟨z, hz⟩
      exact ⟨z, by simpa [matching_degree_chvatal_coeff] using hz⟩
    · intro e
      exact by simpa [matching_degree_chvatal_coeff] using congrArg (fun f ↦ f e) hc
  · rintro ⟨u, v, hu, hv, hint, hc, hβ⟩
    refine ⟨u, v, hu, hv, ?_, ?_, hβ⟩
    · intro e
      rcases hint e with ⟨z, hz⟩
      exact ⟨z, by simpa [matching_degree_chvatal_coeff] using hz⟩
    · funext e
      exact by simpa [matching_degree_chvatal_coeff] using hc e

/-- The first Chvátal closure of the matching degree system, represented as the set of points of
the degree relaxation satisfying every Chvátal inequality derived from that system. -/
def matching_degree_chvatal_closure : Set (G.edgeSet → ℝ) :=
  {x | x ∈ matching_degree_constraint_set G ∧
      ∀ c : G.edgeSet → ℝ, ∀ β : ℝ,
        IsMatchingDegreeSystemChvatalInequality G c β → c ⬝ᵥ x ≤ β}

/-- Membership in `matching_degree_chvatal_closure G` means lying in the degree relaxation and
satisfying every Chvátal inequality of that system. -/
theorem mem_matching_degree_chvatal_closure_iff
    {x : G.edgeSet → ℝ} :
    x ∈ matching_degree_chvatal_closure G ↔
      x ∈ matching_degree_constraint_set G ∧
        ∀ c : G.edgeSet → ℝ, ∀ β : ℝ,
          IsMatchingDegreeSystemChvatalInequality G c β → c ⬝ᵥ x ≤ β := Iff.rfl

/-- The matching degree system has Chvátal rank zero when the original degree relaxation already
equals the matching polytope. -/
def matching_degree_system_has_chvatal_rank_zero : Prop :=
  matching_degree_constraint_set G = G.matchingPolytope

/-- `matching_degree_system_has_chvatal_rank_zero G` means that the degree relaxation is already
the matching polytope. -/
theorem matching_degree_system_has_chvatal_rank_zero_iff :
    matching_degree_system_has_chvatal_rank_zero G ↔
      matching_degree_constraint_set G = G.matchingPolytope := Iff.rfl

/-- The matching degree system has Chvátal rank one when one Chvátal closure step yields the
matching polytope, but the original degree relaxation is strictly larger. -/
def matching_degree_system_has_chvatal_rank_one : Prop :=
  matching_degree_chvatal_closure G = G.matchingPolytope ∧
    matching_degree_constraint_set G ≠ G.matchingPolytope

/-- `matching_degree_system_has_chvatal_rank_one G` unfolds to equality after one Chvátal step
together with failure of equality at rank zero. -/
theorem matching_degree_system_has_chvatal_rank_one_iff :
    matching_degree_system_has_chvatal_rank_one G ↔
      matching_degree_chvatal_closure G = G.matchingPolytope ∧
        matching_degree_constraint_set G ≠ G.matchingPolytope := Iff.rfl

/-- Helper for Exercise 7.4: the incident-edge sum used in the degree relaxation is exactly the
corresponding row of the edge-incidence matrix. -/
private lemma incidentEdgeFinset_sum_eq_edgeIncMatrix_mulVec
    (x : G.edgeSet → ℝ) (v : V) :
    (incidentEdgeFinset G v).sum x = ((G.edgeIncMatrix ℝ).mulVec x) v := by
  -- Expand the restricted incidence matrix and read each entry as the incidence indicator at `v`.
  symm
  rw [SimpleGraph.edgeIncMatrix, Matrix.mulVec, dotProduct]
  calc
    ∑ e : G.edgeSet, G.incMatrix ℝ v (e : Sym2 V) * x e
        = ∑ e : G.edgeSet, if e ∈ incidentEdgeFinset G v then x e else 0 := by
            refine Finset.sum_congr rfl ?_
            intro e he
            by_cases h : (e : Sym2 V) ∈ G.incidenceSet v
            · have hmem : e ∈ incidentEdgeFinset G v := by
                exact (mem_incidentEdgeFinset_iff (G := G) (v := v) (e := e)).2
                  (by simpa [SimpleGraph.edge_mem_incidenceSet_iff] using h)
              simp [G.incMatrix_of_mem_incidenceSet (R := ℝ) h, hmem]
            · have hnotmem : e ∉ incidentEdgeFinset G v := by
                intro hmem
                exact h ((SimpleGraph.edge_mem_incidenceSet_iff (G := G) (a := v) (e := e)).2
                  ((mem_incidentEdgeFinset_iff (G := G) (v := v) (e := e)).1 hmem))
              simp [G.incMatrix_of_notMem_incidenceSet (R := ℝ) h, hnotmem]
    _ = (Finset.univ.filter fun e : G.edgeSet ↦ e ∈ incidentEdgeFinset G v).sum x := by
          rw [Finset.sum_filter]
    _ = (incidentEdgeFinset G v).sum x := by
          simp

/-- Helper for Exercise 7.4: membership in `matching_degree_constraint_set G` is the Chapter 4.19
incidence-matrix system `A_G x ≤ 1, x ≥ 0`. -/
private lemma matchingDegreeConstraintSet_eq_setOf_mulVec_le_one :
    matching_degree_constraint_set G = {x | (G.edgeIncMatrix ℝ).mulVec x ≤ 1 ∧ ∀ e, 0 ≤ x e} := by
  ext x
  constructor
  · intro hx
    rcases (mem_matching_degree_constraint_set_iff (G := G) (x := x)).1 hx with
      ⟨hx_deg, hx_nonneg⟩
    refine ⟨?_, hx_nonneg⟩
    intro v
    simpa [incidentEdgeFinset_sum_eq_edgeIncMatrix_mulVec (G := G) x v] using hx_deg v
  · rintro ⟨hx_deg, hx_nonneg⟩
    refine (mem_matching_degree_constraint_set_iff (G := G) (x := x)).2 ?_
    refine ⟨?_, hx_nonneg⟩
    intro v
    simpa [incidentEdgeFinset_sum_eq_edgeIncMatrix_mulVec (G := G) x v] using hx_deg v
/-- Helper for Exercise 7.4: on a bipartite graph the degree relaxation already equals the
matching polytope. -/
private lemma matchingDegreeConstraintSet_eq_matchingPolytope_of_isBipartite
    (hG : G.IsBipartite) :
    matching_degree_constraint_set G = G.matchingPolytope := by
  rw [matchingDegreeConstraintSet_eq_setOf_mulVec_le_one (G := G)]
  exact (SimpleGraph.matchingPolytope_eq_setOf_mulVec_le_one (G := G) hG).symm

/-- Helper for Exercise 7.4: the Chapter 4 degree row
`∑_{e ∈ incidenceFinset(v)} x_e` is the same edge-coordinate sum as
`(incidentEdgeFinset G v).sum x`. -/
private lemma incidenceFilter_sum_eq_incidentEdgeFinset_sum
    (x : G.edgeSet → ℝ) (v : V) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x =
      (incidentEdgeFinset G v).sum x := by
  -- First normalize the two index finsets themselves; the sum then follows by rewriting.
  have hfinset :
      (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v) =
        incidentEdgeFinset G v := by
    ext e
    simp [incidentEdgeFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  rw [hfinset]

/-- Helper for Exercise 7.4: the blossom coefficient vector sums exactly the coordinates indexed by
`E[G] U`. -/
private lemma blossomVector_dot_eq_inducedEdgeSum
    (U : Set V) (x : G.edgeSet → ℝ) :
    blossom_vector G U ⬝ᵥ x = (E[G] U).sum x := by
  classical
  unfold blossom_vector
  rw [dotProduct]
  calc
    ∑ e : G.edgeSet, (if e ∈ E[G] U then 1 else 0) * x e =
        ∑ e : G.edgeSet, if e ∈ E[G] U then x e else 0 := by
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases h : e ∈ E[G] U
          · simp [h]
          · simp [h]
    _ = (E[G] U).sum x := by
          simpa using
            (Finset.sum_filter
              (s := (Finset.univ : Finset G.edgeSet))
              (p := fun e : G.edgeSet ↦ e ∈ E[G] U)
              (f := x)).symm

/-- Helper for Exercise 7.4: the endpoint finset of an edge-coordinate is the unordered pair of
its canonical `Sym2.out` endpoints. -/
private lemma edgeToFinset_eq_pair
    (e : G.edgeSet) :
    ((e : Sym2 V).toFinset) = {e.1.out.1, e.1.out.2} := by
  -- Rewrite the edge through its canonical endpoint presentation.
  calc
    ((e : Sym2 V).toFinset) = (s(e.1.out.1, e.1.out.2)).toFinset := by
      simpa [e.1.out_eq]
    _ = {e.1.out.1, e.1.out.2} := Sym2.toFinset_mk_eq

/-- Helper for Exercise 7.4: the vertices incident to an edge-coordinate `e` are exactly the two
canonical endpoints of `e`. -/
private lemma incidentVertexFinset_eq_edgeToFinset
    (e : G.edgeSet) :
    (Finset.univ.filter fun w : V ↦ e ∈ incidentEdgeFinset G w) = (e : Sym2 V).toFinset := by
  -- Both finsets encode the same vertex-membership predicate `w ∈ (e : Sym2 V)`.
  ext w
  simp [incidentEdgeFinset, SimpleGraph.edge_mem_incidenceSet_iff]

/-- Helper for Exercise 7.4: an induced edge is characterized by both canonical endpoints lying in
the chosen vertex set. -/
private lemma memInducedEdgeFinsetEndpointsIff
    (U : Set V) (e : G.edgeSet) :
    e ∈ E[G] U ↔ e.1.out.1 ∈ U ∧ e.1.out.2 ∈ U := by
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    have he : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
      simpa [e.1.out_eq] using e.prop
    exact (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 he
  -- Rewrite induced-edge membership through the same canonical endpoint presentation.
  rw [mem_inducedEdgeFinset_iff, ← e.1.out_eq, SimpleGraph.Subgraph.mem_edgeSet]
  simp [SimpleGraph.Subgraph.induce, hadj]

/-- Helper for Exercise 7.4: the full matching-constraint owner implies the degree relaxation
owner by discarding the odd-set inequalities. -/
private lemma matchingConstraintSet_subset_matchingDegreeConstraintSet :
    G.matchingConstraintSet ⊆ matching_degree_constraint_set G := by
  intro x hx
  rcases (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, hx_deg, -⟩
  refine (mem_matching_degree_constraint_set_iff (G := G) (x := x)).2 ?_
  refine ⟨?_, hx_nonneg⟩
  intro v
  rw [← incidenceFilter_sum_eq_incidentEdgeFinset_sum (G := G) x v]
  exact hx_deg v

/-- Helper for Exercise 7.4: every valid blossom inequality cuts out an exposed blossom face on
the matching polytope. -/
private lemma blossomFace_isExposed
    (U : Set V)
    (hvalid : is_valid_inequality G.matchingPolytope (blossom_vector G U) (blossom_rhs U)) :
    IsExposed ℝ G.matchingPolytope (blossom_face G U) := by
  classical
  by_cases hface_nonempty : (blossom_face G U).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hface_nonempty
    let l : StrongDual ℝ (G.edgeSet → ℝ) := blossomStrongDual G U
    have hface_eq : blossom_face G U = l.toExposed G.matchingPolytope := by
      ext x
      constructor
      · intro hx
        rcases (mem_blossom_face_iff (G := G) (U := U) (x := x)).1 hx with ⟨hxP, hxEq⟩
        refine ⟨hxP, ?_⟩
        intro y hyP
        calc
          l y = blossom_vector G U ⬝ᵥ y := blossomStrongDual_apply (G := G) U y
          _ ≤ blossom_rhs U := hvalid hyP
          _ = blossom_vector G U ⬝ᵥ x := by simpa [hxEq]
          _ = l x := (blossomStrongDual_apply (G := G) U x).symm
      · intro hx
        refine (mem_blossom_face_iff (G := G) (U := U) (x := x)).2 ⟨hx.1, ?_⟩
        have hx₀P : x₀ ∈ G.matchingPolytope := (mem_blossom_face_iff (G := G) (U := U) (x := x₀)).1 hx₀ |>.1
        have hx₀Eq : blossom_vector G U ⬝ᵥ x₀ = blossom_rhs U :=
          (mem_blossom_face_iff (G := G) (U := U) (x := x₀)).1 hx₀ |>.2
        have hx_le : l x ≤ l x₀ := by
          calc
            l x = blossom_vector G U ⬝ᵥ x := blossomStrongDual_apply (G := G) U x
            _ ≤ blossom_rhs U := hvalid hx.1
            _ = l x₀ := by
                  simpa [l, blossomStrongDual_apply (G := G) U x₀] using hx₀Eq.symm
        have hx_ge : l x₀ ≤ l x := hx.2 x₀ hx₀P
        have hx_eq : l x = l x₀ := le_antisymm hx_le hx_ge
        have hx_eq' : blossom_vector G U ⬝ᵥ x = blossom_vector G U ⬝ᵥ x₀ := by
          simpa [l, blossomStrongDual_apply (G := G) U x, blossomStrongDual_apply (G := G) U x₀]
            using hx_eq
        exact hx_eq'.trans hx₀Eq
    rw [hface_eq]
    exact ContinuousLinearMap.toExposed.isExposed
  · rw [Set.not_nonempty_iff_eq_empty.mp hface_nonempty]
    exact isExposed_empty

/-- Helper for Exercise 7.4: every point of `G.matchingPolytope` lies in the degree relaxation. -/
private lemma matchingPolytope_subset_matchingDegreeConstraintSet :
    G.matchingPolytope ⊆ matching_degree_constraint_set G := by
  intro x hx
  have hx' : x ∈ G.matchingConstraintSet := by
    rw [← matchingPolytope_eq_matchingConstraintSet (G := G)]
    exact hx
  exact matchingConstraintSet_subset_matchingDegreeConstraintSet (G := G) hx'

/-- Helper for Exercise 7.4: the aggregated coefficient vector attached to multipliers `u` and
`v` is `u ᵥ* A_G - v`. -/
private lemma matchingDegreeChvatalCoeff_eq_vecMul_sub
    (u : V → ℝ) (v : G.edgeSet → ℝ) :
    matching_degree_chvatal_coeff G u v = u ᵥ* (G.edgeIncMatrix ℝ) - v := by
  funext e
  -- Expand the column of `A_G`; its nonzero entries are exactly the endpoints incident to `e`.
  rw [Pi.sub_apply]
  simp [matching_degree_chvatal_coeff, Matrix.vecMul, dotProduct]
  calc
    (Finset.univ.filter fun w : V ↦ e ∈ incidentEdgeFinset G w).sum u =
        ∑ x : V, if e ∈ incidentEdgeFinset G x then u x else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ x : V, u x * G.incMatrix ℝ x (e : Sym2 V) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          by_cases hinc : (e : Sym2 V) ∈ G.incidenceSet x
          · have hmem : e ∈ incidentEdgeFinset G x := by
              simpa [incidentEdgeFinset, SimpleGraph.edge_mem_incidenceSet_iff] using hinc
            simp [hmem, G.incMatrix_of_mem_incidenceSet (R := ℝ) hinc]
          · have hmem : e ∉ incidentEdgeFinset G x := by
              simpa [incidentEdgeFinset, SimpleGraph.edge_mem_incidenceSet_iff] using hinc
            simp [hmem, G.incMatrix_of_notMem_incidenceSet (R := ℝ) hinc]

/-- Helper for Exercise 7.4: at a covered vertex of a matching, the matching incidence vector has
exactly one incident edge coordinate equal to `1`. -/
private lemma matchingIncidenceFilter_sum_eq_one_of_mem_verts
    {M : G.Subgraph} (hM : M.IsMatching) {v : V} (hv : v ∈ M.verts) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = 1 := by
  -- Use the unique matching edge through `v` as the lone nonzero term of the incidence sum.
  obtain ⟨w, hvw, huniq⟩ := hM hv
  let e₀ : G.edgeSet := ⟨s(v, w), M.adj_sub hvw⟩
  have he₀_mem :
      e₀ ∈ Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v := by
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
                e.1 = s(v, Sym2.Mem.other hv_e) := by
                  symm
                  exact Sym2.other_spec hv_e
                _ = s(v, w) := by
                  rw [huniq _ hAdj_e]
                _ = e₀.1 := rfl
            exact (he_ne (Subtype.ext he_eq)).elim
          · simp [SimpleGraph.subgraphIncidenceVector, heM]
    _ = 1 := he₀_val

/-- Helper for Exercise 7.4: every matching incidence vector already satisfies the degree-system
relaxation `∑_{e ∈ δ(v)} x_e ≤ 1, x ≥ 0`. -/
private lemma subgraphIncidenceVector_mem_matchingDegreeConstraintSet_of_isMatching
    {M : G.Subgraph} (hM : M.IsMatching) :
    G.subgraphIncidenceVector ℝ M ∈ matching_degree_constraint_set G := by
  refine (mem_matching_degree_constraint_set_iff
    (G := G) (x := G.subgraphIncidenceVector ℝ M)).2 ?_
  refine ⟨?_, ?_⟩
  · intro v
    have hfilter_le :
        (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
            (G.subgraphIncidenceVector ℝ M) ≤ 1 := by
      by_cases hv : v ∈ M.verts
      · -- Covered vertices contribute exactly one matching edge.
        have hsum_eq_one :=
          matchingIncidenceFilter_sum_eq_one_of_mem_verts (G := G) hM hv
        linarith
      · -- Uncovered vertices contribute no matching edge at all.
        have hsum_eq_zero :
            (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
                (G.subgraphIncidenceVector ℝ M) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro e he
          have hv_mem : v ∈ (e : Sym2 V) := by
            have he_inc : (e : Sym2 V) ∈ G.incidenceFinset v := (Finset.mem_filter.mp he).2
            simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
              using he_inc
          by_cases heM : e.1 ∈ M.edgeSet
          · exact (hv (Subgraph.mem_verts_of_mem_edge heM hv_mem)).elim
          · simp [SimpleGraph.subgraphIncidenceVector, heM]
        linarith
    -- Convert the Chapter 4 incidence-filter row to the Chapter 7 incident-edge finset row.
    rw [← incidenceFilter_sum_eq_incidentEdgeFinset_sum
      (G := G) (x := G.subgraphIncidenceVector ℝ M) v]
    exact hfilter_le
  · intro e
    -- Each edge coordinate of an incidence vector is a `0/1` indicator.
    by_cases he : e.1 ∈ M.edgeSet
    · simp [SimpleGraph.subgraphIncidenceVector, he]
    · simp [SimpleGraph.subgraphIncidenceVector, he]

/-- Helper for Exercise 7.4: every matching generator satisfies each Chvátal inequality derived
from the degree system. -/
private lemma matchingDegreeSystemChvatalInequality_valid_onMatchingGenerator
    {c : G.edgeSet → ℝ} {β : ℝ}
    (hchv : IsMatchingDegreeSystemChvatalInequality G c β)
    {M : G.Subgraph} (hM : M.IsMatching) :
    c ⬝ᵥ G.subgraphIncidenceVector ℝ M ≤ β := by
  rcases hchv with ⟨u, v, hu, hv, hint, rfl, rfl⟩
  let y : G.edgeSet → ℝ := G.subgraphIncidenceVector ℝ M
  have hy_deg : y ∈ matching_degree_constraint_set G := by
    -- Work directly with the matching generator instead of routing through the unresolved
    -- matching-polytope / matching-constraint bridge.
    simpa [y] using
      subgraphIncidenceVector_mem_matchingDegreeConstraintSet_of_isMatching (G := G) hM
  rcases (mem_matching_degree_constraint_set_iff (G := G) (x := y)).1 hy_deg with
    ⟨hy_row, hy_nonneg⟩
  have hdot_nonneg : 0 ≤ v ⬝ᵥ y := by
    rw [dotProduct]
    refine Finset.sum_nonneg ?_
    intro e he
    exact mul_nonneg (hv e) (hy_nonneg e)
  have hupper :
      matching_degree_chvatal_coeff G u v ⬝ᵥ y ≤ ∑ w : V, u w := by
    calc
      matching_degree_chvatal_coeff G u v ⬝ᵥ y
          = u ⬝ᵥ ((G.edgeIncMatrix ℝ).mulVec y) - v ⬝ᵥ y := by
              rw [matchingDegreeChvatalCoeff_eq_vecMul_sub (G := G) u v]
              rw [sub_dotProduct, Matrix.dotProduct_mulVec]
      _ ≤ u ⬝ᵥ (1 : V → ℝ) := by
            have hrow_le :
                u ⬝ᵥ ((G.edgeIncMatrix ℝ).mulVec y) ≤ u ⬝ᵥ (1 : V → ℝ) := by
              refine dotProduct_le_dotProduct_of_nonneg_left ?_ hu
              intro w
              simpa [incidentEdgeFinset_sum_eq_edgeIncMatrix_mulVec (G := G) y w] using hy_row w
            linarith
      _ = ∑ w : V, u w := by
            simp [dotProduct]
  have hterm_int :
      ∀ e : G.edgeSet, ∃ z : ℤ, matching_degree_chvatal_coeff G u v e * y e = (z : ℝ) := by
    intro e
    rcases hint e with ⟨z, hz⟩
    by_cases he : e.1 ∈ M.edgeSet
    · refine ⟨z, ?_⟩
      simp [y, SimpleGraph.subgraphIncidenceVector, he, hz]
    · refine ⟨0, ?_⟩
      simp [y, SimpleGraph.subgraphIncidenceVector, he]
  choose z hz using hterm_int
  have hdot_int :
      ∃ z' : ℤ, matching_degree_chvatal_coeff G u v ⬝ᵥ y = (z' : ℝ) := by
    refine ⟨∑ e, z e, ?_⟩
    simp [dotProduct, hz]
  rcases hdot_int with ⟨z', hz'⟩
  have hz'_floor : z' ≤ Int.floor (∑ w : V, u w) := by
    exact Int.le_floor.mpr (by simpa [hz'] using hupper)
  have hz'_real : (z' : ℝ) ≤ (Int.floor (∑ w : V, u w) : ℝ) := by
    exact_mod_cast hz'_floor
  rw [hz']
  exact hz'_real

/-- Helper for Exercise 7.4: part (1) is needed before the closure-to-polytope step, so we expose
the blossom Chvatal certificate as an earlier helper and keep the theorem statement below as a
thin wrapper. -/
private lemma blossomIsMatchingDegreeSystemChvatal
    (U : Set V) (hUodd : Odd U.ncard) :
    IsMatchingDegreeSystemChvatalInequality G (blossom_vector G U) (blossom_rhs U) := by
  let u : V → ℝ := fun w ↦ if w ∈ U then (1 / 2 : ℝ) else 0
  let v : G.edgeSet → ℝ := fun e ↦
    (Finset.univ.filter fun w : V ↦ e ∈ incidentEdgeFinset G w).sum u - blossom_vector G U e
  have hu_nonneg : ∀ w, 0 ≤ u w := by
    intro w
    -- The degree multipliers are exactly the nonnegative half-indicators of `U`.
    by_cases hw : w ∈ U <;> simp [u, hw]
  have hv_nonneg : ∀ e, 0 ≤ v e := by
    intro e
    have hne : e.1.out.1 ≠ e.1.out.2 := by
      have hadj : G.Adj e.1.out.1 e.1.out.2 := by
        have he : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
          simpa [e.1.out_eq] using e.prop
        exact (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 he
      exact G.ne_of_adj hadj
    by_cases heU : e ∈ E[G] U
    · have hEnds : e.1.out.1 ∈ U ∧ e.1.out.2 ∈ U :=
        (memInducedEdgeFinsetEndpointsIff (G := G) U e).1 heU
      have hsum_eq_one :
          (Finset.univ.filter fun w : V ↦ e ∈ incidentEdgeFinset G w).sum u = 1 := by
        -- On an induced edge, both canonical endpoints contribute `1/2`.
        rw [incidentVertexFinset_eq_edgeToFinset (G := G) e, edgeToFinset_eq_pair (G := G) e]
        norm_num [u, hne, hEnds.1, hEnds.2]
      -- The chosen slack vanishes on induced edges because the aggregate coefficient is already `1`.
      simp [v, blossom_vector, heU, hsum_eq_one]
    · have hsum_nonneg :
          0 ≤ (Finset.univ.filter fun w : V ↦ e ∈ incidentEdgeFinset G w).sum u := by
        -- Outside the induced-edge case, the blossom coefficient is `0`, so nonnegativity comes
        -- from summing nonnegative endpoint weights.
        rw [incidentVertexFinset_eq_edgeToFinset (G := G) e, edgeToFinset_eq_pair (G := G) e]
        by_cases h₁ : e.1.out.1 ∈ U <;> by_cases h₂ : e.1.out.2 ∈ U <;> simp [u, hne, h₁, h₂]
      have hblossom : blossom_vector G U e = 0 := by
        simp [blossom_vector, heU]
      -- Here the slack equals the nonnegative endpoint-weight sum itself.
      simp [v, hblossom, hsum_nonneg]
  have hcoeff :
      matching_degree_chvatal_coeff G u v = blossom_vector G U := by
    funext e
    -- The slack was chosen precisely to turn the half-degree combination into the blossom vector.
    simp [matching_degree_chvatal_coeff, v]
  have hsum_u :
      ∑ w : V, u w = (U.ncard : ℝ) / 2 := by
    letI : Fintype U := Fintype.ofFinite U
    have hUfinset : (Finset.univ.filter fun w : V ↦ w ∈ U) = U.toFinset := by
      ext w
      simp
    -- Summing the half-indicator of `U` counts exactly `|U| / 2`.
    calc
      ∑ w : V, u w = (Finset.univ.filter fun w : V ↦ w ∈ U).sum (fun _ ↦ (1 / 2 : ℝ)) := by
        rw [Finset.sum_filter]
      _ = (U.toFinset.card : ℝ) * (1 / 2 : ℝ) := by
        rw [hUfinset]
        simp
      _ = (U.ncard : ℝ) / 2 := by
        have hcard : U.toFinset.card = U.ncard := by
          simpa [Set.ncard] using (Set.toFinset_card U)
        rw [show (U.ncard : ℝ) / 2 = (U.ncard : ℝ) * (1 / 2 : ℝ) by ring]
        exact congrArg (fun n : ℕ ↦ (n : ℝ) * (1 / 2 : ℝ)) hcard
  rcases hUodd with ⟨k, hk⟩
  refine (isMatchingDegreeSystemChvatalInequality_iff
    (G := G) (c := blossom_vector G U) (β := blossom_rhs U)).2 ?_
  refine ⟨u, v, hu_nonneg, hv_nonneg, ?_, ?_, ?_⟩
  · intro e
    refine ⟨if e ∈ E[G] U then 1 else 0, ?_⟩
    -- The aggregate coefficient is exactly the `0/1` blossom coefficient on each edge.
    simpa [blossom_vector] using congrArg (fun f ↦ f e) hcoeff
  · intro e
    -- Read the coefficient identity pointwise.
    simpa using (congrArg (fun f ↦ f e) hcoeff).symm
  · -- The right-hand side is the floor of the half-size sum, i.e. `( |U| - 1 ) / 2` for odd `U`.
    rw [hsum_u, blossom_rhs, hk]
    have hhalf : ((((2 * k + 1 : ℕ) : ℝ) / 2)) = (1 / 2 : ℝ) + k := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    rw [hhalf, Int.floor_add_natCast]
    norm_num

/-- Helper for Exercise 7.4: every point of `G.matchingPolytope` lies in the first Chvátal
closure of the degree system because the closure cuts are valid on the matching generators. -/
private lemma matchingPolytope_subset_matchingDegreeChvatalClosure :
    G.matchingPolytope ⊆ matching_degree_chvatal_closure G := by
  intro x hx
  refine (mem_matching_degree_chvatal_closure_iff (G := G) (x := x)).2 ?_
  refine ⟨matchingPolytope_subset_matchingDegreeConstraintSet (G := G) hx, ?_⟩
  intro c β hchv
  rw [SimpleGraph.matchingPolytope, mem_convexHull_iff_exists_fintype] at hx
  rcases hx with ⟨ι, _, w, z, hw_nonneg, hw_sum, hz, rfl⟩
  have hzvalid : ∀ i, c ⬝ᵥ z i ≤ β := by
    intro i
    rcases hz i with ⟨M, hM, hzEq⟩
    rw [hzEq]
    exact matchingDegreeSystemChvatalInequality_valid_onMatchingGenerator
      (G := G) hchv hM
  calc
    c ⬝ᵥ ∑ i, w i • z i = ∑ i, w i * (c ⬝ᵥ z i) := by
      rw [dotProduct_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [smul_eq_mul] using dotProduct_smul c (w i) (z i)
    _ ≤ ∑ i, w i * β := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact mul_le_mul_of_nonneg_left (hzvalid i) (hw_nonneg i)
    _ = β * ∑ i, w i := by
          simpa [mul_comm] using
            (Finset.mul_sum (s := (Finset.univ : Finset ι)) (a := β) (f := fun i ↦ w i)).symm
    _ = β := by
          rw [hw_sum, mul_one]

/-- Helper for Exercise 7.4: the Chvátal closure is contained in the matching polytope because
part (1) recovers every odd-set inequality on top of the degree relaxation. -/
private lemma matchingDegreeChvatalClosure_subset_matchingPolytope :
    matching_degree_chvatal_closure G ⊆ G.matchingPolytope := by
  intro x hx
  rcases (mem_matching_degree_chvatal_closure_iff (G := G) (x := x)).1 hx with ⟨hx_deg, hx_cuts⟩
  have hx_match : x ∈ G.matchingConstraintSet := by
    rcases (mem_matching_degree_constraint_set_iff (G := G) (x := x)).1 hx_deg with
      ⟨hx_row, hx_nonneg⟩
    refine (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := x)).2 ?_
    refine ⟨hx_nonneg, ?_, ?_⟩
    · intro v
      rw [incidenceFilter_sum_eq_incidentEdgeFinset_sum (G := G) x v]
      exact hx_row v
    · intro U hUodd
      have hblossom :
          blossom_vector G U ⬝ᵥ x ≤ blossom_rhs U := by
        exact hx_cuts (blossom_vector G U) (blossom_rhs U)
          (blossomIsMatchingDegreeSystemChvatal (G := G) U hUodd)
      simpa [blossomVector_dot_eq_inducedEdgeSum (G := G) U x] using hblossom
  rw [matchingPolytope_eq_matchingConstraintSet (G := G)]
  exact hx_match

/-- Exercise 7.4 (1). For every odd vertex set `U`, the blossom inequality `(4.17)`
`∑_{e ∈ E(U)} x_e ≤ (|U| - 1)/2` is a Chvátal inequality for the degree system
`∑_{e ∈ δ(v)} x_e ≤ 1` together with `x ≥ 0`. -/
theorem exercise_7_4_blossom_is_matching_degree_system_chvatal
    (U : Set V) (hUodd : Odd U.ncard) :
    IsMatchingDegreeSystemChvatalInequality G (blossom_vector G U) (blossom_rhs U) := by
  -- Keep the public theorem statement fixed and reuse the earlier helper in the dependency order
  -- required by the closure proof.
  exact blossomIsMatchingDegreeSystemChvatal (G := G) U hUodd

/-- Helper for Exercise 7.4: every Chvátal inequality derived from the matching degree system is
valid on `G.matchingPolytope`. -/
private lemma matchingDegreeSystemChvatal_isValid
    {c : G.edgeSet → ℝ} {β : ℝ}
    (hchv : IsMatchingDegreeSystemChvatalInequality G c β) :
    is_valid_inequality G.matchingPolytope c β := by
  rw [is_valid_inequality_iff]
  intro x hx
  -- Every point of the matching polytope already lies in the first Chvátal closure.
  have hxClosure :
      x ∈ matching_degree_chvatal_closure G :=
    matchingPolytope_subset_matchingDegreeChvatalClosure (G := G) hx
  -- The closure definition then applies the requested derived inequality at `x`.
  exact (mem_matching_degree_chvatal_closure_iff (G := G) (x := x)).1 hxClosure |>.2 c β hchv

/-- Helper for Exercise 7.4: summing the ambient incident-edge coordinates of a subgraph
incidence vector counts the degree in that subgraph. -/
private lemma incidentIncidenceSum_eq_degree
    (H : G.Subgraph) (v : V) :
    (incidentEdgeFinset G v).sum (G.subgraphIncidenceVector ℝ H) = H.degree v := by
  classical
  let incidentInH : Finset G.edgeSet :=
    (incidentEdgeFinset G v).filter fun e ↦ e.1 ∈ H.edgeSet
  have hsum :
      (incidentEdgeFinset G v).sum (G.subgraphIncidenceVector ℝ H) =
        (incidentInH.card : ℝ) := by
    calc
      (incidentEdgeFinset G v).sum (G.subgraphIncidenceVector ℝ H) =
          incidentInH.sum (fun _ ↦ (1 : ℝ)) := by
            simpa [incidentInH, SimpleGraph.subgraphIncidenceVector] using
              (Finset.sum_filter
                (s := incidentEdgeFinset G v)
                (p := fun e : G.edgeSet ↦ e.1 ∈ H.edgeSet)
                (f := fun _ ↦ (1 : ℝ))).symm
      _ = (incidentInH.card : ℝ) := by
            simp
  let edgeEmbedding : G.edgeSet ↪ Sym2 V :=
    ⟨fun e ↦ (e : Sym2 V), Subtype.val_injective⟩
  have hmap :
      Finset.map edgeEmbedding incidentInH = H.spanningCoe.incidenceFinset v := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_map.1 he with ⟨eG, heG, rfl⟩
      rcases Finset.mem_filter.1 heG with ⟨hinc, hedgeH⟩
      rw [SimpleGraph.mem_incidenceFinset]
      exact ⟨by simpa using hedgeH,
        (mem_incidentEdgeFinset_iff (G := G) (v := v) (e := eG)).1 hinc⟩
    · intro he
      rw [SimpleGraph.mem_incidenceFinset] at he
      rcases he with ⟨hedgeH, hv⟩
      let eG : G.edgeSet := ⟨e, H.edgeSet_subset hedgeH⟩
      refine Finset.mem_map.2 ⟨eG, ?_, rfl⟩
      exact Finset.mem_filter.2
        ⟨(mem_incidentEdgeFinset_iff (G := G) (v := v) (e := eG)).2 hv, by simpa using hedgeH⟩
  have hcardNat : incidentInH.card = H.degree v := by
    calc
      incidentInH.card = (H.spanningCoe.incidenceFinset v).card := by
        simpa using congrArg Finset.card hmap
      _ = H.spanningCoe.degree v := by
        simpa using H.spanningCoe.card_incidenceFinset_eq_degree v
      _ = H.degree v := by
        simpa using (Subgraph.degree_spanningCoe (G' := H) v)
  calc
    (incidentEdgeFinset G v).sum (G.subgraphIncidenceVector ℝ H) = (incidentInH.card : ℝ) := hsum
    _ = H.degree v := by
          exact congrArg (fun n : ℕ ↦ (n : ℝ)) hcardNat

/-- Helper for Exercise 7.4: the edges of a subgraph `T` correspond bijectively to the ambient
edges of `G` that lie in `T.edgeSet`. -/
private lemma cardEdgeSetSubtypeEq
    (T : G.Subgraph) :
    Fintype.card {e : G.edgeSet // e.1 ∈ T.edgeSet} = Fintype.card T.edgeSet := by
  classical
  refine Fintype.card_congr ?_
  refine
    { toFun := fun e ↦ ⟨e.1.1, e.2⟩
      invFun := fun e ↦ ⟨⟨e.1, T.edgeSet_subset e.2⟩, e.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    cases e
    rfl
  · intro e
    cases e
    rfl

/-- Helper for Exercise 7.4: summing the edge-indicator of a subgraph over all ambient edges of
`G` recovers the number of edges of that subgraph. -/
private lemma sumEdgeIndicatorEqCardEdgeSet
    (T : G.Subgraph) :
    (∑ e : G.edgeSet, if e.1 ∈ T.edgeSet then (1 : ℝ) else 0) = Fintype.card T.edgeSet := by
  classical
  calc
    (∑ e : G.edgeSet, if e.1 ∈ T.edgeSet then (1 : ℝ) else 0) =
        ((Finset.univ.filter fun e : G.edgeSet ↦ e.1 ∈ T.edgeSet).card : ℝ) := by
          simpa using
            (Finset.sum_boole (fun e : G.edgeSet ↦ e.1 ∈ T.edgeSet) Finset.univ : _)
    _ = (Fintype.card {e : G.edgeSet // e.1 ∈ T.edgeSet} : ℝ) := by
          exact congrArg (fun n : ℕ ↦ (n : ℝ))
            ((Fintype.card_of_subtype
              (Finset.univ.filter fun e : G.edgeSet ↦ e.1 ∈ T.edgeSet)
              (by
                intro e
                simp)).symm)
    _ = Fintype.card T.edgeSet := by
          exact congrArg (fun n : ℕ ↦ (n : ℝ)) (cardEdgeSetSubtypeEq (G := G) T)

/-- Helper for Exercise 7.4: `T.induce S` keeps exactly the edges of `T` whose endpoints both lie
in `S`. -/
private lemma induceEdgeSetEqInterInduceTop
    (T : G.Subgraph) (S : Set V) :
    (T.induce S).edgeSet = T.edgeSet ∩ ((⊤ : G.Subgraph).induce S).edgeSet := by
  -- Both sides express the same endpoint-membership condition on ambient edges.
  ext e
  induction e using Sym2.ind with
  | h u v =>
      simp only [SimpleGraph.Subgraph.mem_edgeSet, Set.mem_inter_iff, SimpleGraph.Subgraph.induce]
      constructor
      · rintro ⟨hu, hv, huv⟩
        exact ⟨huv, hu, hv, T.adj_sub huv⟩
      · rintro ⟨huv, hu, hv, _⟩
        exact ⟨hu, hv, huv⟩

/-- Helper for Exercise 7.4: the induced-edge sum of a subgraph incidence vector is the number of
induced edges of the restricted subgraph. -/
private lemma inducedIncidenceSumEqCardInducedEdges
    (T : G.Subgraph) (S : Finset V) :
    Finset.sum (G.inducedEdgeFinset (S : Set V)) (fun e ↦ G.subgraphIncidenceVector ℝ T e) =
      Fintype.card ((T.induce (S : Set V)).edgeSet) := by
  classical
  calc
    Finset.sum (G.inducedEdgeFinset (S : Set V)) (fun e ↦ G.subgraphIncidenceVector ℝ T e) =
        ∑ e : G.edgeSet,
          if e.1 ∈ ((⊤ : G.Subgraph).induce (S : Set V)).edgeSet then
            G.subgraphIncidenceVector ℝ T e
          else 0 := by
            rw [SimpleGraph.inducedEdgeFinset, Finset.sum_filter]
    _ = ∑ e : G.edgeSet, if e.1 ∈ (T.induce (S : Set V)).edgeSet then (1 : ℝ) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro e he
          have hmem :
              e.1 ∈ (T.induce (S : Set V)).edgeSet ↔
                e.1 ∈ ((⊤ : G.Subgraph).induce (S : Set V)).edgeSet ∧ e.1 ∈ T.edgeSet := by
            rw [induceEdgeSetEqInterInduceTop (G := G) T (S : Set V)]
            simpa [and_comm]
          by_cases hS : e.1 ∈ ((⊤ : G.Subgraph).induce (S : Set V)).edgeSet
          · by_cases hT : e.1 ∈ T.edgeSet
            · simp [SimpleGraph.subgraphIncidenceVector, hS, hT, hmem]
            · simp [SimpleGraph.subgraphIncidenceVector, hS, hT, hmem]
          · simp [hS, hmem, SimpleGraph.subgraphIncidenceVector]
    _ = Fintype.card ((T.induce (S : Set V)).edgeSet) := by
          simpa using sumEdgeIndicatorEqCardEdgeSet (G := G) (T.induce (S : Set V))

/-- Helper for Exercise 7.4: a nonbipartite graph has a connected component that is already
nonbipartite. -/
private lemma exists_nonbipartite_connectedComponent
    (hG : ¬ G.IsBipartite) :
    ∃ c : G.ConnectedComponent, ¬ c.toSimpleGraph.IsBipartite := by
  by_contra h
  have hcomp : ∀ c : G.ConnectedComponent, c.toSimpleGraph.IsBipartite := by
    intro c
    by_contra hc
    exact h ⟨c, hc⟩
  exact hG (by
    simpa using
      (SimpleGraph.colorable_iff_forall_connectedComponents (G := G) (n := 2)).2 hcomp)

/-- Helper for Exercise 7.4: a nonbipartite finite graph contains an odd cycle walk. -/
private lemma existsOddCycleWalk_of_not_isBipartite
    (hG : ¬ G.IsBipartite) :
    ∃ u : V, ∃ p : G.Walk u u, p.IsCycle ∧ Odd p.length := by
  by_contra hNo
  have hall :
      ∀ u : V, ∀ p : G.Walk u u, p.IsCycle → Odd p.length → ∃ e, e ∈ p.edges ∧ e ∉ G.edgeSet := by
    intro u p hpCycle hpOdd
    exfalso
    exact hNo ⟨u, p, hpCycle, hpOdd⟩
  obtain ⟨S, hS⟩ :=
    (existsCutContainingEdgeSetIffForallOddCycleHasEdgeOutside
      (G := G) (F := G.edgeSet) (hF := Set.Subset.rfl)).2 hall
  refine hG ?_
  -- Every edge of `G` crosses the cut `S`, so `S` and `Sᶜ` form a bipartition.
  refine SimpleGraph.IsBipartiteWith.isBipartite (G := G) (s := S) (t := Sᶜ) ?_
  refine ⟨disjoint_compl_right, ?_⟩
  intro v w hvw
  have hEdge : s(v, w) ∈ (G.between S Sᶜ).edgeSet := hS (G.mem_edgeSet.mpr hvw)
  exact (SimpleGraph.between_adj.mp ((G.between S Sᶜ).mem_edgeSet.mp hEdge)).2

/-- Helper for Exercise 7.4: the cycle subgraph of a cycle walk has as many edges as the walk has
steps. -/
private lemma cycleSubgraph_card_edgeSet_eq_length
    {u : V} {p : G.Walk u u}
    (hpCycle : p.IsCycle) :
    Fintype.card p.toSubgraph.edgeSet = p.length := by
  classical
  have hTrail : p.IsTrail := (SimpleGraph.Walk.isCycle_def (p := p)).1 hpCycle |>.1
  let F : Finset (Sym2 V) := hTrail.edgesFinset
  have hF : ∀ e : Sym2 V, e ∈ F ↔ e ∈ p.toSubgraph.edgeSet := by
    intro e
    simpa [F, SimpleGraph.Walk.IsTrail.edgesFinset] using
      (SimpleGraph.Walk.mem_edges_toSubgraph (p := p) (e := e)).symm
  calc
    Fintype.card p.toSubgraph.edgeSet = F.card := by
      exact Fintype.card_of_finset' F hF
    _ = p.edges.length := by
      simp [F, SimpleGraph.Walk.IsTrail.edgesFinset]
    _ = p.length := SimpleGraph.Walk.length_edges p

/-- Helper for Exercise 7.4: the vertex support of a cycle walk has the same cardinality as its
edge support. -/
private lemma cycleSupport_ncard_eq_card_edgeSet
    {u : V} {p : G.Walk u u}
    (hpCycle : p.IsCycle) :
    p.toSubgraph.verts.ncard = Fintype.card p.toSubgraph.edgeSet := by
  classical
  let T := p.toSubgraph
  have hdeg :
      ∀ v : V, T.spanningCoe.degree v = if v ∈ T.verts then 2 else 0 := by
    intro v
    by_cases hv : v ∈ T.verts
    · have hvSupport : v ∈ p.support :=
        p.mem_verts_toSubgraph.mp hv
      have hNeighborCard : (T.neighborSet v).toFinset.card = 2 := by
        simpa [Set.toFinset_card] using
          (SimpleGraph.Walk.IsCycle.ncard_neighborSet_toSubgraph_eq_two
            (p := p) hpCycle hvSupport)
      have hdegT : T.degree v = 2 := by
        rw [← SimpleGraph.Subgraph.finset_card_neighborSet_eq_degree (G' := T) (v := v)]
        exact hNeighborCard
      calc
        T.spanningCoe.degree v = T.degree v := by
          simpa using (SimpleGraph.Subgraph.degree_spanningCoe (G' := T) v)
        _ = if v ∈ T.verts then 2 else 0 := by simp [hv, hdegT]
    · have hdegT : T.degree v = 0 := SimpleGraph.Subgraph.degree_of_notMem_verts hv
      calc
        T.spanningCoe.degree v = T.degree v := by
          simpa using (SimpleGraph.Subgraph.degree_spanningCoe (G' := T) v)
        _ = if v ∈ T.verts then 2 else 0 := by simp [hv, hdegT]
  have hsumDegrees :
      ∑ v : V, T.spanningCoe.degree v = 2 * Fintype.card T.edgeSet := by
    calc
      ∑ v : V, T.spanningCoe.degree v = 2 * T.spanningCoe.edgeFinset.card := by
        simpa using T.spanningCoe.sum_degrees_eq_twice_card_edges
      _ = 2 * Fintype.card T.edgeSet := by
        simpa using congrArg (fun n : ℕ ↦ 2 * n) T.spanningCoe.edgeFinset_card
  have hsumVerts :
      ∑ v : V, T.spanningCoe.degree v = 2 * Fintype.card T.verts := by
    calc
      ∑ v : V, T.spanningCoe.degree v = ∑ v : V, if v ∈ T.verts then 2 else 0 := by
        refine Finset.sum_congr rfl ?_
        intro v hv
        exact hdeg v
      _ = (Finset.univ.filter fun v : V ↦ v ∈ T.verts).sum (fun _ ↦ (2 : ℕ)) := by
        rw [Finset.sum_filter]
      _ = T.verts.toFinset.card * 2 := by
        simp
      _ = 2 * Fintype.card T.verts := by
        simp [Set.toFinset_card, Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Nat.mul_comm]
  have hsumEdgesNat :
      ∑ v : V, T.spanningCoe.degree v = 2 * Nat.card T.edgeSet := by
    simpa [Nat.card_eq_fintype_card] using hsumDegrees
  have hsumVertsNat :
      ∑ v : V, T.spanningCoe.degree v = 2 * Nat.card T.verts := by
    simpa [Nat.card_eq_fintype_card] using hsumVerts
  have hEq : 2 * Nat.card T.edgeSet = 2 * Nat.card T.verts := by
    rw [← hsumEdgesNat, hsumVertsNat]
  have hcard : Nat.card T.edgeSet = Nat.card T.verts := by
    omega
  calc
    T.verts.ncard = Nat.card T.verts := by
      rw [Nat.card_coe_set_eq]
    _ = Nat.card T.edgeSet := hcard.symm
    _ = T.edgeSet.ncard := by
      rw [Nat.card_coe_set_eq]
    _ = Fintype.card T.edgeSet := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

/-- Helper for Exercise 7.4: the vertex support of an odd cycle walk has odd cardinality equal to
the cycle length. -/
private lemma cycleSupport_ncard_eq_length
    {u : V} {p : G.Walk u u}
    (hpCycle : p.IsCycle) :
    p.toSubgraph.verts.ncard = p.length := by
  -- First identify the support size with the cycle subgraph edge count, then identify the latter
  -- with the trail length.
  calc
    p.toSubgraph.verts.ncard = Fintype.card p.toSubgraph.edgeSet :=
      cycleSupport_ncard_eq_card_edgeSet (G := G) hpCycle
    _ = p.length :=
      cycleSubgraph_card_edgeSet_eq_length (G := G) hpCycle

/-- Helper for Exercise 7.4: the half-incidence vector of an odd cycle lies in the degree
relaxation and strictly violates the blossom inequality of its vertex support. -/
private lemma halfOddCycleWitness_spec
    {u : V} {p : G.Walk u u}
    (hpCycle : p.IsCycle) (hpOdd : Odd p.length) :
    let U : Set V := p.toSubgraph.verts
    let x : G.edgeSet → ℝ := fun e ↦ (1 / 2 : ℝ) * G.subgraphIncidenceVector ℝ p.toSubgraph e
    Odd U.ncard ∧
      x ∈ matching_degree_constraint_set G ∧
        blossom_rhs U < blossom_vector G U ⬝ᵥ x := by
  classical
  let U : Set V := p.toSubgraph.verts
  let x : G.edgeSet → ℝ := fun e ↦ (1 / 2 : ℝ) * G.subgraphIncidenceVector ℝ p.toSubgraph e
  have hUcard : U.ncard = p.length := cycleSupport_ncard_eq_length (G := G) hpCycle
  have hUodd : Odd U.ncard := by
    simpa [hUcard] using hpOdd
  have hx_mem : x ∈ matching_degree_constraint_set G := by
    refine (mem_matching_degree_constraint_set_iff (G := G) (x := x)).2 ?_
    refine ⟨?_, ?_⟩
    · intro v
      have hdeg_le_two : p.toSubgraph.degree v ≤ 2 := by
        by_cases hv : v ∈ p.toSubgraph.verts
        · have hvSupport : v ∈ p.support :=
            p.mem_verts_toSubgraph.mp hv
          have hNeighborCard : (p.toSubgraph.neighborSet v).toFinset.card = 2 := by
            simpa [Set.toFinset_card] using
              (SimpleGraph.Walk.IsCycle.ncard_neighborSet_toSubgraph_eq_two
                (p := p) hpCycle hvSupport)
          rw [← SimpleGraph.Subgraph.finset_card_neighborSet_eq_degree
            (G' := p.toSubgraph) (v := v)]
          exact hNeighborCard.le
        · rw [SimpleGraph.Subgraph.degree_of_notMem_verts hv]
          norm_num
      -- The half-incidence vector scales the cycle degrees by `1/2`.
      calc
        (incidentEdgeFinset G v).sum x =
            (1 / 2 : ℝ) * (incidentEdgeFinset G v).sum
              (G.subgraphIncidenceVector ℝ p.toSubgraph) := by
                simp [x, Finset.mul_sum]
        _ = (1 / 2 : ℝ) * p.toSubgraph.degree v := by
              rw [incidentIncidenceSum_eq_degree (G := G) p.toSubgraph v]
        _ ≤ (1 / 2 : ℝ) * 2 := by
              exact mul_le_mul_of_nonneg_left (by exact_mod_cast hdeg_le_two) (by norm_num)
        _ = 1 := by norm_num
    · intro e
      -- Each coordinate is either `0` or `1/2`.
      by_cases he : e.1 ∈ p.toSubgraph.edgeSet
      · have hmem : e.1 ∈ p.edges := by
          simpa [SimpleGraph.Walk.edgeSet_toSubgraph] using he
        simp [x, SimpleGraph.subgraphIncidenceVector, hmem]
      · have hmem : e.1 ∉ p.edges := by
          simpa [SimpleGraph.Walk.edgeSet_toSubgraph] using he
        simp [x, SimpleGraph.subgraphIncidenceVector, hmem]
  have hsumIncidence :
      (E[G] U).sum (G.subgraphIncidenceVector ℝ p.toSubgraph) =
        Fintype.card p.toSubgraph.edgeSet := by
    have hInduce :
        p.toSubgraph.induce U = p.toSubgraph := by
      simpa [U] using (SimpleGraph.Subgraph.induce_self_verts (G' := p.toSubgraph))
    calc
      (E[G] U).sum (G.subgraphIncidenceVector ℝ p.toSubgraph) =
          Fintype.card ((p.toSubgraph.induce U).edgeSet) := by
            simpa [U] using
              inducedIncidenceSumEqCardInducedEdges (G := G) p.toSubgraph U.toFinset
      _ = Fintype.card p.toSubgraph.edgeSet := by
            simpa [hInduce]
  have hdot :
      blossom_vector G U ⬝ᵥ x = (Fintype.card p.toSubgraph.edgeSet : ℝ) / 2 := by
    rw [blossomVector_dot_eq_inducedEdgeSum (G := G) U x]
    calc
      (E[G] U).sum x =
          (1 / 2 : ℝ) * (E[G] U).sum (G.subgraphIncidenceVector ℝ p.toSubgraph) := by
            simp [x, Finset.mul_sum]
      _ = (Fintype.card p.toSubgraph.edgeSet : ℝ) / 2 := by
            rw [hsumIncidence]
            ring
  have hstrict :
      blossom_rhs U < blossom_vector G U ⬝ᵥ x := by
    rw [hdot, blossom_rhs, hUcard, cycleSubgraph_card_edgeSet_eq_length (G := G) hpCycle]
    rcases hpOdd with ⟨k, hk⟩
    nlinarith [hk]
  exact ⟨hUodd, hx_mem, hstrict⟩

/-- Helper for Exercise 7.4: on a nonbipartite graph the degree relaxation is strictly larger than
the matching polytope, witnessed by the half-incidence vector of an odd cycle. -/
private lemma matchingDegreeConstraintSet_ne_matchingPolytope_of_not_isBipartite
    (hG : ¬ G.IsBipartite) :
    matching_degree_constraint_set G ≠ G.matchingPolytope := by
  obtain ⟨u, p, hpCycle, hpOdd⟩ := existsOddCycleWalk_of_not_isBipartite (G := G) hG
  let U : Set V := p.toSubgraph.verts
  let x : G.edgeSet → ℝ := fun e ↦ (1 / 2 : ℝ) * G.subgraphIncidenceVector ℝ p.toSubgraph e
  rcases halfOddCycleWitness_spec (G := G) hpCycle hpOdd with ⟨hUodd, hx_deg, hstrict⟩
  intro hEq
  have hxMatch : x ∈ G.matchingConstraintSet := by
    -- Transfer the degree-relaxation point through the canonical matching-polytope bridge.
    have hxPoly : x ∈ G.matchingPolytope := by
      simpa [x, hEq] using hx_deg
    rw [matchingPolytope_eq_matchingConstraintSet (G := G)] at hxPoly
    exact hxPoly
  have hvalid :
      blossom_vector G U ⬝ᵥ x ≤ blossom_rhs U := by
    simpa [blossomVector_dot_eq_inducedEdgeSum (G := G) U x, blossom_rhs] using
      (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := x)).1 hxMatch |>.2.2 U hUodd
  linarith

/-- Helper for Exercise 7.4: the `0/1` indicator of a finite edge set evaluates under dot product
as the corresponding coordinate sum. -/
private lemma finsetIndicator_dot_eq_sum
    (S : Finset G.edgeSet) (x : G.edgeSet → ℝ) :
    (fun e : G.edgeSet ↦ if e ∈ S then (1 : ℝ) else 0) ⬝ᵥ x = S.sum x := by
  -- Expand the dot product and discard the coordinates outside `S`.
  rw [dotProduct]
  calc
    ∑ e : G.edgeSet, (if e ∈ S then (1 : ℝ) else 0) * x e =
        ∑ e : G.edgeSet, if e ∈ S then x e else 0 := by
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases h : e ∈ S
          · simp [h]
          · simp [h]
    _ = S.sum x := by
          simpa using
            (Finset.sum_filter
              (s := (Finset.univ : Finset G.edgeSet))
              (p := fun e : G.edgeSet ↦ e ∈ S)
              (f := x)).symm

/-- Helper for Exercise 7.4: reindexing along `Fintype.equivFin G.edgeSet` identifies native
edge-coordinate vectors with `Fin`-indexed vectors. -/
private noncomputable abbrev graphEdgeCoordinateReindex :
    (Fin (Fintype.card G.edgeSet) → ℝ) ≃L[ℝ] (G.edgeSet → ℝ) :=
  (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin G.edgeSet)).toContinuousLinearEquiv

/-- Helper for Exercise 7.4: evaluating a reindexed `Fin`-vector at an edge recovers the native
edge coordinate. -/
@[simp] private theorem graphEdgeCoordinateReindex_apply
    (y : Fin (Fintype.card G.edgeSet) → ℝ)
    (e : G.edgeSet) :
    graphEdgeCoordinateReindex (G := G) y e = y ((Fintype.equivFin G.edgeSet) e) := by
  -- This is the defining formula of `LinearEquiv.funCongrLeft`.
  rw [graphEdgeCoordinateReindex, ContinuousLinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply]

/-- Helper for Exercise 7.4: the canonical `Fin`-indexed view of `matchingPolytope G`. -/
private noncomputable def matchingPolytopeReindexed :
    Set (Fin (Fintype.card G.edgeSet) → ℝ) :=
  (graphEdgeCoordinateReindex (G := G)).symm '' G.matchingPolytope

/-- Helper for Exercise 7.4: membership in the reindexed matching polytope means that the
corresponding native vector lies in `matchingPolytope G`. -/
private theorem mem_matchingPolytopeReindexed_iff
    {y : Fin (Fintype.card G.edgeSet) → ℝ} :
    y ∈ matchingPolytopeReindexed (G := G) ↔
      graphEdgeCoordinateReindex (G := G) y ∈ G.matchingPolytope := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hx
  · intro hy
    exact ⟨graphEdgeCoordinateReindex (G := G) y, hy,
      ContinuousLinearEquiv.symm_apply_apply (graphEdgeCoordinateReindex (G := G)) y⟩

/-- Helper for Exercise 7.4: the reindexed blossom face is the image of `blossom_face G U` under
the inverse coordinate reindexing. -/
private noncomputable def matchingPolytopeReindexedBlossomFace
    (U : Set V) :
    Set (Fin (Fintype.card G.edgeSet) → ℝ) :=
  (graphEdgeCoordinateReindex (G := G)).symm '' blossom_face G U

/-- Helper for Exercise 7.4: membership in the reindexed blossom face is equivalent to membership
in the native blossom face after undoing the coordinate reindexing. -/
private theorem mem_matchingPolytopeReindexedBlossomFace_iff
    {U : Set V}
    {y : Fin (Fintype.card G.edgeSet) → ℝ} :
    y ∈ matchingPolytopeReindexedBlossomFace (G := G) U ↔
      graphEdgeCoordinateReindex (G := G) y ∈ blossom_face G U := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hx
  · intro hy
    exact ⟨graphEdgeCoordinateReindex (G := G) y, hy,
      ContinuousLinearEquiv.symm_apply_apply (graphEdgeCoordinateReindex (G := G)) y⟩

/-- Helper for Exercise 7.4: the odd-set rows of the matching-constraint presentation are indexed
by odd vertex subsets of `V`. -/
private abbrev MatchingConstraintOddSet :=
  {U : Set V // Odd U.ncard}

/-- Helper for Exercise 7.4: the finite row owner for the matching-constraint system consists of
edge nonnegativity rows, vertex degree rows, and odd-set rows. -/
private abbrev MatchingConstraintRow :=
  G.edgeSet ⊕ (V ⊕ MatchingConstraintOddSet (V := V))

/-- Helper for Exercise 7.4: the number of rows in the finite matching-constraint presentation. -/
private noncomputable abbrev matchingConstraintRowCount : ℕ :=
  Fintype.card (MatchingConstraintRow (G := G))

/-- Helper for Exercise 7.4: the row encoding of the nonnegativity inequality `-x_e ≤ 0`. -/
private abbrev matchingConstraintNonnegRow
    (e : G.edgeSet) : MatchingConstraintRow (G := G) :=
  Sum.inl e

/-- Helper for Exercise 7.4: the row encoding of the degree inequality
`∑_{e ∈ δ(v)} x_e ≤ 1`. -/
private abbrev matchingConstraintDegreeRow
    (v : V) : MatchingConstraintRow (G := G) :=
  Sum.inr (Sum.inl v)

/-- Helper for Exercise 7.4: the row encoding of the odd-set inequality attached to `U`. -/
private abbrev matchingConstraintOddRow
    (U : MatchingConstraintOddSet (V := V)) : MatchingConstraintRow (G := G) :=
  Sum.inr (Sum.inr U)

/-- Helper for Exercise 7.4: the finite matrix presentation of the nonnegativity, degree, and
odd-set inequalities defining `matchingConstraintSet G`. -/
private noncomputable def matchingConstraintMatrix :
    Matrix (Fin (matchingConstraintRowCount (G := G)))
      (Fin (Fintype.card G.edgeSet)) ℝ :=
  fun i j ↦
    let row := (Fintype.equivFin (MatchingConstraintRow (G := G))).symm i
    let e := (Fintype.equivFin G.edgeSet).symm j
    match row with
    | Sum.inl e₀ => if e = e₀ then -1 else 0
    | Sum.inr (Sum.inl v) => if e ∈ incidentEdgeFinset G v then 1 else 0
    | Sum.inr (Sum.inr U) => if e ∈ E[G] U.1 then 1 else 0

/-- Helper for Exercise 7.4: the right-hand side of the finite matching-constraint presentation. -/
private noncomputable def matchingConstraintRhs :
    Fin (matchingConstraintRowCount (G := G)) → ℝ :=
  fun i ↦
    match (Fintype.equivFin (MatchingConstraintRow (G := G))).symm i with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 1
    | Sum.inr (Sum.inr U) => blossom_rhs U.1

/-- Helper for Exercise 7.4: reindexing a matrix row back to `G.edgeSet` turns the `Fin`-sum into
the corresponding native edge-coordinate sum. -/
private theorem matchingConstraintRowEvalNative
    (y : Fin (Fintype.card G.edgeSet) → ℝ)
    (row : MatchingConstraintRow (G := G)) :
    (matchingConstraintMatrix (G := G) *ᵥ y)
        ((Fintype.equivFin (MatchingConstraintRow (G := G))) row) =
      ∑ e : G.edgeSet,
        matchingConstraintMatrix (G := G)
            ((Fintype.equivFin (MatchingConstraintRow (G := G))) row)
            ((Fintype.equivFin G.edgeSet) e) *
          graphEdgeCoordinateReindex (G := G) y e := by
  -- Rewrite the `Fin`-indexed matrix row as a native edge-indexed sum.
  rw [Matrix.mulVec, dotProduct]
  symm
  exact Fintype.sum_equiv (Fintype.equivFin G.edgeSet) _ _ fun e ↦ by
    simp [graphEdgeCoordinateReindex_apply]

/-- Helper for Exercise 7.4: the nonnegativity row for `e` evaluates to `-x_e`. -/
private theorem matchingConstraintNonnegRowEval
    (y : Fin (Fintype.card G.edgeSet) → ℝ)
    (e : G.edgeSet) :
    (matchingConstraintMatrix (G := G) *ᵥ y)
        ((Fintype.equivFin (MatchingConstraintRow (G := G)))
          (matchingConstraintNonnegRow (G := G) e)) =
      -graphEdgeCoordinateReindex (G := G) y e := by
  -- Only the chosen edge coordinate contributes, with coefficient `-1`.
  rw [matchingConstraintRowEvalNative (G := G) y]
  calc
    ∑ e' : G.edgeSet,
        matchingConstraintMatrix (G := G)
            ((Fintype.equivFin (MatchingConstraintRow (G := G)))
              (matchingConstraintNonnegRow (G := G) e))
            ((Fintype.equivFin G.edgeSet) e') *
          graphEdgeCoordinateReindex (G := G) y e' =
      ∑ e' : G.edgeSet,
        if e' = e then -graphEdgeCoordinateReindex (G := G) y e' else 0 := by
          refine Finset.sum_congr rfl ?_
          intro e' he'
          by_cases hee : e' = e
          · simp [matchingConstraintMatrix, matchingConstraintNonnegRow, hee]
          · simp [matchingConstraintMatrix, matchingConstraintNonnegRow, hee]
    _ = -graphEdgeCoordinateReindex (G := G) y e := by
          rw [Fintype.sum_eq_single e]
          · simp
          · intro e' he'
            simp [he']

/-- Helper for Exercise 7.4: the degree row at `v` evaluates to the incident-edge sum. -/
private theorem matchingConstraintDegreeRowEval
    (y : Fin (Fintype.card G.edgeSet) → ℝ)
    (v : V) :
    (matchingConstraintMatrix (G := G) *ᵥ y)
        ((Fintype.equivFin (MatchingConstraintRow (G := G)))
          (matchingConstraintDegreeRow (G := G) v)) =
      (incidentEdgeFinset G v).sum (fun e ↦ graphEdgeCoordinateReindex (G := G) y e) := by
  -- The degree row is the indicator of the incident-edge finset of `v`.
  rw [matchingConstraintRowEvalNative (G := G) y]
  calc
    ∑ e : G.edgeSet,
        matchingConstraintMatrix (G := G)
            ((Fintype.equivFin (MatchingConstraintRow (G := G)))
              (matchingConstraintDegreeRow (G := G) v))
            ((Fintype.equivFin G.edgeSet) e) *
          graphEdgeCoordinateReindex (G := G) y e =
      ∑ e : G.edgeSet,
        if e ∈ incidentEdgeFinset G v then graphEdgeCoordinateReindex (G := G) y e else 0 := by
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases hinc : e ∈ incidentEdgeFinset G v
          · simp [matchingConstraintMatrix, matchingConstraintDegreeRow, hinc]
          · simp [matchingConstraintMatrix, matchingConstraintDegreeRow, hinc]
    _ = (incidentEdgeFinset G v).sum (fun e ↦ graphEdgeCoordinateReindex (G := G) y e) := by
          rw [← Finset.sum_filter]
          simp

/-- Helper for Exercise 7.4: the odd-set row for `U` evaluates to the corresponding blossom
left-hand side. -/
private theorem matchingConstraintOddRowEval
    (y : Fin (Fintype.card G.edgeSet) → ℝ)
    (U : MatchingConstraintOddSet (V := V)) :
    (matchingConstraintMatrix (G := G) *ᵥ y)
        ((Fintype.equivFin (MatchingConstraintRow (G := G)))
          (matchingConstraintOddRow (G := G) U)) =
      blossom_vector G U.1 ⬝ᵥ graphEdgeCoordinateReindex (G := G) y := by
  -- The odd-set row is the indicator of the induced-edge finset `E[G] U`.
  rw [matchingConstraintRowEvalNative (G := G) y]
  calc
    ∑ e : G.edgeSet,
        matchingConstraintMatrix (G := G)
            ((Fintype.equivFin (MatchingConstraintRow (G := G)))
              (matchingConstraintOddRow (G := G) U))
            ((Fintype.equivFin G.edgeSet) e) *
          graphEdgeCoordinateReindex (G := G) y e =
      ∑ e : G.edgeSet,
        if e ∈ E[G] U.1 then graphEdgeCoordinateReindex (G := G) y e else 0 := by
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases hU : e ∈ E[G] U.1
          · simp [matchingConstraintMatrix, matchingConstraintOddRow, hU]
          · simp [matchingConstraintMatrix, matchingConstraintOddRow, hU]
    _ = blossom_vector G U.1 ⬝ᵥ graphEdgeCoordinateReindex (G := G) y := by
          rw [← blossomVector_dot_eq_inducedEdgeSum (G := G) U.1
            (graphEdgeCoordinateReindex (G := G) y)]
          rw [← Finset.sum_filter]
          simp

/-- Helper for Exercise 7.4: the explicit finite matrix presentation encodes exactly the native
matching-constraint system after reindexing coordinates. -/
private theorem graphEdgeCoordinateReindex_mem_matchingConstraintSet_iff
    {y : Fin (Fintype.card G.edgeSet) → ℝ} :
    graphEdgeCoordinateReindex (G := G) y ∈ G.matchingConstraintSet ↔
      y ∈ polyhedron_le_set (matchingConstraintMatrix (G := G))
        (matchingConstraintRhs (G := G)) := by
  constructor
  · intro hy
    rcases (SimpleGraph.mem_matchingConstraintSet_iff
      (G := G) (x := graphEdgeCoordinateReindex (G := G) y)).1 hy with
      ⟨hy_nonneg, hy_deg, hy_odd⟩
    rw [mem_polyhedron_le_set_iff]
    intro i
    let row : MatchingConstraintRow (G := G) :=
      (Fintype.equivFin (MatchingConstraintRow (G := G))).symm i
    match hrow : row with
    | Sum.inl e =>
        have hi :
            (Fintype.equivFin (MatchingConstraintRow (G := G)))
              (matchingConstraintNonnegRow (G := G) e) = i := by
          simpa [row, matchingConstraintNonnegRow] using
            congrArg (Fintype.equivFin (MatchingConstraintRow (G := G))) hrow
        have hrowEval :
            (matchingConstraintMatrix (G := G) *ᵥ y) i =
              -graphEdgeCoordinateReindex (G := G) y e := by
          rw [← hi]
          exact matchingConstraintNonnegRowEval (G := G) y e
        have hrhs :
            matchingConstraintRhs (G := G) i = 0 := by
          rw [← hi]
          simp [matchingConstraintRhs, matchingConstraintNonnegRow]
        -- The native nonnegativity constraint is exactly the negated row inequality.
        calc
          (matchingConstraintMatrix (G := G) *ᵥ y) i
              = -graphEdgeCoordinateReindex (G := G) y e := hrowEval
          _ ≤ 0 := by linarith [hy_nonneg e]
          _ = matchingConstraintRhs (G := G) i := hrhs.symm
    | Sum.inr (Sum.inl v) =>
        have hi :
            (Fintype.equivFin (MatchingConstraintRow (G := G)))
              (matchingConstraintDegreeRow (G := G) v) = i := by
          simpa [row, matchingConstraintDegreeRow] using
            congrArg (Fintype.equivFin (MatchingConstraintRow (G := G))) hrow
        have hrowEval :
            (matchingConstraintMatrix (G := G) *ᵥ y) i =
              (incidentEdgeFinset G v).sum
                (fun e ↦ graphEdgeCoordinateReindex (G := G) y e) := by
          rw [← hi]
          exact matchingConstraintDegreeRowEval (G := G) y v
        have hrhs :
            matchingConstraintRhs (G := G) i = 1 := by
          rw [← hi]
          simp [matchingConstraintRhs, matchingConstraintDegreeRow]
        -- The native degree inequality is exactly the stored degree row.
        calc
          (matchingConstraintMatrix (G := G) *ᵥ y) i
              = (incidentEdgeFinset G v).sum
                  (fun e ↦ graphEdgeCoordinateReindex (G := G) y e) := hrowEval
          _ ≤ 1 := hy_deg v
          _ = matchingConstraintRhs (G := G) i := hrhs.symm
    | Sum.inr (Sum.inr U) =>
        have hi :
            (Fintype.equivFin (MatchingConstraintRow (G := G)))
              (matchingConstraintOddRow (G := G) U) = i := by
          simpa [row, matchingConstraintOddRow] using
            congrArg (Fintype.equivFin (MatchingConstraintRow (G := G))) hrow
        have hrowEval :
            (matchingConstraintMatrix (G := G) *ᵥ y) i =
              blossom_vector G U.1 ⬝ᵥ graphEdgeCoordinateReindex (G := G) y := by
          rw [← hi]
          exact matchingConstraintOddRowEval (G := G) y U
        have hrhs :
            matchingConstraintRhs (G := G) i = blossom_rhs U.1 := by
          rw [← hi]
          simp [matchingConstraintRhs, matchingConstraintOddRow]
        -- The native odd-set inequality is exactly the stored blossom row.
        calc
          (matchingConstraintMatrix (G := G) *ᵥ y) i
              = blossom_vector G U.1 ⬝ᵥ graphEdgeCoordinateReindex (G := G) y := hrowEval
          _ ≤ blossom_rhs U.1 := hy_odd U.1 U.2
          _ = matchingConstraintRhs (G := G) i := hrhs.symm
  · intro hy
    rw [mem_polyhedron_le_set_iff] at hy
    refine (SimpleGraph.mem_matchingConstraintSet_iff
      (G := G) (x := graphEdgeCoordinateReindex (G := G) y)).2 ?_
    refine ⟨?_, ?_, ?_⟩
    · intro e
      have hyRow :=
        hy ((Fintype.equivFin (MatchingConstraintRow (G := G)))
          (matchingConstraintNonnegRow (G := G) e))
      -- Read the stored nonnegativity row back as `0 ≤ x_e`.
      simpa [matchingConstraintNonnegRowEval (G := G) y e, matchingConstraintRhs,
        matchingConstraintNonnegRow] using hyRow
    · intro v
      have hyRow :=
        hy ((Fintype.equivFin (MatchingConstraintRow (G := G)))
          (matchingConstraintDegreeRow (G := G) v))
      -- Read the stored degree row back as the native incident-edge inequality.
      simpa [matchingConstraintDegreeRowEval (G := G) y v, matchingConstraintRhs,
        matchingConstraintDegreeRow] using hyRow
    · intro U hUodd
      have hyRow :=
        hy ((Fintype.equivFin (MatchingConstraintRow (G := G)))
          (matchingConstraintOddRow (G := G) ⟨U, hUodd⟩))
      -- Read the stored odd-set row back as the native blossom inequality.
      simpa [matchingConstraintOddRowEval (G := G) y ⟨U, hUodd⟩, matchingConstraintRhs,
        matchingConstraintOddRow] using hyRow

/-- Helper for Exercise 7.4: after reindexing edge coordinates, `matchingPolytope G` becomes the
explicit finite polyhedron encoded by `matchingConstraintMatrix G` and `matchingConstraintRhs G`.
-/
private theorem matchingPolytopeReindexed_eq_polyhedron :
    matchingPolytopeReindexed (G := G) =
      polyhedron_le_set (matchingConstraintMatrix (G := G))
        (matchingConstraintRhs (G := G)) := by
  ext y
  rw [mem_matchingPolytopeReindexed_iff, matchingPolytope_eq_matchingConstraintSet (G := G)]
  exact graphEdgeCoordinateReindex_mem_matchingConstraintSet_iff (G := G)

/-- Helper for Exercise 7.4: the singleton active face of the odd row for `U` is exactly the
reindexed blossom equality face. -/
private theorem oddRowActiveFace_eq_reindexedBlossomFace
    (U : Set V) (hUodd : Odd U.ncard) :
    active_constraint_face (matchingConstraintMatrix (G := G))
        (matchingConstraintRhs (G := G))
        ({(Fintype.equivFin (MatchingConstraintRow (G := G)))
            (matchingConstraintOddRow (G := G) ⟨U, hUodd⟩)} :
          Set (Fin (matchingConstraintRowCount (G := G)))) =
      matchingPolytopeReindexedBlossomFace (G := G) U := by
  ext y
  constructor
  · intro hy
    have hyPoly :
        y ∈ polyhedron_le_set (matchingConstraintMatrix (G := G))
          (matchingConstraintRhs (G := G)) :=
      mem_polyhedron_of_mem_active_constraint_face hy
    have hyMatch : y ∈ matchingPolytopeReindexed (G := G) := by
      rw [matchingPolytopeReindexed_eq_polyhedron (G := G)]
      exact hyPoly
    have hyEq :
        blossom_vector G U ⬝ᵥ graphEdgeCoordinateReindex (G := G) y = blossom_rhs U := by
      have hyRow :
          (matchingConstraintMatrix (G := G) *ᵥ y)
              ((Fintype.equivFin (MatchingConstraintRow (G := G)))
                (matchingConstraintOddRow (G := G) ⟨U, hUodd⟩)) =
            matchingConstraintRhs (G := G)
              ((Fintype.equivFin (MatchingConstraintRow (G := G)))
                (matchingConstraintOddRow (G := G) ⟨U, hUodd⟩)) :=
        (mem_active_constraint_face_iff.mp hy).1 _ (by simp)
      simpa [matchingConstraintOddRowEval (G := G) y ⟨U, hUodd⟩,
        matchingConstraintRhs, matchingConstraintOddRow] using hyRow
    -- The active odd row records the blossom equality after undoing the reindexing.
    rw [mem_matchingPolytopeReindexedBlossomFace_iff]
    exact (mem_blossom_face_iff (G := G) (U := U)
      (x := graphEdgeCoordinateReindex (G := G) y)).2
      ⟨(mem_matchingPolytopeReindexed_iff (G := G)).1 hyMatch, hyEq⟩
  · intro hy
    have hyFaceNative :
        graphEdgeCoordinateReindex (G := G) y ∈ blossom_face G U :=
      (mem_matchingPolytopeReindexedBlossomFace_iff (G := G) (U := U)).1 hy
    have hyPoly :
        y ∈ polyhedron_le_set (matchingConstraintMatrix (G := G))
          (matchingConstraintRhs (G := G)) := by
      rw [← matchingPolytopeReindexed_eq_polyhedron (G := G)]
      exact (mem_matchingPolytopeReindexed_iff (G := G)).2
        ((mem_blossom_face_iff (G := G) (U := U)
          (x := graphEdgeCoordinateReindex (G := G) y)).1 hyFaceNative).1
    have hyEq :
        blossom_vector G U ⬝ᵥ graphEdgeCoordinateReindex (G := G) y = blossom_rhs U :=
      (mem_blossom_face_iff (G := G) (U := U)
        (x := graphEdgeCoordinateReindex (G := G) y)).1 hyFaceNative |>.2
    -- The blossom equality is exactly the equality attached to the odd row for `U`.
    refine (mem_active_constraint_face_iff).2 ?_
    refine ⟨?_, ?_⟩
    · intro i hi
      have hiRow :
          i =
            (Fintype.equivFin (MatchingConstraintRow (G := G)))
              (matchingConstraintOddRow (G := G) ⟨U, hUodd⟩) := by
        simpa using hi
      rw [hiRow]
      simpa [matchingConstraintOddRowEval (G := G) y ⟨U, hUodd⟩, matchingConstraintRhs,
        matchingConstraintOddRow] using hyEq
    · intro i hi
      exact hyPoly i

/-- Helper for Exercise 7.4: a nonempty proper vertex subset of the support of an odd cycle spans
at most one fewer cycle edge than vertices. -/
private lemma properCycleSubset_edgeCountBound
    {u : V} {p : G.Walk u u}
    (hpCycle : p.IsCycle)
    {T : Set V}
    (hT_nonempty : T.Nonempty)
    (hT_subset : T ⊆ p.toSubgraph.verts)
    (hT_ne : T ≠ p.toSubgraph.verts) :
    Fintype.card ((p.toSubgraph.induce T).edgeSet) ≤ T.ncard - 1 := by
  classical
  let C : SimpleGraph V := p.toSubgraph.spanningCoe
  obtain ⟨vIn, hvIn⟩ := hT_nonempty
  have hcomp_nonempty : (p.toSubgraph.verts \ T).Nonempty := by
    by_contra hEmpty
    apply hT_ne
    ext v
    constructor
    · intro hv
      by_cases hvT : v ∈ T
      · exact hvT
      · exfalso
        exact hEmpty ⟨v, hv, hvT⟩
    · exact hT_subset
  obtain ⟨vOut, hvOut, hvOutNot⟩ := hcomp_nonempty
  have hConn : p.toSubgraph.Connected := p.toSubgraph_connected
  obtain ⟨-, hwalk⟩ :=
    (SimpleGraph.Subgraph.connected_iff_forall_exists_walk_subgraph (H := p.toSubgraph)).1 hConn
  obtain ⟨q, hq_le⟩ := hwalk (hT_subset hvIn) hvOut
  let qC : C.Walk vIn vOut := q.map (SimpleGraph.Subgraph.hom hq_le)
  have hcut_nonempty : (δ[C] T).Nonempty := by
    rcases walk_meets_cut_of_endpoints_separated (G := C) qC hvIn hvOutNot with
      ⟨e, heCut, -⟩
    exact ⟨e, heCut⟩
  have hdeg_sum :
      Finset.sum T.toFinset (fun v ↦ C.degree v) = 2 * T.toFinset.card := by
    calc
      Finset.sum T.toFinset (fun v ↦ C.degree v) =
          Finset.sum T.toFinset (fun _ : V ↦ (2 : ℕ)) := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            have hvVerts : v ∈ p.toSubgraph.verts := hT_subset (by simpa using hv)
            have hvSupport : v ∈ p.support := p.mem_verts_toSubgraph.mp hvVerts
            have hdeg : p.toSubgraph.degree v = 2 := by
              rw [← SimpleGraph.Subgraph.finset_card_neighborSet_eq_degree
                (G' := p.toSubgraph) (v := v)]
              simpa [Set.toFinset_card] using
                hpCycle.ncard_neighborSet_toSubgraph_eq_two hvSupport
            simpa [C] using (SimpleGraph.Subgraph.degree_spanningCoe
              (G' := p.toSubgraph) v).trans hdeg
      _ = T.toFinset.card * 2 := by simp
      _ = 2 * T.toFinset.card := by rw [Nat.mul_comm]
  have hcut_positive : 0 < (δ[C] T).card := by
    exact Finset.card_pos.mpr hcut_nonempty
  have hcount :
      2 * T.toFinset.card =
        2 * (E[C] T).card + (δ[C] T).card := by
    calc
      2 * T.toFinset.card = Finset.sum T.toFinset (fun v ↦ C.degree v) := by
        symm
        exact hdeg_sum
      _ = 2 * (E[C] T).card + (δ[C] T).card :=
        sum_degrees_on_set_eq_twice_induced_edges_add_cut_card (G := C) T
  have hcut_two : 2 ≤ (δ[C] T).card := by
    omega
  have hedge_eq :
      (E[C] T).card = Fintype.card ((p.toSubgraph.induce T).edgeSet) := by
    have hsumCard :
        (E[C] T).sum (fun _ ↦ (1 : ℝ)) =
          Fintype.card (((⊤ : C.Subgraph).induce T).edgeSet) := by
      simpa [SimpleGraph.subgraphIncidenceVector] using
        inducedIncidenceSumEqCardInducedEdges (G := C) (T := (⊤ : C.Subgraph)) T.toFinset
    have hedgeSetEq :
        (((⊤ : C.Subgraph).induce T).edgeSet) = (p.toSubgraph.induce T).edgeSet := by
      ext e
      simp [C, SimpleGraph.Subgraph.induce, Set.mem_inter_iff, SimpleGraph.Subgraph.mem_edgeSet]
    calc
      (E[C] T).card = Fintype.card (((⊤ : C.Subgraph).induce T).edgeSet) := by
        simpa using hsumCard
      _ = Fintype.card ((p.toSubgraph.induce T).edgeSet) := by
        rw [hedgeSetEq]
  have hbound_nat :
      Fintype.card ((p.toSubgraph.induce T).edgeSet) ≤ T.toFinset.card - 1 := by
    rw [← hedge_eq] at hcount
    omega
  simpa [Set.ncard_eq_toFinset_card] using hbound_nat

/-- Helper for Exercise 7.4: the half-incidence witness for an odd cycle satisfies every odd-set
row except the blossom row indexed by the full cycle support. -/
private lemma halfOddCycleWitness_satisfiesOtherOddSetRows
    {u : V} {p : G.Walk u u}
    (hpCycle : p.IsCycle) (hpOdd : Odd p.length) :
    let U : Set V := p.toSubgraph.verts
    let x : G.edgeSet → ℝ := fun e ↦ (1 / 2 : ℝ) * G.subgraphIncidenceVector ℝ p.toSubgraph e
    ∀ S : Set V, Odd S.ncard → S ≠ U →
      (E[G] S).sum x ≤ blossom_rhs S := by
  classical
  let U : Set V := p.toSubgraph.verts
  let x : G.edgeSet → ℝ := fun e ↦ (1 / 2 : ℝ) * G.subgraphIncidenceVector ℝ p.toSubgraph e
  intro S hSodd hS_ne
  let T : Set V := S ∩ U
  have hsumT :
      (E[G] S).sum x = (Fintype.card ((p.toSubgraph.induce T).edgeSet) : ℝ) / 2 := by
    have hInduceEq :
        (p.toSubgraph.induce S).edgeSet = (p.toSubgraph.induce T).edgeSet := by
      ext e
      constructor
      · intro he
        rcases (SimpleGraph.Subgraph.mem_edgeSet).1 he with ⟨hS₁, hS₂, hedge⟩
        have hU₁ : e.1.out.1 ∈ U := p.toSubgraph.edge_vert hedge Sym2.out_fst_mem
        have hU₂ : e.1.out.2 ∈ U := p.toSubgraph.edge_vert hedge Sym2.out_snd_mem
        exact (SimpleGraph.Subgraph.mem_edgeSet).2 ⟨⟨hS₁, hU₁⟩, ⟨hS₂, hU₂⟩, hedge⟩
      · intro he
        rcases (SimpleGraph.Subgraph.mem_edgeSet).1 he with ⟨hT₁, hT₂, hedge⟩
        exact (SimpleGraph.Subgraph.mem_edgeSet).2 ⟨hT₁.1, hT₂.1, hedge⟩
    calc
      (E[G] S).sum x =
          (1 / 2 : ℝ) * (E[G] S).sum (G.subgraphIncidenceVector ℝ p.toSubgraph) := by
            simp [x, Finset.mul_sum]
      _ = (1 / 2 : ℝ) * Fintype.card ((p.toSubgraph.induce S).edgeSet) := by
            simpa [S] using
              inducedIncidenceSumEqCardInducedEdges (G := G) p.toSubgraph S.toFinset
      _ = (Fintype.card ((p.toSubgraph.induce T).edgeSet) : ℝ) / 2 := by
            rw [hInduceEq]
            ring
  by_cases hT_empty : T = ∅
  · have hcard_zero :
        Fintype.card ((p.toSubgraph.induce T).edgeSet) = 0 := by
      subst hT_empty
      simp
    have hrhs_nonneg : 0 ≤ blossom_rhs S := by
      rcases hSodd with ⟨k, hk⟩
      rw [blossom_rhs, hk]
      norm_num
    -- When `S ∩ U = ∅`, the witness has zero mass on the odd-set row.
    rw [hsumT, hcard_zero]
    linarith
  · by_cases hT_full : T = U
    · have hUSubset : U ⊆ S := by
        intro v hv
        have : v ∈ T := by simpa [T, hT_full] using hv
        exact this.1
      have hlt : U.ncard < S.ncard := Set.ncard_lt_ncard hUSubset hS_ne
      have hsumU :
          Fintype.card ((p.toSubgraph.induce T).edgeSet) = U.ncard := by
        subst hT_full
        simpa [U] using
          cycleSupport_ncard_eq_card_edgeSet (G := G) (p := p) hpCycle
      rw [hsumT, hsumU, blossom_rhs]
      have hnat : U.ncard ≤ S.ncard - 1 := by omega
      exact (div_le_div_right (by norm_num : (0 : ℝ) < 2)).2 (by exact_mod_cast hnat)
    · have hT_nonempty : T.Nonempty := by
        refine Set.nonempty_iff_ne_empty.mpr ?_
        exact hT_empty
      have hT_subset : T ⊆ p.toSubgraph.verts := by
        intro v hv
        exact hv.2
      have hproper :
          Fintype.card ((p.toSubgraph.induce T).edgeSet) ≤ T.ncard - 1 :=
        properCycleSubset_edgeCountBound (G := G) (p := p) hpCycle hT_nonempty hT_subset hT_full
      have hT_le_S : T.ncard ≤ S.ncard := Set.ncard_mono (by intro v hv; exact hv.1)
      rw [hsumT, blossom_rhs]
      have hnat :
          Fintype.card ((p.toSubgraph.induce T).edgeSet) ≤ S.ncard - 1 := by
        exact le_trans hproper (by omega)
      exact (div_le_div_right (by norm_num : (0 : ℝ) < 2)).2 (by exact_mod_cast hnat)

/-- Helper for Exercise 7.4: the odd-cycle blossom row is irredundant in the finite matching
constraint presentation. -/
private lemma oddCycleBlossomRow_isIrredundant
    {u : V} {p : G.Walk u u}
    (hpCycle : p.IsCycle) (hpOdd : Odd p.length) :
    let U : Set V := p.toSubgraph.verts
    let j :=
      (Fintype.equivFin (MatchingConstraintRow (G := G)))
        (matchingConstraintOddRow (G := G)
          ⟨U, (halfOddCycleWitness_spec (G := G) (p := p) hpCycle hpOdd).1⟩)
    is_irredundant_row (matchingConstraintMatrix (G := G))
      (matchingConstraintRhs (G := G)) j := by
  classical
  let U : Set V := p.toSubgraph.verts
  let x : G.edgeSet → ℝ := fun e ↦ (1 / 2 : ℝ) * G.subgraphIncidenceVector ℝ p.toSubgraph e
  let y : Fin (Fintype.card G.edgeSet) → ℝ :=
    (graphEdgeCoordinateReindex (G := G)).symm x
  rcases halfOddCycleWitness_spec (G := G) (p := p) hpCycle hpOdd with
    ⟨hUodd, hx_deg, hstrict⟩
  let j :=
    (Fintype.equivFin (MatchingConstraintRow (G := G)))
      (matchingConstraintOddRow (G := G) ⟨U, hUodd⟩)
  refine ⟨y, ?_, ?_⟩
  · intro i hi
    let row : MatchingConstraintRow (G := G) :=
      (Fintype.equivFin (MatchingConstraintRow (G := G))).symm i
    match hrow : row with
    | Sum.inl e =>
        have hx_nonneg := (mem_matching_degree_constraint_set_iff (G := G) (x := x)).1 hx_deg |>.2 e
        -- The nonnegativity rows are inherited directly from `hx_deg`.
        simpa [y, matchingConstraintNonnegRowEval (G := G) y e, matchingConstraintRhs,
          matchingConstraintNonnegRow] using (show -x e ≤ 0 by linarith)
    | Sum.inr (Sum.inl v) =>
        have hx_row := (mem_matching_degree_constraint_set_iff (G := G) (x := x)).1 hx_deg |>.1 v
        -- The degree rows are inherited directly from `hx_deg`.
        simpa [y, matchingConstraintDegreeRowEval (G := G) y v, matchingConstraintRhs,
          matchingConstraintDegreeRow] using hx_row
    | Sum.inr (Sum.inr Sodd) =>
        have hrow_ne :
            row ≠ matchingConstraintOddRow (G := G) ⟨U, hUodd⟩ := by
          intro hEq
          apply hi
          simpa [j, row] using congrArg (Fintype.equivFin (MatchingConstraintRow (G := G))) hEq
        have hS_ne : Sodd.1 ≠ U := by
          intro hEq
          apply hrow_ne
          cases Sodd
          simp [matchingConstraintOddRow, hEq]
        have hx_odd :
            (E[G] Sodd.1).sum x ≤ blossom_rhs Sodd.1 :=
          halfOddCycleWitness_satisfiesOtherOddSetRows (G := G) (p := p) hpCycle hpOdd
            Sodd.1 Sodd.2 hS_ne
        -- Every other odd-set row remains valid on the half-cycle witness.
        simpa [y, matchingConstraintOddRowEval (G := G) y Sodd, matchingConstraintRhs,
          matchingConstraintOddRow, blossomVector_dot_eq_inducedEdgeSum (G := G) Sodd.1 x] using
          hx_odd
  · -- The chosen odd row is violated strictly by the half-cycle witness.
    have hrowEval :
        (matchingConstraintMatrix (G := G) *ᵥ y) j =
          blossom_vector G U ⬝ᵥ x := by
      simpa [j, y] using matchingConstraintOddRowEval (G := G) y ⟨U, hUodd⟩
    have hrhs :
        matchingConstraintRhs (G := G) j = blossom_rhs U := by
      simp [j, matchingConstraintRhs, matchingConstraintOddRow]
    rw [hrowEval, hrhs]
    exact hstrict

/-- Exercise 7.4 (2). If `G` is not bipartite, then some blossom inequality is facet-defining for
the matching polytope of `G`. -/
theorem exercise_7_4_exists_facet_defining_blossom_of_not_isBipartite
    (hG : ¬ G.IsBipartite) :
    ∃ U : Set V, Odd U.ncard ∧
      is_valid_inequality G.matchingPolytope (blossom_vector G U) (blossom_rhs U) ∧
        IsFacetOf G.matchingPolytope (blossom_face G U) := by
  classical
  obtain ⟨u, p, hpCycle, hpOdd⟩ := existsOddCycleWalk_of_not_isBipartite (G := G) hG
  let U : Set V := p.toSubgraph.verts
  rcases halfOddCycleWitness_spec (G := G) (p := p) hpCycle hpOdd with ⟨hUodd, -, -⟩
  refine ⟨U, hUodd, ?_, ?_⟩
  · -- Part (1) already supplied the blossom inequality as a Chvátal cut, hence as a valid
    -- inequality of the matching polytope.
    exact matchingDegreeSystemChvatal_isValid (G := G)
      (blossomIsMatchingDegreeSystemChvatal (G := G) U hUodd)
  · let A := matchingConstraintMatrix (G := G)
    let b := matchingConstraintRhs (G := G)
    let j : Fin (matchingConstraintRowCount (G := G)) :=
      (Fintype.equivFin (MatchingConstraintRow (G := G)))
        (matchingConstraintOddRow (G := G) ⟨U, hUodd⟩)
    let Fflat : Set (Fin (Fintype.card G.edgeSet) → ℝ) :=
      active_constraint_face A b ({j} : Set (Fin (matchingConstraintRowCount (G := G))))
    have hrow_irredundant : is_irredundant_row A b j := by
      simpa [A, b, j, U] using
        oddCycleBlossomRow_isIrredundant (G := G) (p := p) hpCycle hpOdd
    have hzero_poly :
        (0 : Fin (Fintype.card G.edgeSet) → ℝ) ∈ polyhedron_le_set A b := by
      rw [← matchingPolytopeReindexed_eq_polyhedron (G := G), mem_matchingPolytopeReindexed_iff]
      rw [matchingPolytope_eq_matchingConstraintSet (G := G)]
      refine (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := 0)).2 ?_
      refine ⟨?_, ?_, ?_⟩
      · intro e
        simp
      · intro v
        simp
      · intro S hSodd
        rcases hSodd with ⟨k, hk⟩
        rw [blossom_rhs, hk]
        norm_num
    have hrow_not_implicit : ¬ is_implicit_equality A b j := by
      intro hj_implicit
      have hz_eq : (A *ᵥ (0 : Fin (Fintype.card G.edgeSet) → ℝ)) j = b j :=
        hj_implicit hzero_poly
      have hUthree : 3 ≤ U.ncard := by
        simpa [U, cycleSupport_ncard_eq_length (G := G) (p := p) hpCycle] using
          hpCycle.three_le_length
      have hblossom_pos : 0 < blossom_rhs U := by
        rw [blossom_rhs]
        have hreal : (3 : ℝ) ≤ U.ncard := by exact_mod_cast hUthree
        nlinarith
      have hbval : b j = blossom_rhs U := by
        simp [A, b, j, matchingConstraintRhs, matchingConstraintOddRow]
      have hzeroEval : (A *ᵥ (0 : Fin (Fintype.card G.edgeSet) → ℝ)) j = 0 := by
        simp [A]
      rw [hzeroEval, hbval] at hz_eq
      linarith
    have hrow_remaining : j ∈ remaining_inequality_indices A b :=
      (mem_remaining_inequality_indices_iff A b j).2 hrow_not_implicit
    have hflat_nonempty : Fflat.Nonempty := by
      obtain ⟨y, hy, -⟩ :=
        exists_point_in_active_constraint_face_singleton_strict_on_other_nonimplicit_rows
          A b j ⟨0, hzero_poly⟩ hrow_irredundant
      exact ⟨y, hy⟩
    have hflat_codim :
        Module.finrank ℝ (affineSpan ℝ Fflat).direction + 1 =
          Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction := by
      simpa [Fflat] using
        (finrank_direction_affineSpan_add_one_eq_of_irredundant_singleton
          A b j hrow_remaining hrow_irredundant)
    have hflat_facet :
        IsFacetOf (polyhedron_le_set A b) Fflat := by
      -- The singleton active face is exposed and has codimension one by irredundancy.
      exact (isFacetOf_iff).2
        ⟨hflat_nonempty, active_constraint_face_isExposed A b ({j} : Set _), hflat_codim⟩
    -- Transport the codimension-one singleton face back to the native edge coordinates.
    simpa [A, b, Fflat, matchingPolytopeReindexed_eq_polyhedron (G := G),
      oddRowActiveFace_eq_reindexedBlossomFace (G := G) U hUodd,
      matchingPolytopeReindexed, matchingPolytopeReindexedBlossomFace]
      using (isFacetOf_image_continuousLinearEquiv
        (graphEdgeCoordinateReindex (G := G))).2 hflat_facet

/-- Exercise 7.4 (3). The matching polytope has Chvátal rank zero or one with respect to the
degree-system relaxation `∑_{e ∈ δ(v)} x_e ≤ 1, x ≥ 0`. -/
theorem exercise_7_4_matching_polytope_chvatal_rank_zero_or_one :
    matching_degree_system_has_chvatal_rank_zero G ∨
      matching_degree_system_has_chvatal_rank_one G := by
  by_cases hG : G.IsBipartite
  · left
    -- In the bipartite branch, the degree relaxation is already the matching polytope.
    exact matchingDegreeConstraintSet_eq_matchingPolytope_of_isBipartite (G := G) hG
  · right
    refine (matching_degree_system_has_chvatal_rank_one_iff (G := G)).2 ?_
    refine ⟨?_, ?_⟩
    · exact le_antisymm
        (matchingDegreeChvatalClosure_subset_matchingPolytope (G := G))
        (matchingPolytope_subset_matchingDegreeChvatalClosure (G := G))
    · exact matchingDegreeConstraintSet_ne_matchingPolytope_of_not_isBipartite (G := G) hG

/-- Exercise 7.4 (4). The matching polytope has Chvátal rank one with respect to the degree
system `∑_{e ∈ δ(v)} x_e ≤ 1, x ≥ 0` if and only if `G` is not bipartite. -/
theorem exercise_7_4_matching_polytope_chvatal_rank_one_iff_not_isBipartite :
    matching_degree_system_has_chvatal_rank_one G ↔ ¬ G.IsBipartite := by
  constructor
  · intro hRankOne hG
    rcases (matching_degree_system_has_chvatal_rank_one_iff (G := G)).1 hRankOne with
      ⟨-, hneq⟩
    exact hneq (matchingDegreeConstraintSet_eq_matchingPolytope_of_isBipartite (G := G) hG)
  · intro hG
    rcases exercise_7_4_matching_polytope_chvatal_rank_zero_or_one (G := G) with hZero | hOne
    · exfalso
      exact
        (matchingDegreeConstraintSet_ne_matchingPolytope_of_not_isBipartite (G := G) hG)
          ((matching_degree_system_has_chvatal_rank_zero_iff (G := G)).1 hZero)
    · exact hOne

end Exercise74

/-- `blossom_rhs U` is the displayed value `( |U| - 1 ) / 2`. -/
theorem blossom_rhs_eq
    {V : Type} (U : Set V) :
    blossom_rhs U = ((U.ncard : ℝ) - 1) / 2 := rfl
