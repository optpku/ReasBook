import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_5.ch4_sec4_5_theorem_4_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_1_proposition_8_9.PairIndicatorHull

-- This file reuses the Chapter 4.25 graph-coordinate owners
-- `SimpleGraph.subgraphIncidenceVector` and `SimpleGraph.inducedEdgeFinset`,
-- and restores the cut-edge notation locally for the Proposition 8.9 proof.

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

namespace SimpleGraph

/-- Helper for Proposition 8.9: the cut edges `δ(S)` in the ambient edge coordinates of `G`. -/
def cutEdgeFinset {V : Type*} (G : SimpleGraph V) [Fintype V] (S : Set V) : Finset G.edgeSet :=
  Finset.univ.filter fun e ↦ ∃ u ∈ S, ∃ v ∉ S, s(u, v) = (e : Sym2 V)

/-- Helper for Proposition 8.9: the cut-edge notation on ambient graph coordinates. -/
notation "δ[" G "] " S:arg => cutEdgeFinset G S

/-- Helper for Proposition 8.9: the induced-edge notation on ambient graph coordinates. -/
notation "E[" G "] " U:arg => SimpleGraph.inducedEdgeFinset G U

/-- Helper for Proposition 8.9: an ambient edge-coordinate belongs to `δ[G] S` exactly when one
endpoint lies in `S` and the other lies outside `S`. -/
theorem mem_cutEdgeFinset_iff {V : Type*} {G : SimpleGraph V} [Fintype V] {S : Set V}
    {e : G.edgeSet} :
    e ∈ δ[G] S ↔ ∃ u ∈ S, ∃ v ∉ S, s(u, v) = (e : Sym2 V) := by
  simp [cutEdgeFinset]

section Proposition_8_9

variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V}

namespace Subgraph

section

variable [DecidableRel G.Adj]

/-- A spanning subgraph of `G` is a 1-tree with distinguished root `root` when the root has degree
`2` and deleting the root leaves a tree. -/
def IsOneTree (H : G.Subgraph) (root : V) : Prop :=
  H.IsSpanning ∧
    H.degree root = 2 ∧
      (H.deleteVerts ({root} : Set V)).coe.IsTree

end

/-- A subgraph is a 1-tree with distinguished root `root` exactly when it is spanning, the root
has degree `2`, and deleting the root leaves a tree. -/
theorem isOneTree_iff {H : G.Subgraph} {root : V} :
    H.IsOneTree root ↔
      H.IsSpanning ∧
        H.degree root = 2 ∧
          (H.deleteVerts ({root} : Set V)).coe.IsTree :=
  Iff.rfl

/-- A 1-tree is spanning. -/
theorem IsOneTree.isSpanning {H : G.Subgraph} {root : V} (hH : H.IsOneTree root) :
    H.IsSpanning :=
  hH.1

/-- In a 1-tree the distinguished root has degree `2`. -/
theorem IsOneTree.degree_root_eq_two {H : G.Subgraph} {root : V} (hH : H.IsOneTree root) :
    H.degree root = 2 :=
  hH.2.1

/-- Deleting the distinguished root from a 1-tree leaves a tree. -/
theorem IsOneTree.deleteVerts_singleton_coe_isTree
    {H : G.Subgraph} {root : V} (hH : H.IsOneTree root) :
    (H.deleteVerts ({root} : Set V)).coe.IsTree :=
  hH.2.2

end Subgraph

section

variable [DecidableRel G.Adj]
variable (G : SimpleGraph V) (root : V)

/-- The incidence vectors of the 1-trees of `G` with distinguished root `root`. -/
def oneTreeVertices (G : SimpleGraph V) (root : V) : Set (G.edgeSet → ℝ) :=
  {x | ∃ H : G.Subgraph, H.IsOneTree root ∧ x = G.subgraphIncidenceVector ℝ H}

/-- A vector belongs to `G.oneTreeVertices root` exactly when it is the incidence vector of a
1-tree of `G` with distinguished root `root`. -/
theorem mem_oneTreeVertices_iff
    (G : SimpleGraph V)
    (root : V)
    {x : G.edgeSet → ℝ} :
    x ∈ G.oneTreeVertices root ↔
      ∃ H : G.Subgraph, H.IsOneTree root ∧ x = G.subgraphIncidenceVector ℝ H :=
  Iff.rfl

/-- The incidence vector of a 1-tree belongs to `G.oneTreeVertices root`. -/
theorem subgraphIncidenceVector_mem_oneTreeVertices
    {H : G.Subgraph}
    (hH : H.IsOneTree root) :
    G.subgraphIncidenceVector ℝ H ∈ G.oneTreeVertices root :=
  (G.mem_oneTreeVertices_iff root).2 ⟨H, hH, rfl⟩

/-- The 1-tree polytope of `G` with distinguished root `root`, defined as the convex hull of the
incidence vectors of the 1-trees of `G`. -/
def oneTreePolytope (G : SimpleGraph V) (root : V) : Set (G.edgeSet → ℝ) :=
  convexHull ℝ (G.oneTreeVertices root)

/-- The 1-tree polytope is the convex hull of the 1-tree incidence vectors. -/
theorem oneTreePolytope_eq_convexHull :
    G.oneTreePolytope root = convexHull ℝ (G.oneTreeVertices root) :=
  rfl

/-- The linear relaxation of the textbook 1-tree system `(8.7)`: box constraints, the root-degree
equation, the total-edge equation, and all subtour inequalities on subsets avoiding the root. -/
def oneTreeLinearRelaxation (G : SimpleGraph V) (root : V) : Set (G.edgeSet → ℝ) :=
  {x | (∀ e, 0 ≤ x e ∧ x e ≤ 1) ∧
      (δ[G] ({root} : Set V)).sum x = (2 : ℝ) ∧
      (∑ e, x e) = (Fintype.card V : ℝ) ∧
      ∀ S : Finset V, S.Nonempty → root ∉ S →
        (E[G] (S : Set V)).sum x ≤ (S.card - 1 : ℝ)}

/-- Membership in `G.oneTreeLinearRelaxation root` is exactly the conjunction of the box
constraints, the root-degree equation, the total-edge equation, and the subtour inequalities on
subsets that avoid the distinguished root. -/
theorem mem_oneTreeLinearRelaxation_iff
    (G : SimpleGraph V)
    (root : V)
    {x : G.edgeSet → ℝ} :
    x ∈ G.oneTreeLinearRelaxation root ↔
      (∀ e, 0 ≤ x e ∧ x e ≤ 1) ∧
      (δ[G] ({root} : Set V)).sum x = (2 : ℝ) ∧
      (∑ e, x e) = (Fintype.card V : ℝ) ∧
      ∀ S : Finset V, S.Nonempty → root ∉ S →
        (E[G] (S : Set V)).sum x ≤ (S.card - 1 : ℝ) := Iff.rfl

/-- Helper for Proposition 8.9: an ambient edge lies in the induced deleted-root edge block
exactly when neither endpoint is the distinguished root. -/
private lemma mem_deletedRootInducedEdgeFinset_iff
    (e : G.edgeSet) :
    e ∈ E[G] ({root}ᶜ : Set V) ↔ e.1.out.1 ≠ root ∧ e.1.out.2 ≠ root := by
  -- Rewrite induced-edge membership through the canonical endpoint presentation of `e`.
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    have he : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
      simpa [e.1.out_eq] using e.prop
    exact (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 he
  rw [mem_inducedEdgeFinset_iff, ← e.1.out_eq, SimpleGraph.Subgraph.mem_edgeSet]
  simp [SimpleGraph.Subgraph.induce, hadj]

/-- Helper for Proposition 8.9: an ambient edge lies in the root cut exactly when one canonical
endpoint is the distinguished root and the other is not. -/
private lemma mem_rootCutEdgeFinset_iff
    (e : G.edgeSet) :
    e ∈ δ[G] ({root} : Set V) ↔
      (e.1.out.1 = root ∧ e.1.out.2 ≠ root) ∨
        (e.1.out.2 = root ∧ e.1.out.1 ≠ root) := by
  constructor
  · intro he
    rcases (mem_cutEdgeFinset_iff (G := G) (S := ({root} : Set V)) (e := e)).1 he with
      ⟨u, hu, v, hv, huv⟩
    -- Normalize the cut-edge witness to the concrete endpoints of `e`.
    rw [← e.1.out_eq] at huv
    rw [Sym2.eq_iff] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨by simpa using hu, by simpa using hv⟩
    · exact Or.inr ⟨by simpa using hu, by simpa using hv⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact (mem_cutEdgeFinset_iff (G := G) (S := ({root} : Set V)) (e := e)).2
        ⟨e.1.out.1, by simpa [h₁], e.1.out.2, by simpa [h₂], e.1.out_eq⟩
    · exact (mem_cutEdgeFinset_iff (G := G) (S := ({root} : Set V)) (e := e)).2
        ⟨e.1.out.2, by simpa [h₁], e.1.out.1, by simpa [h₂],
          Sym2.eq_swap.trans e.1.out_eq⟩

/-- Helper for Proposition 8.9: every ambient edge belongs to exactly one of the root-cut and
deleted-root edge blocks. -/
private lemma mem_deletedRootInducedEdgeFinset_iff_not_mem_rootCut
    (e : G.edgeSet) :
    e ∈ E[G] ({root}ᶜ : Set V) ↔ e ∉ δ[G] ({root} : Set V) := by
  -- An edge in a simple graph has two distinct endpoints, so the only alternative to lying in the
  -- root cut is to avoid the root entirely.
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    have he : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
      simpa [e.1.out_eq] using e.prop
    exact (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 he
  have hneq : e.1.out.1 ≠ e.1.out.2 := G.ne_of_adj hadj
  constructor
  · intro he hcut
    rcases (mem_deletedRootInducedEdgeFinset_iff (G := G) (root := root) e).1 he with ⟨h₁, h₂⟩
    rcases (mem_rootCutEdgeFinset_iff (G := G) (root := root) e).1 hcut with
      (⟨hroot, _⟩ | ⟨hroot, _⟩)
    · exact h₁ hroot
    · exact h₂ hroot
  · intro hnot
    by_cases h₁ : e.1.out.1 = root
    · have h₂ : e.1.out.2 ≠ root := by
        intro h₂
        exact hneq (h₁.trans h₂.symm)
      exact False.elim (hnot ((mem_rootCutEdgeFinset_iff (G := G) (root := root) e).2
        (Or.inl ⟨h₁, h₂⟩)))
    · by_cases h₂ : e.1.out.2 = root
      · exact False.elim (hnot ((mem_rootCutEdgeFinset_iff (G := G) (root := root) e).2
          (Or.inr ⟨h₂, h₁⟩)))
      · exact (mem_deletedRootInducedEdgeFinset_iff (G := G) (root := root) e).2 ⟨h₁, h₂⟩

/-- Helper for Proposition 8.9: on a singleton, cut-edge membership is equivalent to the edge
containing the distinguished root. -/
private lemma mem_rootCutEdgeFinset_iff_mem_root
    (e : G.edgeSet) :
    e ∈ δ[G] ({root} : Set V) ↔ root ∈ (e : Sym2 V) := by
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    have he : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
      simpa [e.1.out_eq] using e.prop
    exact (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 he
  have hneq : e.1.out.1 ≠ e.1.out.2 := G.ne_of_adj hadj
  constructor
  · intro hcut
    rcases (mem_rootCutEdgeFinset_iff (G := G) (root := root) e).1 hcut with
      (⟨h₁, _⟩ | ⟨h₂, _⟩)
    · rw [← e.1.out_eq]
      exact Sym2.mem_iff.2 (Or.inl h₁.symm)
    · rw [← e.1.out_eq]
      exact Sym2.mem_iff.2 (Or.inr h₂.symm)
  · intro hroot
    rw [← e.1.out_eq] at hroot
    rcases Sym2.mem_iff.1 hroot with h₁ | h₂
    · exact (mem_rootCutEdgeFinset_iff (G := G) (root := root) e).2
        (Or.inl ⟨h₁.symm, by
          intro h₂'
          exact hneq (h₁.symm.trans h₂'.symm)⟩)
    · exact (mem_rootCutEdgeFinset_iff (G := G) (root := root) e).2
        (Or.inr ⟨h₂.symm, by
          intro h₁'
          exact hneq (h₁'.trans h₂)⟩)

/-- Helper for Proposition 8.9: the ambient total edge sum splits into the root-cut block and the
deleted-root block. -/
theorem sumEdges_eq_rootCut_sum_add_deletedRoot_sum
    (x : G.edgeSet → ℝ) :
    (∑ e : G.edgeSet, x e) =
      (δ[G] ({root} : Set V)).sum x + (E[G] ({root}ᶜ : Set V)).sum x := by
  -- Split the universal edge sum by membership in the root cut, then rewrite the complementary
  -- filter as the deleted-root edge block.
  let p : G.edgeSet → Prop :=
    fun e ↦ ∃ u ∈ ({root} : Set V), ∃ v ∉ ({root} : Set V), s(u, v) = (e : Sym2 V)
  have hrootFilter :
      Finset.univ.filter p =
        δ[G] ({root} : Set V) := by
    -- This is the defining filter for the root cut.
    rfl
  have hdeletedFilter :
      Finset.univ.filter (fun e : G.edgeSet ↦ ¬ p e) =
        E[G] ({root}ᶜ : Set V) := by
    -- The complement of the root cut is exactly the deleted-root induced edge block.
    ext e
    simp [p, cutEdgeFinset,
      mem_deletedRootInducedEdgeFinset_iff_not_mem_rootCut (G := G) (root := root) e]
  calc
    (∑ e : G.edgeSet, x e) =
        (Finset.univ.filter p).sum x +
          (Finset.univ.filter (fun e : G.edgeSet ↦ ¬ p e)).sum x := by
            simpa using
              (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
                (p := p) x).symm
    _ = (δ[G] ({root} : Set V)).sum x +
          (Finset.univ.filter (fun e : G.edgeSet ↦ ¬ p e)).sum x := by
            rw [hrootFilter]
    _ = (δ[G] ({root} : Set V)).sum x + (E[G] ({root}ᶜ : Set V)).sum x := by
            rw [hdeletedFilter]

/-- Helper for Proposition 8.9: the canonical embedding of deleted-root subtype vertices into the
ambient vertex type. -/
private abbrev deletedRootVertexEmbedding :
    {v : V // v ≠ root} ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- Helper for Proposition 8.9: mapping a deleted-root subtype finset to ambient vertices does not
introduce the distinguished root. -/
private theorem root_not_mem_map_subtypeVal
    (S : Finset {v : V // v ≠ root}) :
    root ∉ S.map (deletedRootVertexEmbedding (root := root)) := by
  -- Every subtype vertex already carries the certificate that it differs from `root`.
  intro hroot
  rcases Finset.mem_map.1 hroot with ⟨v, hv, hvroot⟩
  exact v.2 hvroot

/-- Helper for Proposition 8.9: forgetting the deleted-root subtype on a finite vertex set
preserves cardinality. -/
private theorem card_map_subtypeVal
    (S : Finset {v : V // v ≠ root}) :
    (S.map (deletedRootVertexEmbedding (root := root))).card = S.card := by
  -- The vertex inclusion `{v // v ≠ root} ↪ V` is injective, so the finset map is cardinality
  -- preserving.
  simpa using Finset.card_map (deletedRootVertexEmbedding (root := root)) S

/-- Helper for Proposition 8.9: the deleted-root ambient edge block of a feasible relaxation point
has total sum `|V| - 2`. -/
private theorem deletedRootSum_eq_card_sub_two_of_mem_oneTreeLinearRelaxation
    {x : G.edgeSet → ℝ}
    (hx : x ∈ G.oneTreeLinearRelaxation root) :
    (E[G] ({root}ᶜ : Set V)).sum x = (Fintype.card V - 2 : ℝ) := by
  rcases (G.mem_oneTreeLinearRelaxation_iff root).1 hx with
    ⟨_, hx_root, hx_total, _⟩
  -- Split the ambient total sum into the root-cut and deleted-root blocks and evaluate the
  -- root-cut block by the defining degree equation.
  have hsplit :=
    sumEdges_eq_rootCut_sum_add_deletedRoot_sum (G := G) (root := root) (x := x)
  nlinarith [hsplit, hx_root, hx_total]

/-- Helper for Proposition 8.9: every root-free ambient vertex subset of a feasible relaxation
point satisfies the deleted-root subtour inequality after forgetting the subtype coordinates. -/
private theorem deletedRootSubsetInequality_of_mem_oneTreeLinearRelaxation
    {x : G.edgeSet → ℝ}
    (hx : x ∈ G.oneTreeLinearRelaxation root)
    (S : Finset {v : V // v ≠ root})
    (hS : S.Nonempty) :
    (E[G] ((S.map (deletedRootVertexEmbedding (root := root)) : Finset V) : Set V)).sum x ≤
      (S.card - 1 : ℝ) := by
  rcases (G.mem_oneTreeLinearRelaxation_iff root).1 hx with
    ⟨_, _, _, hx_subtour⟩
  let S' : Finset V := S.map (deletedRootVertexEmbedding (root := root))
  have hS' : S'.Nonempty := by
    -- Mapping along the injective subtype inclusion preserves positive cardinality.
    have hcardS' : 0 < S'.card := by
      rw [card_map_subtypeVal (root := root) S]
      exact Finset.card_pos.mpr hS
    exact Finset.card_pos.mp hcardS'
  have hrootS' : root ∉ S' := by
    -- The mapped ambient vertex set still avoids `root`.
    simpa [S'] using root_not_mem_map_subtypeVal (root := root) S
  have hineq := hx_subtour S' hS' hrootS'
  -- Finish by rewriting the mapped ambient vertex count back to the subtype cardinality.
  rw [show (S.card - 1 : ℝ) = (S'.card - 1 : ℝ) by
    simp [S', card_map_subtypeVal (root := root) S]]
  exact hineq

/-- Helper for Proposition 8.9: an induced-edge membership test can be read directly on the
canonical endpoints of the ambient edge. -/
private theorem mem_inducedEdgeFinset_endpoints_iff
    {W : Type*} {H : SimpleGraph W} [Fintype W] {S : Set W} {e : H.edgeSet} :
    e ∈ E[H] S ↔ e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S := by
  -- Rewrite induced-edge membership through the concrete endpoint presentation of `e`.
  have hadj : H.Adj e.1.out.1 e.1.out.2 := by
    have he : s(e.1.out.1, e.1.out.2) ∈ H.edgeSet := by
      simpa [e.1.out_eq] using e.prop
    exact (SimpleGraph.mem_edgeSet (G := H) (v := e.1.out.1) (w := e.1.out.2)).1 he
  rw [mem_inducedEdgeFinset_iff, ← e.1.out_eq, SimpleGraph.Subgraph.mem_edgeSet]
  simp [SimpleGraph.Subgraph.induce, hadj]

/-- Helper for Proposition 8.9: the deleted-root induced graph used for the Chapter 4.25
transport. -/
private abbrev deletedRootGraph : SimpleGraph {v : V // v ≠ root} :=
  G.induce ({root}ᶜ : Set V)

/-- Helper for Proposition 8.9: every deleted-root induced edge has a canonical ambient edge
coordinate. -/
private def deletedRootEdgeEmbedding :
    (deletedRootGraph (G := G) (root := root)).edgeSet ↪ G.edgeSet :=
  (SimpleGraph.Embedding.induce ({root}ᶜ : Set V)).mapEdgeSet

/-- Helper for Proposition 8.9: the ambient edge obtained from a deleted-root induced edge still
avoids the distinguished root. -/
private lemma deletedRootEdgeEmbedding_avoids_root
    (e : (deletedRootGraph (G := G) (root := root)).edgeSet) :
    root ∉ ((deletedRootEdgeEmbedding (G := G) (root := root) e : G.edgeSet) : Sym2 V) := by
  intro hroot
  rcases Sym2.mem_map.mp hroot with ⟨w, hw, hwroot⟩
  exact w.2 (by simpa using hwroot)

/-- Helper for Proposition 8.9: an ambient edge avoiding the distinguished root can be reread as
an edge of the deleted-root induced graph. -/
private noncomputable def ambientEdgeAvoidingRootToDeletedRootEdge :
    {e : G.edgeSet // root ∉ (e : Sym2 V)} →
      (deletedRootGraph (G := G) (root := root)).edgeSet := fun e ↦ by
  let a : {x : V // x ≠ root} := ⟨e.1.1.out.1, by
    intro ha
    have hroot : root ∈ (e.1 : Sym2 V) := by
      simpa [ha] using Sym2.out_fst_mem e.1.1
    exact e.2 hroot⟩
  let b : {x : V // x ≠ root} := ⟨e.1.1.out.2, by
    intro hb
    have hroot : root ∈ (e.1 : Sym2 V) := by
      simpa [hb] using Sym2.out_snd_mem e.1.1
    exact e.2 hroot⟩
  refine ⟨s(a, b), ?_⟩
  -- The same unordered pair is an edge in the induced deleted-root graph.
  have hab : G.Adj e.1.1.out.1 e.1.1.out.2 := by
    exact G.mem_edgeSet.mp (by simpa [e.1.1.out_eq] using e.1.2)
  exact ((deletedRootGraph (G := G) (root := root)).mem_edgeSet).2 <| by
    simpa [deletedRootGraph, SimpleGraph.induce_adj, a, b] using hab

/-- Helper for Proposition 8.9: converting an avoiding ambient edge to the deleted-root owner and
embedding it back recovers the original ambient edge. -/
private lemma deletedRootEdgeEmbedding_ambientEdgeAvoidingRootToDeletedRootEdge
    (e : {f : G.edgeSet // root ∉ (f : Sym2 V)}) :
    deletedRootEdgeEmbedding (G := G) (root := root)
        (ambientEdgeAvoidingRootToDeletedRootEdge (G := G) (root := root) e) = e.1 := by
  apply Subtype.ext
  -- Rebuilding the deleted-root edge from the concrete ambient endpoints preserves the edge pair.
  change s(e.1.1.out.1, e.1.1.out.2) = e.1.1
  exact e.1.1.out_eq

/-- Helper for Proposition 8.9: deleting `root` identifies the induced graph edge set with the
ambient edges that avoid `root`. -/
private noncomputable def deletedRootEdgeEquivAvoidingRoot :
    (deletedRootGraph (G := G) (root := root)).edgeSet ≃
      {e : G.edgeSet // root ∉ (e : Sym2 V)} where
  toFun e :=
    ⟨deletedRootEdgeEmbedding (G := G) (root := root) e,
      deletedRootEdgeEmbedding_avoids_root (G := G) (root := root) e⟩
  invFun := ambientEdgeAvoidingRootToDeletedRootEdge (G := G) (root := root)
  left_inv := by
    intro e
    apply (deletedRootEdgeEmbedding (G := G) (root := root)).injective
    simpa using
      deletedRootEdgeEmbedding_ambientEdgeAvoidingRootToDeletedRootEdge (G := G) (root := root)
        ⟨deletedRootEdgeEmbedding (G := G) (root := root) e,
          deletedRootEdgeEmbedding_avoids_root (G := G) (root := root) e⟩
  right_inv := by
    intro e
    apply Subtype.ext
    simpa using
      deletedRootEdgeEmbedding_ambientEdgeAvoidingRootToDeletedRootEdge (G := G) (root := root) e

/-- Helper for Proposition 8.9: restrict an ambient edge vector to the deleted-root induced graph
coordinates. -/
private def deletedRootRestriction
    (x : G.edgeSet → ℝ) :
    (deletedRootGraph (G := G) (root := root)).edgeSet → ℝ :=
  fun e ↦ x (deletedRootEdgeEmbedding (G := G) (root := root) e)

/-- Helper for Proposition 8.9: the ambient image of a deleted-root edge is the same unordered
pair of endpoints, now viewed in the ambient vertex type. -/
private lemma coe_deletedRootEdgeEmbedding_eq_pair
    (e : (deletedRootGraph (G := G) (root := root)).edgeSet) :
    ((deletedRootEdgeEmbedding (G := G) (root := root) e : G.edgeSet) : Sym2 V) =
      s((e.1.out.1 : V), (e.1.out.2 : V)) := by
  -- Normalize the map-edge embedding to the concrete endpoint pair of the deleted-root edge.
  calc
    ((deletedRootEdgeEmbedding (G := G) (root := root) e : G.edgeSet) : Sym2 V) =
        Sym2.map (fun v : {v : V // v ≠ root} ↦ (v : V)) (e : Sym2 {v : V // v ≠ root}) := by
          rfl
    _ = Sym2.map (fun v : {v : V // v ≠ root} ↦ (v : V)) (s(e.1.out.1, e.1.out.2)) := by
          exact congrArg
            (fun z : Sym2 {v : V // v ≠ root} ↦
              Sym2.map (fun v : {v : V // v ≠ root} ↦ (v : V)) z)
            e.1.out_eq.symm
    _ = s((e.1.out.1 : V), (e.1.out.2 : V)) := by
          rw [Sym2.map_mk]

/-- Helper for Proposition 8.9: a deleted-root induced edge belongs to the subtype owner exactly
when its ambient image belongs to the corresponding mapped ambient induced edge block. -/
private theorem mem_deletedRootInducedEdgeFinset_iff_mem_mappedAmbientInducedEdgeFinset
    (S : Finset {v : V // v ≠ root})
    (e : (deletedRootGraph (G := G) (root := root)).edgeSet) :
    e ∈ (deletedRootGraph (G := G) (root := root)).inducedEdgeFinset (S : Set _) ↔
      deletedRootEdgeEmbedding (G := G) (root := root) e ∈
        E[G] (((S.map (deletedRootVertexEmbedding (root := root))) : Finset V) : Set V) := by
  have hadj : G.Adj (e.1.out.1 : V) (e.1.out.2 : V) := by
    -- Read the deleted-root edge as an ambient adjacent pair once and reuse that normalization.
    have heEdge :
        s(e.1.out.1, e.1.out.2) ∈
          (deletedRootGraph (G := G) (root := root)).edgeSet := by
      simpa [e.1.out_eq] using e.prop
    have hDeletedAdj :
        (deletedRootGraph (G := G) (root := root)).Adj e.1.out.1 e.1.out.2 :=
      ((deletedRootGraph (G := G) (root := root)).mem_edgeSet).1 heEdge
    simpa [deletedRootGraph, SimpleGraph.induce_adj] using hDeletedAdj
  -- Rewrite both induced-edge owners to the same endpoint pair in ambient coordinates.
  rw [mem_inducedEdgeFinset_endpoints_iff
    (H := deletedRootGraph (G := G) (root := root)) (S := (S : Set _)) (e := e)]
  rw [SimpleGraph.mem_inducedEdgeFinset_iff,
    coe_deletedRootEdgeEmbedding_eq_pair (G := G) (root := root) e,
    SimpleGraph.Subgraph.mem_edgeSet]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_, hadj⟩
    · show ((e.1.out.1 : V) ∈
        (((S.map (deletedRootVertexEmbedding (root := root))) : Finset V) : Set V))
      exact Finset.mem_coe.2 <|
        Finset.mem_map.2 ⟨e.1.out.1, by simpa [Finset.mem_coe] using h₁, rfl⟩
    · show ((e.1.out.2 : V) ∈
        (((S.map (deletedRootVertexEmbedding (root := root))) : Finset V) : Set V))
      exact Finset.mem_coe.2 <|
        Finset.mem_map.2 ⟨e.1.out.2, by simpa [Finset.mem_coe] using h₂, rfl⟩
  · rintro ⟨h₁, h₂, _⟩
    refine ⟨?_, ?_⟩
    · have h₁' :
          (e.1.out.1 : V) ∈ S.map (deletedRootVertexEmbedding (root := root)) :=
        Finset.mem_coe.1 h₁
      rcases Finset.mem_map.1 h₁' with ⟨v, hv, hvEq⟩
      have hvSub : v = e.1.out.1 := Subtype.ext hvEq
      simpa [Finset.mem_coe, hvSub] using hv
    · have h₂' :
          (e.1.out.2 : V) ∈ S.map (deletedRootVertexEmbedding (root := root)) :=
        Finset.mem_coe.1 h₂
      rcases Finset.mem_map.1 h₂' with ⟨v, hv, hvEq⟩
      have hvSub : v = e.1.out.2 := Subtype.ext hvEq
      simpa [Finset.mem_coe, hvSub] using hv

/-- Helper for Proposition 8.9: summing the deleted-root restriction on a subtype-induced edge
block agrees with summing the ambient vector on the corresponding mapped ambient induced edge
block. -/
private theorem deletedRootInducedSum_eq_mappedAmbientSum
    (x : G.edgeSet → ℝ)
    (S : Finset {v : V // v ≠ root}) :
    ((deletedRootGraph (G := G) (root := root)).inducedEdgeFinset (S : Set _)).sum
        (deletedRootRestriction (G := G) (root := root) x) =
      (E[G] (((S.map (deletedRootVertexEmbedding (root := root))) : Finset V) : Set V)).sum x := by
  have hmap :
      ((deletedRootGraph (G := G) (root := root)).inducedEdgeFinset (S : Set _)).map
          (deletedRootEdgeEmbedding (G := G) (root := root)) =
        E[G] (((S.map (deletedRootVertexEmbedding (root := root))) : Finset V) : Set V) := by
    -- Reindex the deleted-root induced edges by the canonical ambient embedding.
    ext e
    constructor
    · intro he
      rcases Finset.mem_map.1 he with ⟨e', he', rfl⟩
      exact
        (mem_deletedRootInducedEdgeFinset_iff_mem_mappedAmbientInducedEdgeFinset
          (G := G) (root := root) S e').1 he'
    · intro he
      have hEnds :
          e.1.out.1 ∈ (S.map (deletedRootVertexEmbedding (root := root))) ∧
            e.1.out.2 ∈ (S.map (deletedRootVertexEmbedding (root := root))) := by
        simpa [Finset.mem_coe] using
          (mem_inducedEdgeFinset_endpoints_iff
            (H := G)
            (S := ((((S.map (deletedRootVertexEmbedding (root := root))) : Finset V) : Set V)))
            (e := e)).1 he
      have hAvoid : root ∉ (e : Sym2 V) := by
        -- Any edge inside the mapped deleted-root vertex set avoids the distinguished root.
        intro hroot
        rw [← e.1.out_eq] at hroot
        rcases Sym2.mem_iff.1 hroot with hfst | hsnd
        · rcases Finset.mem_map.1 hEnds.1 with ⟨v, _, hvEq⟩
          exact v.2 (hvEq.trans hfst.symm)
        · rcases Finset.mem_map.1 hEnds.2 with ⟨v, _, hvEq⟩
          exact v.2 (hvEq.trans hsnd.symm)
      refine Finset.mem_map.2 ⟨
        ambientEdgeAvoidingRootToDeletedRootEdge (G := G) (root := root) ⟨e, hAvoid⟩,
        ?_, ?_⟩
      · -- Pull the ambient induced-edge membership back through the canonical inverse map.
        exact
          (mem_deletedRootInducedEdgeFinset_iff_mem_mappedAmbientInducedEdgeFinset
            (G := G) (root := root) S
            (ambientEdgeAvoidingRootToDeletedRootEdge (G := G) (root := root) ⟨e, hAvoid⟩)).2
            (by
              rw [deletedRootEdgeEmbedding_ambientEdgeAvoidingRootToDeletedRootEdge
                (G := G) (root := root) ⟨e, hAvoid⟩]
              exact he)
      · -- The forward/backward edge conversion is definitionally the identity on ambient edges.
        exact
          deletedRootEdgeEmbedding_ambientEdgeAvoidingRootToDeletedRootEdge
            (G := G) (root := root) ⟨e, hAvoid⟩
  -- Rewrite the left sum as the sum over the mapped ambient finset, then substitute the finset
  -- equality proved above.
  calc
    ((deletedRootGraph (G := G) (root := root)).inducedEdgeFinset (S : Set _)).sum
        (deletedRootRestriction (G := G) (root := root) x) =
      (((deletedRootGraph (G := G) (root := root)).inducedEdgeFinset (S : Set _)).map
        (deletedRootEdgeEmbedding (G := G) (root := root))).sum x := by
          simpa [deletedRootRestriction] using
            (Finset.sum_map
              (f := x)
              (deletedRootEdgeEmbedding (G := G) (root := root))
              ((deletedRootGraph (G := G) (root := root)).inducedEdgeFinset (S : Set _))).symm
    _ = (E[G] (((S.map (deletedRootVertexEmbedding (root := root))) : Finset V) : Set V)).sum x := by
          rw [hmap]

/-- Helper for Proposition 8.9: the deleted-root slice of a feasible relaxation point is a point
of the spanning-tree polytope on the induced deleted-root graph. -/
private theorem deletedRootRestriction_mem_spanningTreePolytope
    {x : G.edgeSet → ℝ}
    (hx : x ∈ G.oneTreeLinearRelaxation root) :
    deletedRootRestriction (G := G) (root := root) x ∈
      (deletedRootGraph (G := G) (root := root)).spanningTreePolytope := by
  let G0 := deletedRootGraph (G := G) (root := root)
  rw [spanningTreePolytope_eq_spanningTreeConstraintSet G0]
  refine (mem_spanningTreeConstraintSet_iff).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · intro S hS hS_ne_univ
    -- Transport the deleted-root induced-edge inequality to the ambient root-free coordinates.
    calc
      Finset.sum (G0.inducedEdgeFinset (S : Set _))
          (fun e ↦ deletedRootRestriction (G := G) (root := root) x e) =
          (E[G] (((S.map (deletedRootVertexEmbedding (root := root))) : Finset V) : Set V)).sum x := by
            exact deletedRootInducedSum_eq_mappedAmbientSum (G := G) (root := root) x S
      _ ≤ (S.card - 1 : ℝ) := by
            exact deletedRootSubsetInequality_of_mem_oneTreeLinearRelaxation
              (G := G) (root := root) hx S hS
  · -- Route correction: normalize the total deleted-root sum through the direct transport lemma,
    -- then rewrite the owner cardinality to the ambient `|V| - 2` count once.
    have hUnivEdges :
        G0.inducedEdgeFinset ((Finset.univ : Finset {v : V // v ≠ root}) : Set _) = Finset.univ := by
      ext e
      constructor
      · intro he
        simp
      · intro he
        rw [SimpleGraph.inducedEdgeFinset, Finset.mem_filter]
        constructor
        · simp
        · have hadj : G0.Adj e.1.out.1 e.1.out.2 := by
            have heEdge : s(e.1.out.1, e.1.out.2) ∈ G0.edgeSet := by
              simpa [e.1.out_eq] using e.prop
            exact (SimpleGraph.mem_edgeSet (G := G0) (v := e.1.out.1) (w := e.1.out.2)).1 heEdge
          rw [← e.1.out_eq, SimpleGraph.Subgraph.mem_edgeSet]
          simp [SimpleGraph.Subgraph.induce_adj, hadj]
    have hMappedUniv :
        ((((Finset.univ : Finset {v : V // v ≠ root}).map
          (deletedRootVertexEmbedding (root := root))) : Finset V) : Set V) = ({root}ᶜ : Set V) := by
      ext v
      simp [deletedRootVertexEmbedding]
    calc
      Finset.sum Finset.univ (fun e ↦ deletedRootRestriction (G := G) (root := root) x e) =
          Finset.sum (G0.inducedEdgeFinset ((Finset.univ : Finset {v : V // v ≠ root}) : Set _))
            (fun e ↦ deletedRootRestriction (G := G) (root := root) x e) := by
              rw [hUnivEdges]
      _ =
          (E[G]
            ((((Finset.univ : Finset {v : V // v ≠ root}).map
              (deletedRootVertexEmbedding (root := root))) : Finset V) : Set V)).sum x := by
                exact deletedRootInducedSum_eq_mappedAmbientSum
                  (G := G) (root := root) x Finset.univ
      _ = (E[G] ({root}ᶜ : Set V)).sum x := by
            rw [hMappedUniv]
      _ = (Fintype.card V - 2 : ℝ) := by
            exact deletedRootSum_eq_card_sub_two_of_mem_oneTreeLinearRelaxation
              (G := G) (root := root) hx
      _ = (Fintype.card {v : V // v ≠ root} - 1 : ℝ) := by
            have hcardSubtype : Fintype.card {v : V // v ≠ root} = Fintype.card V - 1 := by
              simpa using Set.card_ne_eq (α := V) root
            have hcardV_pos : 1 ≤ Fintype.card V := by
              exact Fintype.card_pos_iff.mpr ⟨root⟩
            have hcardSubtypeReal :
                (Fintype.card {v : V // v ≠ root} : ℝ) = (Fintype.card V : ℝ) - 1 := by
              calc
                (Fintype.card {v : V // v ≠ root} : ℝ) = ((Fintype.card V - 1 : ℕ) : ℝ) := by
                    exact congrArg (fun n : ℕ ↦ (n : ℝ)) hcardSubtype
                _ = (Fintype.card V : ℝ) - 1 := by
                    rw [Nat.cast_sub hcardV_pos]
                    norm_num
            nlinarith
  · intro e
    -- The deleted-root restriction inherits coordinatewise nonnegativity from the ambient box
    -- constraints on the embedded edge coordinate.
    exact ((G.mem_oneTreeLinearRelaxation_iff root).1 hx).1
      (deletedRootEdgeEmbedding (G := G) (root := root) e) |>.1

/-- Helper for Proposition 8.9: the defining inequalities of `G.oneTreeLinearRelaxation root` are
preserved under convex combinations. -/
theorem convex_oneTreeLinearRelaxation :
    Convex ℝ (G.oneTreeLinearRelaxation root) := by
  intro x hx y hy a b ha hb hab
  rcases (G.mem_oneTreeLinearRelaxation_iff root).1 hx with
    ⟨hx_box, hx_root, hx_total, hx_subtour⟩
  rcases (G.mem_oneTreeLinearRelaxation_iff root).1 hy with
    ⟨hy_box, hy_root, hy_total, hy_subtour⟩
  refine (G.mem_oneTreeLinearRelaxation_iff root).2 ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e
    rcases hx_box e with ⟨hx_nonneg, hx_le_one⟩
    rcases hy_box e with ⟨hy_nonneg, hy_le_one⟩
    constructor
    · -- Coordinatewise lower bounds are preserved by nonnegative affine combinations.
      exact add_nonneg (mul_nonneg ha hx_nonneg) (mul_nonneg hb hy_nonneg)
    · -- Coordinatewise upper bounds use the normalization `a + b = 1`.
      have hxScaled : a * x e ≤ a * 1 := mul_le_mul_of_nonneg_left hx_le_one ha
      have hyScaled : b * y e ≤ b * 1 := mul_le_mul_of_nonneg_left hy_le_one hb
      have hupper : a * x e + b * y e ≤ a + b := by
        simpa using add_le_add hxScaled hyScaled
      calc
        (a • x + b • y) e = a * x e + b * y e := by
          simp [Pi.add_apply, Pi.smul_apply]
        _ ≤ a + b := hupper
        _ = (1 : ℝ) := hab
  · -- The root-degree equation is affine-linear in the edge coordinates.
    calc
      (δ[G] ({root} : Set V)).sum (a • x + b • y)
          = a * (δ[G] ({root} : Set V)).sum x +
              b * (δ[G] ({root} : Set V)).sum y := by
            simp [Pi.add_apply, Pi.smul_apply, Finset.mul_sum, Finset.sum_add_distrib]
      _ = a * 2 + b * 2 := by rw [hx_root, hy_root]
      _ = (2 : ℝ) := by nlinarith
  · -- The total-edge equation is affine-linear for the same reason.
    calc
      (∑ e, (a • x + b • y) e) = a * (∑ e, x e) + b * (∑ e, y e) := by
        simp [Pi.add_apply, Pi.smul_apply, Finset.mul_sum, Finset.sum_add_distrib]
      _ = a * (Fintype.card V : ℝ) + b * (Fintype.card V : ℝ) := by
        rw [hx_total, hy_total]
      _ = (Fintype.card V : ℝ) := by nlinarith
  · intro S hS hrootS
    have hxS := hx_subtour S hS hrootS
    have hyS := hy_subtour S hS hrootS
    -- Each deleted-root subtour inequality is preserved coordinatewise under the same weights.
    calc
      (E[G] (S : Set V)).sum (a • x + b • y)
          = a * (E[G] (S : Set V)).sum x +
              b * (E[G] (S : Set V)).sum y := by
            simp [Pi.add_apply, Pi.smul_apply, Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ a * (S.card - 1 : ℝ) + b * (S.card - 1 : ℝ) := by
            gcongr
      _ = (S.card - 1 : ℝ) := by
            nlinarith

/-- Helper for Proposition 8.9: keep only the root-cut coordinates of an ambient edge vector. -/
private def rootCutSlice
    (x : G.edgeSet → ℝ) :
    G.edgeSet → ℝ :=
  fun e ↦ if e ∈ δ[G] ({root} : Set V) then x e else 0

/-- Helper for Proposition 8.9: keep only the deleted-root coordinates of an ambient edge vector.
-/
private def deletedRootSlice
    (x : G.edgeSet → ℝ) :
    G.edgeSet → ℝ :=
  fun e ↦ if e ∈ E[G] ({root}ᶜ : Set V) then x e else 0

/-- Helper for Proposition 8.9: zero-extend a deleted-root edge vector back to the ambient edge
coordinates of `G`. -/
private def deletedRootLift
    (y : (deletedRootGraph (G := G) (root := root)).edgeSet → ℝ) :
    G.edgeSet → ℝ :=
  fun e ↦
    if hAvoid : root ∉ (e : Sym2 V) then
      y (ambientEdgeAvoidingRootToDeletedRootEdge (G := G) (root := root) ⟨e, hAvoid⟩)
    else
      0

/-- Helper for Proposition 8.9: converting an embedded deleted-root edge back to the deleted-root
owner recovers the original edge. -/
private lemma ambientEdgeAvoidingRootToDeletedRootEdge_embedding
    (e : (deletedRootGraph (G := G) (root := root)).edgeSet) :
    ambientEdgeAvoidingRootToDeletedRootEdge (G := G) (root := root)
        ⟨deletedRootEdgeEmbedding (G := G) (root := root) e,
          deletedRootEdgeEmbedding_avoids_root (G := G) (root := root) e⟩ = e := by
  -- The ambient/deleted-root edge equivalence is already normalized by the embedding-cancellation
  -- lemma; apply injectivity once to avoid repeating the transport later.
  apply (deletedRootEdgeEmbedding (G := G) (root := root)).injective
  simpa using
    deletedRootEdgeEmbedding_ambientEdgeAvoidingRootToDeletedRootEdge
      (G := G) (root := root)
      ⟨deletedRootEdgeEmbedding (G := G) (root := root) e,
        deletedRootEdgeEmbedding_avoids_root (G := G) (root := root) e⟩

/-- Helper for Proposition 8.9: the deleted-root lift reads an embedded deleted-root edge exactly
as its original deleted-root coordinate. -/
private lemma deletedRootLift_apply_embedding
    (y : (deletedRootGraph (G := G) (root := root)).edgeSet → ℝ)
    (e : (deletedRootGraph (G := G) (root := root)).edgeSet) :
    deletedRootLift (G := G) (root := root) y
        (deletedRootEdgeEmbedding (G := G) (root := root) e) = y e := by
  -- On an embedded deleted-root edge, the ambient zero-extension uses the canonical inverse map.
  simp [deletedRootLift,
    ambientEdgeAvoidingRootToDeletedRootEdge_embedding (G := G) (root := root) e,
    deletedRootEdgeEmbedding_avoids_root (G := G) (root := root) e]

/-- Helper for Proposition 8.9: the deleted-root zero-extension is linear in the deleted-root
coordinates. -/
private def deletedRootLiftLinear :
    ((deletedRootGraph (G := G) (root := root)).edgeSet → ℝ) →ₗ[ℝ] (G.edgeSet → ℝ) where
  toFun := deletedRootLift (G := G) (root := root)
  map_add' := by
    intro y z
    -- The zero-extension acts coordinatewise, so additivity is pointwise.
    ext e
    by_cases hAvoid : root ∉ (e : Sym2 V)
    · simp [deletedRootLift, hAvoid]
    · simp [deletedRootLift, hAvoid]
  map_smul' := by
    intro a y
    -- Scalar multiplication also stays pointwise under the same case split.
    ext e
    by_cases hAvoid : root ∉ (e : Sym2 V)
    · simp [deletedRootLift, hAvoid]
    · simp [deletedRootLift, hAvoid]

/-- Helper for Proposition 8.9: lifting the deleted-root restriction of an ambient vector recovers
exactly its deleted-root slice. -/
private theorem deletedRootLift_deletedRootRestriction_eq_deletedRootSlice
    (x : G.edgeSet → ℝ) :
    deletedRootLiftLinear (G := G) (root := root)
        (deletedRootRestriction (G := G) (root := root) x) =
      deletedRootSlice (G := G) (root := root) x := by
  -- Compare the two ambient vectors coordinatewise, using the edge-block partition to decide
  -- whether the coordinate lies in the deleted-root owner.
  ext e
  by_cases hAvoid : root ∉ (e : Sym2 V)
  · have hnotCut : e ∉ δ[G] ({root} : Set V) := by
      intro hcut
      exact hAvoid ((mem_rootCutEdgeFinset_iff_mem_root (G := G) (root := root) e).1 hcut)
    have hdeleted : e ∈ E[G] ({root}ᶜ : Set V) := by
      exact
        (mem_deletedRootInducedEdgeFinset_iff_not_mem_rootCut
          (G := G) (root := root) e).2 hnotCut
    -- In the deleted-root block, the lift evaluates the restricted coordinate and the slice keeps
    -- the original ambient value.
    simp [deletedRootLiftLinear, deletedRootLift, deletedRootSlice, deletedRootRestriction,
      hAvoid, hdeleted,
      deletedRootEdgeEmbedding_ambientEdgeAvoidingRootToDeletedRootEdge
        (G := G) (root := root) ⟨e, hAvoid⟩]
  · have hroot : root ∈ (e : Sym2 V) := by
      simpa using hAvoid
    have hnotDeleted : e ∉ E[G] ({root}ᶜ : Set V) := by
      intro hdeleted
      have hnotCut :=
        (mem_deletedRootInducedEdgeFinset_iff_not_mem_rootCut
          (G := G) (root := root) e).1 hdeleted
      exact hnotCut ((mem_rootCutEdgeFinset_iff_mem_root (G := G) (root := root) e).2 hroot)
    -- On a root-cut edge, both constructions vanish by definition.
    simp [deletedRootLiftLinear, deletedRootLift, deletedRootSlice, hAvoid, hnotDeleted]

/-- Helper for Proposition 8.9: the root-cut slice and the deleted-root slice form a partition of
the ambient edge coordinates. -/
private theorem rootCutSlice_add_deletedRootSlice
    (x : G.edgeSet → ℝ) :
    x = rootCutSlice (G := G) (root := root) x + deletedRootSlice (G := G) (root := root) x := by
  -- The root cut and the deleted-root induced block partition the ambient edge coordinates.
  ext e
  by_cases hcut : e ∈ δ[G] ({root} : Set V)
  · have hnotDeleted : e ∉ E[G] ({root}ᶜ : Set V) := by
      intro hdeleted
      exact
        ((mem_deletedRootInducedEdgeFinset_iff_not_mem_rootCut
          (G := G) (root := root) e).1 hdeleted) hcut
    -- On the root cut, the deleted-root slice vanishes and the root-cut slice is unchanged.
    simp [rootCutSlice, deletedRootSlice, hcut, hnotDeleted]
  · have hdeleted : e ∈ E[G] ({root}ᶜ : Set V) := by
      rw [mem_deletedRootInducedEdgeFinset_iff_not_mem_rootCut (G := G) (root := root) e]
      exact hcut
    -- Away from the root cut, the deleted-root slice carries the whole coordinate.
    simp [rootCutSlice, deletedRootSlice, hcut, hdeleted]

/-- Helper for Proposition 8.9: the root-cut slice is supported on the root-cut block. -/
private theorem rootCutSlice_eq_zero_of_not_mem_rootCut
    (x : G.edgeSet → ℝ)
    {e : G.edgeSet}
    (hcut : e ∉ δ[G] ({root} : Set V)) :
    rootCutSlice (G := G) (root := root) x e = 0 := by
  -- Outside the cut block, the slice definition is already zero.
  simp [rootCutSlice, hcut]

/-- Helper for Proposition 8.9: on root-cut coordinates, the root-cut slice agrees with the
original ambient vector. -/
private theorem rootCutSlice_eq_self_of_mem_rootCut
    (x : G.edgeSet → ℝ)
    {e : G.edgeSet}
    (hcut : e ∈ δ[G] ({root} : Set V)) :
    rootCutSlice (G := G) (root := root) x e = x e := by
  -- Inside the cut block, the slice simply keeps the ambient coordinate.
  simp [rootCutSlice, hcut]

/-- Helper for Proposition 8.9: the root-cut slice inherits the box bounds of a feasible
relaxation point. -/
private theorem rootCutSlice_bounds_of_mem_oneTreeLinearRelaxation
    {x : G.edgeSet → ℝ}
    (hx : x ∈ G.oneTreeLinearRelaxation root) :
    ∀ e, 0 ≤ rootCutSlice (G := G) (root := root) x e ∧
      rootCutSlice (G := G) (root := root) x e ≤ 1 := by
  -- The slice is either the original coordinate on the cut or zero away from it.
  intro e
  rcases ((G.mem_oneTreeLinearRelaxation_iff root).1 hx).1 e with ⟨hx_nonneg, hx_le_one⟩
  by_cases hcut : e ∈ δ[G] ({root} : Set V)
  · simpa [rootCutSlice, hcut] using ⟨hx_nonneg, hx_le_one⟩
  · simpa [rootCutSlice, hcut]

/-- Helper for Proposition 8.9: the root-cut slice keeps the defining root-degree sum of a
feasible relaxation point. -/
private theorem rootCutSlice_rootCut_sum_eq_two_of_mem_oneTreeLinearRelaxation
    {x : G.edgeSet → ℝ}
    (hx : x ∈ G.oneTreeLinearRelaxation root) :
    (δ[G] ({root} : Set V)).sum (rootCutSlice (G := G) (root := root) x) = (2 : ℝ) := by
  -- Every edge in the cut contributes its original coordinate to the slice, so the cut sum is
  -- unchanged.
  have hx_root := ((G.mem_oneTreeLinearRelaxation_iff root).1 hx).2.1
  calc
    (δ[G] ({root} : Set V)).sum (rootCutSlice (G := G) (root := root) x) =
        (δ[G] ({root} : Set V)).sum x := by
          refine Finset.sum_congr rfl ?_
          intro e he
          exact rootCutSlice_eq_self_of_mem_rootCut (G := G) (root := root) x he
    _ = (2 : ℝ) := hx_root

/-- Helper for Proposition 8.9: the ambient incidence vector of a chosen pair of distinct
root-cut edges. -/
private def rootPairIncidence
    (e f : G.edgeSet) :
    G.edgeSet → ℝ :=
  fun g ↦ if g = e ∨ g = f then 1 else 0

/-- Helper for Proposition 8.9: the ambient pair-incidence generators supported on the root cut.
-/
private def rootPairIncidenceSet : Set (G.edgeSet → ℝ) :=
  {x |
    ∃ e f : G.edgeSet,
      e ∈ δ[G] ({root} : Set V) ∧
        f ∈ δ[G] ({root} : Set V) ∧
          e ≠ f ∧
            x = rootPairIncidence (G := G) e f}

/-- Helper for Proposition 8.9: the root-cut rank-two slice is the convex hull of its two-edge
incidence generators. -/
private theorem mem_convexHull_rootPairIncidenceSet
    {x : G.edgeSet → ℝ}
    (hxBounds : ∀ e, 0 ≤ x e ∧ x e ≤ 1)
    (hxSupport : ∀ e, e ∉ δ[G] ({root} : Set V) → x e = 0)
    (hxSum : (δ[G] ({root} : Set V)).sum x = (2 : ℝ)) :
    x ∈ convexHull ℝ (rootPairIncidenceSet (G := G) (root := root)) := by
  -- Apply the finite rank-two theorem on the root-cut edge coordinates and unfold only the
  -- indicator interfaces needed to identify its generators with `rootPairIncidenceSet`.
  simpa [rootPairIncidenceSet, rootPairIncidence, FinitePairSlice.pairIndicatorSet,
    FinitePairSlice.pairIndicator] using
    (FinitePairSlice.mem_convexHull_pairIndicatorSet
      (S := δ[G] ({root} : Set V)) x hxBounds hxSupport hxSum)

/-- Helper for Proposition 8.9: a root-pair incidence generator takes value `1` on its left edge.
-/
private theorem rootPairIncidence_apply_left
    {e f : G.edgeSet}
    (hef : e ≠ f) :
    rootPairIncidence (G := G) e f e = 1 := by
  -- The left generator edge is one of the two designated root-cut edges.
  simp [rootPairIncidence, hef]

/-- Helper for Proposition 8.9: a root-pair incidence generator takes value `1` on its right
edge. -/
private theorem rootPairIncidence_apply_right
    {e f : G.edgeSet}
    (hef : e ≠ f) :
    rootPairIncidence (G := G) e f f = 1 := by
  -- The right generator edge is also one of the two designated root-cut edges.
  simp [rootPairIncidence, hef]

/-- Helper for Proposition 8.9: a root-pair incidence generator vanishes away from the two chosen
edges. -/
private theorem rootPairIncidence_eq_zero_of_ne
    {e f g : G.edgeSet}
    (hge : g ≠ e)
    (hgf : g ≠ f) :
    rootPairIncidence (G := G) e f g = 0 := by
  -- Every ambient edge outside the chosen pair receives coefficient `0`.
  simp [rootPairIncidence, hge, hgf]

/-- Helper for Proposition 8.9: the graph obtained by adjoining a root-pair to a lifted
spanning-tree graph. -/
private def oneTreeExtensionGraph
    (T : (deletedRootGraph (G := G) (root := root)).Subgraph)
    (e f : G.edgeSet) : SimpleGraph V :=
  T.spanningCoe.spanningCoe ⊔ SimpleGraph.fromEdgeSet ({(e : Sym2 V), (f : Sym2 V)} : Set (Sym2 V))

/-- Helper for Proposition 8.9: the extension consists exactly of the lifted tree edges and the
two selected root edges. -/
private theorem mem_oneTreeExtensionGraph_edgeSet_iff
    (T : (deletedRootGraph (G := G) (root := root)).Subgraph)
    (e f : G.edgeSet)
    (g : Sym2 V) :
    g ∈ (oneTreeExtensionGraph (G := G) (root := root) T e f).edgeSet ↔
      (∃ d ∈ T.spanningCoe.edgeSet,
          (Function.Embedding.subtype fun v : V ↦ v ≠ root).sym2Map d = g) ∨
        g = e ∨ g = f := by
  have heDiag : (e : Sym2 V) ∉ Sym2.diagSet := by
    simpa only [Sym2.mem_diagSet] using G.not_isDiag_of_mem_edgeSet e.2
  have hfDiag : (f : Sym2 V) ∉ Sym2.diagSet := by
    simpa only [Sym2.mem_diagSet] using G.not_isDiag_of_mem_edgeSet f.2
  -- Normalize the supremum and mapped edge set once; the only discarded pairs are diagonal.
  rw [oneTreeExtensionGraph, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_map,
    SimpleGraph.edgeSet_fromEdgeSet]
  simp only [Set.mem_union, Set.mem_image, Set.mem_diff, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro (hT | ⟨hpair, -⟩)
    · exact Or.inl hT
    · exact Or.inr hpair
  · rintro (hT | hge | hgf)
    · exact Or.inl hT
    · subst g
      exact Or.inr ⟨Or.inl rfl, heDiag⟩
    · subst g
      exact Or.inr ⟨Or.inr rfl, hfDiag⟩

/-- Helper for Proposition 8.9: a lifted deleted-root edge cannot contain the distinguished
root. -/
private lemma root_not_mem_liftedDeletedRootEdge
    (d : Sym2 {v : V // v ≠ root}) :
    root ∉ (Function.Embedding.subtype fun v : V ↦ v ≠ root).sym2Map d := by
  intro hroot
  rw [Function.Embedding.sym2Map_apply] at hroot
  rcases Sym2.mem_map.mp hroot with ⟨v, -, hv⟩
  exact v.2 hv

/-- Helper for Proposition 8.9: adjoining two distinct root edges to a deleted-root graph gives
the distinguished root degree two. -/
private theorem oneTreeExtensionGraph_degree_root_eq_two
    (T : (deletedRootGraph (G := G) (root := root)).Subgraph)
    (e f : G.edgeSet)
    (he : root ∈ (e : Sym2 V))
    (hf : root ∈ (f : Sym2 V))
    (hef : e ≠ f) :
    (oneTreeExtensionGraph (G := G) (root := root) T e f).degree root = 2 := by
  let H := oneTreeExtensionGraph (G := G) (root := root) T e f
  have hIncidence : H.incidenceFinset root = {(e : Sym2 V), (f : Sym2 V)} := by
    ext g
    rw [H.mem_incidenceFinset]
    change (g ∈ H.edgeSet ∧ root ∈ g) ↔ g ∈ {(e : Sym2 V), (f : Sym2 V)}
    constructor
    · rintro ⟨hg, hroot⟩
      rcases (mem_oneTreeExtensionGraph_edgeSet_iff
        (G := G) (root := root) T e f g).1 hg with ⟨d, hd, hdg⟩ | hge | hgf
      · subst g
        exact (root_not_mem_liftedDeletedRootEdge (root := root) d hroot).elim
      · simp [hge]
      · simp [hgf]
    · intro hg
      simp only [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with hge | hgf
      · subst g
        exact ⟨(mem_oneTreeExtensionGraph_edgeSet_iff
          (G := G) (root := root) T e f e).2 (Or.inr (Or.inl rfl)), he⟩
      · subst g
        exact ⟨(mem_oneTreeExtensionGraph_edgeSet_iff
          (G := G) (root := root) T e f f).2 (Or.inr (Or.inr rfl)), hf⟩
  have hefVal : (e : Sym2 V) ≠ (f : Sym2 V) := by
    intro h
    exact hef (Subtype.ext h)
  -- Degree is the cardinality of this explicit two-edge incidence finset.
  rw [← H.card_incidenceFinset_eq_degree, hIncidence]
  simp [hefVal]

/-- Helper for Proposition 8.9: deleting vertices from a full-vertex subgraph is tree-equivalent
to inducing its spanning graph on the complementary vertex subtype. -/
private theorem toSubgraph_deleteVerts_coe_isTree_iff
    (H : SimpleGraph V)
    (h : H ≤ G)
    (S : Set V) :
    ((G.toSubgraph H h).deleteVerts S).coe.IsTree ↔ (H.induce Sᶜ).IsTree := by
  let toComplement : ((G.toSubgraph H h).deleteVerts S).verts → {v : V // v ∈ Sᶜ} :=
    fun v ↦ ⟨v.1, v.2.2⟩
  let fromComplement : {v : V // v ∈ Sᶜ} → ((G.toSubgraph H h).deleteVerts S).verts :=
    fun v ↦ ⟨v.1, ⟨Set.mem_univ v.1, v.2⟩⟩
  have hleft : Function.LeftInverse fromComplement toComplement := by
    intro v
    apply Subtype.ext
    rfl
  have hright : Function.RightInverse fromComplement toComplement := by
    intro v
    apply Subtype.ext
    rfl
  have hadj : ∀ u v,
      (H.induce Sᶜ).Adj (toComplement u) (toComplement v) ↔
        ((G.toSubgraph H h).deleteVerts S).coe.Adj u v := by
    intro u v
    -- Both sides reduce to adjacency in `H`; the subtype domains carry the restrictions.
    simp [SimpleGraph.toSubgraph, toComplement]
  let deletionIso : ((G.toSubgraph H h).deleteVerts S).coe ≃g H.induce Sᶜ :=
    { toFun := toComplement
      invFun := fromComplement
      left_inv := hleft
      right_inv := hright
      map_rel_iff' := fun {u v} ↦ hadj u v }
  -- Transport treehood across the explicit graph isomorphism.
  exact deletionIso.isTree_iff

/-- Helper for Proposition 8.9: a root-pair extension graph is a subgraph of the ambient graph. -/
private theorem oneTreeExtensionGraph_le
    {T : (deletedRootGraph (G := G) (root := root)).Subgraph}
    {e f : G.edgeSet}
    (he : e ∈ δ[G] ({root} : Set V))
    (hf : f ∈ δ[G] ({root} : Set V)) :
    oneTreeExtensionGraph (G := G) (root := root) T e f ≤ G := by
  refine sup_le ?_ ?_
  · exact
      (SimpleGraph.map_monotone (fun v : {v : V // v ≠ root} ↦ (v : V)) T.spanningCoe_le).trans
        (SimpleGraph.spanningCoe_induce_le G ({root}ᶜ : Set V))
  · rw [SimpleGraph.fromEdgeSet_le]
    rintro z hz
    rcases hz with ⟨rfl | rfl, -⟩
    · exact e.prop
    · exact f.prop

/-- Helper for Proposition 8.9: the ambient subgraph underlying a root-pair extension. -/
private def oneTreeExtension
    (T : (deletedRootGraph (G := G) (root := root)).Subgraph)
    (e f : G.edgeSet)
    (he : e ∈ δ[G] ({root} : Set V))
    (hf : f ∈ δ[G] ({root} : Set V)) : G.Subgraph :=
  G.toSubgraph (oneTreeExtensionGraph (G := G) (root := root) T e f)
    (oneTreeExtensionGraph_le (G := G) (root := root) he hf)

/-- Helper for Proposition 8.9: edge membership in the extension subgraph is the edge-membership
test in its underlying extension graph. -/
private theorem mem_oneTreeExtension_edgeSet_iff
    {T : (deletedRootGraph (G := G) (root := root)).Subgraph}
    {e f g : G.edgeSet}
    {he : e ∈ δ[G] ({root} : Set V)}
    {hf : f ∈ δ[G] ({root} : Set V)} :
    (g : Sym2 V) ∈ (oneTreeExtension (G := G) (root := root) T e f he hf).edgeSet ↔
      (g : Sym2 V) ∈ (oneTreeExtensionGraph (G := G) (root := root) T e f).edgeSet := by
  -- `toSubgraph` retains the edge relation of the supplied spanning graph verbatim.
  rfl

/-- Helper for Proposition 8.9: the canonical spanning extension from the deleted-root subtype
restricts back to its original graph. -/
private theorem induce_spanningCoe_compl_singleton
    (K : SimpleGraph {v : V // v ≠ root}) :
    K.spanningCoe.induce ({root}ᶜ : Set V) = K := by
  -- This is the standard `induce_spanningCoe` cancellation with singleton-complement notation.
  exact SimpleGraph.induce_spanningCoe

/-- Helper for Proposition 8.9: deleting the distinguished root from an extension recovers the
original deleted-root spanning subgraph. -/
private theorem oneTreeExtensionGraph_induce_compl_singleton
    {T : (deletedRootGraph (G := G) (root := root)).Subgraph}
    {e f : G.edgeSet}
    (he : e ∈ δ[G] ({root} : Set V))
    (hf : f ∈ δ[G] ({root} : Set V)) :
    (oneTreeExtensionGraph (G := G) (root := root) T e f).induce ({root}ᶜ : Set V) =
      T.spanningCoe := by
  ext u v
  constructor
  · intro huv
    have huv' : (oneTreeExtensionGraph (G := G) (root := root) T e f).Adj
        (u : V) (v : V) := huv
    rcases huv' with huv' | huv'
    · have hbase :
          ((T.spanningCoe.spanningCoe).induce ({root}ᶜ : Set V)).Adj u v := huv'
      rw [induce_spanningCoe_compl_singleton] at hbase
      exact hbase
    · rcases huv' with ⟨hedge, hne⟩
      rcases hedge with hedge | hedge
      · have hrootEdge : root ∈ (e : Sym2 V) :=
          (mem_rootCutEdgeFinset_iff_mem_root (G := G) (root := root) e).1 he
        have hrootPair : root ∈ s((u : V), (v : V)) := by
          rw [hedge]
          exact hrootEdge
        rcases Sym2.mem_iff.1 hrootPair with hru | hrv
        · exact (u.2 (by simpa using hru.symm)).elim
        · exact (v.2 (by simpa using hrv.symm)).elim
      · have hrootEdge : root ∈ (f : Sym2 V) :=
          (mem_rootCutEdgeFinset_iff_mem_root (G := G) (root := root) f).1 hf
        have hrootPair : root ∈ s((u : V), (v : V)) := by
          rw [hedge]
          exact hrootEdge
        rcases Sym2.mem_iff.1 hrootPair with hru | hrv
        · exact (u.2 (by simpa using hru.symm)).elim
        · exact (v.2 (by simpa using hrv.symm)).elim
  · intro huv
    have hbase : ((T.spanningCoe.spanningCoe).induce ({root}ᶜ : Set V)).Adj u v := by
      rw [induce_spanningCoe_compl_singleton]
      exact huv
    exact Or.inl hbase

/-- Helper for Proposition 8.9: deleting the root from the extension preserves the treehood of
the chosen deleted-root spanning tree. -/
private theorem oneTreeExtension_deleteVerts_singleton_coe_isTree
    {T : (deletedRootGraph (G := G) (root := root)).Subgraph}
    {e f : G.edgeSet}
    (hT : T.IsSpanningTree)
    (he : e ∈ δ[G] ({root} : Set V))
    (hf : f ∈ δ[G] ({root} : Set V)) :
    ((oneTreeExtension (G := G) (root := root) T e f he hf).deleteVerts
      ({root} : Set V)).coe.IsTree := by
  -- Convert deletion of the full-vertex subgraph to complement induction, then cancel the
  -- extension and use the spanning-tree hypothesis.
  rw [oneTreeExtension,
    toSubgraph_deleteVerts_coe_isTree_iff
      (G := G)
      (H := oneTreeExtensionGraph (G := G) (root := root) T e f)
      (oneTreeExtensionGraph_le (G := G) (root := root) he hf)
      ({root} : Set V),
    oneTreeExtensionGraph_induce_compl_singleton (G := G) (root := root) he hf]
  exact hT

/-- Helper for Proposition 8.9: adjoining two distinct root-cut edges to a deleted-root spanning
tree produces a 1-tree of the ambient graph. -/
private theorem oneTreeExtension_isOneTree
    {T : (deletedRootGraph (G := G) (root := root)).Subgraph}
    {e f : G.edgeSet}
    (hT : T.IsSpanningTree)
    (he : e ∈ δ[G] ({root} : Set V))
    (hf : f ∈ δ[G] ({root} : Set V))
    (hef : e ≠ f) :
    (oneTreeExtension (G := G) (root := root) T e f he hf).IsOneTree root := by
  refine ⟨?_, ?_, ?_⟩
  · -- The extension was built with every ambient vertex retained.
    exact SimpleGraph.toSubgraph.isSpanning _ _
  · -- Its only root incidences are the two chosen, distinct cut edges.
    rw [oneTreeExtension, SimpleGraph.degree_toSubgraph]
    exact oneTreeExtensionGraph_degree_root_eq_two
      (G := G) (root := root) T e f
      ((mem_rootCutEdgeFinset_iff_mem_root (G := G) (root := root) e).1 he)
      ((mem_rootCutEdgeFinset_iff_mem_root (G := G) (root := root) f).1 hf) hef
  · -- Deleting the root recovers the original deleted-root spanning tree.
    exact oneTreeExtension_deleteVerts_singleton_coe_isTree
      (G := G) (root := root) hT he hf

/-- Helper for Proposition 8.9: the incidence vector of an extension is the sum of its root-pair
indicator and the zero-extension of the deleted-root tree incidence vector. -/
private theorem subgraphIncidenceVector_oneTreeExtension_eq
    {T : (deletedRootGraph (G := G) (root := root)).Subgraph}
    {e f : G.edgeSet}
    (he : e ∈ δ[G] ({root} : Set V))
    (hf : f ∈ δ[G] ({root} : Set V)) :
    G.subgraphIncidenceVector ℝ (oneTreeExtension (G := G) (root := root) T e f he hf) =
      rootPairIncidence (G := G) e f +
        deletedRootLiftLinear (G := G) (root := root)
          ((deletedRootGraph (G := G) (root := root)).subgraphIncidenceVector ℝ T) := by
  ext g
  have heRoot : root ∈ (e : Sym2 V) :=
    (mem_rootCutEdgeFinset_iff_mem_root (G := G) (root := root) e).1 he
  have hfRoot : root ∈ (f : Sym2 V) :=
    (mem_rootCutEdgeFinset_iff_mem_root (G := G) (root := root) f).1 hf
  by_cases hge : g = e
  · subst g
    have heExtension : (e : Sym2 V) ∈
        (oneTreeExtensionGraph (G := G) (root := root) T e f).edgeSet :=
      (mem_oneTreeExtensionGraph_edgeSet_iff
        (G := G) (root := root) T e f e).2 (Or.inr (Or.inl rfl))
    have heSubgraph : (e : Sym2 V) ∈
        (oneTreeExtension (G := G) (root := root) T e f he hf).edgeSet :=
      (mem_oneTreeExtension_edgeSet_iff (G := G) (root := root)).2 heExtension
    -- On `e`, the pair indicator is one and the deleted-root lift vanishes.
    simp [SimpleGraph.subgraphIncidenceVector, heSubgraph,
      rootPairIncidence, deletedRootLiftLinear, deletedRootLift, heRoot]
  · by_cases hgf : g = f
    · subst g
      have hfExtension : (f : Sym2 V) ∈
          (oneTreeExtensionGraph (G := G) (root := root) T e f).edgeSet :=
        (mem_oneTreeExtensionGraph_edgeSet_iff
          (G := G) (root := root) T e f f).2 (Or.inr (Or.inr rfl))
      have hfSubgraph : (f : Sym2 V) ∈
          (oneTreeExtension (G := G) (root := root) T e f he hf).edgeSet :=
        (mem_oneTreeExtension_edgeSet_iff (G := G) (root := root)).2 hfExtension
      -- The same calculation applies to the second selected edge.
      simp [SimpleGraph.subgraphIncidenceVector, hfSubgraph,
        rootPairIncidence, deletedRootLiftLinear, deletedRootLift, hfRoot]
    · by_cases hroot : root ∈ (g : Sym2 V)
      · have hnotExtension : (g : Sym2 V) ∉
            (oneTreeExtensionGraph (G := G) (root := root) T e f).edgeSet := by
          intro hg
          rcases (mem_oneTreeExtensionGraph_edgeSet_iff
            (G := G) (root := root) T e f g).1 hg with ⟨d, hd, hdg⟩ | hge' | hgf'
          · have hrootLifted :
                root ∈ (Function.Embedding.subtype fun v : V ↦ v ≠ root).sym2Map d := by
              rw [hdg]
              exact hroot
            exact (root_not_mem_liftedDeletedRootEdge (root := root) d hrootLifted).elim
          · exact hge (Subtype.ext hge')
          · exact hgf (Subtype.ext hgf')
        have hnotSubgraph : (g : Sym2 V) ∉
            (oneTreeExtension (G := G) (root := root) T e f he hf).edgeSet := by
          rwa [mem_oneTreeExtension_edgeSet_iff]
        -- Any other edge containing `root` belongs to neither summand.
        simp [SimpleGraph.subgraphIncidenceVector, hnotSubgraph,
          rootPairIncidence, deletedRootLiftLinear, deletedRootLift, hge, hgf, hroot]
      · let d := ambientEdgeAvoidingRootToDeletedRootEdge
            (G := G) (root := root) ⟨g, hroot⟩
        have hEmbedding : deletedRootEdgeEmbedding (G := G) (root := root) d = g := by
          exact deletedRootEdgeEmbedding_ambientEdgeAvoidingRootToDeletedRootEdge
            (G := G) (root := root) ⟨g, hroot⟩
        have hmem : (g : Sym2 V) ∈
              (oneTreeExtensionGraph (G := G) (root := root) T e f).edgeSet ↔
            (d : Sym2 {v : V // v ≠ root}) ∈ T.edgeSet := by
          constructor
          · intro hg
            rcases (mem_oneTreeExtensionGraph_edgeSet_iff
              (G := G) (root := root) T e f g).1 hg with
              ⟨d', hd', hd'g⟩ | hge' | hgf'
            · have hd'T : d' ∈ T.edgeSet := by simpa using hd'
              let d0 : (deletedRootGraph (G := G) (root := root)).edgeSet :=
                ⟨d', T.edgeSet_subset hd'T⟩
              have hEmbedding' : deletedRootEdgeEmbedding (G := G) (root := root) d0 = g := by
                apply Subtype.ext
                exact hd'g
              have hdd0 : d = d0 := by
                apply (deletedRootEdgeEmbedding (G := G) (root := root)).injective
                exact hEmbedding.trans hEmbedding'.symm
              rw [hdd0]
              exact hd'T
            · exact (hge (Subtype.ext hge')).elim
            · exact (hgf (Subtype.ext hgf')).elim
          · intro hd
            apply (mem_oneTreeExtensionGraph_edgeSet_iff
              (G := G) (root := root) T e f g).2
            left
            refine ⟨d, ?_, ?_⟩
            · simpa using hd
            · exact congrArg Subtype.val hEmbedding
        by_cases hd : (d : Sym2 {v : V // v ≠ root}) ∈ T.edgeSet
        · have hgExtension := hmem.2 hd
          have hgSubgraph : (g : Sym2 V) ∈
              (oneTreeExtension (G := G) (root := root) T e f he hf).edgeSet :=
            (mem_oneTreeExtension_edgeSet_iff (G := G) (root := root)).2 hgExtension
          -- On an avoiding edge, both sides are the same deleted-root incidence indicator.
          simp [SimpleGraph.subgraphIncidenceVector, hgSubgraph,
            rootPairIncidence, deletedRootLiftLinear, deletedRootLift, hge, hgf, hroot, d, hd]
        · have hgExtension := (not_congr hmem).2 hd
          have hgSubgraph : (g : Sym2 V) ∉
              (oneTreeExtension (G := G) (root := root) T e f he hf).edgeSet := by
            rwa [mem_oneTreeExtension_edgeSet_iff]
          -- If the inverse edge is absent from `T`, both incidence indicators vanish.
          simp [SimpleGraph.subgraphIncidenceVector, hgSubgraph,
            rootPairIncidence, deletedRootLiftLinear, deletedRootLift, hge, hgf, hroot, d, hd]

/-- Helper for Proposition 8.9: every sum of a root-pair generator and a lifted deleted-root
spanning-tree generator is the incidence vector of an ambient 1-tree. -/
private theorem rootPairIncidenceSet_add_liftedSpanningTreeVertices_subset_oneTreeVertices :
    rootPairIncidenceSet (G := G) (root := root) +
        (deletedRootLiftLinear (G := G) (root := root) ''
          (deletedRootGraph (G := G) (root := root)).spanningTreeVertices) ⊆
      G.oneTreeVertices root := by
  rintro z ⟨xRoot, hxRoot, xDel, hxDel, rfl⟩
  rcases hxRoot with ⟨e, f, he, hf, hef, rfl⟩
  rcases hxDel with ⟨y, hy, rfl⟩
  rcases ((deletedRootGraph (G := G) (root := root)).mem_spanningTreeVertices_iff).1 hy with
    ⟨T, hT, rfl⟩
  -- The extension realizes this generator sum coordinatewise and satisfies all 1-tree axioms.
  have hExtensionMem :
      G.subgraphIncidenceVector ℝ (oneTreeExtension (G := G) (root := root) T e f he hf) ∈
        G.oneTreeVertices root :=
    G.subgraphIncidenceVector_mem_oneTreeVertices (root := root)
      (oneTreeExtension_isOneTree (G := G) (root := root) hT he hf hef)
  have hIncidence := subgraphIncidenceVector_oneTreeExtension_eq
    (G := G) (root := root) (T := T) he hf
  rw [hIncidence] at hExtensionMem
  exact hExtensionMem

/-- Helper for Proposition 8.9: the deleted-root subgraph has the same native edge set as the
subgraph induced on the complement of `{root}`. -/
private theorem deleteVerts_edgeSet_eq_induce_compl_singleton
    {H : G.Subgraph} :
    (H.deleteVerts ({root} : Set V)).edgeSet = (H.induce ({root}ᶜ : Set V)).edgeSet := by
  -- Both owners keep exactly the edges of `H` whose endpoints avoid the distinguished root.
  ext e
  induction e using Sym2.ind with
  | h u v =>
      rw [SimpleGraph.Subgraph.mem_edgeSet, SimpleGraph.Subgraph.mem_edgeSet]
      rw [SimpleGraph.Subgraph.deleteVerts_adj]
      constructor
      · rintro ⟨huH, hu, hvH, hv, huv⟩
        exact ⟨hu, hv, huv⟩
      · rintro ⟨hu, hv, huv⟩
        exact ⟨huv.fst_mem, hu, huv.snd_mem, hv, huv⟩

/-- Helper for Proposition 8.9: summing the ambient incidence vector on deleted-root coordinates
counts the edges of `H.deleteVerts {root}`. -/
private theorem deletedRootInduced_sum_eq_card_deleteVerts
    {H : G.Subgraph} :
    (E[G] ({root}ᶜ : Set V)).sum (G.subgraphIncidenceVector ℝ H) =
      Fintype.card ((H.deleteVerts ({root} : Set V)).edgeSet) := by
  classical
  let S : Finset V := Finset.univ.erase root
  have hS : (S : Set V) = ({root}ᶜ : Set V) := by
    -- The finite owner `erase root` is exactly the complement of the singleton.
    ext v
    simp [S]
  -- Rewrite the deleted-root block through the canonical induced-edge owner from Chapter 4.25.
  calc
    (E[G] ({root}ᶜ : Set V)).sum (G.subgraphIncidenceVector ℝ H)
        = (E[G] (S : Set V)).sum (G.subgraphIncidenceVector ℝ H) := by
            rw [← hS]
    _ = Fintype.card ((H.induce (S : Set V)).edgeSet) := by
          simpa using induced_incidence_sum_eq_card_induced_edges G H S
    _ = Fintype.card ((H.deleteVerts ({root} : Set V)).edgeSet) := by
          rw [deleteVerts_edgeSet_eq_induce_compl_singleton (G := G) (root := root) (H := H),
            hS]

/-- Helper for Proposition 8.9: summing the root-cut coordinates of an incidence vector counts
the edges of `H` incident to the distinguished root. -/
private theorem rootCutIncidenceSum_eq_degree
    {H : G.Subgraph} :
    (δ[G] ({root} : Set V)).sum (G.subgraphIncidenceVector ℝ H) = H.degree root := by
  classical
  let rootCutInH : Finset G.edgeSet :=
    (δ[G] ({root} : Set V)).filter fun e ↦ e.1 ∈ H.edgeSet
  have hsum :
      (δ[G] ({root} : Set V)).sum (G.subgraphIncidenceVector ℝ H) =
        (rootCutInH.card : ℝ) := by
    -- Expand the indicator and keep only the root-cut edges that actually belong to `H`.
    calc
      (δ[G] ({root} : Set V)).sum (G.subgraphIncidenceVector ℝ H) =
          rootCutInH.sum (fun _ ↦ (1 : ℝ)) := by
            simpa [rootCutInH, SimpleGraph.subgraphIncidenceVector] using
              (Finset.sum_filter
                (s := δ[G] ({root} : Set V))
                (p := fun e : G.edgeSet ↦ e.1 ∈ H.edgeSet)
                (f := fun _ ↦ (1 : ℝ))).symm
      _ = (rootCutInH.card : ℝ) := by
            simp
  let edgeEmbedding : G.edgeSet ↪ Sym2 V :=
    ⟨fun e ↦ (e : Sym2 V), Subtype.val_injective⟩
  have hmap :
      Finset.map edgeEmbedding rootCutInH = H.spanningCoe.incidenceFinset root := by
    -- After forgetting the ambient-edge subtype, the filtered root-cut edges are exactly the
    -- incident edges of `root` in the spanning coercion of `H`.
    ext e
    constructor
    · intro he
      rcases Finset.mem_map.1 he with ⟨eG, heG, rfl⟩
      rcases Finset.mem_filter.1 heG with ⟨hcut, hedgeH⟩
      rw [SimpleGraph.mem_incidenceFinset]
      exact ⟨by simpa using hedgeH,
        (mem_rootCutEdgeFinset_iff_mem_root (G := G) (root := root) eG).1 hcut⟩
    · intro he
      rw [SimpleGraph.mem_incidenceFinset] at he
      rcases he with ⟨hedgeH, hroot⟩
      let eG : G.edgeSet := ⟨e, H.edgeSet_subset hedgeH⟩
      have hcut : eG ∈ δ[G] ({root} : Set V) := by
        exact (mem_rootCutEdgeFinset_iff_mem_root (G := G) (root := root) eG).2 (by simpa using hroot)
      refine Finset.mem_map.2 ⟨eG, ?_, rfl⟩
      exact Finset.mem_filter.2 ⟨hcut, by simpa using hedgeH⟩
  have hcardNat : rootCutInH.card = H.degree root := by
    -- Convert the filtered cardinality into the incidence-finset cardinal of `H.spanningCoe`.
    calc
      rootCutInH.card = (H.spanningCoe.incidenceFinset root).card := by
        simpa using congrArg Finset.card hmap
      _ = H.spanningCoe.degree root := by
        simpa using H.spanningCoe.card_incidenceFinset_eq_degree root
      _ = H.degree root := by
        simpa using (Subgraph.degree_spanningCoe (G' := H) root)
  calc
    (δ[G] ({root} : Set V)).sum (G.subgraphIncidenceVector ℝ H) = (rootCutInH.card : ℝ) := hsum
    _ = H.degree root := by
          exact congrArg (fun n : ℕ ↦ (n : ℝ)) hcardNat

/-- Helper for Proposition 8.9: a 1-tree contributes exactly `|V| - 2` deleted-root edges in the
ambient coordinates. -/
theorem deletedRootIncidenceSum_eq_card_sub_two_of_isOneTree
    {H : G.Subgraph}
    (hH : H.IsOneTree root) :
    (E[G] ({root}ᶜ : Set V)).sum (G.subgraphIncidenceVector ℝ H) =
      (Fintype.card V - 2 : ℝ) := by
  classical
  have hTree := hH.deleteVerts_singleton_coe_isTree
  have hcoeEdgeCard :
      ((H.deleteVerts ({root} : Set V)).coe.edgeSet).ncard =
        ((H.deleteVerts ({root} : Set V)).edgeSet).ncard := by
    -- Forgetting the deleted-root vertex subtype does not change the edge count.
    calc
      ((H.deleteVerts ({root} : Set V)).coe.edgeSet).ncard =
          (Sym2.map ((↑) : (H.deleteVerts ({root} : Set V)).verts → V) ''
            (H.deleteVerts ({root} : Set V)).coe.edgeSet).ncard := by
              symm
              exact Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
      _ = ((H.deleteVerts ({root} : Set V)).edgeSet).ncard := by
            rw [(H.deleteVerts ({root} : Set V)).image_coe_edgeSet_coe]
  have htreeCard :
      ((H.deleteVerts ({root} : Set V)).coe.edgeSet).ncard + 1 =
        ((H.deleteVerts ({root} : Set V)).verts).ncard := by
    -- A finite tree has one fewer edge than vertices.
    have htreeCardNat := (SimpleGraph.isTree_iff_connected_and_card.mp hTree).2
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at htreeCardNat
    exact htreeCardNat
  have hvertsCard :
      ((H.deleteVerts ({root} : Set V)).verts).ncard = Fintype.card V - 1 := by
    -- Deleting the root from a spanning subgraph leaves exactly the complement subtype `{v ≠ root}`.
    have hvertsEq :
        (H.deleteVerts ({root} : Set V)).verts = {v : V | v ≠ root} := by
      ext v
      simp [hH.isSpanning v]
    rw [hvertsEq]
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    exact Set.card_ne_eq (α := V) root
  have hdeletedCardNat :
      ((H.deleteVerts ({root} : Set V)).edgeSet).ncard = Fintype.card V - 2 := by
    omega
  have hcardV_ge_two : 2 ≤ Fintype.card V := by
    -- The distinguished root has degree `2`, so the ambient graph has at least two other vertices.
    have hdegLt : H.spanningCoe.degree root < Fintype.card V := by
      simpa using (SimpleGraph.degree_lt_card_verts (G := H.spanningCoe) root)
    have hdegEq : H.spanningCoe.degree root = 2 := by
      rw [Subgraph.degree_spanningCoe]
      exact hH.degree_root_eq_two
    omega
  -- Rewrite the deleted-root block as the edge count of `H.deleteVerts {root}` and then
  -- specialize the tree cardinality.
  calc
    (E[G] ({root}ᶜ : Set V)).sum (G.subgraphIncidenceVector ℝ H) =
        Fintype.card ((H.deleteVerts ({root} : Set V)).edgeSet) := by
          exact deletedRootInduced_sum_eq_card_deleteVerts (G := G) (root := root) (H := H)
    _ = (((H.deleteVerts ({root} : Set V)).edgeSet).ncard : ℝ) := by
          rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    _ = ((Fintype.card V - 2 : ℕ) : ℝ) := by
          exact congrArg (fun n : ℕ ↦ (n : ℝ)) hdeletedCardNat
    _ = (Fintype.card V : ℝ) - 2 := by
          rw [Nat.cast_sub hcardV_ge_two]
          norm_num

/-- Helper for Proposition 8.9: the root-cut coordinates of a 1-tree incidence vector sum to `2`.
-/
theorem rootCutIncidenceSum_eq_two_of_isOneTree
    {H : G.Subgraph}
    (hH : H.IsOneTree root) :
    (δ[G] ({root} : Set V)).sum (G.subgraphIncidenceVector ℝ H) = (2 : ℝ) := by
  -- Reinterpret the root-cut count as the root degree and use the defining `1`-tree condition.
  calc
    (δ[G] ({root} : Set V)).sum (G.subgraphIncidenceVector ℝ H) = H.degree root := by
      exact rootCutIncidenceSum_eq_degree (G := G) (root := root) (H := H)
    _ = (2 : ℝ) := by
          exact congrArg (fun n : ℕ ↦ (n : ℝ)) hH.degree_root_eq_two

/-- Helper for Proposition 8.9: a 1-tree incidence vector has total edge sum `|V|`. -/
theorem subgraphIncidenceVector_total_sum_of_isOneTree
    {H : G.Subgraph}
    (hH : H.IsOneTree root) :
    (∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ H e) = (Fintype.card V : ℝ) := by
  -- Split the ambient edge sum into the root-cut and deleted-root blocks, then evaluate each
  -- block by the dedicated one-tree counting lemmas above.
  calc
    (∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ H e) =
        (δ[G] ({root} : Set V)).sum (G.subgraphIncidenceVector ℝ H) +
          (E[G] ({root}ᶜ : Set V)).sum (G.subgraphIncidenceVector ℝ H) := by
            rw [sumEdges_eq_rootCut_sum_add_deletedRoot_sum (G := G) (root := root)
              (x := G.subgraphIncidenceVector ℝ H)]
    _ = (2 : ℝ) + (Fintype.card V - 2 : ℝ) := by
          rw [rootCutIncidenceSum_eq_two_of_isOneTree (G := G) (root := root) hH,
            deletedRootIncidenceSum_eq_card_sub_two_of_isOneTree (G := G) (root := root) hH]
    _ = (Fintype.card V : ℝ) := by
          ring

/-- Helper for Proposition 8.9: forgetting the ambient subtype on a subgraph preserves the edge
cardinality. -/
private theorem card_coe_edgeSet_eq_card_edgeSet
    {W : Type*} {K : SimpleGraph W} [Fintype W] [DecidableRel K.Adj] (L : K.Subgraph) :
    Fintype.card L.coe.edgeSet = Fintype.card L.edgeSet := by
  -- The native edge set is the image of the subtype-owner edge set under the canonical vertex
  -- inclusion, so both have the same finite cardinality.
  calc
    Fintype.card L.coe.edgeSet = Nat.card L.coe.edgeSet := by
      rw [Nat.card_eq_fintype_card]
    _ = Nat.card L.edgeSet := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      calc
        L.coe.edgeSet.ncard =
            (Sym2.map ((↑) : L.verts → W) '' L.coe.edgeSet).ncard := by
              symm
              exact Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
        _ = L.edgeSet.ncard := by
              rw [L.image_coe_edgeSet_coe]
    _ = Fintype.card L.edgeSet := by
      rw [Nat.card_eq_fintype_card]

/-- Helper for Proposition 8.9: forgetting the ambient subtype on a subgraph preserves the edge
cardinality at the `Nat.card` level, which avoids instance-sensitive rewrites later. -/
private theorem natCard_coe_edgeSet_eq_natCard_edgeSet
    {W : Type*} {K : SimpleGraph W} (L : K.Subgraph) :
    Nat.card L.coe.edgeSet = Nat.card L.edgeSet := by
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  calc
    L.coe.edgeSet.ncard =
        (Sym2.map ((↑) : L.verts → W) '' L.coe.edgeSet).ncard := by
          symm
          exact Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
    _ = L.edgeSet.ncard := by
          rw [L.image_coe_edgeSet_coe]

/-- Helper for Proposition 8.9: a finite acyclic graph has at most one fewer edge than vertices. -/
private theorem isAcyclic_card_edgeSet_le_card_verts_sub_one
    {W : Type*} [Fintype W] {K : SimpleGraph W} (hK : K.IsAcyclic) :
    Fintype.card K.edgeSet ≤ Fintype.card W - 1 := by
  classical
  by_cases hW : IsEmpty W
  · let _ : IsEmpty W := hW
    simp
  · let _ : Nonempty W := not_isEmpty_iff.mp hW
    obtain ⟨T, hTK, -, hT⟩ :=
      SimpleGraph.Connected.exists_isTree_le_of_le_of_isAcyclic
        (G := (⊤ : SimpleGraph W)) (H := K) SimpleGraph.connected_top le_top hK
    have hEdgeLe : Fintype.card K.edgeSet ≤ Fintype.card T.edgeSet := by
      rw [← K.edgeFinset_card, ← T.edgeFinset_card]
      exact Finset.card_mono (SimpleGraph.edgeFinset_mono hTK)
    have hTreeCard : Fintype.card T.edgeSet + 1 = Fintype.card W := by
      rw [SimpleGraph.card_edgeSet]
      exact hT.card_edgeFinset
    omega

/-- Helper for Proposition 8.9: if a vertex subset avoids the distinguished root, then inducing
after deleting the root has the same ambient edge set as inducing directly. -/
private theorem induce_edgeSet_eq_deleteVerts_induce_edgeSet_of_root_not_mem
    {H : G.Subgraph}
    (hHSpanning : H.IsSpanning)
    {S : Finset V}
    (hrootS : root ∉ S) :
    (H.induce (S : Set V)).edgeSet =
      ((H.deleteVerts ({root} : Set V)).induce (S : Set V)).edgeSet := by
  ext e
  induction e using Sym2.ind with
  | h u v =>
      rw [SimpleGraph.Subgraph.mem_edgeSet, SimpleGraph.Subgraph.mem_edgeSet]
      rw [SimpleGraph.Subgraph.induce_adj, SimpleGraph.Subgraph.induce_adj]
      rw [SimpleGraph.Subgraph.deleteVerts_adj]
      constructor
      · rintro ⟨huS, hvS, huv⟩
        have huNotRoot : u ∉ ({root} : Set V) := by
          simp only [Set.mem_singleton_iff]
          intro huRoot
          exact hrootS (by simpa [huRoot] using huS)
        have hvNotRoot : v ∉ ({root} : Set V) := by
          simp only [Set.mem_singleton_iff]
          intro hvRoot
          exact hrootS (by simpa [hvRoot] using hvS)
        exact ⟨huS, hvS, hHSpanning u, huNotRoot, hHSpanning v, hvNotRoot, huv⟩
      · rintro ⟨huS, hvS, _, _, _, _, huv⟩
        exact ⟨huS, hvS, huv⟩

/-- Helper for Proposition 8.9: on any root-free vertex subset, a 1-tree induces at most
`|S| - 1` ambient edges. -/
private theorem deletedRootInducedEdgeCard_eq
    {H : G.Subgraph}
    (hHSpanning : H.IsSpanning)
    {S : Finset V}
    (hrootS : root ∉ S) :
    Fintype.card ((H.induce (S : Set V)).edgeSet) =
      Fintype.card ((((H.deleteVerts ({root} : Set V)).coe).induce
        {v : (H.deleteVerts ({root} : Set V)).verts | (v : V) ∈ (S : Set V)}).edgeSet) := by
  classical
  let T : G.Subgraph := H.deleteVerts ({root} : Set V)
  let U : Set T.verts := {v | (v : V) ∈ (S : Set V)}
  have hsubset : (S : Set V) ⊆ T.verts := by
    intro v hvS
    refine ⟨hHSpanning v, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hvRoot
    exact hrootS (by simpa [hvRoot] using hvS)
  have hIso :
      (T.induce (S : Set V)).coe ≃g T.coe.induce U :=
    SimpleGraph.Subgraph.coeInduceIso (G' := T) (s := (S : Set V)) hsubset
  have hInducedCard :
      Fintype.card ((H.induce (S : Set V)).edgeSet) =
        Fintype.card ((T.coe.induce U).edgeSet) := by
    -- Route correction: rewrite the ambient induced graph through the deleted-root owner once,
    -- then compare edge counts through `Subgraph.coeInduceIso` instead of further owner transport.
    rw [induce_edgeSet_eq_deleteVerts_induce_edgeSet_of_root_not_mem
      (G := G) (root := root) hHSpanning hrootS]
    have hIsoCard :
        Fintype.card ((T.induce (S : Set V)).coe.edgeSet) =
          Fintype.card ((T.coe.induce U).edgeSet) := by
      rw [SimpleGraph.card_edgeSet, SimpleGraph.card_edgeSet]
      simpa using hIso.card_edgeFinset_eq
    calc
      Fintype.card ((T.induce (S : Set V)).edgeSet) =
          Fintype.card ((T.induce (S : Set V)).coe.edgeSet) := by
            rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
            exact (natCard_coe_edgeSet_eq_natCard_edgeSet (L := T.induce (S : Set V))).symm
      _ = Fintype.card ((T.coe.induce U).edgeSet) := hIsoCard
  simpa [T, U] using hInducedCard

/-- Helper for Proposition 8.9: viewing a root-free ambient vertex subset inside the deleted-root
owner does not change its cardinality. -/
private theorem deletedRootVertexSet_card_eq
    {H : G.Subgraph}
    (hHSpanning : H.IsSpanning)
    {S : Finset V}
    (hrootS : root ∉ S) :
    Fintype.card {v : (H.deleteVerts ({root} : Set V)).verts // (v : V) ∈ (S : Set V)} = S.card := by
  classical
  let T : G.Subgraph := H.deleteVerts ({root} : Set V)
  have hsubset : (S : Set V) ⊆ T.verts := by
    intro v hvS
    refine ⟨hHSpanning v, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hvRoot
    exact hrootS (by simpa [hvRoot] using hvS)
  let U : Set T.verts := {v | (v : V) ∈ (S : Set V)}
  have hUCard : Fintype.card U = S.card := by
    let e : ↥U ≃ {v : V // v ∈ (S : Set V)} := {
      toFun := fun v ↦ ⟨v.1.1, v.2⟩
      invFun := fun v ↦ ⟨⟨v.1, hsubset v.2⟩, v.2⟩
      left_inv := by
        intro v
        cases v
        rfl
      right_inv := by
        intro v
        cases v
        rfl }
    calc
      Fintype.card U = Fintype.card {v : V // v ∈ (S : Set V)} := Fintype.card_congr e
      _ = S.card := by
            simpa using (Fintype.card_subtype fun v : V ↦ v ∈ (S : Set V))
  simpa [T, U] using hUCard

/-- Helper for Proposition 8.9: the deleted-root induced owner satisfies the forest edge bound on
its native subtype vertex set. -/
private theorem deletedRootOwnerInducedCard_le_deletedRootVertexCard_sub_one
    {H : G.Subgraph}
    (hH : H.IsOneTree root)
    {S : Finset V} :
    Fintype.card ((((H.deleteVerts ({root} : Set V)).coe).induce
      {v : (H.deleteVerts ({root} : Set V)).verts | (v : V) ∈ (S : Set V)}).edgeSet) ≤
        Fintype.card {v : (H.deleteVerts ({root} : Set V)).verts // (v : V) ∈ (S : Set V)} - 1 := by
  let U : Set (H.deleteVerts ({root} : Set V)).verts := {v | (v : V) ∈ (S : Set V)}
  have hAcyclic :
      (((H.deleteVerts ({root} : Set V)).coe).induce U).IsAcyclic := by
    -- The deleted-root owner remains acyclic after inducing on the root-free subtype set.
    exact hH.deleteVerts_singleton_coe_isTree.isAcyclic.induce U
  -- Apply the generic forest bound in the owner normal form, keeping the `S.card` rewrite out of
  -- this theorem.
  simpa [U] using
    isAcyclic_card_edgeSet_le_card_verts_sub_one
      (K := (((H.deleteVerts ({root} : Set V)).coe).induce U)) hAcyclic

/-- Helper for Proposition 8.9: the deleted-root induced owner satisfies the forest edge bound on
every root-free vertex subset. -/
private theorem deletedRootOwnerInducedCard_le_card_sub_one
    {H : G.Subgraph}
    (hH : H.IsOneTree root)
    {S : Finset V}
    (hrootS : root ∉ S) :
    Fintype.card ((((H.deleteVerts ({root} : Set V)).coe).induce
      {v : (H.deleteVerts ({root} : Set V)).verts | (v : V) ∈ (S : Set V)}).edgeSet) ≤
        S.card - 1 := by
  -- Route correction: first prove the forest bound in the deleted-root owner's native subtype
  -- cardinality, then rewrite that cardinality once to `S.card`.
  calc
    Fintype.card ((((H.deleteVerts ({root} : Set V)).coe).induce
      {v : (H.deleteVerts ({root} : Set V)).verts | (v : V) ∈ (S : Set V)}).edgeSet) ≤
        Fintype.card {v : (H.deleteVerts ({root} : Set V)).verts // (v : V) ∈ (S : Set V)} - 1 := by
          exact deletedRootOwnerInducedCard_le_deletedRootVertexCard_sub_one
            (G := G) (root := root) hH
    _ = S.card - 1 := by
          rw [deletedRootVertexSet_card_eq (G := G) (root := root) hH.isSpanning hrootS]

/-- Helper for Proposition 8.9: on any root-free vertex subset, a 1-tree induces at most
`|S| - 1` ambient edges. -/
theorem deletedRootInduceCard_le_card_sub_one_of_isOneTree
    {H : G.Subgraph}
    (hH : H.IsOneTree root)
    (S : Finset V)
    (hrootS : root ∉ S) :
    Fintype.card ((H.induce (S : Set V)).edgeSet) ≤ S.card - 1 := by
  -- Transport the ambient induced subgraph to the deleted-root owner, apply the forest bound
  -- there, and transport the edge count back.
  calc
    Fintype.card ((H.induce (S : Set V)).edgeSet) =
        Fintype.card ((((H.deleteVerts ({root} : Set V)).coe).induce
          {v : (H.deleteVerts ({root} : Set V)).verts | (v : V) ∈ (S : Set V)}).edgeSet) := by
            exact deletedRootInducedEdgeCard_eq (G := G) (root := root) hH.isSpanning hrootS
    _ ≤ S.card - 1 := by
          exact deletedRootOwnerInducedCard_le_card_sub_one
            (G := G) (root := root) hH hrootS

/-- Helper for Proposition 8.9: every 1-tree incidence vector satisfies the linear relaxation. -/
theorem subgraphIncidenceVector_mem_oneTreeLinearRelaxation
    {H : G.Subgraph}
    (hH : H.IsOneTree root) :
    G.subgraphIncidenceVector ℝ H ∈ G.oneTreeLinearRelaxation root := by
  refine (G.mem_oneTreeLinearRelaxation_iff root).2 ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e
    constructor
    · -- Incidence vectors are coordinatewise nonnegative.
      exact subgraphIncidenceVector_nonneg G H e
    · -- Each incidence coordinate is an indicator, so it is at most `1`.
      by_cases he : e.1 ∈ H.edgeSet
      · simp [SimpleGraph.subgraphIncidenceVector, he]
      · simp [SimpleGraph.subgraphIncidenceVector, he]
  · -- The root-cut block of a 1-tree incidence vector sums to `2`.
    exact rootCutIncidenceSum_eq_two_of_isOneTree (G := G) (root := root) hH
  · -- The total edge sum of a 1-tree incidence vector is `|V|`.
    exact subgraphIncidenceVector_total_sum_of_isOneTree (G := G) (root := root) hH
  · intro S hS hrootS
    -- Rewrite the subtour inequality as an induced-edge count and apply the deleted-root tree
    -- bound proved above.
    calc
      (E[G] (S : Set V)).sum (G.subgraphIncidenceVector ℝ H) =
          Fintype.card ((H.induce (S : Set V)).edgeSet) := by
            simpa using induced_incidence_sum_eq_card_induced_edges G H S
      _ ≤ (S.card - 1 : ℝ) := by
            have hnat :
                Fintype.card ((H.induce (S : Set V)).edgeSet) ≤ S.card - 1 :=
              deletedRootInduceCard_le_card_sub_one_of_isOneTree
                (G := G) (root := root) hH S hrootS
            have hnat_add : Fintype.card ((H.induce (S : Set V)).edgeSet) + 1 ≤ S.card := by
              have hlt : Fintype.card ((H.induce (S : Set V)).edgeSet) < S.card := by
                exact lt_of_le_of_lt hnat
                  (Nat.sub_lt (Finset.card_pos.mpr hS) (by decide))
              exact Nat.succ_le_of_lt hlt
            have hreal_add : (Fintype.card ((H.induce (S : Set V)).edgeSet) : ℝ) + 1 ≤ S.card := by
              exact_mod_cast hnat_add
            nlinarith

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap08/section_8_1/ch8_sec8_1_1_proposition_8_9.lean

Proposition 8.9. The 1-tree polytope of `G` is described by the linear relaxation of the
constraints in `(8.7)`, with `root` representing the distinguished textbook vertex `1`. -/
theorem oneTreePolytope_eq_oneTreeLinearRelaxation
    (G : SimpleGraph V)
    (root : V) :
    G.oneTreePolytope root = G.oneTreeLinearRelaxation root := by
  apply le_antisymm
  · -- Every 1-tree vertex already satisfies the linear relaxation, so the convex hull does too.
    rw [G.oneTreePolytope_eq_convexHull]
    refine convexHull_min ?_ (G.convex_oneTreeLinearRelaxation root)
    intro x hx
    rcases (G.mem_oneTreeVertices_iff root).1 hx with ⟨H, hH, rfl⟩
    exact G.subgraphIncidenceVector_mem_oneTreeLinearRelaxation (root := root) hH
  · -- Route correction: the reverse inclusion should now start from the ambient decomposition
    -- `x = xRoot + xDel`, then transport `xDel` to the deleted-root tree polytope and handle the
    -- root-cut slice as the convex hull of two-edge root-pair vertices.
    intro x hx
    let xRoot := rootCutSlice (G := G) (root := root) x
    let xDel := deletedRootSlice (G := G) (root := root) x
    have hsplit : x = xRoot + xDel := by
      -- The current proof frontier is the canonical ambient split from the source product route.
      simpa [xRoot, xDel] using
        rootCutSlice_add_deletedRootSlice (G := G) (root := root) x
    have hxDel :
        deletedRootRestriction (G := G) (root := root) x ∈
          (deletedRootGraph (G := G) (root := root)).spanningTreePolytope := by
      -- The deleted-root factor is already transported to Chapter 4.25.
      exact deletedRootRestriction_mem_spanningTreePolytope (G := G) (root := root) hx
    have hDelLift :
        xDel =
          deletedRootLiftLinear (G := G) (root := root)
            (deletedRootRestriction (G := G) (root := root) x) := by
      -- The new lift API rewrites the deleted-root slice into a linear image of the transported
      -- spanning-tree polytope point.
      simpa [xDel] using
        (deletedRootLift_deletedRootRestriction_eq_deletedRootSlice
          (G := G) (root := root) x).symm
    have hxRootBox :
        ∀ e, 0 ≤ xRoot e ∧ xRoot e ≤ 1 := by
      -- The root-cut slice inherits the ambient box constraints pointwise.
      simpa [xRoot] using
        rootCutSlice_bounds_of_mem_oneTreeLinearRelaxation
          (G := G) (root := root) hx
    have hxRootSum :
        (δ[G] ({root} : Set V)).sum xRoot = (2 : ℝ) := by
      -- The root-degree equation is unchanged on the root-cut slice.
      simpa [xRoot] using
        rootCutSlice_rootCut_sum_eq_two_of_mem_oneTreeLinearRelaxation
          (G := G) (root := root) hx
    have hxRootSupport :
        ∀ e, e ∉ δ[G] ({root} : Set V) → xRoot e = 0 := by
      intro e he
      -- The root-cut slice vanishes identically off the distinguished cut.
      simpa [xRoot] using
        rootCutSlice_eq_zero_of_not_mem_rootCut (G := G) (root := root) x he
    have hxDelConv :
        deletedRootRestriction (G := G) (root := root) x ∈
          convexHull ℝ
            (deletedRootGraph (G := G) (root := root)).spanningTreeVertices := by
      -- Rewrite the deleted-root polytope as the convex hull of its spanning-tree generators.
      rwa [(deletedRootGraph (G := G) (root := root)).spanningTreePolytope_eq_convexHull] at hxDel
    have hxDelHull :
        xDel ∈
          convexHull ℝ
            ((deletedRootLiftLinear (G := G) (root := root)) ''
              (deletedRootGraph (G := G) (root := root)).spanningTreeVertices) := by
      -- Transport the deleted-root spanning-tree hull to ambient coordinates once, so the
      -- remaining reverse inclusion only has to absorb the independent root-cut factor.
      have hxDelImage :
          deletedRootLiftLinear (G := G) (root := root)
              (deletedRootRestriction (G := G) (root := root) x) ∈
            (deletedRootLiftLinear (G := G) (root := root)) ''
              convexHull ℝ
                (deletedRootGraph (G := G) (root := root)).spanningTreeVertices := by
        exact ⟨deletedRootRestriction (G := G) (root := root) x, hxDelConv, rfl⟩
      rw [LinearMap.image_convexHull] at hxDelImage
      simpa [hDelLift] using hxDelImage
    have hxRootHull :
        xRoot ∈ convexHull ℝ (rootPairIncidenceSet (G := G) (root := root)) := by
      -- The cut slice is a rank-two point in the unit box, hence a convex combination of pairs.
      exact mem_convexHull_rootPairIncidenceSet
        (G := G) (root := root) hxRootBox hxRootSupport hxRootSum
    have hxSumHull :
        xRoot + xDel ∈
          convexHull ℝ
            (rootPairIncidenceSet (G := G) (root := root) +
              (deletedRootLiftLinear (G := G) (root := root) ''
                (deletedRootGraph (G := G) (root := root)).spanningTreeVertices)) := by
      -- Combine the independent hull memberships through the Minkowski-sum identity.
      rw [convexHull_add]
      exact Set.add_mem_add hxRootHull hxDelHull
    rw [G.oneTreePolytope_eq_convexHull, hsplit]
    -- Each generator sum is a 1-tree incidence vector, so convex-hull monotonicity closes.
    exact convexHull_mono
      (rootPairIncidenceSet_add_liftedSpanningTreeVertices_subset_oneTreeVertices
        (G := G) (root := root)) hxSumHull

end

end Proposition_8_9

end SimpleGraph

#print axioms SimpleGraph.oneTreePolytope_eq_oneTreeLinearRelaxation
