module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Connected.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Order.CompletePartialOrder
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Topology.Connected.Clopen

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace SimpleGraph

/-
Domain-style sampling for Lemma 5.8.17:
- primary domain: irreducible components of a connected topological space
- inspected owner declarations:
  `irreducibleComponents`,
  `sUnion_irreducibleComponents`,
  `SimpleGraph.Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial`,
  `IsConnected.iUnion_of_reflTransGen`
- best owner abstraction: `irreducibleComponents X`
- layer triage:
  `source-facing`: existence of an irreducible component whose omission leaves a connected union of
    the remaining components
  `core/canonical`: `irreducibleComponents X` together with the connectedness API for finite
    simple graphs
  `bridge/view`: the simple graph on `irreducibleComponents X` whose edges record nonempty
    intersections
- primitive-vs-derived split: the primitive data are the canonical irreducible components and
  their intersection relation; a raw witness `Z : Set X` with a separate membership proof is
  derived boilerplate, so the theorem should quantify directly over `irreducibleComponents X`
-/

variable {X : Type u} [TopologicalSpace X]

private abbrev irreducibleComponentGraph : SimpleGraph (irreducibleComponents X) :=
  SimpleGraph.fromRel fun A B ↦ ((A : Set X) ∩ (B : Set X)).Nonempty

variable [ConnectedSpace X]

private theorem irreducibleComponentGraph_connected [Finite (irreducibleComponents X)] :
    (irreducibleComponentGraph : SimpleGraph (irreducibleComponents X)).Connected := by
  classical
  let G : SimpleGraph (irreducibleComponents X) := irreducibleComponentGraph
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  let Z₀ : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨Z₀, fun A ↦ ?_⟩
  by_contra hA
  let T : Set (irreducibleComponents X) := {B | G.Reachable Z₀ B}
  let U : Set (irreducibleComponents X) := Tᶜ
  let V : Set X := ⋃ B ∈ T, (B : Set X)
  have hT_finite : T.Finite := Set.toFinite T
  have hU_finite : U.Finite := Set.toFinite U
  have hV_closed : IsClosed V := by
    simpa [V, Set.sUnion_image] using
      (hT_finite.image fun B : irreducibleComponents X ↦ (B : Set X)).isClosed_biUnion
        fun W hW ↦ by
          rcases hW with ⟨B, hBT, rfl⟩
          simpa using isClosed_of_mem_irreducibleComponents (B : Set X) B.2
  have hU_union_closed : IsClosed (⋃ B ∈ U, (B : Set X)) := by
    simpa [Set.sUnion_image] using
      (hU_finite.image fun B : irreducibleComponents X ↦ (B : Set X)).isClosed_biUnion
        fun W hW ↦ by
          rcases hW with ⟨B, hBU, rfl⟩
          simpa using isClosed_of_mem_irreducibleComponents (B : Set X) B.2
  have hV_eq : V = (⋃ B ∈ U, (B : Set X))ᶜ := by
    ext y
    constructor
    · intro hy hyU
      rcases mem_iUnion₂.1 hy with ⟨B, hBT, hyB⟩
      rcases mem_iUnion₂.1 hyU with ⟨C, hCU, hyC⟩
      have hBC : B ≠ C := by
        intro hBC
        exact hCU (hBC ▸ hBT)
      have hBC_adj : G.Adj B C := by
        simpa [G, SimpleGraph.fromRel_adj, inter_comm] using
          show B ≠ C ∧ ((((B : Set X) ∩ C).Nonempty) ∨ (((C : Set X) ∩ B).Nonempty)) from
            ⟨hBC, Or.inl ⟨y, hyB, hyC⟩⟩
      exact hCU <| hBT.trans hBC_adj.reachable
    · intro hy
      have hy' : y ∈ ⋃₀ irreducibleComponents X := by
        simp [sUnion_irreducibleComponents]
      rcases mem_sUnion.1 hy' with ⟨B, hB, hyB⟩
      let B' : irreducibleComponents X := ⟨B, hB⟩
      have hBT : B' ∈ T := by
        by_contra hBU
        exact hy <| mem_iUnion₂.2 ⟨B', hBU, hyB⟩
      exact mem_iUnion₂.2 ⟨B', hBT, hyB⟩
  have hV_open : IsOpen V := by
    rw [hV_eq]
    exact hU_union_closed.isOpen_compl
  have hxV : x ∈ V := by
    have hZ₀ : G.Reachable Z₀ Z₀ :=
      (SimpleGraph.reachable_iff_reflTransGen Z₀ Z₀).2 .refl
    exact mem_iUnion₂.2 ⟨Z₀, hZ₀, mem_irreducibleComponent⟩
  have hV_univ : V = univ := IsClopen.eq_univ ⟨hV_closed, hV_open⟩ ⟨x, hxV⟩
  obtain ⟨y, hyA⟩ := A.2.1.nonempty
  have hy_notV : y ∉ V := by
    simpa [hV_eq] using (mem_iUnion₂.2 ⟨A, hA, hyA⟩ : y ∈ ⋃ B ∈ U, (B : Set X))
  exact hy_notV (hV_univ ▸ mem_univ y)

omit [ConnectedSpace X] in
private theorem iUnion_components_ne_eq_sUnion_diff_singleton (Z : irreducibleComponents X) :
    (⋃ W : {W : irreducibleComponents X // W ≠ Z}, ((W : irreducibleComponents X) : Set X)) =
      ⋃₀ (irreducibleComponents X \ {(Z : Set X)}) := by
  ext x
  constructor
  · intro hx
    rcases mem_iUnion.1 hx with ⟨W, hxW⟩
    refine mem_sUnion.2 ⟨(W : irreducibleComponents X), ?_, hxW⟩
    refine ⟨W.1.2, ?_⟩
    intro hW
    exact W.2 (Subtype.ext <| by simpa using hW)
  · intro hx
    rcases mem_sUnion.1 hx with ⟨W, hW, hxW⟩
    refine mem_iUnion.2 ⟨⟨⟨W, hW.1⟩, ?_⟩, hxW⟩
    intro hWZ
    exact hW.2 <| by simpa using congrArg (fun T : irreducibleComponents X ↦ (T : Set X)) hWZ

-- Proof sketch: view the irreducible components as the vertices of a finite graph, joining two
-- vertices when the corresponding components meet. Since irreducible sets are connected and the
-- components cover a connected space, this graph is connected. A finite connected graph with more
-- than one vertex has a vertex whose deletion leaves the graph connected; translating back gives
-- the required component to omit.
/-- Lemma 5.8.17: if a connected topological space has finitely many irreducible components
and more than one irreducible component, then omitting one of them leaves a connected union of
the remaining components. -/
theorem exists_connected_union_irreducibleComponents_except
    [Finite (irreducibleComponents X)] (hn : 1 < Nat.card (irreducibleComponents X)) :
    ∃ Z : irreducibleComponents X,
      IsConnected (⋃₀ (irreducibleComponents X \ {(Z : Set X)})) := by
  classical
  let G : SimpleGraph (irreducibleComponents X) := irreducibleComponentGraph
  have hG_connected : G.Connected := by
    simpa [G] using irreducibleComponentGraph_connected
  haveI : Nontrivial (irreducibleComponents X) := Finite.one_lt_card_iff_nontrivial.mp hn
  obtain ⟨Z, hZ_connected⟩ :=
    hG_connected.exists_connected_induce_compl_singleton_of_finite_nontrivial
  letI : Nonempty {W : irreducibleComponents X // W ≠ Z} := hZ_connected.nonempty
  have hRemaining_connected :
      IsConnected (⋃ W : {W : irreducibleComponents X // W ≠ Z},
        ((W : irreducibleComponents X) : Set X)) := by
    refine IsConnected.iUnion_of_reflTransGen (fun W ↦ W.1.2.1.isConnected) ?_
    intro A B
    have hAB :
        Relation.ReflTransGen
          ((G.induce ({Z}ᶜ : Set (irreducibleComponents X))).Adj) A B :=
      (SimpleGraph.reachable_iff_reflTransGen A B).1 (hZ_connected A B)
    refine hAB.mono ?_
    intro U V hUV
    have hUV' : G.Adj (U : irreducibleComponents X) (V : irreducibleComponents X) := by
      simpa [SimpleGraph.induce_adj] using hUV
    rcases (by simpa [G, SimpleGraph.fromRel_adj] using hUV') with
      ⟨_, hUV'' | hVU''⟩
    · exact hUV''
    · simpa [inter_comm] using hVU''
  exact ⟨Z, iUnion_components_ne_eq_sUnion_diff_singleton Z ▸ hRemaining_connected⟩
