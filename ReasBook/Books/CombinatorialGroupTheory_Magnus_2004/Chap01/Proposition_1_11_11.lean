/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

section

/- Layer triage:
- `source-facing`: the proposition that `N` is the tree product of `Δ`, recorded as the existence
  of a cocone `T : TreeProductCocone Δ N` with the universal property.
- `core/canonical`: the explicit cocone `TreeProductCocone Δ N` and its universal property
  `IsTreeProduct`.
- `bridge/view`: `CompatibleFamily` and `vertexImageSet` express the compatibility and generation
  conditions imposed on a cocone.

Domain sampling:
1. `SimpleGraph.IsTree` is mathlib's canonical owner for the graph-theoretic tree condition.
2. `SimpleGraph.edgeSet` is mathlib's canonical owner for undirected geometric edges of a simple
   graph; using `Δ.graph.edgeSet` avoids orienting one edge twice.
3. `MonoidHom` together with `Function.Injective` is the canonical owner for group embeddings in
   this chapter, and `MonoidHom.ofInjective` is the derived equivalence to the image subgroup.
4. `Subgroup.closure` together with `Set.range` is the canonical owner for the statement that the
   vertex-group images generate `N`.
5. No existing mathlib declaration packages tree products of groups with amalgamated edge
   subgroups, so this item remains source-facing rather than a recall-only recall block.

Primitive vs. derived:
the primitive source data are the tree of groups `Δ` itself and the specified cocone of vertex
embeddings into `N`; compatibility along geometric edges and the generation statement belong to
that cocone. The universal mapping property is derived structure on top of this explicit owner
object, while the source phrase "`N` is the tree product of `Δ`" is the existence statement built
from those core owners rather than a theorem about every compatible-generating cocone. For each
edge, the homomorphisms into the incident vertex groups are primitive data, while the identified
edge subgroup inside a vertex group is derived canonically from injectivity via
`MonoidHom.ofInjective`.
-/

/-- A tree-product diagram consists of vertex groups and edge groups arranged over a tree, with
monomorphism data from each geometric edge group into its incident vertex groups. -/
structure TreeProductDiagram where
  Vertex : Type u
  graph : SimpleGraph Vertex
  isTree : graph.IsTree
  vertexGroup : Vertex → Type v
  edgeGroup : graph.edgeSet → Type w
  vertexGroup_inst (a : Vertex) : Group (vertexGroup a)
  edgeGroup_inst (e : graph.edgeSet) : Group (edgeGroup e)
  edgeToVertex (e : graph.edgeSet) {a : Vertex} (_ : a ∈ (e : Sym2 Vertex)) :
      edgeGroup e →* vertexGroup a
  edgeToVertex_injective (e : graph.edgeSet) {a : Vertex} (ha : a ∈ (e : Sym2 Vertex)) :
      Function.Injective (edgeToVertex e ha)

attribute [instance] TreeProductDiagram.vertexGroup_inst TreeProductDiagram.edgeGroup_inst

namespace TreeProductDiagram

variable (Δ : TreeProductDiagram.{u, v, w}) {N : Type x} [Group N]

/-- The set of elements of `N` lying in the image of some vertex-group map. -/
def vertexImageSet (φ : (a : Δ.Vertex) → Δ.vertexGroup a →* N) : Set N :=
  Set.range fun p : Σ a : Δ.Vertex, Δ.vertexGroup a ↦ φ p.1 p.2

/-- A family of vertex-group homomorphisms is compatible when the two maps induced by every edge
group agree after passing to the target group. -/
def CompatibleFamily (φ : (a : Δ.Vertex) → Δ.vertexGroup a →* N) : Prop :=
  ∀ (e : Δ.graph.edgeSet) {a b : Δ.Vertex} (ha : a ∈ (e : Sym2 Δ.Vertex))
    (hb : b ∈ (e : Sym2 Δ.Vertex)) (z : Δ.edgeGroup e),
      φ a (Δ.edgeToVertex e ha z) = φ b (Δ.edgeToVertex e hb z)

end TreeProductDiagram

/-- A cocone over `Δ` with specified vertex-group embeddings into `N`, together with the
source-side compatibility and generation data used in the tree-product universal property. -/
structure TreeProductCocone (Δ : TreeProductDiagram.{u, v, w}) (N : Type x) [Group N] where
  vertexHom : (a : Δ.Vertex) → Δ.vertexGroup a →* N
  vertexHom_injective (a : Δ.Vertex) : Function.Injective (vertexHom a)
  compatible : Δ.CompatibleFamily vertexHom
  generates : Subgroup.closure (Δ.vertexImageSet vertexHom) = ⊤

variable {Δ : TreeProductDiagram.{u, v, w}} {N : Type x} [Group N]

/-- A cocone `T` exhibits `N` as the tree product of `Δ` if every compatible family of vertex
group maps out of `Δ` factors uniquely through `T.vertexHom`. -/
def IsTreeProduct (T : TreeProductCocone Δ N) : Prop :=
  ∀ {Q : Type (max u v w x)} [Group Q] (φ : (a : Δ.Vertex) → Δ.vertexGroup a →* Q),
    Δ.CompatibleFamily φ →
      ∃! ψ : N →* Q, ∀ (a : Δ.Vertex) (x : Δ.vertexGroup a), ψ (T.vertexHom a x) = φ a x

namespace TreeProductDiagram

variable (Δ : TreeProductDiagram.{u, v, w}) (N : Type x) [Group N]

/-- Proposition 1-11-11, source-facing form: `N` is the tree product of `Δ` when there exists a
compatible generating cocone of vertex embeddings over `Δ` with the tree-product universal
property. -/
def IsTreeProductOf : Prop :=
  ∃ T : TreeProductCocone Δ N, IsTreeProduct T

end TreeProductDiagram

end
