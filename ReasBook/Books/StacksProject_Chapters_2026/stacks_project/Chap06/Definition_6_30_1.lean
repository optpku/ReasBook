module

public import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Definition_4_3_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The full subcategory of `Opens X` spanned by the basis members `B`. -/
abbrev BasisOpen (B : Set (Opens X)) :=
  ObjectProperty.FullSubcategory fun U : Opens X ↦ U ∈ B

variable {B : Set (Opens X)}

/- Definition 6.30.1:
- primary domain: set-valued presheaves on the basis-open category of a topological space
- sampled owner abstractions:
  `ObjectProperty.FullSubcategory`,
  `Presheaf`,
  `((BasisOpen B)ᵒᵖ ⥤ Type _)`,
  `TopCat.Presheaf`
- source-facing layer: the basis-open category `BasisOpen B`
- core/canonical owner: `Presheaf`, specialized to `BasisOpen B`
- primitive data: only the underlying contravariant functor on basis opens
- derived API: morphisms are natural transformations in this functor category
-/
/-
Definition 6.30.1 lives at the source/core boundary: once the source-facing owner
`BasisOpen B` is fixed, a presheaf of sets on the basis `B` is exactly the canonical project owner
`Presheaf (BasisOpen B)`.
-/
recall Presheaf

#check (Presheaf (BasisOpen B))

variable (ℱ 𝒢 : Presheaf (BasisOpen B))

/- Companion recall: morphisms of presheaves on the basis `B` are the natural transformations in
this functor category. -/
#check (ℱ ⟶ 𝒢)
