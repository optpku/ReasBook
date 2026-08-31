module

public import Mathlib.Topology.Sheaves.Sheaf


@[expose] public section

open TopologicalSpace Opposite CategoryTheory TopCat

universe u v w

noncomputable section

/-- The local sheaf data carried by an open cover of a topological space. -/
structure SheafGlueingData (X : TopCat.{u}) where
  /-- The index type for the chosen open cover. -/
  J : Type v
  /-- The members of the open cover. -/
  U : J → Opens X
  /-- The sheaf given on each member of the cover. -/
  localSheaf : ∀ i, TopCat.Sheaf (Type w) ((Opens.toTopCat X).obj (U i))

/-- Morphisms into and out of a glued sheaf: a package-level universal property for a sheaf
obtained by glueing local sheaf data on an open cover. It packages the two hom-set equivalences
asserting that maps from the glued sheaf, and maps into the glued sheaf, are determined by the
corresponding compatible families of local morphisms on the cover.
-/
structure GluedSheafUniversalProperty {X : TopCat.{u}} (D : SheafGlueingData.{u, v, w} X)
    (glued : X.Sheaf (Type w)) where
  /-- For a target sheaf `F`, `compatibleTo F` is the type of compatible local morphism families
  from the local glueing data carried by `D` to `F`.
  -/
  compatibleTo : X.Sheaf (Type w) → Type (max u (max v w))
  /-- For a source sheaf `F`, `compatibleFrom F` is the type of compatible local morphism families
  from `F` to the local glueing data carried by `D`.
  -/
  compatibleFrom : X.Sheaf (Type w) → Type (max u (max v w))
  /-- Morphisms from the glued sheaf to a global sheaf are equivalent to compatible local maps on
  the chosen cover.
  -/
  homToEquiv : ∀ F : X.Sheaf (Type w), (glued ⟶ F) ≃ compatibleTo F
  /-- Morphisms from a global sheaf to the glued sheaf are equivalent to compatible local maps on
  the chosen cover.
  -/
  homFromEquiv : ∀ F : X.Sheaf (Type w), (F ⟶ glued) ≃ compatibleFrom F

namespace GluedSheafUniversalProperty

/-- A glued-sheaf universal property can be evaluated on a target sheaf to recover the type of
compatible local morphism families out of the glued sheaf. -/
instance {X : TopCat.{u}} {D : SheafGlueingData.{u, v, w} X} {glued : X.Sheaf (Type w)} :
    CoeFun (GluedSheafUniversalProperty D glued)
      (fun _ ↦ X.Sheaf (Type w) → Type (max u (max v w))) where
  coe P := P.compatibleTo

end GluedSheafUniversalProperty
