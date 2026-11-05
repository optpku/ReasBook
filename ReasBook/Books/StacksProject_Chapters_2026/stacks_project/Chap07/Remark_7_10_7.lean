module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] CategoryTheory.Types.instFunLike
attribute [local instance] CategoryTheory.Types.instConcreteCategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X : C} {P : Cᵒᵖ ⥤ Type w}
variable {𝒰 𝒱 : J.Cover X}

/-
Domain-style sampling for Remark 7.10.7:
- primary domain: matching families for set-valued presheaves on a Grothendieck site;
- sampled owner API:
  `CategoryTheory.GrothendieckTopology.Cover`,
  `CategoryTheory.leOfHom`,
  `CategoryTheory.GrothendieckTopology.Meq`,
  `Equiv.cast`;
- source/core/bridge triage:
  `source-facing`: mutually refining covers define the same matching-family model for `H^0`;
  `core/canonical`: `J.Cover X` is the owner poset of covers, with equality supplied by
    antisymmetry from the refinement morphisms, and `Meq P` is the dependent owner family over
    that poset;
  `bridge/view`: the canonical identification below is transport of `Meq P` along that equality
    via `Equiv.cast`.

Primitive data are only the two refinement morphisms `𝒰 ⟶ 𝒱` and `𝒱 ⟶ 𝒰`. The equivalence of
matching-family types is derived API from equality in `J.Cover X`, so no parallel public
cover-equality wrapper is needed here beyond the canonical antisymmetry step.
-/
namespace Meq

/-- Remark 7.10.7: if the covers `𝒰` and `𝒱` refine each other, then they are equal in the
poset `J.Cover X`, so the matching-family types `Meq P 𝒰` and `Meq P 𝒱`, which model
`H^0(𝒰, P)` and `H^0(𝒱, P)`, are canonically identified. -/
def equivOfMutualRefinements
    (h𝒰𝒱 : 𝒰 ⟶ 𝒱) (h𝒱𝒰 : 𝒱 ⟶ 𝒰) :
    Meq P 𝒰 ≃ Meq P 𝒱 :=
  Equiv.cast <| congrArg (Meq P) <| le_antisymm (leOfHom h𝒰𝒱) (leOfHom h𝒱𝒰)

/-- The equivalence from mutually refining covers is transport of matching families along the
equality of covers induced by antisymmetry. -/
-- Proof sketch: unfold `equivOfMutualRefinements`; both sides are definitionally the same
-- transport equivalence given by `Equiv.cast`.
theorem equivOfMutualRefinements_def
    (h𝒰𝒱 : 𝒰 ⟶ 𝒱) (h𝒱𝒰 : 𝒱 ⟶ 𝒰) :
    equivOfMutualRefinements h𝒰𝒱 h𝒱𝒰 =
      Equiv.cast (congrArg (Meq P) (le_antisymm (leOfHom h𝒰𝒱) (leOfHom h𝒱𝒰))) := by
  -- Unfold the canonical identification to expose the underlying transport equivalence.
  rfl

end Meq

end CategoryTheory.GrothendieckTopology
