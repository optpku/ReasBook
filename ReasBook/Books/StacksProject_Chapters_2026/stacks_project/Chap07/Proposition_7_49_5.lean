module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u v

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) [HasWeakSheafify J (Type (max u v))]
variable (F : Cᵒᵖ ⥤ Type (max u v)) (𝒢 : Sheaf J (Type (max u v)))

/- Domain-style sampling for Proposition 7.49.5:
- primary domain: sheafification on a site and its adjunction with the inclusion of sheaves into
  presheaves;
- sampled owner API:
  `presheafToSheaf`,
  `sheafificationAdjunction`,
  `CategoryTheory.toSheafify`,
  `CategoryTheory.sheafifyLift`;
- source-facing layer: the universal property of the sheafification unit `J.toSheafify F`;
- core/canonical owner: the adjunction `sheafificationAdjunction J (Type (max u v))`;
- bridge/view: the specialized Hom-set equivalence for the given presheaf `F` and sheaf `𝒢`.

Primitive data are the site `(C, J)`, the weak sheafification instance, the presheaf `F`, and the
target sheaf `𝒢`. The universal morphism and its uniqueness are derived API of the owner
adjunction, so this item should expose the specialized `homEquiv` directly rather than introduce a
parallel local wrapper for the same bijection.
-/

/- Proposition 7.49.5: the sheafification unit `J.toSheafify F : F ⟶ J.sheafify F` is universal
for maps from `F` to sheaves of sets; equivalently, precomposition with `J.toSheafify F`
induces a bijection from morphisms out of the sheafification to morphisms from `F`.
The canonical library-facing form is the sheafification adjunction hom-equivalence below. -/
recall sheafificationAdjunction

#check (((sheafificationAdjunction J (Type (max u v))).homEquiv F 𝒢) :
  ((presheafToSheaf J _).obj F ⟶ 𝒢) ≃
    (F ⟶ (sheafToPresheaf J _).obj 𝒢))

end
