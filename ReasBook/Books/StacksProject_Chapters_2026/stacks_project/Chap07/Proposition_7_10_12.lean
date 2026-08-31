module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) [HasWeakSheafify J (Type (max u v))]
variable (P : Cᵒᵖ ⥤ Type (max u v)) (𝒢 : Sheaf J (Type (max u v)))

/- Domain-style sampling for Proposition 7.10.12:
- primary domain: sheafification of set-valued presheaves on a Grothendieck site, specifically the
  universal property of the sheafification unit;
- sampled owner declarations:
  `sheafificationAdjunction`,
  `GrothendieckTopology.toSheafify`,
  `GrothendieckTopology.sheafifyLift`,
  `GrothendieckTopology.sheafifyLift_unique`;
- best owner abstraction: the sheafification adjunction Hom-set equivalence
  `((sheafificationAdjunction J (Type (max u v))).homEquiv P 𝒢)`;
- primitive data: the presheaf `P` and the sheaf `𝒢`;
- derived API: the factorization morphism `J.sheafifyLift`, its compatibility with the unit
  `J.toSheafify_sheafifyLift`, and the uniqueness theorem `J.sheafifyLift_unique`.

The source proposition is therefore a `bridge/view` statement whose mathematically canonical owner
is the adjunction equivalence, not a separate local universal-property wrapper.
-/
/- Source/core/bridge triage for Proposition 7.10.12:
- source-facing content: the sheafification unit `J.toSheafify P` is universal for maps from `P`
  to sheaves of sets
- core/canonical owner: the sheafification adjunction Hom-set equivalence
  `((sheafificationAdjunction J (Type (max u v))).homEquiv P 𝒢)`
- bridge/view: the explicit factorization map `J.sheafifyLift` together with
  `J.toSheafify_sheafifyLift` and `J.sheafifyLift_unique`
- primitive data: the presheaf `P` and the sheaf `𝒢`
- derived API: the unique factorization through `J.toSheafify P`
-/
/- Proposition 7.10.12: the sheafification unit `J.toSheafify P : P ⟶ J.sheafify P` is universal
for maps from `P` to sheaves of sets. The canonical owner-level form is the sheafification
adjunction, and the source-facing universal property is the derived bridge API consisting of
`J.sheafifyLift`, `J.toSheafify_sheafifyLift`, and `J.sheafifyLift_unique`. -/
recall CategoryTheory.sheafificationAdjunction
recall CategoryTheory.toSheafify
recall CategoryTheory.sheafifyLift
recall CategoryTheory.toSheafify_sheafifyLift
recall CategoryTheory.sheafifyLift_unique

variable {P 𝒢}

/- Owner-level form: the sheafification adjunction Hom-set equivalence. -/
#check (((sheafificationAdjunction J (Type (max u v))).homEquiv P 𝒢) :
  ((presheafToSheaf J _).obj P ⟶ 𝒢) ≃
    (P ⟶ 𝒢.obj))

/- Source-facing factorization: a map `φ : P ⟶ 𝒢.obj` uniquely lifts through `J.toSheafify P`. -/
#check (fun φ : P ⟶ 𝒢.obj ↦ J.sheafifyLift φ 𝒢.property :
  (P ⟶ 𝒢.obj) → (J.sheafify P ⟶ 𝒢.obj))

/- The factorization equation is exactly `toSheafify_sheafifyLift`. -/
#check (fun φ : P ⟶ 𝒢.obj ↦ J.toSheafify_sheafifyLift φ 𝒢.property :
  ∀ φ : P ⟶ 𝒢.obj, J.toSheafify P ≫ J.sheafifyLift φ 𝒢.property = φ)

/- Uniqueness is exactly `sheafifyLift_unique`. -/
#check (fun φ : P ⟶ 𝒢.obj ↦ fun γ : J.sheafify P ⟶ 𝒢.obj ↦
    J.sheafifyLift_unique φ 𝒢.property γ)

end
