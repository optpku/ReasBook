module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Definition_6_15_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite TopCat TopologicalSpace

noncomputable section

universe w v u

section

variable {C : Type u} [Category.{v} C]
variable (F : C ⥤ Type w) [IsAlgebraicStructure C F]
variable {X : TopCat.{w}} (ℱ : X.Presheaf C)

local notation "J" => Opens.grothendieckTopology X

variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type w)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) C]
variable [CategoryTheory.GrothendieckTopology.HasSheafCompose (Opens.grothendieckTopology X) F]
variable [CategoryTheory.GrothendieckTopology.PreservesSheafification
  (Opens.grothendieckTopology X) F]

/-
Domain-style sampling for Lemma 6.19.1:
- primary domain: sheafification of presheaves valued in a category of algebraic structures whose
  underlying-set functor preserves limits and filtered colimits and reflects isomorphisms;
- sampled owner declarations:
  `CategoryTheory.presheafToSheaf`,
  `CategoryTheory.toSheafify`,
  `CategoryTheory.sheafificationAdjunction`,
  `CategoryTheory.sheafifyComposeIso`;
- best owner abstraction:
  the canonical owner is the `C`-valued sheafification `(presheafToSheaf J C).obj ℱ`, with unit
  `toSheafify J ℱ`; the underlying set-valued comparison to the sheafification of `ℱ ⋙ F` is the
  bridge isomorphism `sheafifyComposeIso J F ℱ`;
- derived API:
  the compatibility equation for the unit after forgetting to sets and the unique factorization
  property into `C`-valued sheaves.

Source/core/bridge triage:
- `source-facing`: the Stacks-project assertion that presheaves of algebraic structures admit a
  sheafification whose underlying sheaf of sets is the usual one and that maps into sheaves factor
  uniquely through it;
- `core/canonical`: the `C`-valued sheafification owner `(presheafToSheaf J C).obj ℱ` with unit
  `toSheafify J ℱ`;
- `bridge/view`: `sheafifyComposeIso J F ℱ`, comparing the sheafification of the underlying
  set-valued presheaf with the underlying set-valued sheaf of the canonical `C`-valued
  sheafification.

Primitive data are only `ℱ`, the owner `(presheafToSheaf J C).obj ℱ`, and its unit
`toSheafify J ℱ`; the compatibility equation with the underlying set-valued sheafification and the
universal factorization property are derived API and should not be repackaged as a second public
predicate on arbitrary witnesses.
-/
/- Lemma 6.19.1 is the direct specialization of the canonical sheafification owner and its
forgetful comparison isomorphism once the ambient sheafification and compatibility instances are
in scope, so this file keeps those owner recalls together with the source-facing specializations of
the object, comparison isomorphism, unit compatibility, and universal factorization API. -/
recall CategoryTheory.presheafToSheaf
recall CategoryTheory.toSheafify
recall CategoryTheory.sheafificationAdjunction
recall CategoryTheory.sheafifyComposeIso
recall CategoryTheory.sheafComposeIso_hom_fac
recall CategoryTheory.sheafifyLift
recall CategoryTheory.toSheafify_sheafifyLift
recall CategoryTheory.sheafifyLift_unique

variable {ℱ}

/- The source-facing `C`-valued sheafification object. -/
#check (presheafToSheaf J C).obj ℱ

/- Its canonical unit on underlying presheaves. -/
#check toSheafify J ℱ

/- Forgetting the `C`-valued sheafification to sets identifies its underlying `Type`-valued sheaf
with the ordinary sheafification of the underlying presheaf. -/
#check sheafifyComposeIso J F ℱ

/- The comparison isomorphism carries the ordinary sheafification unit to the forgotten
`C`-valued unit. -/
#check sheafComposeIso_hom_fac J F ℱ

variable (𝒢 : X.Sheaf C)

/- The sheafification adjunction specialized to `C`-valued sheaves on `X`. -/
#check (sheafificationAdjunction J C).homEquiv ℱ 𝒢

variable {𝒢}

/- The canonical factorization of a map into a `C`-valued sheaf. -/
#check fun φ : ℱ ⟶ 𝒢.obj ↦ sheafifyLift J φ 𝒢.property

/- The factorization equation is `toSheafify_sheafifyLift`. -/
#check fun φ : ℱ ⟶ 𝒢.obj ↦ toSheafify_sheafifyLift J φ 𝒢.property

/- The factorization is unique. -/
#check fun φ : ℱ ⟶ 𝒢.obj ↦ sheafifyLift_unique J φ 𝒢.property

end
