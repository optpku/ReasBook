module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Definition_4_3_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Functor

universe u₁ u₂ v₁ v₂ w

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D)
variable [∀ ℱ : Presheaf C, u.op.HasLeftKanExtension ℱ]

/- Domain-style sampling:
- primary domain: presheaf Kan-extension adjunctions;
- sampled owner API:
  `Functor.lanAdjunction`,
  `Adjunction.homEquiv`,
  `Functor.leftKanExtensionUnit`,
  and the chapter-level owner-form recall in `Remark_7_5_5`;
- source/core/bridge triage:
  `source-facing`: the hom-set identification attached to presheaf pullback and pushforward;
  `core/canonical`: the adjunction `Functor.lanAdjunction`;
  `bridge/view`: the specialization of `Adjunction.homEquiv` to set-valued presheaves.

Primitive data are the functor `u` and the existence of left Kan extensions along `u.op`. The
hom-set equivalence is derived API from the owner adjunction, so this file should recall that
owner directly and keep the specialized hom-set bijection only as the thin source-facing bridge.
-/

variable (ℱ : Presheaf C) (𝒢 : Presheaf D)

/- Lemma 7.5.4, owner form: on set-valued presheaves the lower shriek `uₚ`, realized as the left
Kan extension along `u.op`, is left adjoint to pullback `u^p`. This is exactly the canonical
specialized adjunction `u.op.lanAdjunction (Type w)`. -/
#check (u.op.lanAdjunction (Type w) :
  u.op.lan ⊣ (whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op)

/- Lemma 7.5.4: the functor `uₚ` on presheaves, realized as left Kan extension along `u.op`, is
left adjoint to the pullback functor `u^p`, realized as precomposition by `u.op`; equivalently,
this adjunction gives the bifunctorial identification
`Mor_{PSh(D)}(uₚ ℱ, 𝒢) ≃ Mor_{PSh(C)}(ℱ, u^p 𝒢)`. This is the canonical hom-set equivalence
coming from `u.op.lanAdjunction (Type w)`, i.e. the presheaf specialization of
`Adjunction.homEquiv`. -/
#check (((u.op.lanAdjunction (Type w)).homEquiv ℱ 𝒢) :
    ((u.op.lan).obj ℱ ⟶ 𝒢) ≃ (ℱ ⟶ u.op ⋙ 𝒢))

end CategoryTheory
