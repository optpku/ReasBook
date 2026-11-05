module

public import stacks_project.Chap07.Lemma_7_32_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Domain-style sampling for Lemma 7.34.1:
- primary domain: set-valued presheaf fibers, presheaf costalks, and left Kan extension along
  `u.op`;
- sampled owner API:
  `Functor.lanAdjunction`,
  `presheafCostalkAdjunction`,
  `Functor.whiskeringLeftObjCompIso`,
  `Adjunction.leftAdjointUniq`;
- source/core/bridge triage:
  `source-facing`: the comparison from the `v`-fiber of the pushforward `uₚ F` to the
  `(u ⋙ v)`-fiber of `F`;
  `core/canonical`: the owners `u.op.lan`, `Functor.presheafFiber`, and the right-adjoint
  description by presheaf costalks;
  `bridge/view`: the canonical identification of right adjoints
  `(u ⋙ v)^p ≅ v^p ⋙ (whiskeringLeft _ _ _).obj u.op`, obtained by combining
  `Functor.associator` with `Functor.whiskeringLeftObjCompIso u.op v.op`.

Primitive data are only the functors `u` and `v`, with `v` valued in a sufficiently large `Type`
so that the canonical left Kan extension and presheaf-fiber owners exist without extra public
smallness assumptions. The comparison isomorphism is derived API from the canonical adjunctions
`u.op.lan ⊣ u^p` and `v.presheafFiber ⊣ v^p`, together with the composition formula for
pullback/costalk. The refinement therefore removes the private generator-level comparison maps and
defines the source-facing isomorphism directly as the canonical uniqueness isomorphism between two
left adjoints to the same right adjoint.
-/

/-- Lemma 7.34.1: for a functor `u : \mathcal C \to \mathcal D`, a set-valued functor
`v : \mathcal D \to \mathrm{Sets}`, and `w = v \circ u`, the canonical natural transformation from
the `v`-fiber of the pushforward presheaf, realized canonically as the left Kan extension of `F`
along `u.op`, to the `w`-fiber of `F` is an isomorphism.
This is the functorial form of `(uₚ F)_q = F_p`. -/
@[simps!]
noncomputable def presheafPushforwardFiberIso
    (u : C ⥤ D) (v : D ⥤ Type (max u₁ u₂ v₁ v₂ w)) :
    u.op.lan ⋙ v.presheafFiber ≅ (u ⋙ v).presheafFiber :=
  (((u.op.lanAdjunction (Type (max u₁ u₂ v₁ v₂ w))).comp (presheafCostalkAdjunction v)).ofNatIsoRight
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (whiskeringLeftObjCompIso u.op v.op).symm)).leftAdjointUniq
    (presheafCostalkAdjunction (u ⋙ v))

/-- Proposition-level companion to `presheafPushforwardFiberIso`: pushing a presheaf forward
along `u` and then taking the `v`-fiber is canonically isomorphic to taking the `(u ⋙ v)`-fiber
directly. -/
theorem presheafPushforwardFiber_isomorphic
    (u : C ⥤ D) (v : D ⥤ Type (max u₁ u₂ v₁ v₂ w)) :
    IsIsomorphic (u.op.lan ⋙ v.presheafFiber) ((u ⋙ v).presheafFiber) :=
  ⟨presheafPushforwardFiberIso u v⟩

-- Proof sketch: the hom component of any natural isomorphism is an isomorphism objectwise, so
-- this follows by applying the canonical instance to the component of
-- `presheafPushforwardFiberIso`.
/-- The canonical comparison map from the `v`-fiber of the pushforward presheaf to the
`(u ⋙ v)`-fiber is objectwise an isomorphism. -/
theorem presheafPushforwardFiberIso_hom_app_isIso
    (u : C ⥤ D) (v : D ⥤ Type (max u₁ u₂ v₁ v₂ w))
    (F : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)) :
    IsIso ((presheafPushforwardFiberIso u v).hom.app F) := by
  -- The comparison is a natural isomorphism, so each component map is an isomorphism.
  simpa using (show IsIso (((presheafPushforwardFiberIso u v).app F).hom) by infer_instance)

end Functor

end CategoryTheory
