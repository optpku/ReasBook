module

public import stacks_project.Chap04.Lemma_4_31_6
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open CategoricalPullback

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {X : Type u₁} [Category.{v₁} X]
variable {Y : Type u₂} [Category.{v₂} Y]
variable {Z : Type u₃} [Category.{v₃} Z]
variable {A : Type u₄} [Category.{v₄} A]
variable {B : Type u₅} [Category.{v₅} B]
variable {C : Type u₆} [Category.{v₆} C]

variable {H : X ⥤ Z} {I : Y ⥤ Z} {L : X ⥤ A} {K : Y ⥤ B}
variable {M : Z ⥤ C} {F : A ⥤ C} {G : B ⥤ C}
variable (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F)

/- Domain-style sampling for Lemma 4.31.7:
- primary domain: categorical pullbacks of functors and the induced functor on pullback categories;
- sampled owner API:
  `CategoricalPullback.Hom`,
  `CategoricalPullback.hom_ext`,
  `Limits.CatCospanTransform`,
  `two_fibre_product_map`,
  `Functor.FullyFaithful.ofFullyFaithful`;
- best owner abstraction: the source-facing functor `two_fibre_product_map α β`, whose canonical
  derived API is expressed by the owner predicates `Functor.Faithful`, `Functor.Full`,
  `Functor.FullyFaithful`, and `Functor.IsEquivalence`;
- primitive-vs-derived split: the primitive source-facing data are the comparison isomorphisms
  `α` and `β` together with the functors `K`, `L`, and `M`; the public hypotheses should live in
  the owner predicates `Functor.Full`, `Functor.Faithful`, and `Functor.IsEquivalence`, while the
  non-`Prop` witness `Functor.FullyFaithful` is derived API recovered canonically by
  `Functor.FullyFaithful.ofFullyFaithful` when needed.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma about `two_fibre_product_map α β`;
- `core/canonical`: `Functor.Faithful`, `Functor.Full`, `Functor.FullyFaithful`, and
  `Functor.IsEquivalence` applied to `two_fibre_product_map α β`;
- `bridge/view`: this file specializes those owner predicates to the functor of Lemma 4.31.6. -/

-- Proof sketch: on morphisms, `two_fibre_product_map α β` is induced by the map between the
-- defining pullback hom-sets coming from `L.map` and `K.map`; if `K` and `L` are faithful, this
-- induced map is injective.
/-- Lemma 4.31.7 (1): under the assumptions of `Lemma 4.31.6`, if `K` and `L` are faithful, then
the induced functor `X ×[Z] Y ⥤ A ×[C] B` is faithful. -/
theorem two_fibre_product_map_faithful
    [K.Faithful] [L.Faithful] :
    (two_fibre_product_map α β).Faithful where
  map_injective {P Q} f g h := by
    apply hom_ext
    · exact L.map_injective (congrArg Hom.fst h)
    · exact K.map_injective (congrArg Hom.snd h)

private theorem two_fibre_product_map_preimage_w
    [K.Full] [L.Full] {P Q : H ⊡ I}
    (f : (two_fibre_product_map α β).obj P ⟶ (two_fibre_product_map α β).obj Q) :
    M.map (H.map (L.preimage f.fst)) ≫ M.map Q.iso.hom =
      M.map P.iso.hom ≫ M.map (I.map (K.preimage f.snd)) := by
  let lhs := M.map (H.map (L.preimage f.fst)) ≫ M.map Q.iso.hom
  let rhs := M.map P.iso.hom ≫ M.map (I.map (K.preimage f.snd))
  -- Move the target compatibility relation back across the comparison isomorphisms.
  have hβ :=
    (β.inv.naturality_assoc (L.preimage f.fst) (M.map Q.iso.hom ≫ α.inv.app Q.snd)).symm
  simp only [Functor.comp_map, L.map_preimage] at hβ
  have hα := α.inv.naturality_assoc (K.preimage f.snd) (𝟙 _)
  simp only [Functor.comp_map, K.map_preimage, Category.comp_id] at hα
  have hα' := congrArg (fun k ↦ β.inv.app P.fst ≫ M.map P.iso.hom ≫ k) hα
  have h₁ :
      β.inv.app P.fst ≫ lhs ≫ α.inv.app Q.snd =
        F.map f.fst ≫ β.inv.app Q.fst ≫ M.map Q.iso.hom ≫ α.inv.app Q.snd := by
    simpa [lhs, Category.assoc] using hβ
  have h₂ :
      F.map f.fst ≫ β.inv.app Q.fst ≫ M.map Q.iso.hom ≫ α.inv.app Q.snd =
        β.inv.app P.fst ≫ M.map P.iso.hom ≫ α.inv.app P.snd ≫ G.map f.snd := by
    simpa [two_fibre_product_map_obj_iso_hom, Category.assoc] using f.w
  have h₃ :
      β.inv.app P.fst ≫ rhs ≫ α.inv.app Q.snd =
        β.inv.app P.fst ≫ M.map P.iso.hom ≫ α.inv.app P.snd ≫ G.map f.snd := by
    simpa [rhs, Category.assoc] using hα'
  have h' : β.inv.app P.fst ≫ lhs ≫ α.inv.app Q.snd = β.inv.app P.fst ≫ rhs ≫ α.inv.app Q.snd :=
    h₁.trans (h₂.trans h₃.symm)
  have h'' : β.inv.app P.fst ≫ lhs = β.inv.app P.fst ≫ rhs := by
    exact
      (Iso.cancel_iso_hom_right _ _ (α.symm.app Q.snd)).1
        (by simpa [Category.assoc] using h')
  exact
    (Iso.cancel_iso_hom_left (β.symm.app P.fst) _ _).1
      (by simpa [lhs, rhs, Category.assoc] using h'')

theorem two_fibre_product_map_full
    [K.Full] [L.Full] [M.Faithful] :
    (two_fibre_product_map α β).Full := by
  refine ⟨?_⟩
  intro P Q f
  have hw :
      H.map (L.preimage f.fst) ≫ Q.iso.hom =
        P.iso.hom ≫ I.map (K.preimage f.snd) := by
    apply M.map_injective
    simpa using two_fibre_product_map_preimage_w α β f
  refine ⟨⟨L.preimage f.fst, K.preimage f.snd, hw⟩, ?_⟩
  ext <;> simp [two_fibre_product_map]

attribute [local instance] two_fibre_product_map_faithful two_fibre_product_map_full

-- Proof sketch: the map on morphisms is the pullback of the hom-set maps induced by `L` and `K`;
-- full faithfulness of `K` and `L` gives surjectivity on the outer hom-sets, and faithfulness of
-- `M` ensures the chosen lifts satisfy the required compatibility over the middle hom-set.
/-- Lemma 4.31.7 (2): if `K` and `L` are full and faithful, and `M` is faithful, then the induced
functor `X ×[Z] Y ⥤ A ×[C] B` is fully faithful. -/
noncomputable abbrev two_fibre_product_map_fullyFaithful
    [K.Full] [K.Faithful] [L.Full] [L.Faithful] [M.Faithful] :
    (two_fibre_product_map α β).FullyFaithful :=
  .ofFullyFaithful (two_fibre_product_map α β)

-- Proof sketch: apply the canonical `map_bijective` field of the bundled fully faithful witness
-- for `two_fibre_product_map α β`.
/-- The fully faithful `2`-fibre product map induces bijections on all hom-sets. -/
theorem two_fibre_product_map_fullyFaithful_map_bijective
    [K.Full] [K.Faithful] [L.Full] [L.Faithful] [M.Faithful] (P Q : H ⊡ I) :
    Function.Bijective
      ((two_fibre_product_map α β).map :
        (P ⟶ Q) → ((two_fibre_product_map α β).obj P ⟶ (two_fibre_product_map α β).obj Q)) := by
  -- The bundled fully faithful witness already records bijectivity on every hom-set.
  simpa using (two_fibre_product_map_fullyFaithful α β).map_bijective P Q

private noncomputable def two_fibre_product_map_preimage
    [K.IsEquivalence] [L.IsEquivalence] [M.Full] [M.Faithful] (P : F ⊡ G) :
    H ⊡ I where
  fst := L.objPreimage P.fst
  snd := K.objPreimage P.snd
  iso :=
    M.preimageIso <|
      β.app (L.objPreimage P.fst) ≪≫
        F.mapIso (L.objObjPreimageIso P.fst) ≪≫
        P.iso ≪≫
        G.mapIso (K.objObjPreimageIso P.snd).symm ≪≫
        α.app (K.objPreimage P.snd)

private theorem two_fibre_product_map_preimage_hom
    [K.IsEquivalence] [L.IsEquivalence] [M.Full] [M.Faithful] (P : F ⊡ G) :
    F.map (L.objObjPreimageIso P.fst).hom ≫ P.iso.hom =
      ((two_fibre_product_map α β).obj (two_fibre_product_map_preimage α β P)).iso.hom ≫
        G.map (K.objObjPreimageIso P.snd).hom := by
  -- Expand the chosen `M`-preimage iso so the inserted comparison isomorphisms become visible.
  suffices hmain :
      F.map (L.objObjPreimageIso P.fst).hom ≫ P.iso.hom =
        β.inv.app (L.objPreimage P.fst) ≫
          β.hom.app (L.objPreimage P.fst) ≫
            F.map (L.objObjPreimageIso P.fst).hom ≫
              P.iso.hom ≫
                G.map (K.objObjPreimageIso P.snd).inv ≫
                  α.hom.app (K.objPreimage P.snd) ≫
                    α.inv.app (K.objPreimage P.snd) ≫
                      G.map (K.objObjPreimageIso P.snd).hom by
    simpa [two_fibre_product_map_preimage, two_fibre_product_map_obj_iso_hom, Category.assoc] using
      hmain
  let e := K.objObjPreimageIso P.snd
  let tail :=
    F.map (L.objObjPreimageIso P.fst).hom ≫
      P.iso.hom ≫ G.map e.inv ≫
        α.hom.app (K.objPreimage P.snd) ≫ α.inv.app (K.objPreimage P.snd) ≫ G.map e.hom
  have rhs_eq_tail :
      β.inv.app (L.objPreimage P.fst) ≫
          β.hom.app (L.objPreimage P.fst) ≫
            F.map (L.objObjPreimageIso P.fst).hom ≫
              P.iso.hom ≫
                G.map e.inv ≫
                  α.hom.app (K.objPreimage P.snd) ≫ α.inv.app (K.objPreimage P.snd) ≫ G.map e.hom =
        tail := by
    simpa [tail, Category.assoc] using β.inv_hom_id_app_assoc (L.objPreimage P.fst) tail
  have hα₀ :
      α.hom.app (K.objPreimage P.snd) ≫ α.inv.app (K.objPreimage P.snd) ≫ G.map e.hom =
        G.map e.hom := by
    simpa [Category.assoc] using α.hom_inv_id_app_assoc (K.objPreimage P.snd) (G.map e.hom)
  have hα₁ :
      G.map e.inv ≫ α.hom.app (K.objPreimage P.snd) ≫ α.inv.app (K.objPreimage P.snd) ≫ G.map e.hom =
        G.map e.inv ≫ G.map e.hom := by
    simpa [Category.assoc] using congrArg (fun k ↦ G.map e.inv ≫ k) hα₀
  have tail_step :
      F.map (L.objObjPreimageIso P.fst).hom ≫
          P.iso.hom ≫ G.map e.inv ≫ α.hom.app (K.objPreimage P.snd) ≫ α.inv.app (K.objPreimage P.snd) ≫ G.map e.hom =
        F.map (L.objObjPreimageIso P.fst).hom ≫ P.iso.hom ≫ G.map e.inv ≫ G.map e.hom := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ F.map (L.objObjPreimageIso P.fst).hom ≫ P.iso.hom ≫ k) hα₁
  have tail_eq : tail = F.map (L.objObjPreimageIso P.fst).hom ≫ P.iso.hom := by
    dsimp [tail]
    exact tail_step.trans (by rw [← G.map_comp, Iso.inv_hom_id, Functor.map_id, Category.comp_id])
  exact tail_eq.symm.trans rhs_eq_tail.symm

private theorem two_fibre_product_map_essSurj
    [K.IsEquivalence] [L.IsEquivalence] [M.Full] [M.Faithful] :
    (two_fibre_product_map α β).EssSurj := by
  refine ⟨?_⟩
  intro P
  refine ⟨two_fibre_product_map_preimage α β P, ⟨?_⟩⟩
  refine CategoricalPullback.mkIso (L.objObjPreimageIso P.fst) (K.objObjPreimageIso P.snd) ?_
  simpa using two_fibre_product_map_preimage_hom α β P

-- Proof sketch: choose quasi-inverses to `K` and `L` from the equivalence hypotheses; the fully
-- faithfulness of `M` lets one lift the comparison isomorphism in `A ×[C] B` to one in `X ×[Z] Y`,
-- yielding essential surjectivity, while the previous parts provide the faithful and fully
-- faithful input needed to upgrade the functor to an equivalence.
/-- Lemma 4.31.7 (3): under the assumptions of `Lemma 4.31.6`, if `K` and `L` are equivalences and
`M` is full and faithful, then the induced functor `X ×[Z] Y ⥤ A ×[C] B` is an equivalence. -/
theorem two_fibre_product_map_isEquivalence
    [K.IsEquivalence] [L.IsEquivalence] [M.Full] [M.Faithful] :
    (two_fibre_product_map α β).IsEquivalence := by
  let _ : (two_fibre_product_map α β).Faithful := two_fibre_product_map_faithful α β
  let _ : (two_fibre_product_map α β).Full := two_fibre_product_map_full α β
  let _ : (two_fibre_product_map α β).EssSurj := two_fibre_product_map_essSurj α β
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

end CategoryTheory
