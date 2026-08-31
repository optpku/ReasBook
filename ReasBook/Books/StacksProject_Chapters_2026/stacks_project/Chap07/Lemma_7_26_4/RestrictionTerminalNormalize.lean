module

public import stacks_project.Chap07.Lemma_7_26_4.GluedDescentConstruction

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}

/-- Helper for Lemma 7.26.4: the owner-side transition of the source restriction datum expands
to the transported `W`-side transition with the two identity pullback `mapComp'` factors exposed.
-/
theorem localized_cover_descent_restrict_source_pullFunctorObjHom_eq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    Pseudofunctor.DescentData.pullFunctorObjHom
        (F := J.pseudofunctorOver (Type w))
        (f := fun K : (𝒰.pullback W.hom).Arrow ↦ K.f)
        (p := g.left)
        (f' := fun K : (𝒰.pullback V.hom).Arrow ↦ K.f)
        (α := fun K ↦ localized_cover_descent_pullback_arrow_map
          (J := J) (U := U) 𝒰 g K)
        (p' := fun K ↦ 𝟙 K.Y)
        (w := localized_cover_descent_pullback_arrow_map_w (J := J) (U := U) 𝒰 g)
        (localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W)
        (R.r.g₁ ≫ R.fst.f) R.r.g₁ R.r.g₂
        (hf₁ := by rfl)
        (hf₂ := by exact R.r.w.symm)
      =
      ((J.pseudofunctorOver (Type w)).mapComp'
          (𝟙 R.fst.Y).op.toLoc R.r.g₁.op.toLoc R.r.g₁.op.toLoc
          (by simp)).inv.toNatTrans.app
          ((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
            (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g R.fst)) ≫
        (localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).hom
          ((localized_cover_descent_pullback_relation_cover_map
            (J := J) (U := U) 𝒰 g R).r.g₁ ≫
            (localized_cover_descent_pullback_relation_cover_map
              (J := J) (U := U) 𝒰 g R).fst.f)
          (localized_cover_descent_pullback_relation_cover_map
            (J := J) (U := U) 𝒰 g R).r.g₁
          (localized_cover_descent_pullback_relation_cover_map
            (J := J) (U := U) 𝒰 g R).r.g₂
          (by
            simpa [localized_cover_descent_pullback_relation_cover_map_g₁,
              localized_cover_descent_pullback_relation_cover_map_fst_f,
              Category.assoc])
          (by
            simpa [localized_cover_descent_pullback_relation_cover_map_g₂,
              localized_cover_descent_pullback_relation_cover_map_snd_f,
              Category.assoc] using congrArg (fun f ↦ f ≫ g.left) R.r.w.symm) ≫
        ((J.pseudofunctorOver (Type w)).mapComp'
          (𝟙 R.snd.Y).op.toLoc R.r.g₂.op.toLoc R.r.g₂.op.toLoc
          (by simp)).hom.toNatTrans.app
          ((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
            (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g R.snd)) := by
  -- `pullFunctorObjHom_eq` is applied with the source cover relation and the identity
  -- pullback legs explicit, so no default side-condition search is needed.
  simpa [localized_cover_descent_pullback_relation_cover_map_g₁,
    localized_cover_descent_pullback_relation_cover_map_g₂,
    localized_cover_descent_pullback_relation_cover_map_fst_f,
    localized_cover_descent_pullback_relation_cover_map_snd_f,
    localized_cover_descent_pullback_relation_cover_map_fst,
    localized_cover_descent_pullback_relation_cover_map_snd,
    Category.assoc] using
    (Pseudofunctor.DescentData.pullFunctorObjHom_eq
      (F := J.pseudofunctorOver (Type w))
      (f := fun K : (𝒰.pullback W.hom).Arrow ↦ K.f)
      (p := g.left)
      (f' := fun K : (𝒰.pullback V.hom).Arrow ↦ K.f)
      (α := fun K ↦ localized_cover_descent_pullback_arrow_map
        (J := J) (U := U) 𝒰 g K)
      (p' := fun K ↦ 𝟙 K.Y)
      (w := localized_cover_descent_pullback_arrow_map_w (J := J) (U := U) 𝒰 g)
      (D := localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W)
      (q := R.r.g₁ ≫ R.fst.f)
      (f₁ := R.r.g₁)
      (f₂ := R.r.g₂)
      (q' := (R.r.g₁ ≫ R.fst.f) ≫ g.left)
      (f₁' := R.r.g₁)
      (f₂' := R.r.g₂)
      (hf₁ := by rfl)
      (hf₂ := by simpa using R.r.w.symm)
      (hq' := rfl)
      (hf₁' := by exact Category.comp_id R.r.g₁)
      (hf₂' := by exact Category.comp_id R.r.g₂))

end

end GrothendieckTopology
end CategoryTheory
