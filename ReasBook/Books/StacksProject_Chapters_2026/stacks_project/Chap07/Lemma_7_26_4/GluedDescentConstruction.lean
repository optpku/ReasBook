module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_26_1
public import stacks_project.Chap07.Lemma_7_26_4.RestrictionCompatibility
public import stacks_project.Chap07.Lemma_7_26_4.GlueFamilies

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}

/-- Helper for Lemma 7.26.4: first pull the glued datum over `W` back along `g.left`, keeping the
indexing of the pullback cover over `V` explicit. -/
noncomputable def localized_cover_descent_pullbackDatum_restrict_source
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W) :
    (J.pseudofunctorOver (Type w)).DescentData
      (fun K : (𝒰.pullback V.hom).Arrow ↦ K.f) :=
  (Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
    (f := fun K : (𝒰.pullback W.hom).Arrow ↦ K.f)
    (p := g.left)
    (f' := fun K : (𝒰.pullback V.hom).Arrow ↦ K.f)
    (α := fun K ↦ localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K)
    (p' := fun K ↦ 𝟙 K.Y)
    (w := localized_cover_descent_pullback_arrow_map_w (J := J) (U := U) 𝒰 g)).obj
      (localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W)

/-- Helper for Lemma 7.26.4: pull `D` directly to the cover over `V`, but index by the base of
the transported pullback-cover arrow. -/
noncomputable def localized_cover_descent_pullbackDatum_restrict_direct
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W) :
    (J.pseudofunctorOver (Type w)).DescentData
      (fun K : (𝒰.pullback V.hom).Arrow ↦ K.f) :=
  (Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
    (f := fun I : 𝒰.Arrow ↦ I.f)
    (p := V.hom)
    (f' := fun K : (𝒰.pullback V.hom).Arrow ↦ K.f)
    (α := fun K ↦
      (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K).base)
    (p' := fun K ↦ 𝟙 K.Y)
    (w := localized_cover_descent_glue_restrict_hom_left_fac
      (J := J) (U := U) 𝒰 g)).obj D

/-- Helper for Lemma 7.26.4: the two-step restriction through `W` is canonically identified with
the direct pullback of `D` along `V.hom`, before replacing the transported base by `K.base`. -/
noncomputable def localized_cover_descent_pullbackDatum_restrict_source_iso
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W) :
    localized_cover_descent_pullbackDatum_restrict_source (J := J) (U := U) 𝒰 D g ≅
      localized_cover_descent_pullbackDatum_restrict_direct (J := J) (U := U) 𝒰 D g :=
  -- First compose the two pullFunctor restrictions, then erase the proof-term spelling of the
  -- resulting direct pullback comparison.
  ((Pseudofunctor.DescentData.pullFunctorCompIso
      (F := J.pseudofunctorOver (Type w))
      (f := fun I : 𝒰.Arrow ↦ I.f)
      (p := W.hom)
      (f' := fun K : (𝒰.pullback W.hom).Arrow ↦ K.f)
      (α := fun K ↦ K.base)
      (p' := fun K ↦ 𝟙 K.Y)
      (w := localized_cover_descent_pullbackDatum_w (J := J) (U := U) 𝒰 W)
      (q := g.left)
      (f'' := fun K : (𝒰.pullback V.hom).Arrow ↦ K.f)
      (β := fun K ↦ localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K)
      (q' := fun K ↦ 𝟙 K.Y)
      (w' := localized_cover_descent_pullback_arrow_map_w (J := J) (U := U) 𝒰 g)
      (r := V.hom)
      (r' := fun K ↦ 𝟙 K.Y)
      (hr := Over.w g)
      (hr' := localized_cover_descent_pullback_arrow_map_comp_id
        (J := J) (U := U) 𝒰 g)).app D).trans
    ((Pseudofunctor.DescentData.pullFunctorIso
      (F := J.pseudofunctorOver (Type w))
      (f := fun I : 𝒰.Arrow ↦ I.f)
      (p := V.hom)
      (f' := fun K : (𝒰.pullback V.hom).Arrow ↦ K.f)
      (α := fun K ↦
        (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K).base)
      (p' := fun K ↦ 𝟙 K.Y)
      (w := localized_cover_descent_glue_restrict_hom_left_fac
        (J := J) (U := U) 𝒰 g)
      (β := fun K ↦
        (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K).base)
      (p'' := fun K ↦ 𝟙 K.Y)
      (w' := localized_cover_descent_glue_restrict_hom_left_fac
        (J := J) (U := U) 𝒰 g)).app D)

/-- Helper for Lemma 7.26.4: replacing the transported base of a pullback-cover arrow by its
canonical base identifies the direct restriction datum with the ordinary pullback datum over
`V`. -/
noncomputable def localized_cover_descent_pullbackDatum_restrict_direct_iso
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W) :
    localized_cover_descent_pullbackDatum_restrict_direct (J := J) (U := U) 𝒰 D g ≅
      localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D V :=
  -- The transported arrow has the same base as `K`, so `pullFunctorIso` reindexes the direct
  -- datum to the canonical pullback datum over `V`.
  (Pseudofunctor.DescentData.pullFunctorIso
    (F := J.pseudofunctorOver (Type w))
    (f := fun I : 𝒰.Arrow ↦ I.f)
    (p := V.hom)
    (f' := fun K : (𝒰.pullback V.hom).Arrow ↦ K.f)
    (α := fun K ↦
      (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K).base)
    (p' := fun K ↦ 𝟙 K.Y)
    (w := localized_cover_descent_glue_restrict_hom_left_fac
      (J := J) (U := U) 𝒰 g)
    (β := fun K ↦ K.base)
    (p'' := fun K ↦ 𝟙 K.Y)
    (w' := localized_cover_descent_pullbackDatum_w (J := J) (U := U) 𝒰 V)).app D

/-- Helper for Lemma 7.26.4: the canonical descent-data comparison from the pullback of the
`W`-datum along `g` to the ordinary pullback datum over `V`. -/
noncomputable def localized_cover_descent_pullbackDatum_restrict_iso
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W) :
    localized_cover_descent_pullbackDatum_restrict_source (J := J) (U := U) 𝒰 D g ≅
      localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D V :=
  localized_cover_descent_pullbackDatum_restrict_source_iso (J := J) (U := U) 𝒰 D g ≪≫
    localized_cover_descent_pullbackDatum_restrict_direct_iso (J := J) (U := U) 𝒰 D g

/-- Helper for Lemma 7.26.4: terminal sections of an arbitrary descent datum over a cover are
compatible when the two restrictions to every overlap agree after applying the datum's transition
map. This abstracts the compatibility shape away from the concrete pulled-back datum. -/
def localized_cover_descent_terminalCompatible
    {S : C}
    (𝒱 : J.Cover S)
    (P : (J.pseudofunctorOver (Type w)).DescentData (fun K : 𝒱.Arrow ↦ K.f))
    (s : ∀ K : 𝒱.Arrow,
      (((P.obj K).1.obj (Opposite.op (Over.mk (𝟙 K.Y)))))) : Prop :=
  ∀ R : 𝒱.Relation,
    (P.hom (R.r.g₁ ≫ R.fst.f) R.r.g₁ R.r.g₂ rfl R.r.w.symm).hom.app
        (Opposite.op (Over.mk (𝟙 R.r.Z)))
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := R.r.g₁) (M := P.obj R.fst)).symm
          (((P.obj R.fst).1.map (Over.homMk R.r.g₁).op) (s R.fst))) =
      cast
        (localized_cover_descent_overMap_terminal_section_eq
          (J := J) (f := R.r.g₂) (M := P.obj R.snd)).symm
        (((P.obj R.snd).1.map (Over.homMk R.r.g₂).op) (s R.snd))

/-- Helper for Lemma 7.26.4: for the ordinary pulled-back datum, the generic terminal-section
compatibility predicate is exactly the concrete glued-family predicate already used in the
source-facing construction. -/
theorem localized_cover_descent_terminalCompatible_pullbackDatum_iff
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (V : Over U)
    (s : localized_cover_descent_glue_family (J := J) (U := U) 𝒰 D V) :
    localized_cover_descent_terminalCompatible (J := J) (𝒰.pullback V.hom)
      (localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D V) s ↔
      localized_cover_descent_glue_compatible (J := J) (U := U) 𝒰 D V s := by
  -- Both predicates use the same overlap equation; the concrete predicate names the terminal
  -- section cast through the pulled-back datum's specialized normalization lemma.
  dsimp [localized_cover_descent_terminalCompatible, localized_cover_descent_glue_compatible]
  constructor
  · intro h R
    simpa [localized_cover_descent_pullbackDatum_section_eq] using h R
  · intro h R
    simpa [localized_cover_descent_pullbackDatum_section_eq] using h R

/-- Helper for Lemma 7.26.4: pulling a sheaf morphism back along a slice map commutes with the
named cast from the pulled-back terminal object to the ordinary section over `Over.mk f`. -/
theorem localized_cover_descent_overMap_hom_terminal_cast_naturality
    {X Y : C}
    (f : X ⟶ Y)
    {M N : Sheaf (J.over Y) (Type w)}
    (φ : M ⟶ N)
    (x : M.1.obj (Opposite.op (Over.mk (𝟙 Y)))) :
    ((J.overMapPullback (Type w) f).map φ).hom.app (Opposite.op (Over.mk (𝟙 X)))
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := f) (M := M)).symm
          (((M.1).map
            (show Over.mk f ⟶ Over.mk (𝟙 Y) from Over.homMk f).op) x)) =
      cast
        (localized_cover_descent_overMap_terminal_section_eq
          (J := J) (f := f) (M := N)).symm
        (((N.1).map
          (show Over.mk f ⟶ Over.mk (𝟙 Y) from Over.homMk f).op)
          ((φ.hom.app (Opposite.op (Over.mk (𝟙 Y)))) x)) := by
  -- The cast only identifies the pulled-back terminal object with `Over.mk f`; after unfolding it,
  -- the claim is exactly naturality of the underlying presheaf morphism along `Over.homMk f`.
  have hObj : (Over.map f).obj (Over.mk (𝟙 X)) = Over.mk f :=
    localized_cover_descent_overMap_terminal_obj f
  have hLeft :
      HEq
        (((J.overMapPullback (Type w) f).map φ).hom.app (Opposite.op (Over.mk (𝟙 X)))
          (cast
            (localized_cover_descent_overMap_terminal_section_eq
              (J := J) (f := f) (M := M)).symm
            (((M.1).map
              (show Over.mk f ⟶ Over.mk (𝟙 Y) from Over.homMk f).op) x)))
        (φ.hom.app (Opposite.op (Over.mk f))
          (((M.1).map
            (show Over.mk f ⟶ Over.mk (𝟙 Y) from Over.homMk f).op) x)) := by
    simpa [GrothendieckTopology.overMapPullback] using
      dep_app_heq
        (fun T (y : M.1.obj (Opposite.op T)) ↦ φ.hom.app (Opposite.op T) y)
        hObj
        (cast_heq _ _)
  have hNat :=
    congrFun
      (φ.hom.naturality
        (show Over.mk f ⟶ Over.mk (𝟙 Y) from Over.homMk f).op) x
  have hRight :
      HEq
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := f) (M := N)).symm
          (((N.1).map
            (show Over.mk f ⟶ Over.mk (𝟙 Y) from Over.homMk f).op)
            ((φ.hom.app (Opposite.op (Over.mk (𝟙 Y)))) x)))
        (((N.1).map
          (show Over.mk f ⟶ Over.mk (𝟙 Y) from Over.homMk f).op)
          ((φ.hom.app (Opposite.op (Over.mk (𝟙 Y)))) x)) :=
    cast_heq _ _
  exact eq_of_heq (hLeft.trans ((heq_of_eq hNat).trans hRight.symm))

/-- Helper for Lemma 7.26.4: a descent-data morphism carries compatible terminal sections to
compatible terminal sections. -/
theorem localized_cover_descent_terminalCompatible_map
    {S : C}
    (𝒱 : J.Cover S)
    (P Q : (J.pseudofunctorOver (Type w)).DescentData (fun K : 𝒱.Arrow ↦ K.f))
    (φ : P ⟶ Q)
    (s : ∀ K : 𝒱.Arrow,
      (((P.obj K).1.obj (Opposite.op (Over.mk (𝟙 K.Y))))))
    (hs : localized_cover_descent_terminalCompatible (J := J) 𝒱 P s) :
    localized_cover_descent_terminalCompatible (J := J) 𝒱 Q
      (fun K ↦ (φ.hom K).hom.app (Opposite.op (Over.mk (𝟙 K.Y))) (s K)) := by
  -- Route correction: first move component morphisms through the terminal-section casts, then
  -- apply the descent-data morphism square at the normalized source section.
  intro R
  let x₁ :=
    cast
      (localized_cover_descent_overMap_terminal_section_eq
        (J := J) (f := R.r.g₁) (M := P.obj R.fst)).symm
      (((P.obj R.fst).1.map (Over.homMk R.r.g₁).op) (s R.fst))
  let x₂ :=
    cast
      (localized_cover_descent_overMap_terminal_section_eq
        (J := J) (f := R.r.g₂) (M := P.obj R.snd)).symm
      (((P.obj R.snd).1.map (Over.homMk R.r.g₂).op) (s R.snd))
  have hleft :
      ((J.overMapPullback (Type w) R.r.g₁).map (φ.hom R.fst)).hom.app
          (Opposite.op (Over.mk (𝟙 R.r.Z))) x₁ =
        cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := R.r.g₁) (M := Q.obj R.fst)).symm
          (((Q.obj R.fst).1.map (Over.homMk R.r.g₁).op)
            ((φ.hom R.fst).hom.app (Opposite.op (Over.mk (𝟙 R.fst.Y))) (s R.fst))) := by
    -- Naturality of the component morphism supplies the first terminal-cast transport.
    simpa [x₁] using
      localized_cover_descent_overMap_hom_terminal_cast_naturality
        (J := J) (f := R.r.g₁) (φ := φ.hom R.fst) (x := s R.fst)
  have hright :
      ((J.overMapPullback (Type w) R.r.g₂).map (φ.hom R.snd)).hom.app
          (Opposite.op (Over.mk (𝟙 R.r.Z))) x₂ =
        cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := R.r.g₂) (M := Q.obj R.snd)).symm
          (((Q.obj R.snd).1.map (Over.homMk R.r.g₂).op)
            ((φ.hom R.snd).hom.app (Opposite.op (Over.mk (𝟙 R.snd.Y))) (s R.snd))) := by
    -- The same terminal-cast transport applies at the second cover member.
    simpa [x₂] using
      localized_cover_descent_overMap_hom_terminal_cast_naturality
        (J := J) (f := R.r.g₂) (φ := φ.hom R.snd) (x := s R.snd)
  have hcompat :
      (P.hom (R.r.g₁ ≫ R.fst.f) R.r.g₁ R.r.g₂ rfl R.r.w.symm).hom.app
          (Opposite.op (Over.mk (𝟙 R.r.Z))) x₁ = x₂ := by
    -- This is the original compatibility equation for the source terminal sections.
    simpa [x₁, x₂, localized_cover_descent_terminalCompatible] using hs R
  have hcomm :
      (Q.hom (R.r.g₁ ≫ R.fst.f) R.r.g₁ R.r.g₂ rfl R.r.w.symm).hom.app
          (Opposite.op (Over.mk (𝟙 R.r.Z)))
          (((J.overMapPullback (Type w) R.r.g₁).map (φ.hom R.fst)).hom.app
            (Opposite.op (Over.mk (𝟙 R.r.Z))) x₁) =
        ((J.overMapPullback (Type w) R.r.g₂).map (φ.hom R.snd)).hom.app
          (Opposite.op (Over.mk (𝟙 R.r.Z)))
          ((P.hom (R.r.g₁ ≫ R.fst.f) R.r.g₁ R.r.g₂ rfl R.r.w.symm).hom.app
            (Opposite.op (Over.mk (𝟙 R.r.Z))) x₁) := by
    -- Apply the descent-data morphism square to the normalized first source section.
    simpa [Category.assoc] using
      congrFun
        (congrArg (fun η => η.hom.app (Opposite.op (Over.mk (𝟙 R.r.Z))))
          (φ.comm (R.r.g₁ ≫ R.fst.f) R.r.g₁ R.r.g₂ rfl R.r.w.symm))
        x₁
  calc
    (Q.hom (R.r.g₁ ≫ R.fst.f) R.r.g₁ R.r.g₂ rfl R.r.w.symm).hom.app
        (Opposite.op (Over.mk (𝟙 R.r.Z)))
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := R.r.g₁) (M := Q.obj R.fst)).symm
          (((Q.obj R.fst).1.map (Over.homMk R.r.g₁).op)
            ((φ.hom R.fst).hom.app (Opposite.op (Over.mk (𝟙 R.fst.Y))) (s R.fst)))) =
      (Q.hom (R.r.g₁ ≫ R.fst.f) R.r.g₁ R.r.g₂ rfl R.r.w.symm).hom.app
        (Opposite.op (Over.mk (𝟙 R.r.Z)))
        (((J.overMapPullback (Type w) R.r.g₁).map (φ.hom R.fst)).hom.app
          (Opposite.op (Over.mk (𝟙 R.r.Z))) x₁) :=
        congrArg
          ((Q.hom (R.r.g₁ ≫ R.fst.f) R.r.g₁ R.r.g₂ rfl R.r.w.symm).hom.app
            (Opposite.op (Over.mk (𝟙 R.r.Z)))) hleft.symm
    _ = ((J.overMapPullback (Type w) R.r.g₂).map (φ.hom R.snd)).hom.app
          (Opposite.op (Over.mk (𝟙 R.r.Z)))
          ((P.hom (R.r.g₁ ≫ R.fst.f) R.r.g₁ R.r.g₂ rfl R.r.w.symm).hom.app
            (Opposite.op (Over.mk (𝟙 R.r.Z))) x₁) := hcomm
    _ = ((J.overMapPullback (Type w) R.r.g₂).map (φ.hom R.snd)).hom.app
          (Opposite.op (Over.mk (𝟙 R.r.Z))) x₂ := by
        rw [hcompat]
    _ = cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := R.r.g₂) (M := Q.obj R.snd)).symm
          (((Q.obj R.snd).1.map (Over.homMk R.r.g₂).op)
            ((φ.hom R.snd).hom.app (Opposite.op (Over.mk (𝟙 R.snd.Y))) (s R.snd))) := hright
end

end GrothendieckTopology
end CategoryTheory
