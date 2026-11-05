module

public import stacks_project.Chap07.Lemma_7_26_4.RestrictionTerminalNormalize

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}

/-- Helper for Lemma 7.26.4: transporting a pullback-cover arrow along a slice morphism does
not change the terminal-section type of the pulled-back descent datum. -/
theorem localized_cover_descent_pullbackDatum_arrowMap_terminal_eq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (K : (𝒰.pullback V.hom).Arrow) :
    (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
        (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K)).1.obj
          (Opposite.op (Over.mk (𝟙 K.Y)))) =
      (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D V).obj K).1.obj
          (Opposite.op (Over.mk (𝟙 K.Y)))) := by
  cases K with
  | mk Y f hf =>
      dsimp [localized_cover_descent_pullbackDatum,
        localized_cover_descent_pullback_arrow_map,
        GrothendieckTopology.Cover.Arrow.base]
      congr 3
      ext
      · rfl
      · exact heq_of_eq <|
          (Category.assoc f g.left W.hom).trans
            (congrArg (fun h => f ≫ h) (Over.w g))

/-- Helper for Lemma 7.26.4: a compatible family over `W/U` restricts along a slice morphism
`g : V ⟶ W` to a terminal section over each member of the pulled-back cover above `V`. -/
noncomputable def localized_cover_descent_glue_restrict_section
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D W)
    (K : (𝒰.pullback V.hom).Arrow) :
    (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D V).obj K).1.obj
      (Opposite.op (Over.mk (𝟙 K.Y)))) :=
  cast
    (localized_cover_descent_pullbackDatum_arrowMap_terminal_eq
      (J := J) (U := U) 𝒰 D g K)
    (s.1 (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K))

/-- Helper for Lemma 7.26.4: the restricted terminal section is just the source terminal section
at the transported pullback-cover arrow, viewed through the named terminal-section cast. -/
theorem localized_cover_descent_glue_restrict_section_heq_source
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D W)
    (K : (𝒰.pullback V.hom).Arrow) :
    HEq
      (localized_cover_descent_glue_restrict_section (J := J) (U := U) 𝒰 D g s K)
      (s.1 (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K)) := by
  unfold localized_cover_descent_glue_restrict_section
  exact cast_heq _ _

/-- Helper for Lemma 7.26.4: restricting a transported terminal section commutes
heterogeneously with restriction to a smaller overlap object. -/
theorem localized_cover_descent_glue_restrict_section_map_heq_source
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D W)
    (K : (𝒰.pullback V.hom).Arrow)
    {Z : C}
    (a : Z ⟶ K.Y) :
    HEq
      (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
          (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K)).1.map
        (show Over.mk a ⟶ Over.mk (𝟙 K.Y) from Over.homMk a).op
        (s.1 (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K)))
      (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D V).obj K).1.map
        (show Over.mk a ⟶ Over.mk (𝟙 K.Y) from Over.homMk a).op
        (localized_cover_descent_glue_restrict_section (J := J) (U := U) 𝒰 D g s K)) := by
  cases K with
  | mk Y f hf =>
      have hbase :
          (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g
            ({ Y := Y, f := f, hf := hf } : (𝒰.pullback V.hom).Arrow)).base =
            ({ Y := Y, f := f, hf := hf } : (𝒰.pullback V.hom).Arrow).base :=
        localized_cover_descent_pullback_arrow_map_base
          (J := J) (U := U) 𝒰 g ({ Y := Y, f := f, hf := hf } : (𝒰.pullback V.hom).Arrow)
      dsimp [localized_cover_descent_glue_restrict_section,
        localized_cover_descent_pullbackDatum,
        localized_cover_descent_pullback_arrow_map,
        GrothendieckTopology.Cover.Arrow.base]
      congr!
      · exact eq_of_heq (by
          simpa [localized_cover_descent_pullback_arrow_map,
            GrothendieckTopology.Cover.Arrow.base] using
            congr_arg_heq D.obj hbase)
      · exact (cast_heq _ _).symm

/-- Helper for Lemma 7.26.4: restricting a terminal section along the identity slice morphism
recovers the original terminal section. -/
theorem localized_cover_descent_glue_restrict_section_id
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (V : Over U)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D V)
    (K : (𝒰.pullback V.hom).Arrow) :
    localized_cover_descent_glue_restrict_section (J := J) (U := U) 𝒰 D (𝟙 V) s K =
      s.1 K := by
  let K' := localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 (𝟙 V) K
  have hK : K' = K :=
    localized_cover_descent_pullback_arrow_map_id (J := J) (U := U) 𝒰 V K
  unfold localized_cover_descent_glue_restrict_section
  change cast _ (s.1 K') = s.1 K
  rw [cast_eq_iff_heq]
  exact hK.rec HEq.rfl

/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the source-side restriction datum
has a canonical terminal section obtained from the transported `W`-section. -/
noncomputable def localized_cover_descent_pullbackDatum_restrict_source_terminal_section
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D W)
    (K : (𝒰.pullback V.hom).Arrow) :
    (((localized_cover_descent_pullbackDatum_restrict_source
      (J := J) (U := U) 𝒰 D g).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y)))) :=
  cast
    (localized_cover_descent_overMap_terminal_section_eq (J := J) (f := 𝟙 K.Y)
      (M := (localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
        (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K))).symm
    (s.1 (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K))

/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the normalized source-side terminal
section is heterogeneously equal to the transported `W`-section. -/
theorem localized_cover_descent_pullbackDatum_restrict_source_terminal_section_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D W)
    (K : (𝒰.pullback V.hom).Arrow) :
    HEq
      (localized_cover_descent_pullbackDatum_restrict_source_terminal_section
        (J := J) (U := U) 𝒰 D g s K)
      (s.1 (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K)) := by
  unfold localized_cover_descent_pullbackDatum_restrict_source_terminal_section
  exact cast_heq _ _

/-- Helper for Lemma 7.26.4: the source-restriction terminal section and the concrete restricted
glued section are the same transported `W`-section, up to their two canonical terminal casts. -/
theorem localized_cover_descent_pullbackDatum_restrict_source_terminal_section_heq_glue_restrict
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D W)
    (K : (𝒰.pullback V.hom).Arrow) :
    HEq
      (localized_cover_descent_pullbackDatum_restrict_source_terminal_section
        (J := J) (U := U) 𝒰 D g s K)
      (localized_cover_descent_glue_restrict_section (J := J) (U := U) 𝒰 D g s K) := by
  exact
    (localized_cover_descent_pullbackDatum_restrict_source_terminal_section_heq
      (J := J) (U := U) 𝒰 D g s K).trans
      (localized_cover_descent_glue_restrict_section_heq_source
        (J := J) (U := U) 𝒰 D g s K).symm

/-- Helper for Lemma 7.26.4: the source terminal section over the first projection of a transported
relation is the corresponding `W`-section at that packaged projection. -/
theorem localized_cover_descent_restrict_source_terminal_section_fst_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D W)
    (R : (𝒰.pullback V.hom).Relation) :
    HEq
      (localized_cover_descent_pullbackDatum_restrict_source_terminal_section
        (J := J) (U := U) 𝒰 D g s R.fst)
      (s.1 (localized_cover_descent_pullback_relation_cover_map
        (J := J) (U := U) 𝒰 g R).fst) := by
  refine (localized_cover_descent_pullbackDatum_restrict_source_terminal_section_heq
    (J := J) (U := U) 𝒰 D g s R.fst).trans ?_
  exact (localized_cover_descent_pullback_relation_cover_map_fst_apply_heq
    (J := J) (U := U) 𝒰 g R s.1).symm

/-- Helper for Lemma 7.26.4: the source terminal section over the second projection of a transported
relation is the corresponding `W`-section at that packaged projection. -/
theorem localized_cover_descent_restrict_source_terminal_section_snd_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D W)
    (R : (𝒰.pullback V.hom).Relation) :
    HEq
      (localized_cover_descent_pullbackDatum_restrict_source_terminal_section
        (J := J) (U := U) 𝒰 D g s R.snd)
      (s.1 (localized_cover_descent_pullback_relation_cover_map
        (J := J) (U := U) 𝒰 g R).snd) := by
  refine (localized_cover_descent_pullbackDatum_restrict_source_terminal_section_heq
    (J := J) (U := U) 𝒰 D g s R.snd).trans ?_
  exact (localized_cover_descent_pullback_relation_cover_map_snd_apply_heq
    (J := J) (U := U) 𝒰 g R s.1).symm

/-- Helper for Lemma 7.26.4: a sheaf map is stable under replacing the source and target
objects in an over category by propositionally equal objects. -/
theorem sheaf_map_heq_of_over_source_target_eq
    {Y : C}
    (M : Sheaf (J.over Y) (Type w))
    {A₁ A₂ B₁ B₂ : Over Y}
    (hA : A₁ = A₂)
    (hB : B₁ = B₂)
    (m₁ : A₁ ⟶ B₁)
    (m₂ : A₂ ⟶ B₂)
    (hmleft : HEq m₁.left m₂.left)
    {x₁ : M.1.obj (Opposite.op B₁)}
    {x₂ : M.1.obj (Opposite.op B₂)}
    (hx : HEq x₁ x₂) :
    HEq (M.1.map m₁.op x₁) (M.1.map m₂.op x₂) := by
  subst hA
  subst hB
  exact heq_of_eq (by
    have hm : m₁ = m₂ := Over.OverMorphism.ext (eq_of_heq hmleft)
    subst hm
    rw [eq_of_heq hx])

/-- Helper for Lemma 7.26.4: applying an identity-over-map restriction to a normalized
source-side terminal section gives the same section as the ordinary overlap restriction. -/
theorem localized_cover_descent_pullbackDatum_restrict_source_terminal_section_map_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D W)
    (K : (𝒰.pullback V.hom).Arrow)
    {Z : C}
    (a : Z ⟶ K.Y) :
    HEq
      (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
          (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K)).1.map
        ((Over.map (𝟙 K.Y)).map
          (show Over.mk a ⟶ Over.mk (𝟙 K.Y) from Over.homMk a)).op
        (localized_cover_descent_pullbackDatum_restrict_source_terminal_section
          (J := J) (U := U) 𝒰 D g s K))
      (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
          (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K)).1.map
        (show Over.mk a ⟶ Over.mk (𝟙 K.Y) from Over.homMk a).op
        (s.1 (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K))) := by
  let M := (localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
    (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K)
  have hA : (Over.map (𝟙 K.Y)).obj (Over.mk a) = Over.mk a :=
    congrArg Over.mk (Category.comp_id a)
  have hB : (Over.map (𝟙 K.Y)).obj (Over.mk (𝟙 K.Y)) = Over.mk (𝟙 K.Y) :=
    congrArg Over.mk (Category.comp_id (𝟙 K.Y))
  exact sheaf_map_heq_of_over_source_target_eq (J := J) M hA hB _ _ (by simp)
    (localized_cover_descent_pullbackDatum_restrict_source_terminal_section_heq
      (J := J) (U := U) 𝒰 D g s K)

/-- Helper for Lemma 7.26.4: restricting the first source terminal section along the overlap map
matches the first transported relation section. -/
theorem localized_cover_descent_restrict_source_terminal_section_map_fst_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D W)
    (R : (𝒰.pullback V.hom).Relation) :
    let RW := localized_cover_descent_pullback_relation_cover_map (J := J) (U := U) 𝒰 g R
    HEq
      (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
          (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g R.fst)).1.map
        ((Over.map (𝟙 R.fst.Y)).map
          (show Over.mk R.r.g₁ ⟶ Over.mk (𝟙 R.fst.Y) from Over.homMk R.r.g₁)).op
        (localized_cover_descent_pullbackDatum_restrict_source_terminal_section
          (J := J) (U := U) 𝒰 D g s R.fst))
      (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj RW.fst).1.map
        (show Over.mk RW.r.g₁ ⟶ Over.mk (𝟙 RW.fst.Y) from Over.homMk RW.r.g₁).op
        (s.1 RW.fst)) := by
  intro RW
  simpa [RW, localized_cover_descent_pullback_relation_cover_map_fst,
    localized_cover_descent_pullback_relation_cover_map_g₁] using
    (localized_cover_descent_pullbackDatum_restrict_source_terminal_section_map_heq
      (J := J) (U := U) 𝒰 D g s R.fst R.r.g₁)

/-- Helper for Lemma 7.26.4: restricting the second source terminal section along the overlap map
matches the second transported relation section. -/
theorem localized_cover_descent_restrict_source_terminal_section_map_snd_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D W)
    (R : (𝒰.pullback V.hom).Relation) :
    let RW := localized_cover_descent_pullback_relation_cover_map (J := J) (U := U) 𝒰 g R
    HEq
      (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
          (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g R.snd)).1.map
        ((Over.map (𝟙 R.snd.Y)).map
          (show Over.mk R.r.g₂ ⟶ Over.mk (𝟙 R.snd.Y) from Over.homMk R.r.g₂)).op
        (localized_cover_descent_pullbackDatum_restrict_source_terminal_section
          (J := J) (U := U) 𝒰 D g s R.snd))
      (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj RW.snd).1.map
        (show Over.mk RW.r.g₂ ⟶ Over.mk (𝟙 RW.snd.Y) from Over.homMk RW.r.g₂).op
        (s.1 RW.snd)) := by
  intro RW
  simpa [RW, localized_cover_descent_pullback_relation_cover_map_snd,
    localized_cover_descent_pullback_relation_cover_map_g₂] using
    (localized_cover_descent_pullbackDatum_restrict_source_terminal_section_map_heq
      (J := J) (U := U) 𝒰 D g s R.snd R.r.g₂)

/-- Helper for Lemma 7.26.4: the source-restriction transition is the raw
`pullFunctorObjHom` transition before the owner-side `mapComp` factors are expanded. -/
theorem localized_cover_descent_restrict_source_hom_app_eq_pullFunctorObjHom
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation)
    (x :
      (((J.overMapPullback (Type w) R.r.g₁).obj
        ((localized_cover_descent_pullbackDatum_restrict_source
          (J := J) (U := U) 𝒰 D g).obj R.fst)).1.obj
        (Opposite.op (Over.mk (𝟙 R.r.Z))))) :
    (((localized_cover_descent_pullbackDatum_restrict_source
        (J := J) (U := U) 𝒰 D g).hom
        (R.r.g₁ ≫ R.fst.f) R.r.g₁ R.r.g₂ rfl R.r.w.symm).hom.app
      (Opposite.op (Over.mk (𝟙 R.r.Z))) x) =
      (Pseudofunctor.DescentData.pullFunctorObjHom
        (F := J.pseudofunctorOver (Type w))
        (f := fun K : (𝒰.pullback W.hom).Arrow ↦ K.f)
        (p := g.left)
        (f' := fun K : (𝒰.pullback V.hom).Arrow ↦ K.f)
        (α := fun K ↦ localized_cover_descent_pullback_arrow_map
          (J := J) (U := U) 𝒰 g K)
        (p' := fun K ↦ 𝟙 K.Y)
        (w := localized_cover_descent_pullback_arrow_map_w
          (J := J) (U := U) 𝒰 g)
        (localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W)
        (R.r.g₁ ≫ R.fst.f) R.r.g₁ R.r.g₂
        (hf₁ := by rfl)
        (hf₂ := by exact R.r.w.symm)).hom.app
      (Opposite.op (Over.mk (𝟙 R.r.Z))) x := by
  rfl


end

end GrothendieckTopology
end CategoryTheory
