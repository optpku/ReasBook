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
variable [UnivLE.{max u v, w}]

omit [UnivLE.{max u v, w}] in
theorem localized_cover_descent_reindex_presheaf_map_heq_of_eqs
    {D : Type*} [Category D] {F G : Dᵒᵖ ⥤ Type w}
    (hF : HEq F G)
    {A B A' B' : D} (hA : A = A') (hB : B = B')
    (φ : A ⟶ B) (ψ : A' ⟶ B')
    (hφ : HEq φ ψ)
    {x : F.obj (Opposite.op B)} {y : G.obj (Opposite.op B')}
    (hxy : HEq x y) :
    HEq (F.map φ.op x) (G.map ψ.op y) := by
  cases hF
  subst hA
  subst hB
  have hφ' : φ = ψ := eq_of_heq hφ
  subst hφ'
  rw [eq_of_heq hxy]

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: reindexing an over-map glued section to the normalized iterated
pullback cover does not change the terminal section after unfolding the two pullback data. -/
theorem localized_cover_descent_glue_section_to_direct
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow) :
    (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D ((Over.map I.f).obj T)).obj
        (K.map (Cover.pullbackComp 𝒰 T.hom I.f).inv)).1.obj
      (Opposite.op (Over.mk (𝟙 K.Y)))) =
    (((localized_cover_descent_pullbackDatum_over_direct_source (J := J) (U := U) 𝒰 D I T).obj K).1.obj
  (Opposite.op (Over.mk (𝟙 K.Y)))) := by
  cases T
  cases K
  dsimp [localized_cover_descent_pullbackDatum, localized_cover_descent_pullbackDatum_over_direct_source,
    Cover.pullbackComp, Cover.Arrow.map, Cover.Arrow.base]
  congr 3
  ext
  · rfl
  · exact heq_of_eq (Category.assoc _ _ _).symm

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: reindexing a normalized direct-source glued section back to the
over-map pullback cover does not change the terminal section. -/
theorem localized_cover_descent_glue_section_from_direct
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K : (𝒰.pullback ((Over.map I.f).obj T).hom).Arrow) :
    (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D ((Over.map I.f).obj T)).obj K).1.obj
      (Opposite.op (Over.mk (𝟙 K.Y)))) =
    (((localized_cover_descent_pullbackDatum_over_direct_source (J := J) (U := U) 𝒰 D I T).obj
        (K.map (Cover.pullbackComp 𝒰 T.hom I.f).hom)).1.obj
      (Opposite.op (Over.mk (𝟙 K.Y)))) := by
  cases T
  cases K
  dsimp [localized_cover_descent_pullbackDatum, localized_cover_descent_pullbackDatum_over_direct_source,
    Cover.pullbackComp, Cover.Arrow.map, Cover.Arrow.base]
  congr 3
  ext
  · rfl
  · exact heq_of_eq (Category.assoc _ _ _).symm

/-- Helper for Lemma 7.26.4: families over the direct pullback along `T.hom ≫ I.f` are equivalent
to families over the normalized iterated pullback cover. -/
noncomputable def localized_cover_descent_glue_family_overMap_equiv_direct_source
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    localized_cover_descent_glue_family (J := J) (U := U) 𝒰 D ((Over.map I.f).obj T) ≃
      localized_cover_descent_glue_direct_family_over (J := J) (U := U) 𝒰 D I T where
  toFun s K :=
    cast (localized_cover_descent_glue_section_to_direct (J := J) (U := U) 𝒰 D I T K)
      (s (K.map (Cover.pullbackComp 𝒰 T.hom I.f).inv))
  invFun t K :=
    cast (localized_cover_descent_glue_section_from_direct (J := J) (U := U) 𝒰 D I T K).symm
      (t (K.map (Cover.pullbackComp 𝒰 T.hom I.f).hom))
  left_inv s := by
    funext K
    cases T
    cases K
    dsimp [Cover.pullbackComp, Cover.Arrow.map, localized_cover_descent_pullbackDatum,
      Cover.Arrow.base]
    rw [cast_eq_iff_heq]
    refine (cast_heq _ _).trans ?_
    exact congr_arg_heq s (Cover.Arrow.ext rfl (heq_of_eq rfl))
  right_inv t := by
    funext K
    cases T
    cases K
    dsimp [Cover.pullbackComp, Cover.Arrow.map, localized_cover_descent_pullbackDatum,
      Cover.Arrow.base]
    rw [cast_eq_iff_heq]
    refine (cast_heq _ _).trans ?_
    exact congr_arg_heq t (Cover.Arrow.ext rfl (heq_of_eq rfl))

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: applying the over-map/direct-source family equivalence at a
pullback-cover arrow gives the original over-map family section at the inverse-reindexed arrow,
up to the named section cast. -/
theorem localized_cover_descent_glue_family_overMap_equiv_direct_source_apply_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s : localized_cover_descent_glue_family (J := J) (U := U) 𝒰 D ((Over.map I.f).obj T))
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow) :
    HEq
      ((localized_cover_descent_glue_family_overMap_equiv_direct_source
        (J := J) (U := U) 𝒰 D I T s) K)
      (s (K.map (Cover.pullbackComp 𝒰 T.hom I.f).inv)) := by
  unfold localized_cover_descent_glue_family_overMap_equiv_direct_source
  exact cast_heq _ _

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: applying the inverse over-map/direct-source family equivalence at an
over-map pullback-cover arrow gives the direct-source family section at the hom-reindexed arrow,
up to the named section cast. -/
theorem localized_cover_descent_glue_family_overMap_equiv_direct_source_symm_apply_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (t : localized_cover_descent_glue_direct_family_over (J := J) (U := U) 𝒰 D I T)
    (K : (𝒰.pullback ((Over.map I.f).obj T).hom).Arrow) :
    HEq
      (((localized_cover_descent_glue_family_overMap_equiv_direct_source
        (J := J) (U := U) 𝒰 D I T).symm t) K)
      (t (K.map (Cover.pullbackComp 𝒰 T.hom I.f).hom)) := by
  unfold localized_cover_descent_glue_family_overMap_equiv_direct_source
  exact cast_heq _ _

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: a relation between two normalized direct pullback arrows gives the
same left-map equality after the cover-composition equivalence is read as an over-map cover
relation. -/
theorem localized_cover_descent_overMap_direct_relation_w
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K L : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    {Z : Over T.left}
    (gi : Z ⟶ Over.mk K.f)
    (gj : Z ⟶ Over.mk L.f)
    (h :
      gi ≫ (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f) =
        gj ≫ (show Over.mk L.f ⟶ Over.mk (𝟙 T.left) from Over.homMk L.f)) :
    gi.left ≫ (K.map (Cover.pullbackComp 𝒰 T.hom I.f).inv).f =
      gj.left ≫ (L.map (Cover.pullbackComp 𝒰 T.hom I.f).inv).f := by
  simpa [Cover.pullbackComp, Cover.Arrow.map, Category.assoc] using
    congrArg (fun e ↦ e.left) h

/-- Helper for Lemma 7.26.4: a direct component-side relation can be viewed as an over-map
pullback-cover relation after applying the inverse cover-composition equivalence. -/
def localized_cover_descent_overMap_relation_of_direct
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K L : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    {Z : Over T.left}
    (gi : Z ⟶ Over.mk K.f)
    (gj : Z ⟶ Over.mk L.f)
    (h :
      gi ≫ (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f) =
        gj ≫ (show Over.mk L.f ⟶ Over.mk (𝟙 T.left) from Over.homMk L.f)) :
    (K.map (Cover.pullbackComp 𝒰 T.hom I.f).inv).Relation
      (L.map (Cover.pullbackComp 𝒰 T.hom I.f).inv) where
  Z := Z.left
  g₁ := gi.left
  g₂ := gj.left
  w := localized_cover_descent_overMap_direct_relation_w
    (J := J) (U := U) 𝒰 I T K L gi gj h

/-- Helper for Lemma 7.26.4: package the direct relation as a relation of the over-map pullback
cover, ready to be consumed by the source glued-family compatibility equation. -/
def localized_cover_descent_overMap_cover_relation_of_direct
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K L : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    {Z : Over T.left}
    (gi : Z ⟶ Over.mk K.f)
    (gj : Z ⟶ Over.mk L.f)
    (h :
      gi ≫ (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f) =
        gj ≫ (show Over.mk L.f ⟶ Over.mk (𝟙 T.left) from Over.homMk L.f)) :
    (𝒰.pullback ((Over.map I.f).obj T).hom).Relation :=
  Cover.Relation.mk'
    (localized_cover_descent_overMap_relation_of_direct
      (J := J) (U := U) 𝒰 I T K L gi gj h)

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the first projection of the over-map relation attached to a direct
relation is the inverse cover-composition reindexing of the first direct arrow. -/
theorem localized_cover_descent_overMap_cover_relation_of_direct_fst
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K L : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    {Z : Over T.left}
    (gi : Z ⟶ Over.mk K.f)
    (gj : Z ⟶ Over.mk L.f)
    (h :
      gi ≫ (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f) =
        gj ≫ (show Over.mk L.f ⟶ Over.mk (𝟙 T.left) from Over.homMk L.f)) :
    (localized_cover_descent_overMap_cover_relation_of_direct
      (J := J) (U := U) 𝒰 I T K L gi gj h).fst =
        K.map (Cover.pullbackComp 𝒰 T.hom I.f).inv := by
  rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the second projection of the over-map relation attached to a direct
relation is the inverse cover-composition reindexing of the second direct arrow. -/
theorem localized_cover_descent_overMap_cover_relation_of_direct_snd
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K L : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    {Z : Over T.left}
    (gi : Z ⟶ Over.mk K.f)
    (gj : Z ⟶ Over.mk L.f)
    (h :
      gi ≫ (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f) =
        gj ≫ (show Over.mk L.f ⟶ Over.mk (𝟙 T.left) from Over.homMk L.f)) :
    (localized_cover_descent_overMap_cover_relation_of_direct
      (J := J) (U := U) 𝒰 I T K L gi gj h).snd =
        L.map (Cover.pullbackComp 𝒰 T.hom I.f).inv := by
  rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the first over-map relation projection has the same base cover
member as the first normalized direct-source arrow. -/
theorem localized_cover_descent_overMap_cover_relation_of_direct_fst_base
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K L : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    {Z : Over T.left}
    (gi : Z ⟶ Over.mk K.f)
    (gj : Z ⟶ Over.mk L.f)
    (h :
      gi ≫ (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f) =
        gj ≫ (show Over.mk L.f ⟶ Over.mk (𝟙 T.left) from Over.homMk L.f)) :
    (localized_cover_descent_overMap_cover_relation_of_direct
      (J := J) (U := U) 𝒰 I T K L gi gj h).fst.base = K.base.base := by
  -- This is only the associativity normal form hidden by `Cover.pullbackComp`.
  cases T
  cases K
  dsimp [localized_cover_descent_overMap_cover_relation_of_direct,
    localized_cover_descent_overMap_relation_of_direct, Cover.pullbackComp, Cover.Arrow.map,
    Cover.Arrow.base]
  exact Cover.Arrow.ext rfl (heq_of_eq (Category.assoc _ _ _).symm)

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the second over-map relation projection has the same base cover
member as the second normalized direct-source arrow. -/
theorem localized_cover_descent_overMap_cover_relation_of_direct_snd_base
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K L : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    {Z : Over T.left}
    (gi : Z ⟶ Over.mk K.f)
    (gj : Z ⟶ Over.mk L.f)
    (h :
      gi ≫ (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f) =
        gj ≫ (show Over.mk L.f ⟶ Over.mk (𝟙 T.left) from Over.homMk L.f)) :
    (localized_cover_descent_overMap_cover_relation_of_direct
      (J := J) (U := U) 𝒰 I T K L gi gj h).snd.base = L.base.base := by
  -- This is the symmetric base-arrow normal form hidden by `Cover.pullbackComp`.
  cases T
  cases L
  dsimp [localized_cover_descent_overMap_cover_relation_of_direct,
    localized_cover_descent_overMap_relation_of_direct, Cover.pullbackComp, Cover.Arrow.map,
    Cover.Arrow.base]
  exact Cover.Arrow.ext rfl (heq_of_eq (Category.assoc _ _ _).symm)

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the first arrow of the over-map relation attached to a direct
relation has the expected inverse-reindexed structure map. -/
theorem localized_cover_descent_overMap_cover_relation_of_direct_fst_f
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K L : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    {Z : Over T.left}
    (gi : Z ⟶ Over.mk K.f)
    (gj : Z ⟶ Over.mk L.f)
    (h :
      gi ≫ (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f) =
        gj ≫ (show Over.mk L.f ⟶ Over.mk (𝟙 T.left) from Over.homMk L.f)) :
    HEq
      (localized_cover_descent_overMap_cover_relation_of_direct
        (J := J) (U := U) 𝒰 I T K L gi gj h).fst.f
      (K.map (Cover.pullbackComp 𝒰 T.hom I.f).inv).f := by
  exact congr_arg_heq (fun A => A.f)
    (localized_cover_descent_overMap_cover_relation_of_direct_fst
      (J := J) (U := U) 𝒰 I T K L gi gj h)

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the second arrow of the over-map relation attached to a direct
relation has the expected inverse-reindexed structure map. -/
theorem localized_cover_descent_overMap_cover_relation_of_direct_snd_f
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K L : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    {Z : Over T.left}
    (gi : Z ⟶ Over.mk K.f)
    (gj : Z ⟶ Over.mk L.f)
    (h :
      gi ≫ (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f) =
        gj ≫ (show Over.mk L.f ⟶ Over.mk (𝟙 T.left) from Over.homMk L.f)) :
    HEq
      (localized_cover_descent_overMap_cover_relation_of_direct
        (J := J) (U := U) 𝒰 I T K L gi gj h).snd.f
      (L.map (Cover.pullbackComp 𝒰 T.hom I.f).inv).f := by
  exact congr_arg_heq (fun A => A.f)
    (localized_cover_descent_overMap_cover_relation_of_direct_snd
      (J := J) (U := U) 𝒰 I T K L gi gj h)

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the overlap object of the over-map relation attached to a direct
relation is the underlying object of the direct overlap. -/
theorem localized_cover_descent_overMap_cover_relation_of_direct_Z
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K L : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    {Z : Over T.left}
    (gi : Z ⟶ Over.mk K.f)
    (gj : Z ⟶ Over.mk L.f)
    (h :
      gi ≫ (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f) =
        gj ≫ (show Over.mk L.f ⟶ Over.mk (𝟙 T.left) from Over.homMk L.f)) :
    (localized_cover_descent_overMap_cover_relation_of_direct
      (J := J) (U := U) 𝒰 I T K L gi gj h).r.Z = Z.left := by
  rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the first overlap map of the over-map relation attached to a direct
relation is the underlying map of the first direct overlap morphism. -/
theorem localized_cover_descent_overMap_cover_relation_of_direct_g₁
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K L : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    {Z : Over T.left}
    (gi : Z ⟶ Over.mk K.f)
    (gj : Z ⟶ Over.mk L.f)
    (h :
      gi ≫ (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f) =
        gj ≫ (show Over.mk L.f ⟶ Over.mk (𝟙 T.left) from Over.homMk L.f)) :
    (localized_cover_descent_overMap_cover_relation_of_direct
      (J := J) (U := U) 𝒰 I T K L gi gj h).r.g₁ = gi.left := by
  rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the second overlap map of the over-map relation attached to a direct
relation is the underlying map of the second direct overlap morphism. -/
theorem localized_cover_descent_overMap_cover_relation_of_direct_g₂
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K L : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    {Z : Over T.left}
    (gi : Z ⟶ Over.mk K.f)
    (gj : Z ⟶ Over.mk L.f)
    (h :
      gi ≫ (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f) =
        gj ≫ (show Over.mk L.f ⟶ Over.mk (𝟙 T.left) from Over.homMk L.f)) :
    (localized_cover_descent_overMap_cover_relation_of_direct
      (J := J) (U := U) 𝒰 I T K L gi gj h).r.g₂ = gj.left := by
  rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: an over-map pullback-cover relation
induces the corresponding component-side relation after reindexing by the pullback-composition
equivalence. -/
theorem localized_cover_descent_direct_relation_of_overMap_w
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (R : (𝒰.pullback ((Over.map I.f).obj T).hom).Relation) :
    let K := R.fst.map (Cover.pullbackComp 𝒰 T.hom I.f).hom
    let L := R.snd.map (Cover.pullbackComp 𝒰 T.hom I.f).hom
    let Z : Over T.left := Over.mk (R.r.g₁ ≫ R.fst.f)
    (show Z ⟶ Over.mk K.f from Over.homMk R.r.g₁) ≫
        (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f) =
      (show Z ⟶ Over.mk L.f from Over.homMk R.r.g₂ (by
        simpa [Z, K, L, Cover.pullbackComp, Cover.Arrow.map] using R.r.w.symm)) ≫
        (show Over.mk L.f ⟶ Over.mk (𝟙 T.left) from Over.homMk L.f) := by
  dsimp only
  ext
  simpa [Cover.pullbackComp, Cover.Arrow.map, Category.assoc] using R.r.w

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the underlying overlap equality of
an over-map relation after reindexing to the normalized direct-source cover. -/
theorem localized_cover_descent_direct_relation_of_overMap_w_raw
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (R : (𝒰.pullback ((Over.map I.f).obj T).hom).Relation) :
    R.r.g₁ ≫ (R.fst.map (Cover.pullbackComp 𝒰 T.hom I.f).hom).f =
      R.r.g₂ ≫ (R.snd.map (Cover.pullbackComp 𝒰 T.hom I.f).hom).f := by
  -- Read the equality of over-morphisms supplied by the over-map bridge on underlying arrows.
  have h := congrArg (fun e => e.left)
    (localized_cover_descent_direct_relation_of_overMap_w
      (J := J) (U := U) 𝒰 I T R)
  simpa [Cover.pullbackComp, Cover.Arrow.map, Category.assoc] using h

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: an over-map relation reindexed by
`Cover.pullbackComp` as a direct-source arrow relation. -/
def localized_cover_descent_direct_relation_of_overMap
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (R : (𝒰.pullback ((Over.map I.f).obj T).hom).Relation) :
    (R.fst.map (Cover.pullbackComp 𝒰 T.hom I.f).hom).Relation
      (R.snd.map (Cover.pullbackComp 𝒰 T.hom I.f).hom) where
  Z := R.r.Z
  g₁ := R.r.g₁
  g₂ := R.r.g₂
  w := localized_cover_descent_direct_relation_of_overMap_w_raw
    (J := J) (U := U) 𝒰 I T R

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: package the reindexed over-map
relation as a relation of the normalized direct-source cover. -/
def localized_cover_descent_direct_cover_relation_of_overMap
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (R : (𝒰.pullback ((Over.map I.f).obj T).hom).Relation) :
    ((𝒰.pullback I.f).pullback T.hom).Relation :=
  Cover.Relation.mk'
    (localized_cover_descent_direct_relation_of_overMap (J := J) (U := U) 𝒰 I T R)

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: reindexing an over-map relation to the direct cover and then back
recovers its first projection. -/
theorem localized_cover_descent_direct_cover_relation_of_overMap_fst_inv
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (R : (𝒰.pullback ((Over.map I.f).obj T).hom).Relation) :
    ((localized_cover_descent_direct_cover_relation_of_overMap
      (J := J) (U := U) 𝒰 I T R).fst.map
        (Cover.pullbackComp 𝒰 T.hom I.f).inv) = R.fst := by
  -- Destructure the relation so the two cover arrows differ only by the membership proof.
  cases T
  cases R
  dsimp [localized_cover_descent_direct_cover_relation_of_overMap,
    localized_cover_descent_direct_relation_of_overMap, Cover.pullbackComp, Cover.Arrow.map]
  apply Cover.Arrow.ext rfl
  exact heq_of_eq rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: reindexing an over-map relation to the direct cover and then back
recovers its second projection. -/
theorem localized_cover_descent_direct_cover_relation_of_overMap_snd_inv
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (R : (𝒰.pullback ((Over.map I.f).obj T).hom).Relation) :
    ((localized_cover_descent_direct_cover_relation_of_overMap
      (J := J) (U := U) 𝒰 I T R).snd.map
        (Cover.pullbackComp 𝒰 T.hom I.f).inv) = R.snd := by
  -- The symmetric projection has the same proof-term mismatch as the first projection.
  cases T
  cases R
  dsimp [localized_cover_descent_direct_cover_relation_of_overMap,
    localized_cover_descent_direct_relation_of_overMap, Cover.pullbackComp, Cover.Arrow.map]
  apply Cover.Arrow.ext rfl
  exact heq_of_eq rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the direct-source family obtained from an over-map family evaluates
at a reindexed over-map relation as the original family on the relation's two projections. -/
theorem localized_cover_descent_glue_family_overMap_equiv_direct_source_overMap_relation_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s : localized_cover_descent_glue_family (J := J) (U := U) 𝒰 D ((Over.map I.f).obj T))
    (R : (𝒰.pullback ((Over.map I.f).obj T).hom).Relation) :
    HEq
      ((localized_cover_descent_glue_family_overMap_equiv_direct_source
        (J := J) (U := U) 𝒰 D I T s)
        (localized_cover_descent_direct_cover_relation_of_overMap
          (J := J) (U := U) 𝒰 I T R).fst)
      (s R.fst) ∧
    HEq
      ((localized_cover_descent_glue_family_overMap_equiv_direct_source
        (J := J) (U := U) 𝒰 D I T s)
        (localized_cover_descent_direct_cover_relation_of_overMap
          (J := J) (U := U) 𝒰 I T R).snd)
      (s R.snd) := by
  -- Combine the pointwise family cast with the projection inverse normal forms.
  constructor
  · exact
      (localized_cover_descent_glue_family_overMap_equiv_direct_source_apply_heq
        (J := J) (U := U) 𝒰 D I T s
        (localized_cover_descent_direct_cover_relation_of_overMap
          (J := J) (U := U) 𝒰 I T R).fst).trans
        (congr_arg_heq s
          (localized_cover_descent_direct_cover_relation_of_overMap_fst_inv
            (J := J) (U := U) 𝒰 I T R))
  · exact
      (localized_cover_descent_glue_family_overMap_equiv_direct_source_apply_heq
        (J := J) (U := U) 𝒰 D I T s
        (localized_cover_descent_direct_cover_relation_of_overMap
          (J := J) (U := U) 𝒰 I T R).snd).trans
        (congr_arg_heq s
          (localized_cover_descent_direct_cover_relation_of_overMap_snd_inv
            (J := J) (U := U) 𝒰 I T R))

/-- Helper for Lemma 7.26.4: the direct source-side pullback datum over `T` is identified with
the ordinary descent datum of the pulled-back component sheaf. -/
noncomputable def localized_cover_descent_pullbackDatum_over_direct_to_component_iso
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    localized_cover_descent_pullbackDatum_over_direct_source
        (J := J) (U := U) 𝒰 D I T ≅
      (((J.pseudofunctorOver (Type w)).toDescentData
        (fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ K.f)).obj
        ((J.overMapPullback (Type w) T.hom).obj (D.obj I))) :=
  (localized_cover_descent_pullbackDatum_over_direct_source_iso
    (J := J) (U := U) 𝒰 D I T).symm ≪≫
    localized_cover_descent_pullbackDatum_toDescentData_over
      (J := J) (U := U) 𝒰 D I T

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the direct-to-component descent-data isomorphism acts on terminal
sections as the named direct section equivalence. -/
theorem localized_cover_descent_pullbackDatum_over_direct_to_component_iso_apply
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    (x : (((localized_cover_descent_pullbackDatum_over_direct_source
      (J := J) (U := U) 𝒰 D I T).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))) :
    cast
      (localized_cover_descent_toDescentData_over_section_eq
        (J := J) (U := U) 𝒰 D I T K)
      (((localized_cover_descent_pullbackDatum_over_direct_to_component_iso
        (J := J) (U := U) 𝒰 D I T).hom.hom K).hom.app
          (Opposite.op (Over.mk (𝟙 K.Y))) x) =
      localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T K x := by
  rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the inverse of the direct-to-component descent-data isomorphism
acts on terminal sections as the inverse named direct section equivalence. -/
theorem localized_cover_descent_pullbackDatum_over_direct_to_component_iso_inv_apply
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    (y : ((((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1).obj
      (Opposite.op (Over.mk K.f)))) :
    (((localized_cover_descent_pullbackDatum_over_direct_to_component_iso
      (J := J) (U := U) 𝒰 D I T).inv.hom K).hom.app
        (Opposite.op (Over.mk (𝟙 K.Y)))
        (cast
          (localized_cover_descent_toDescentData_over_section_eq
            (J := J) (U := U) 𝒰 D I T K).symm y)) =
      (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T K).symm y := by
  rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the inverse direct-to-component
comparison has the same pointwise formula when the terminal section is cast through the pulled
back component sheaf normal form. -/
theorem localized_cover_descent_pullbackDatum_over_direct_to_component_iso_inv_apply_terminal
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    (y : ((((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1).obj
      (Opposite.op (Over.mk K.f)))) :
    (((localized_cover_descent_pullbackDatum_over_direct_to_component_iso
      (J := J) (U := U) 𝒰 D I T).inv.hom K).hom.app
        (Opposite.op (Over.mk (𝟙 K.Y)))
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := K.f)
            (M := (J.overMapPullback (Type w) T.hom).obj (D.obj I))).symm y)) =
      (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T K).symm y := by
  -- The two casts are the same terminal-section normal form; reuse the owner-level inverse
  -- computation instead of unfolding the composite isomorphism again.
  simpa [localized_cover_descent_toDescentData_over_section_eq] using
    localized_cover_descent_pullbackDatum_over_direct_to_component_iso_inv_apply
      (J := J) (U := U) 𝒰 D I T K y


end

end GrothendieckTopology
end CategoryTheory
