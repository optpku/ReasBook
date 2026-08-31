module

public import stacks_project.Chap07.Lemma_7_26_4.DirectSourceComparison.Index

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}
variable [univLE : UnivLE.{max u v, w}]

omit [UnivLE.{max u v, w}] in
private theorem equiv_cast_symm_apply {α β : Sort _} (h : α = β) (b : β) :
    (Equiv.cast h).symm b = cast h.symm b := by
  subst h
  rfl

/-
This file keeps the component-source restriction comparison separate from
`DirectSourceComparison.lean`.

The source-family reindexing step reduces the comparison to:

* `t1` is a compatible component-source family over `T1`;
* `t2` is a compatible component-source family over `T2`;
* `hsource` says that `t2` and `t1` agree pointwise after reindexing cover arrows
  along `g : T2 -> T1`;
* prove that the glued component section for `t2` is heterogeneously the restriction
  of the glued component section for `t1`.

The closing route is:

1. use component-section extensionality over every pulled-back cover arrow `K`;
2. evaluate both glued sections using `localized_cover_descent_glue_component_equiv_over_valid_glue`;
3. use `component_restriction_overMap_pullback_map_comp_heq` to identify the
   sheaf restriction of the `T1` glued section along `K` with the restriction along
   the reindexed cover arrow over `T1`;
4. finish with `hsource K`.
-/

omit [UnivLE.{max u v, w}] in
/-- Local copy of the valid-glue computation needed for the component restriction comparison. -/
private theorem component_restriction_valid_glue
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s : localized_cover_descent_glue_component_source_over (J := J) (U := U) 𝒰 D I T)
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow) :
    ((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1.map (Over.homMk K.f).op
      (cast (localized_cover_descent_overMap_terminal_section_eq
        (J := J) (f := T.hom) (M := D.obj I)).symm
        (localized_cover_descent_glue_component_equiv_over (J := J) (U := U) 𝒰 D I T s)) =
    s.1 K := by
  let P := (((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1)
  let π :=
    fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow =>
      (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f (by simp))
  have hsheaf :
      Presieve.IsSheafFor P
        (Presieve.ofArrows
          (fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow => Over.mk K.f) π) := by
    rw [Presieve.isSheafFor_iff_generate]
    simpa [P, π, localized_cover_descent_terminal_cover] using
      (Presheaf.IsSheaf.isSheafFor
        (((J.overMapPullback (Type w) T.hom).obj (D.obj I)).2)
        ((localized_cover_descent_terminal_cover
          (J := J) (U := T.left) ((𝒰.pullback I.f).pullback T.hom)).1)
        ((localized_cover_descent_terminal_cover
          (J := J) (U := T.left) ((𝒰.pullback I.f).pullback T.hom)).condition))
  let hbij :=
    (Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible P π).mp hsheaf
  let e := Equiv.ofBijective (Presieve.Arrows.toCompatible P π) hbij
  have h : P.map (π K).op (e.symm s) = s.1 K :=
    congrFun (congrArg Subtype.val (e.right_inv s)) K
  unfold localized_cover_descent_glue_component_equiv_over
  unfold localized_cover_descent_component_sections_equiv_over
  simp only [Equiv.trans_apply, Equiv.cast_apply]
  change P.map (π K).op (cast _ (cast _ (e.symm s))) = s.1 K
  convert h using 1
  exact congrArg (P.map (π K).op)
    (eq_of_heq ((cast_heq _ _).trans (cast_heq _ _)))

omit [UnivLE.{max u v, w}] in
/-- Local extensionality principle for glued component sections. -/
private theorem component_restriction_ext
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    {x y : (D.obj I).1.obj (Opposite.op T)}
    (h : ∀ K : ((𝒰.pullback I.f).pullback T.hom).Arrow,
      ((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1.map
          (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f).op
          (cast
            (localized_cover_descent_overMap_terminal_section_eq
              (J := J) (f := T.hom) (M := D.obj I)).symm x) =
        ((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1.map
          (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f).op
          (cast
            (localized_cover_descent_overMap_terminal_section_eq
              (J := J) (f := T.hom) (M := D.obj I)).symm y)) :
    x = y := by
  apply (localized_cover_descent_glue_component_equiv_over
    (J := J) (U := U) 𝒰 D I T).symm.injective
  ext K
  unfold localized_cover_descent_glue_component_equiv_over
  unfold localized_cover_descent_component_sections_equiv_over
  rw [Equiv.symm_trans_apply]
  rw [Equiv.symm_symm_apply]
  rw [equiv_cast_symm_apply]
  rw [Equiv.ofBijective_apply]
  rw [Equiv.symm_trans_apply]
  rw [Equiv.symm_symm_apply]
  rw [equiv_cast_symm_apply]
  rw [Equiv.ofBijective_apply]
  exact h K

omit [UnivLE.{max u v, w}] in
private theorem component_restriction_presheaf_map_heq_of_eqToHom_conj
    {D : Type*} [Category D] (F : Dᵒᵖ ⥤ Type w)
    {A B A' B' : D} (hA : A = A') (hB : B = B')
    (φ : A ⟶ B) (ψ : A' ⟶ B')
    (hφ : φ = eqToHom hA ≫ ψ ≫ eqToHom hB.symm)
    {x : F.obj (Opposite.op B)} {y : F.obj (Opposite.op B')}
    (hxy : HEq x y) :
    HEq (F.map φ.op x) (F.map ψ.op y) := by
  subst hA
  subst hB
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hφ
  subst hφ
  rw [eq_of_heq hxy]

omit [UnivLE.{max u v, w}] in
/-- Local copy of the over-map composition transport needed by the component comparison. -/
private theorem component_restriction_overMap_pullback_map_comp_heq
    {S : C}
    (M : Sheaf (J.over S) (Type w))
    {A B : Over S}
    (g : A ⟶ B)
    {Z : C}
    (a : Z ⟶ A.left)
    (x : M.1.obj (Opposite.op B)) :
    HEq
      (((J.overMapPullback (Type w) B.hom).obj M).1.map
        (show Over.mk (a ≫ g.left) ⟶ Over.mk (𝟙 B.left) from
          Over.homMk (a ≫ g.left)).op
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := B.hom) (M := M)).symm
          x))
      (((J.overMapPullback (Type w) A.hom).obj M).1.map
        (show Over.mk a ⟶ Over.mk (𝟙 A.left) from Over.homMk a).op
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := A.hom) (M := M)).symm
          (M.1.map g.op x))) := by
  let A₀ : Over S := (Over.map B.hom).obj (Over.mk (a ≫ g.left))
  let A₁ : Over S := (Over.map A.hom).obj (Over.mk a)
  let B₀ : Over S := (Over.map B.hom).obj (Over.mk (𝟙 B.left))
  let Aₜ : Over S := (Over.map A.hom).obj (Over.mk (𝟙 A.left))
  have hA₀ : A₀ = A₁ := by
    dsimp [A₀, A₁]
    apply over_mk_hext (𝒞 := C) (B := S) (hY := rfl)
    exact heq_of_eq (by
      simpa [Category.assoc] using congrArg (fun h ↦ a ≫ h) (Over.w g))
  have hB₀ : B₀ = B := by
    dsimp [B₀]
    apply over_mk_hext (𝒞 := C) (B := S) (hY := rfl)
    exact heq_of_eq (Category.id_comp B.hom)
  have hAₜ : Aₜ = A := by
    dsimp [Aₜ]
    apply over_mk_hext (𝒞 := C) (B := S) (hY := rfl)
    exact heq_of_eq (Category.id_comp A.hom)
  let φ : A₀ ⟶ B₀ :=
    (Over.map B.hom).map
      (show Over.mk (a ≫ g.left) ⟶ Over.mk (𝟙 B.left) from
        Over.homMk (a ≫ g.left))
  let ψ : A₁ ⟶ B :=
    (show A₁ ⟶ A from Over.homMk a) ≫ g
  have hφ : φ = eqToHom hA₀ ≫ ψ ≫ eqToHom hB₀.symm := by
    apply Over.OverMorphism.ext
    have hAleft : (eqToHom hA₀).left = 𝟙 Z := by
      rw [over_eqToHom_left hA₀]
      simp [A₀, A₁]
    have hBleft : (eqToHom hB₀.symm).left = 𝟙 B.left := by
      rw [over_eqToHom_left hB₀.symm]
      simp [B₀]
    dsimp [φ, ψ, A₀, A₁, B₀]
    calc
      a ≫ g.left = 𝟙 Z ≫ (a ≫ g.left) :=
        (Category.id_comp (a ≫ g.left)).symm
      _ = 𝟙 Z ≫ (a ≫ g.left) ≫ 𝟙 B.left :=
        congrArg (fun h => 𝟙 Z ≫ h) (Category.comp_id (a ≫ g.left)).symm
      _ = (eqToHom hA₀).left ≫ (a ≫ g.left) ≫ (eqToHom hB₀.symm).left := by
        rw [hAleft, hBleft]
        rfl
  have hleft :
      HEq
        (((J.overMapPullback (Type w) B.hom).obj M).1.map
          (show Over.mk (a ≫ g.left) ⟶ Over.mk (𝟙 B.left) from
            Over.homMk (a ≫ g.left)).op
          (cast
            (localized_cover_descent_overMap_terminal_section_eq
              (J := J) (f := B.hom) (M := M)).symm
            x))
        (M.1.map ψ.op x) := by
    simpa [GrothendieckTopology.overMapPullback, A₀, B₀, φ, ψ] using
      (component_restriction_presheaf_map_heq_of_eqToHom_conj
        M.1 hA₀ hB₀ φ ψ hφ (cast_heq _ _))
  let ρ : A₁ ⟶ Aₜ :=
    (Over.map A.hom).map
      (show Over.mk a ⟶ Over.mk (𝟙 A.left) from Over.homMk a)
  let ρ' : A₁ ⟶ A := show A₁ ⟶ A from Over.homMk a
  have hρ : ρ = eqToHom (rfl : A₁ = A₁) ≫ ρ' ≫ eqToHom hAₜ.symm := by
    apply Over.OverMorphism.ext
    have hAleft : (eqToHom hAₜ.symm).left = 𝟙 A.left := by
      rw [over_eqToHom_left hAₜ.symm]
      simp [Aₜ]
    dsimp [ρ, ρ', A₁, Aₜ]
    calc
      a = 𝟙 Z ≫ a :=
        (Category.id_comp a).symm
      _ = 𝟙 Z ≫ a ≫ 𝟙 A.left :=
        congrArg (fun h => 𝟙 Z ≫ h) (Category.comp_id a).symm
      _ = 𝟙 Z ≫ a ≫ (eqToHom hAₜ.symm).left := by
        rw [hAleft]
        rfl
  have hright₀ :
      HEq
        (((J.overMapPullback (Type w) A.hom).obj M).1.map
          (show Over.mk a ⟶ Over.mk (𝟙 A.left) from Over.homMk a).op
          (cast
            (localized_cover_descent_overMap_terminal_section_eq
              (J := J) (f := A.hom) (M := M)).symm
            (M.1.map g.op x)))
        (M.1.map ρ'.op (M.1.map g.op x)) := by
    simpa [GrothendieckTopology.overMapPullback, A₁, Aₜ, ρ, ρ'] using
      (component_restriction_presheaf_map_heq_of_eqToHom_conj
        M.1 (rfl : A₁ = A₁) hAₜ ρ ρ' hρ (cast_heq _ _))
  have hright₁ :
      M.1.map ρ'.op (M.1.map g.op x) = M.1.map ψ.op x := by
    simp [ψ, ρ', FunctorToTypes.map_comp_apply]
  exact hleft.trans ((hright₀.trans (heq_of_eq hright₁)).symm)

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: component-source gluing commutes with restriction along a
slice morphism, assuming the source families agree after reindexing cover arrows. -/
theorem localized_cover_descent_glue_component_source_restrict_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    {T₁ T₂ : Over I.Y}
    (g : T₂ ⟶ T₁)
    (t₁ : localized_cover_descent_glue_component_source_over (J := J) (U := U) 𝒰 D I T₁)
    (t₂ : localized_cover_descent_glue_component_source_over (J := J) (U := U) 𝒰 D I T₂)
    (hsource : ∀ K : ((𝒰.pullback I.f).pullback T₂.hom).Arrow,
      HEq (t₂.1 K)
        (t₁.1
          (localized_cover_descent_pullback_arrow_map
            (J := J) (U := I.Y) (𝒰.pullback I.f) g K))) :
    HEq
      (localized_cover_descent_glue_component_equiv_over
        (J := J) (U := U) 𝒰 D I T₂ t₂)
      ((D.obj I).1.map g.op
        (localized_cover_descent_glue_component_equiv_over
          (J := J) (U := U) 𝒰 D I T₁ t₁)) := by
  apply heq_of_eq
  apply component_restriction_ext (J := J) (U := U) 𝒰 D I T₂
  intro K
  let K' :=
    localized_cover_descent_pullback_arrow_map
      (J := J) (U := I.Y) (𝒰.pullback I.f) g K
  have hleft :=
    component_restriction_valid_glue (J := J) (U := U) 𝒰 D I T₂ t₂ K
  have hrightValid :
      HEq
        (t₁.1 K')
        (((J.overMapPullback (Type w) T₁.hom).obj (D.obj I)).1.map
          (show Over.mk (K.f ≫ g.left) ⟶ Over.mk (𝟙 T₁.left) from
            Over.homMk (K.f ≫ g.left)).op
          (cast
            (localized_cover_descent_overMap_terminal_section_eq
              (J := J) (f := T₁.hom) (M := D.obj I)).symm
            (localized_cover_descent_glue_component_equiv_over
              (J := J) (U := U) 𝒰 D I T₁ t₁))) := by
    have h :=
      component_restriction_valid_glue (J := J) (U := U) 𝒰 D I T₁ t₁ K'
    exact (heq_of_eq h).symm
  have hcomp :=
    component_restriction_overMap_pullback_map_comp_heq
      (J := J) (M := D.obj I) g K.f
      (localized_cover_descent_glue_component_equiv_over
        (J := J) (U := U) 𝒰 D I T₁ t₁)
  exact eq_of_heq
    ((heq_of_eq hleft).trans
      ((hsource K).trans (hrightValid.trans hcomp)))

end

end GrothendieckTopology
end CategoryTheory
