module

public import stacks_project.Chap07.Lemma_7_26_4.DirectSourceComparison.SourceRestrictionSections

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
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the source-restriction transition
at a terminal overlap is the transported transition for the corresponding relation over the
target slice. -/
theorem localized_cover_descent_restrict_source_terminal_left_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D W)
    (R : (𝒰.pullback V.hom).Relation) :
    let RW := localized_cover_descent_pullback_relation_cover_map (J := J) (U := U) 𝒰 g R
    HEq
      (((localized_cover_descent_pullbackDatum_restrict_source
          (J := J) (U := U) 𝒰 D g).hom
          (R.r.g₁ ≫ R.fst.f) R.r.g₁ R.r.g₂ rfl R.r.w.symm).hom.app
        (Opposite.op (Over.mk (𝟙 R.r.Z)))
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := R.r.g₁)
            (M := (localized_cover_descent_pullbackDatum_restrict_source
              (J := J) (U := U) 𝒰 D g).obj R.fst)).symm
          ((((localized_cover_descent_pullbackDatum_restrict_source
              (J := J) (U := U) 𝒰 D g).obj R.fst).1.map
            (Over.homMk R.r.g₁).op)
            (localized_cover_descent_pullbackDatum_restrict_source_terminal_section
              (J := J) (U := U) 𝒰 D g s R.fst))))
      (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).hom
          (RW.r.g₁ ≫ RW.fst.f) RW.r.g₁ RW.r.g₂ rfl RW.r.w.symm).hom.app
        (Opposite.op (Over.mk (𝟙 RW.r.Z)))
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := RW.r.g₁)
            (M := (localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
              RW.fst)).symm
          ((((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
            RW.fst).1.map (Over.homMk RW.r.g₁).op) (s.1 RW.fst)))) := by
  intro RW
  have hpull :=
    localized_cover_descent_restrict_source_pullFunctorObjHom_eq
      (J := J) (U := U) 𝒰 D g R
  have happ :=
    congrArg
      (fun η => η.hom.app (Opposite.op (Over.mk (𝟙 R.r.Z)))) hpull
  let x :=
    cast
      (localized_cover_descent_overMap_terminal_section_eq
        (J := J) (f := R.r.g₁)
        (M := (localized_cover_descent_pullbackDatum_restrict_source
          (J := J) (U := U) 𝒰 D g).obj R.fst)).symm
      ((((localized_cover_descent_pullbackDatum_restrict_source
        (J := J) (U := U) 𝒰 D g).obj R.fst).1.map (Over.homMk R.r.g₁).op)
        (localized_cover_descent_pullbackDatum_restrict_source_terminal_section
          (J := J) (U := U) 𝒰 D g s R.fst))
  have hraw :=
    localized_cover_descent_restrict_source_hom_app_eq_pullFunctorObjHom
      (J := J) (U := U) 𝒰 D g R x
  refine (heq_of_eq hraw).trans ?_
  refine (heq_of_eq (congrFun happ x)).trans ?_
  let y :=
    cast
      (localized_cover_descent_overMap_terminal_section_eq
        (J := J) (f := RW.r.g₁)
        (M := (localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
          RW.fst)).symm
      ((((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
        RW.fst).1.map (Over.homMk RW.r.g₁).op) (s.1 RW.fst))
  have hinput : HEq x y := by
    dsimp [x, y]
    refine (cast_heq _ _).trans ?_
    refine (localized_cover_descent_restrict_source_terminal_section_map_fst_heq
      (J := J) (U := U) 𝒰 D g s R).trans ?_
    exact (cast_heq _ _).symm
  let X₀ := Opposite.op ((Over.mk (𝟙 R.r.Z)) : Over R.r.Z)
  let X₁ := Opposite.op ((Over.mk (𝟙 RW.r.Z)) : Over RW.r.Z)
  let A :=
    ((J.pseudofunctorOver (Type w)).mapComp'
      (𝟙 R.fst.Y).op.toLoc R.r.g₁.op.toLoc R.r.g₁.op.toLoc
      (by simp)).inv.toNatTrans.app
      ((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
        (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g R.fst))
  let B :=
    (localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).hom
      (RW.r.g₁ ≫ RW.fst.f) RW.r.g₁ RW.r.g₂ rfl RW.r.w.symm
  let T :=
    ((J.pseudofunctorOver (Type w)).mapComp'
      (𝟙 R.snd.Y).op.toLoc R.r.g₂.op.toLoc R.r.g₂.op.toLoc
      (by simp)).hom.toNatTrans.app
      ((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
        (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g R.snd))
  have hleft : HEq (A.hom.app X₀ x) x := by
    -- Strip the identity-composition comparison on the first restricted section.
    simpa [A, X₀] using
      (pf_mapComp'_inv_component_apply_heq
        (J := J)
        (f := (𝟙 R.fst.Y).op.toLoc)
        (g' := R.r.g₁.op.toLoc)
        (k := R.r.g₁.op.toLoc)
        (hk := by simp)
        ((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
          (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g R.fst))
        X₀ x)
  have harg : HEq (A.hom.app X₀ x) y := hleft.trans hinput
  have hX : X₀ = X₁ := by
    have hZ :=
      localized_cover_descent_pullback_relation_cover_map_Z
        (J := J) (U := U) 𝒰 g R
    cases hZ.symm
    rfl
  have hmiddle : HEq (B.hom.app X₀ (A.hom.app X₀ x)) (B.hom.app X₁ y) := by
    -- Apply the middle descent-data morphism after transporting both object and input.
    exact dep_app_heq (fun X z ↦ B.hom.app X z) hX harg
  have hright :
      HEq (T.hom.app X₀ (B.hom.app X₀ (A.hom.app X₀ x)))
        (B.hom.app X₀ (A.hom.app X₀ x)) := by
    -- Strip the identity-composition comparison after the transition morphism.
    simpa [T, X₀, B, RW,
      localized_cover_descent_pullback_relation_cover_map_snd,
      localized_cover_descent_pullback_relation_cover_map_g₂,
      localized_cover_descent_pullback_relation_cover_map_snd_f,
      Category.assoc] using
      (pf_mapComp'_hom_component_apply_heq
        (J := J)
        (f := (𝟙 R.snd.Y).op.toLoc)
        (g' := R.r.g₂.op.toLoc)
        (k := R.r.g₂.op.toLoc)
        (hk := by simp)
        ((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
          (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g R.snd))
        X₀ (B.hom.app X₀ (A.hom.app X₀ x)))
  simpa [x, y, X₀, X₁, A, B, T, RW,
    Pseudofunctor.DescentData.pullFunctorObjHom,
    localized_cover_descent_pullback_relation_cover_map_Z,
    localized_cover_descent_pullback_relation_cover_map_g₁,
    localized_cover_descent_pullback_relation_cover_map_g₂,
    localized_cover_descent_pullback_relation_cover_map_fst,
    localized_cover_descent_pullback_relation_cover_map_snd,
    localized_cover_descent_pullback_relation_cover_map_fst_f,
    localized_cover_descent_pullback_relation_cover_map_snd_f,
    Category.assoc] using hright.trans hmiddle

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the right terminal-section cast for
source restriction is the right terminal-section cast for the transported relation. -/
theorem localized_cover_descent_restrict_source_terminal_right_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D W)
    (R : (𝒰.pullback V.hom).Relation) :
    let RW := localized_cover_descent_pullback_relation_cover_map (J := J) (U := U) 𝒰 g R
    HEq
      (cast
        (localized_cover_descent_overMap_terminal_section_eq
          (J := J) (f := RW.r.g₂)
          (M := (localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
            RW.snd)).symm
        ((((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
          RW.snd).1.map (Over.homMk RW.r.g₂).op) (s.1 RW.snd)))
      (cast
        (localized_cover_descent_overMap_terminal_section_eq
          (J := J) (f := R.r.g₂)
          (M := (localized_cover_descent_pullbackDatum_restrict_source
            (J := J) (U := U) 𝒰 D g).obj R.snd)).symm
        ((((localized_cover_descent_pullbackDatum_restrict_source
          (J := J) (U := U) 𝒰 D g).obj R.snd).1.map
          (Over.homMk R.r.g₂).op)
          (localized_cover_descent_pullbackDatum_restrict_source_terminal_section
            (J := J) (U := U) 𝒰 D g s R.snd))) := by
  intro RW
  simpa [RW, localized_cover_descent_pullbackDatum_restrict_source,
    localized_cover_descent_pullback_relation_cover_map_snd,
    localized_cover_descent_pullback_relation_cover_map_g₂] using
    (localized_cover_descent_pullbackDatum_restrict_source_terminal_section_map_heq
      (J := J) (U := U) 𝒰 D g s R.snd R.r.g₂).symm

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the source restriction datum
inherits terminal compatibility from the original glued family. -/
theorem localized_cover_descent_restrict_source_terminalCompatible
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D W) :
    localized_cover_descent_terminalCompatible (J := J) (𝒰.pullback V.hom)
      (localized_cover_descent_pullbackDatum_restrict_source (J := J) (U := U) 𝒰 D g)
      (fun K ↦ localized_cover_descent_pullbackDatum_restrict_source_terminal_section
        (J := J) (U := U) 𝒰 D g s K) := by
  intro R
  dsimp [localized_cover_descent_terminalCompatible,
    localized_cover_descent_pullbackDatum_restrict_source]
  let RW := localized_cover_descent_pullback_relation_cover_map (J := J) (U := U) 𝒰 g R
  have hRW := s.2 RW
  refine eq_of_heq ?_
  refine HEq.trans ?_ ((heq_of_eq hRW).trans ?_)
  · simpa [RW, localized_cover_descent_pullbackDatum_restrict_source] using
      (localized_cover_descent_restrict_source_terminal_left_heq
        (J := J) (U := U) 𝒰 D g s R)
  · simpa [RW, localized_cover_descent_pullbackDatum_restrict_source] using
      (localized_cover_descent_restrict_source_terminal_right_heq
        (J := J) (U := U) 𝒰 D g s R)

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: terminal compatibility is stable
under replacing the section family by a definitionally equal family. -/
theorem localized_cover_descent_terminalCompatible_eq
    {S : C}
    (𝒱 : J.Cover S)
    (P : (J.pseudofunctorOver (Type w)).DescentData (fun K : 𝒱.Arrow ↦ K.f))
    {s t : ∀ K : 𝒱.Arrow,
      (((P.obj K).1.obj (Opposite.op (Over.mk (𝟙 K.Y)))))}
    (hst : s = t)
    (hs : localized_cover_descent_terminalCompatible (J := J) 𝒱 P s) :
    localized_cover_descent_terminalCompatible (J := J) 𝒱 P t := by
  -- Equality of the whole section family lets us reuse the same overlap equations unchanged.
  subst hst
  exact hs

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: descent transition maps are
heterogeneously independent of the proof witnesses for the two overlap equations. -/
theorem localized_cover_descent_descent_hom_app_proof_irrel
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {Y : C} {q : Y ⟶ U} {I₁ I₂ : 𝒰.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {hf₁ hf₁' : f₁ ≫ I₁.f = q}
    {hf₂ hf₂' : f₂ ≫ I₂.f = q}
    (X : (Over Y)ᵒᵖ)
    (x :
      (((J.pseudofunctorOver (Type w)).map f₁.op.toLoc).toFunctor.obj
        (D.obj I₁)).1.obj X) :
    HEq ((D.hom q f₁ f₂ hf₁ hf₂).hom.app X x)
      ((D.hom q f₁ f₂ hf₁' hf₂').hom.app X x) := by
  cases proof_irrel hf₁ hf₁'
  cases proof_irrel hf₂ hf₂'
  rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: a descent transition from a cover
member to itself acts as the identity on sections, up to the proof witnesses. -/
theorem localized_cover_descent_descent_hom_self_app_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {Y : C} {q : Y ⟶ U} {I : 𝒰.Arrow}
    (f : Y ⟶ I.Y)
    (hf₁ hf₂ : f ≫ I.f = q)
    (hf : f ≫ I.f = q)
    (X : (Over Y)ᵒᵖ)
    (x :
      (((J.pseudofunctorOver (Type w)).map f.op.toLoc).toFunctor.obj
        (D.obj I)).1.obj X) :
    HEq ((D.hom q f f hf₁ hf₂).hom.app X x) x := by
  refine (localized_cover_descent_descent_hom_app_proof_irrel
    (J := J) (U := U) 𝒰 D (f₁ := f) (f₂ := f)
    (hf₁' := hf) (hf₂' := hf) X x).trans ?_
  have hhom := D.hom_self q (i := I) f hf
  have happ := congrArg (fun m => m.hom.app X x) hhom
  exact (heq_of_eq happ).trans (heq_of_eq rfl)

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: if two cover arrows and maps agree
heterogeneously, the corresponding descent transition acts as the identity on sections. -/
theorem localized_cover_descent_descent_hom_app_heq_of_arrow_eq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {Y : C} {I₁ I₂ : 𝒰.Arrow}
    (hI : I₁ = I₂)
    {q : Y ⟶ U}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf : HEq f₁ f₂)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
    (X : (Over Y)ᵒᵖ)
    (x :
      (((J.pseudofunctorOver (Type w)).map f₁.op.toLoc).toFunctor.obj
        (D.obj I₁)).1.obj X) :
    HEq ((D.hom q f₁ f₂ hf₁ hf₂).hom.app X x) x := by
  subst hI
  have hf_eq : f₁ = f₂ := eq_of_heq hf
  subst hf_eq
  exact localized_cover_descent_descent_hom_self_app_heq
    (J := J) (U := U) 𝒰 D (f := f₁) hf₁ hf₂ hf₁ X x

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the direct restriction comparison
acts trivially on terminal sections. -/
theorem localized_cover_descent_pullbackDatum_restrict_direct_iso_hom_terminal_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (K : (𝒰.pullback V.hom).Arrow)
    (x :
      (((localized_cover_descent_pullbackDatum_restrict_direct
        (J := J) (U := U) 𝒰 D g).obj K).1.obj
          (Opposite.op (Over.mk (𝟙 K.Y))))) :
    HEq
      (((localized_cover_descent_pullbackDatum_restrict_direct_iso
        (J := J) (U := U) 𝒰 D g).hom.hom K).hom.app
          (Opposite.op (Over.mk (𝟙 K.Y))) x)
      x := by
  unfold localized_cover_descent_pullbackDatum_restrict_direct_iso
  dsimp
  let A := localized_cover_descent_pullback_arrow_map
    (J := J) (U := U) 𝒰 g K
  have hbase : A.base = K.base := by
    simpa [A] using localized_cover_descent_pullback_arrow_map_base
      (J := J) (U := U) 𝒰 g K
  refine localized_cover_descent_descent_hom_app_heq_of_arrow_eq
    (J := J) (U := U) 𝒰 D hbase (𝟙 K.Y) (𝟙 K.Y) ?_ ?_ ?_
    (Opposite.op (Over.mk (𝟙 K.Y))) x
  · rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the source restriction comparison
acts trivially on terminal sections. -/
theorem localized_cover_descent_pullbackDatum_restrict_source_iso_hom_terminal_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (K : (𝒰.pullback V.hom).Arrow)
    (x :
      (((localized_cover_descent_pullbackDatum_restrict_source
        (J := J) (U := U) 𝒰 D g).obj K).1.obj
          (Opposite.op (Over.mk (𝟙 K.Y))))) :
    HEq
      (((localized_cover_descent_pullbackDatum_restrict_source_iso
        (J := J) (U := U) 𝒰 D g).hom.hom K).hom.app
          (Opposite.op (Over.mk (𝟙 K.Y))) x)
      x := by
  unfold localized_cover_descent_pullbackDatum_restrict_source_iso
  simp only [Iso.trans_hom, Pseudofunctor.DescentData.comp_hom]
  dsimp
  let A := localized_cover_descent_pullback_arrow_map
    (J := J) (U := U) 𝒰 g K
  let X₀ := Opposite.op ((Over.mk (𝟙 K.Y)) : Over K.Y)
  let α :=
    ((J.pseudofunctorOver (Type w)).mapComp'
      (𝟙 A.Y).op.toLoc (𝟙 K.Y).op.toLoc (𝟙 K.Y).op.toLoc
      (by
        dsimp [A, localized_cover_descent_pullback_arrow_map]
        simp)).inv.toNatTrans.app (D.obj A.base)
  let β :=
    D.hom (𝟙 K.Y ≫ A.f ≫ W.hom)
      (i₁ := A.base) (i₂ := A.base) (𝟙 K.Y) (𝟙 K.Y)
  change (β.hom.app X₀ (α.hom.app X₀ x)) ≍ x
  have hα : HEq (α.hom.app X₀ x) x := by
    simpa [α, X₀, A] using
      (pf_mapComp'_inv_component_apply_heq
        (J := J)
        (f := (𝟙 A.Y).op.toLoc)
        (g' := (𝟙 K.Y).op.toLoc)
        (k := (𝟙 K.Y).op.toLoc)
        (hk := by
          dsimp [A, localized_cover_descent_pullback_arrow_map]
          simp)
        (D.obj A.base) X₀ x)
  have hβ : HEq (β.hom.app X₀ (α.hom.app X₀ x)) (α.hom.app X₀ x) := by
    refine localized_cover_descent_descent_hom_app_heq_of_arrow_eq
      (J := J) (U := U) 𝒰 D (rfl : A.base = A.base)
      (𝟙 K.Y) (𝟙 K.Y) ?_ ?_ ?_ X₀ (α.hom.app X₀ x)
    rfl
  exact hβ.trans hα

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the composite restriction
comparison sends the source terminal section to the concrete restricted glued section. -/
theorem localized_cover_descent_pullbackDatum_restrict_iso_hom_terminal_section_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D W)
    (K : (𝒰.pullback V.hom).Arrow) :
    HEq
      (((localized_cover_descent_pullbackDatum_restrict_iso
        (J := J) (U := U) 𝒰 D g).hom.hom K).hom.app
          (Opposite.op (Over.mk (𝟙 K.Y)))
          (localized_cover_descent_pullbackDatum_restrict_source_terminal_section
            (J := J) (U := U) 𝒰 D g s K))
      (localized_cover_descent_glue_restrict_section (J := J) (U := U) 𝒰 D g s K) := by
  unfold localized_cover_descent_pullbackDatum_restrict_iso
  simp only [Iso.trans_hom, Pseudofunctor.DescentData.comp_hom]
  change
    ((localized_cover_descent_pullbackDatum_restrict_direct_iso
        (J := J) (U := U) 𝒰 D g).hom.hom K).hom.app
      (Opposite.op (Over.mk (𝟙 K.Y)))
      (((localized_cover_descent_pullbackDatum_restrict_source_iso
          (J := J) (U := U) 𝒰 D g).hom.hom K).hom.app
        (Opposite.op (Over.mk (𝟙 K.Y)))
        (localized_cover_descent_pullbackDatum_restrict_source_terminal_section
          (J := J) (U := U) 𝒰 D g s K)) ≍
      localized_cover_descent_glue_restrict_section (J := J) (U := U) 𝒰 D g s K
  let t :=
    localized_cover_descent_pullbackDatum_restrict_source_terminal_section
      (J := J) (U := U) 𝒰 D g s K
  let y :=
    (((localized_cover_descent_pullbackDatum_restrict_source_iso
      (J := J) (U := U) 𝒰 D g).hom.hom K).hom.app
        (Opposite.op (Over.mk (𝟙 K.Y))) t)
  have hsource : HEq y t := by
    simpa [y, t] using
      localized_cover_descent_pullbackDatum_restrict_source_iso_hom_terminal_heq
        (J := J) (U := U) 𝒰 D g K t
  have hdirect : HEq
      (((localized_cover_descent_pullbackDatum_restrict_direct_iso
        (J := J) (U := U) 𝒰 D g).hom.hom K).hom.app
          (Opposite.op (Over.mk (𝟙 K.Y))) y) y := by
    simpa [y] using
      localized_cover_descent_pullbackDatum_restrict_direct_iso_hom_terminal_heq
        (J := J) (U := U) 𝒰 D g K y
  exact hdirect.trans
    (hsource.trans
      (localized_cover_descent_pullbackDatum_restrict_source_terminal_section_heq_glue_restrict
        (J := J) (U := U) 𝒰 D g s K))

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: restricting a source-style glued
compatible family along a slice morphism preserves the overlap compatibility equations. -/
theorem localized_cover_descent_glue_restrict_compatible
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D W) :
    localized_cover_descent_glue_compatible (J := J) (U := U) 𝒰 D V
      (fun K ↦ localized_cover_descent_glue_restrict_section (J := J) (U := U)
        𝒰 D g s K) := by
  have hsource :=
    localized_cover_descent_restrict_source_terminalCompatible
      (J := J) (U := U) 𝒰 D g s
  have htarget :=
    localized_cover_descent_terminalCompatible_map (J := J) (𝒰.pullback V.hom)
      (localized_cover_descent_pullbackDatum_restrict_source
        (J := J) (U := U) 𝒰 D g)
      (localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D V)
      (localized_cover_descent_pullbackDatum_restrict_iso
        (J := J) (U := U) 𝒰 D g).hom
      (fun K ↦ localized_cover_descent_pullbackDatum_restrict_source_terminal_section
        (J := J) (U := U) 𝒰 D g s K)
      hsource
  have hsections :
      (fun K : (𝒰.pullback V.hom).Arrow ↦
        (((localized_cover_descent_pullbackDatum_restrict_iso
          (J := J) (U := U) 𝒰 D g).hom.hom K).hom.app
            (Opposite.op (Over.mk (𝟙 K.Y)))
            (localized_cover_descent_pullbackDatum_restrict_source_terminal_section
              (J := J) (U := U) 𝒰 D g s K))) =
      (fun K ↦ localized_cover_descent_glue_restrict_section (J := J) (U := U)
        𝒰 D g s K) := by
    funext K
    exact eq_of_heq
      (localized_cover_descent_pullbackDatum_restrict_iso_hom_terminal_section_heq
        (J := J) (U := U) 𝒰 D g s K)
  exact (localized_cover_descent_terminalCompatible_pullbackDatum_iff
    (J := J) (U := U) 𝒰 D V
    (fun K ↦ localized_cover_descent_glue_restrict_section
      (J := J) (U := U) 𝒰 D g s K)).1
      (localized_cover_descent_terminalCompatible_eq
        (J := J) (𝒱 := 𝒰.pullback V.hom)
        (P := localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D V)
        hsections htarget)

/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the named restriction map on glued
compatible-family values. -/
noncomputable def localized_cover_descent_glue_restrict_value
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W) :
    localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D W →
      localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D V :=
  fun s ↦
    ⟨fun K ↦ localized_cover_descent_glue_restrict_section (J := J) (U := U)
      𝒰 D g s K,
      localized_cover_descent_glue_restrict_compatible (J := J) (U := U) 𝒰 D g s⟩

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: restricting a glued compatible
family along the identity slice morphism leaves it unchanged. -/
theorem localized_cover_descent_glue_restrict_value_id
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (V : Over U)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D V) :
    localized_cover_descent_glue_restrict_value (J := J) (U := U) 𝒰 D (𝟙 V) s = s := by
  -- Equality of glued values is equality of their terminal-section families; compatibility
  -- witnesses are propositions and disappear by subtype extensionality.
  apply Subtype.ext
  funext K
  exact localized_cover_descent_glue_restrict_section_id (J := J) (U := U) 𝒰 D V s K

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: restricting terminal sections along a
composite slice morphism agrees with restricting in two steps. -/
theorem localized_cover_descent_glue_restrict_section_comp
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W X : Over U}
    (g : V ⟶ W)
    (h : W ⟶ X)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D X)
    (K : (𝒰.pullback V.hom).Arrow) :
    localized_cover_descent_glue_restrict_section (J := J) (U := U) 𝒰 D (g ≫ h) s K =
      localized_cover_descent_glue_restrict_section (J := J) (U := U) 𝒰 D g
        (localized_cover_descent_glue_restrict_value (J := J) (U := U) 𝒰 D h s) K := by
  -- The two restriction formulas use the same transported pullback-cover arrow; only the proof
  -- spelling of that arrow and the terminal-section casts differ.
  let Kgh := localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 (g ≫ h) K
  let Khg := localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 h
    (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K)
  have hK : Khg = Kgh :=
    localized_cover_descent_pullback_arrow_map_comp (J := J) (U := U) 𝒰 g h K
  unfold localized_cover_descent_glue_restrict_section
  change cast _ (s.1 Kgh) = cast _ (cast _ (s.1 Khg))
  rw [cast_eq_iff_heq]
  rw [heq_cast_iff_heq]
  rw [heq_cast_iff_heq]
  exact hK.symm.rec HEq.rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: value-level restriction along a
composite slice morphism agrees with restricting in two steps. -/
theorem localized_cover_descent_glue_restrict_value_comp
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W X : Over U}
    (g : V ⟶ W)
    (h : W ⟶ X)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D X) :
    localized_cover_descent_glue_restrict_value (J := J) (U := U) 𝒰 D (g ≫ h) s =
      localized_cover_descent_glue_restrict_value (J := J) (U := U) 𝒰 D g
        (localized_cover_descent_glue_restrict_value (J := J) (U := U) 𝒰 D h s) := by
  -- Subtype equality is pointwise equality of the underlying terminal-section families.
  apply Subtype.ext
  funext K
  exact localized_cover_descent_glue_restrict_section_comp
    (J := J) (U := U) 𝒰 D g h s K

/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the identity map of the shrink-wrapped
glued-value presheaf is the identity function. -/
theorem localized_cover_descent_glue_presheaf_map_id
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (V : (Over U)ᵒᵖ) :
    (fun x : Shrink (localized_cover_descent_glue_value
        (J := J) (U := U) 𝒰 D (Opposite.unop V)) ↦
      equivShrink _ (localized_cover_descent_glue_restrict_value
        (J := J) (U := U) 𝒰 D (𝟙 V).unop
        ((equivShrink _).symm x))) = id := by
  -- Unwrap the resizing equivalence, then use the identity law for restriction.
  funext x
  rw [← Equiv.apply_symm_apply
    (equivShrink (localized_cover_descent_glue_value
      (J := J) (U := U) 𝒰 D (Opposite.unop V))) x]
  apply congrArg (equivShrink (localized_cover_descent_glue_value
    (J := J) (U := U) 𝒰 D (Opposite.unop V)))
  simp only [Equiv.symm_apply_apply]
  simpa using
    localized_cover_descent_glue_restrict_value_id
      (J := J) (U := U) 𝒰 D (Opposite.unop V) ((equivShrink _).symm x)

/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: restriction maps on the shrink-wrapped
glued-value presheaf compose functorially. -/
theorem localized_cover_descent_glue_presheaf_map_comp
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W X : (Over U)ᵒᵖ}
    (f : V ⟶ W)
    (h : W ⟶ X) :
    (fun x : Shrink (localized_cover_descent_glue_value
        (J := J) (U := U) 𝒰 D (Opposite.unop V)) ↦
      equivShrink _ (localized_cover_descent_glue_restrict_value
        (J := J) (U := U) 𝒰 D (f ≫ h).unop
        ((equivShrink _).symm x))) =
      (fun x ↦
        equivShrink _ (localized_cover_descent_glue_restrict_value
          (J := J) (U := U) 𝒰 D h.unop
          ((equivShrink _).symm
            (equivShrink _ (localized_cover_descent_glue_restrict_value
              (J := J) (U := U) 𝒰 D f.unop
              ((equivShrink _).symm x)))))) := by
  -- Unwrap the resizing equivalence, then use the composition law for restriction.
  funext x
  rw [Equiv.apply_eq_iff_eq]
  simp only [Equiv.symm_apply_apply]
  simpa using
    localized_cover_descent_glue_restrict_value_comp
      (J := J) (U := U) 𝒰 D h.unop f.unop ((equivShrink _).symm x)

/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the source-compatible-family
construction is a `Type w`-valued presheaf on the localized site `J.over U`. -/
noncomputable def localized_cover_descent_glue_presheaf
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰) :
    (Over U)ᵒᵖ ⥤ Type w where
  obj V := Shrink (localized_cover_descent_glue_value
    (J := J) (U := U) 𝒰 D (Opposite.unop V))
  map f x :=
    equivShrink _ (localized_cover_descent_glue_restrict_value
      (J := J) (U := U) 𝒰 D f.unop ((equivShrink _).symm x))
  map_id V := localized_cover_descent_glue_presheaf_map_id
    (J := J) (U := U) 𝒰 D V
  map_comp f h := localized_cover_descent_glue_presheaf_map_comp
    (J := J) (U := U) 𝒰 D f h

/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: sheafify the source-style glued
compatible-family presheaf to obtain the candidate global sheaf on the localized site. -/
noncomputable def localized_cover_descent_glue_sheaf
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰) :
    Sheaf (J.over U) (Type w) :=
  (presheafToSheaf (J.over U) (Type w)).obj
    (localized_cover_descent_glue_presheaf (J := J) (U := U) 𝒰 D)

end

end GrothendieckTopology
end CategoryTheory
