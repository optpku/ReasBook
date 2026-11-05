module

public import stacks_project.Chap06.Glueing_data_for_sheaves_on_an_open_cover
public import stacks_project.Chap06.Lemma_6_33_1
public import stacks_project.Chap06.Lemma_6_33_2
public import stacks_project.Chap04.Lemma_4_2_18
@[expose] public section

open CategoryTheory Opposite TopologicalSpace TopCat
open TopologicalSpace.Opens

noncomputable section

universe u v

section

variable {X : TopCat.{u}} {ι : Type v}

private theorem over_obj_eq_mk
    (U : Opens X) (V : Over U) :
    V = Over.mk (homOfLE (leOfHom V.hom)) := by
  cases V
  rename_i left right hom
  cases right
  congr

private theorem overlap_left_open_eq
    (U V : Opens X) (W : Over (U ⊓ V)) :
    (openSubsetIntersectionLeftInclusion_isOpenEmbedding_6_33_2 U V).functor.obj
        ((overFunctor (U ⊓ V)).obj W) =
      (overFunctor U).obj ((Over.map (infLELeft U V)).obj W) := by
  ext x
  simp [overFunctor, overEquiv, TopologicalSpace.Opens.overEquivalence,
    Topology.IsOpenEmbedding.functor, IsOpenMap.functor]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    refine ⟨⟨x.1, ?_⟩, hx, ?_⟩
    · exact ⟨x.2, (leOfHom W.hom hx).2⟩
    · apply Subtype.ext
      rfl

private theorem overlap_right_open_eq
    (U V : Opens X) (W : Over (U ⊓ V)) :
    (openSubsetIntersectionRightInclusion_isOpenEmbedding_6_33_2 U V).functor.obj
        ((overFunctor (U ⊓ V)).obj W) =
      (overFunctor V).obj ((Over.map (infLERight U V)).obj W) := by
  ext x
  simp [overFunctor, overEquiv, TopologicalSpace.Opens.overEquivalence,
    Topology.IsOpenEmbedding.functor, IsOpenMap.functor]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    refine ⟨⟨x.1, ?_⟩, hx, ?_⟩
    · exact ⟨(leOfHom W.hom hx).1, x.2⟩
    · apply Subtype.ext
      rfl

private theorem localHomSection_apply_raw
    (U : Opens X) (F G : X.Sheaf (Type u))
    (φ : F ↾ U ⟶ G ↾ U)
    (W : (Over U)ᵒᵖ)
    (x : (((Opens.grothendieckTopology X).overPullback (Type u) U).obj F).1.obj W) :
    let αF := restrictOpenToOverPullbackIso U F
    let αG := restrictOpenToOverPullbackIso U G
    let e := (overEquiv U).op
    let H : ((Opens (TopCat.of U))ᵒᵖ ⥤ Type u) ⥤ ((Over U)ᵒᵖ ⥤ Type u) :=
      e.congrLeft.inverse
    αG.inv.app W ((localHomSection U F G φ).hom.app W x) =
      (H.map φ.hom).app W (αF.inv.app W x) := by
  dsimp only
  simp [localHomSection]

private theorem ambient_open_section_iso_hom_restrictOpenToOverPullbackIso_inv
    (U : Opens X) (F : X.Sheaf (Type u))
    {W : Opens X} (hW : W ≤ U)
    (x : (((Opens.grothendieckTopology X).overPullback (Type u) U).obj F).1.obj
       (op (Over.mk (homOfLE hW)))) :
    (ambient_open_section_iso (X := X) F hW).hom
      ((restrictOpenToOverPullbackIso U F).inv.app (op (Over.mk (homOfLE hW))) x) =
    x := by
  let α := restrictOpenToOverPullbackIso U F
  have hα :
      α.hom.app (op (Over.mk (homOfLE hW)))
        (α.inv.app (op (Over.mk (homOfLE hW))) x) = x := by
    simp [α]
  have hobj :
      (overFunctor U).obj (Over.mk (homOfLE hW)) = subspace_open_of_le hW := rfl
  simpa [α, restrictOpenToOverPullbackIso, ambient_open_section_iso, TopCat.Sheaf.forget,
    Category.assoc, overEquivalenceFunctorCompInclusionIsoOp,
    overEquivalenceFunctorCompInclusionIso, overEquivalence_functor_obj_eq,
    hobj, subspace_open_of_le_congr, eqToHom_map] using hα

private theorem restrictOpenToOverPullbackIso_hom_eq_ambient_open_section_iso_hom
    (U : Opens X) (F : X.Sheaf (Type u))
    {W : Opens X} (hW : W ≤ U)
    (x : (((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion U)).obj F)).1.obj
        (op (subspace_open_of_le hW))) :
    (restrictOpenToOverPullbackIso U F).hom.app (op (Over.mk (homOfLE hW))) x =
      (ambient_open_section_iso (X := X) F hW).hom x := by
  let α := restrictOpenToOverPullbackIso U F
  apply (show Function.Injective (α.inv.app (op (Over.mk (homOfLE hW)))) from by
    intro a b h
    simpa [α] using congrArg (α.hom.app (op (Over.mk (homOfLE hW)))) h)
  have hleft :
      α.inv.app (op (Over.mk (homOfLE hW)))
        (α.hom.app (op (Over.mk (homOfLE hW))) x) = x := by
    simp [α]
  have hright :
      α.inv.app (op (Over.mk (homOfLE hW)))
        ((ambient_open_section_iso (X := X) F hW).hom x) = x := by
    apply (show Function.Injective (ambient_open_section_iso (X := X) F hW).hom from by
      intro a b h
      simpa using congrArg (ambient_open_section_iso (X := X) F hW).inv h)
    simpa [α] using
      ambient_open_section_iso_hom_restrictOpenToOverPullbackIso_inv
        (U := U) (F := F) (hW := hW)
        ((ambient_open_section_iso (X := X) F hW).hom x)
  exact hleft.trans hright.symm

private theorem left_source_endpoint
    (U V : Opens X) (F : X.Sheaf (Type u))
    {W : Opens X} (hW : W ≤ U ⊓ V)
    (x : (((Opens.grothendieckTopology X).overPullback (Type u) (U ⊓ V)).obj F).1.obj
       (op (Over.mk (homOfLE hW)))) :
    let Wop : (Over (U ⊓ V))ᵒᵖ := op (Over.mk (homOfLE hW))
    let Wleft : (Over U)ᵒᵖ := op ((Over.map (infLELeft U V)).obj (Over.mk (homOfLE hW)))
    let yO := (restrictOpenToOverPullbackIso (U ⊓ V) F).inv.app Wop x
    let leftComp := TopCat.Sheaf.pullbackComp (A := Type u)
      (openSubsetIntersectionLeftInclusion U V) (openSubsetInclusion U)
    let z := (leftComp.inv.app F).hom.app (op (subspace_open_of_le hW)) yO
    (restrictOpenToOverPullbackIso U F).inv.app Wleft x =
      (openSubsetHomOfLE_section_iso hW inf_le_left
        ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion U)).obj F)).hom z := by
  dsimp only
  let Wop : (Over (U ⊓ V))ᵒᵖ := op (Over.mk (homOfLE hW))
  let Wleft : (Over U)ᵒᵖ := op ((Over.map (infLELeft U V)).obj (Over.mk (homOfLE hW)))
  let αΩ := restrictOpenToOverPullbackIso (U ⊓ V) F
  let αU := restrictOpenToOverPullbackIso U F
  let yO := αΩ.inv.app Wop x
  let leftComp := TopCat.Sheaf.pullbackComp (A := Type u)
    (openSubsetIntersectionLeftInclusion U V) (openSubsetInclusion U)
  let z := (leftComp.inv.app F).hom.app (op (subspace_open_of_le hW)) yO
  let sF := openSubsetHomOfLE_section_iso hW inf_le_left
    ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion U)).obj F)
  let membF := ambient_open_section_iso (X := X) F (hW.trans inf_le_left)
  let ambF := ambient_open_section_iso (X := X) F hW
  apply (show Function.Injective membF.hom from by
    intro a b h
    simpa [membF] using congrArg membF.inv h)
  have hleft : membF.hom (αU.inv.app Wleft x) = x := by
    simpa [membF, αU, Wleft] using
      ambient_open_section_iso_hom_restrictOpenToOverPullbackIso_inv
        (U := U) (F := F) (hW := hW.trans inf_le_left) x
  have hright : membF.hom (sF.hom z) = x := by
    have hcmp := congrFun
      (actualOwnerPullbackComp_compare (X := X) (ℱ := F) (hWA := hW)
        (hAB := inf_le_left)) z
    have hcancel :
        ((leftComp.hom.app F).hom.app (op (subspace_open_of_le hW))) z = yO := by
      simpa [leftComp, yO, z, Category.assoc] using
        congrFun
          (congrArg (fun k ↦ k.hom.app (op (subspace_open_of_le hW)))
            (Iso.inv_hom_id_app leftComp F))
          yO
    have hamb : ambF.hom yO = x := by
      simpa [ambF, αΩ, Wop, yO] using
        ambient_open_section_iso_hom_restrictOpenToOverPullbackIso_inv
          (U := U ⊓ V) (F := F) (hW := hW) x
    simpa [sF, membF, ambF, leftComp, z, hcancel, hamb, Category.assoc] using hcmp
  exact hleft.trans hright.symm

private theorem left_target_endpoint
    (U V : Opens X) (G : X.Sheaf (Type u))
    {W : Opens X} (hW : W ≤ U ⊓ V)
    (y :
      (((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionLeftInclusion U V)).obj
          ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion U)).obj G))).1.obj
        (op (subspace_open_of_le hW))) :
    let Wop : (Over (U ⊓ V))ᵒᵖ := op (Over.mk (homOfLE hW))
    let Wleft : (Over U)ᵒᵖ := op ((Over.map (infLELeft U V)).obj (Over.mk (homOfLE hW)))
    let leftComp := TopCat.Sheaf.pullbackComp (A := Type u)
      (openSubsetIntersectionLeftInclusion U V) (openSubsetInclusion U)
    (restrictOpenToOverPullbackIso (U ⊓ V) G).inv.app Wop
        ((restrictOpenToOverPullbackIso U G).hom.app Wleft
          ((openSubsetHomOfLE_section_iso hW inf_le_left
            ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion U)).obj G)).hom y)) =
      ((leftComp.hom.app G).hom.app (op (subspace_open_of_le hW))) y := by
  dsimp only
  let Wop : (Over (U ⊓ V))ᵒᵖ := op (Over.mk (homOfLE hW))
  let Wleft : (Over U)ᵒᵖ := op ((Over.map (infLELeft U V)).obj (Over.mk (homOfLE hW)))
  let αΩ := restrictOpenToOverPullbackIso (U ⊓ V) G
  let αU := restrictOpenToOverPullbackIso U G
  let leftComp := TopCat.Sheaf.pullbackComp (A := Type u)
    (openSubsetIntersectionLeftInclusion U V) (openSubsetInclusion U)
  let sG := openSubsetHomOfLE_section_iso hW inf_le_left
    ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion U)).obj G)
  let membG := ambient_open_section_iso (X := X) G (hW.trans inf_le_left)
  let ambG := ambient_open_section_iso (X := X) G hW
  apply (show Function.Injective ambG.hom from by
    intro a b h
    simpa [ambG] using congrArg ambG.inv h)
  have hleft :
      ambG.hom
        (αΩ.inv.app Wop
          (αU.hom.app Wleft (sG.hom y))) =
      membG.hom (sG.hom y) := by
    have h₁ :
        ambG.hom (αΩ.inv.app Wop (αU.hom.app Wleft (sG.hom y))) =
          αU.hom.app Wleft (sG.hom y) := by
      simpa [ambG, αΩ, Wop] using
        ambient_open_section_iso_hom_restrictOpenToOverPullbackIso_inv
          (U := U ⊓ V) (F := G) (hW := hW)
          (αU.hom.app Wleft (sG.hom y))
    have h₂ :
        αU.hom.app Wleft (sG.hom y) =
          membG.hom (sG.hom y) := by
      simpa [membG, αU, Wleft] using
        restrictOpenToOverPullbackIso_hom_eq_ambient_open_section_iso_hom
          (U := U) (F := G) (hW := hW.trans inf_le_left) (sG.hom y)
    exact h₁.trans h₂
  have hright :
      ambG.hom (((leftComp.hom.app G).hom.app (op (subspace_open_of_le hW))) y) =
      membG.hom (sG.hom y) := by
    have hcmp := congrFun
      (actualOwnerPullbackComp_compare (X := X) (ℱ := G) (hWA := hW)
        (hAB := inf_le_left)) y
    simpa [sG, membG, ambG, leftComp, Category.assoc] using hcmp.symm
  exact hleft.trans hright.symm

private theorem right_source_endpoint
    (U V : Opens X) (F : X.Sheaf (Type u))
    {W : Opens X} (hW : W ≤ U ⊓ V)
    (x : (((Opens.grothendieckTopology X).overPullback (Type u) (U ⊓ V)).obj F).1.obj
       (op (Over.mk (homOfLE hW)))) :
    let Wop : (Over (U ⊓ V))ᵒᵖ := op (Over.mk (homOfLE hW))
    let Wright : (Over V)ᵒᵖ := op ((Over.map (infLERight U V)).obj (Over.mk (homOfLE hW)))
    let yO := (restrictOpenToOverPullbackIso (U ⊓ V) F).inv.app Wop x
    let rightComp := TopCat.Sheaf.pullbackComp (A := Type u)
      (openSubsetIntersectionRightInclusion U V) (openSubsetInclusion V)
    let z := (rightComp.inv.app F).hom.app (op (subspace_open_of_le hW)) yO
    (restrictOpenToOverPullbackIso V F).inv.app Wright x =
      (openSubsetHomOfLE_section_iso hW inf_le_right
        ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion V)).obj F)).hom z := by
  dsimp only
  let Wop : (Over (U ⊓ V))ᵒᵖ := op (Over.mk (homOfLE hW))
  let Wright : (Over V)ᵒᵖ := op ((Over.map (infLERight U V)).obj (Over.mk (homOfLE hW)))
  let αΩ := restrictOpenToOverPullbackIso (U ⊓ V) F
  let αV := restrictOpenToOverPullbackIso V F
  let yO := αΩ.inv.app Wop x
  let rightComp := TopCat.Sheaf.pullbackComp (A := Type u)
    (openSubsetIntersectionRightInclusion U V) (openSubsetInclusion V)
  let z := (rightComp.inv.app F).hom.app (op (subspace_open_of_le hW)) yO
  let sF := openSubsetHomOfLE_section_iso hW inf_le_right
    ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion V)).obj F)
  let membF := ambient_open_section_iso (X := X) F (hW.trans inf_le_right)
  let ambF := ambient_open_section_iso (X := X) F hW
  apply (show Function.Injective membF.hom from by
    intro a b h
    simpa [membF] using congrArg membF.inv h)
  have hleft : membF.hom (αV.inv.app Wright x) = x := by
    simpa [membF, αV, Wright] using
      ambient_open_section_iso_hom_restrictOpenToOverPullbackIso_inv
        (U := V) (F := F) (hW := hW.trans inf_le_right) x
  have hright : membF.hom (sF.hom z) = x := by
    have hcmp := congrFun
      (actualOwnerPullbackComp_compare (X := X) (ℱ := F) (hWA := hW)
        (hAB := inf_le_right)) z
    have hcancel :
        ((rightComp.hom.app F).hom.app (op (subspace_open_of_le hW))) z = yO := by
      simpa [rightComp, yO, z, Category.assoc] using
        congrFun
          (congrArg (fun k ↦ k.hom.app (op (subspace_open_of_le hW)))
            (Iso.inv_hom_id_app rightComp F))
          yO
    have hamb : ambF.hom yO = x := by
      simpa [ambF, αΩ, Wop, yO] using
        ambient_open_section_iso_hom_restrictOpenToOverPullbackIso_inv
          (U := U ⊓ V) (F := F) (hW := hW) x
    simpa [sF, membF, ambF, rightComp, z, hcancel, hamb, Category.assoc] using hcmp
  exact hleft.trans hright.symm

private theorem right_target_endpoint
    (U V : Opens X) (G : X.Sheaf (Type u))
    {W : Opens X} (hW : W ≤ U ⊓ V)
    (y :
      (((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionRightInclusion U V)).obj
          ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion V)).obj G))).1.obj
        (op (subspace_open_of_le hW))) :
    let Wop : (Over (U ⊓ V))ᵒᵖ := op (Over.mk (homOfLE hW))
    let Wright : (Over V)ᵒᵖ := op ((Over.map (infLERight U V)).obj (Over.mk (homOfLE hW)))
    let rightComp := TopCat.Sheaf.pullbackComp (A := Type u)
      (openSubsetIntersectionRightInclusion U V) (openSubsetInclusion V)
    (restrictOpenToOverPullbackIso (U ⊓ V) G).inv.app Wop
        ((restrictOpenToOverPullbackIso V G).hom.app Wright
          ((openSubsetHomOfLE_section_iso hW inf_le_right
            ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion V)).obj G)).hom y)) =
      ((rightComp.hom.app G).hom.app (op (subspace_open_of_le hW))) y := by
  dsimp only
  let Wop : (Over (U ⊓ V))ᵒᵖ := op (Over.mk (homOfLE hW))
  let Wright : (Over V)ᵒᵖ := op ((Over.map (infLERight U V)).obj (Over.mk (homOfLE hW)))
  let αΩ := restrictOpenToOverPullbackIso (U ⊓ V) G
  let αV := restrictOpenToOverPullbackIso V G
  let rightComp := TopCat.Sheaf.pullbackComp (A := Type u)
    (openSubsetIntersectionRightInclusion U V) (openSubsetInclusion V)
  let sG := openSubsetHomOfLE_section_iso hW inf_le_right
    ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion V)).obj G)
  let membG := ambient_open_section_iso (X := X) G (hW.trans inf_le_right)
  let ambG := ambient_open_section_iso (X := X) G hW
  apply (show Function.Injective ambG.hom from by
    intro a b h
    simpa [ambG] using congrArg ambG.inv h)
  have hleft :
      ambG.hom
        (αΩ.inv.app Wop
          (αV.hom.app Wright (sG.hom y))) =
      membG.hom (sG.hom y) := by
    have h₁ :
        ambG.hom (αΩ.inv.app Wop (αV.hom.app Wright (sG.hom y))) =
          αV.hom.app Wright (sG.hom y) := by
      simpa [ambG, αΩ, Wop] using
        ambient_open_section_iso_hom_restrictOpenToOverPullbackIso_inv
          (U := U ⊓ V) (F := G) (hW := hW)
          (αV.hom.app Wright (sG.hom y))
    have h₂ :
        αV.hom.app Wright (sG.hom y) =
          membG.hom (sG.hom y) := by
      simpa [membG, αV, Wright] using
        restrictOpenToOverPullbackIso_hom_eq_ambient_open_section_iso_hom
          (U := V) (F := G) (hW := hW.trans inf_le_right) (sG.hom y)
    exact h₁.trans h₂
  have hright :
      ambG.hom (((rightComp.hom.app G).hom.app (op (subspace_open_of_le hW))) y) =
      membG.hom (sG.hom y) := by
    have hcmp := congrFun
      (actualOwnerPullbackComp_compare (X := X) (ℱ := G) (hWA := hW)
        (hAB := inf_le_right)) y
    simpa [sG, membG, ambG, rightComp, Category.assoc] using hcmp.symm
  exact hleft.trans hright.symm

private theorem localHomSection_map_infLELeft
    (U V : Opens X) (F G : X.Sheaf (Type u))
    (φ : F ↾ U ⟶ G ↾ U) :
    (sheafHom F G).1.map (infLELeft U V).op
        (localHomSection U F G φ) =
      localHomSection (U ⊓ V) F G
        ((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetIntersectionLeftInclusion U V)
          (openSubsetInclusion U)).inv.app F ≫
          (TopCat.Sheaf.pullback (Type u)
            (openSubsetIntersectionLeftInclusion U V)).map φ ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetIntersectionLeftInclusion U V)
            (openSubsetInclusion U)).hom.app G) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply CategoryTheory.NatTrans.ext
  funext W
  cases W using Opposite.rec
  rename_i Wover
  let W₀ : Opens X := Wover.left
  let hW : W₀ ≤ U ⊓ V := leOfHom Wover.hom
  have hWover : Wover = Over.mk (homOfLE hW) := by
    simpa [W₀, hW] using over_obj_eq_mk (U ⊓ V) Wover
  cases hWover
  funext x
  let Wop : (Over (U ⊓ V))ᵒᵖ := op Wover
  let Wleft : (Over U)ᵒᵖ := op ((Over.map (infLELeft U V)).obj (Over.mk (homOfLE hW)))
  let αΩF := restrictOpenToOverPullbackIso (U ⊓ V) F
  let αΩG := restrictOpenToOverPullbackIso (U ⊓ V) G
  let αUF := restrictOpenToOverPullbackIso U F
  let αUG := restrictOpenToOverPullbackIso U G
  let leftComp := TopCat.Sheaf.pullbackComp (A := Type u)
    (openSubsetIntersectionLeftInclusion U V) (openSubsetInclusion U)
  let yO := αΩF.inv.app Wop x
  let z := (leftComp.inv.app F).hom.app (op (subspace_open_of_le hW)) yO
  let sF := openSubsetHomOfLE_section_iso hW inf_le_left
    ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion U)).obj F)
  let sG := openSubsetHomOfLE_section_iso hW inf_le_left
    ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion U)).obj G)
  let pullφ :=
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetIntersectionLeftInclusion U V)).map φ).hom.app
      (op (subspace_open_of_le hW))
  let lhsSection :=
    (((sheafHom F G).1.map (infLELeft U V).op
      (localHomSection U F G φ)).hom.app Wop x)
  let rhsSection :=
    ((localHomSection (U ⊓ V) F G
      (leftComp.inv.app F ≫
        (TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionLeftInclusion U V)).map φ ≫
        leftComp.hom.app G)).hom.app Wop x)
  have hobjΩ' :
      (overEquiv (U ⊓ V)).functor.obj (Over.mk (homOfLE hW)) =
        subspace_open_of_le hW := rfl
  have hobjU' :
      (overEquiv U).functor.obj ((Over.map (infLELeft U V)).obj (Over.mk (homOfLE hW))) =
        subspace_open_of_le (hW.trans inf_le_left) := rfl
  have hsrc :
      αUF.inv.app Wleft x = sF.hom z := by
    simpa [αUF, αΩF, Wop, Wleft, yO, z, leftComp, sF] using
      left_source_endpoint (U := U) (V := V) (F := F) (hW := hW) x
  have hmap_app :
      φ.hom.app (op (subspace_open_of_le (hW.trans inf_le_left))) (sF.hom z) =
        sG.hom (pullφ z) := by
    have hmap := openSubsetHomOfLE_section_iso_map_compare
      (hAB := hW) (hBC := inf_le_left) (η := φ)
    have hz := congrFun hmap z
    have hz' := congrArg sG.hom hz
    simpa [sF, sG, pullφ, Category.assoc] using hz'
  have hrawLeft :
      αUG.inv.app Wleft lhsSection =
        φ.hom.app (op (subspace_open_of_le (hW.trans inf_le_left)))
          (αUF.inv.app Wleft x) := by
    have hraw := localHomSection_apply_raw (U := U) (F := F) (G := G) (φ := φ)
      (W := Wleft) (x := x)
    simpa [lhsSection, Wop, Wleft, αUF, αUG, sheafHom, sheafHom',
      CategoryTheory.GrothendieckTopology.overMapPullback,
      hobjU', overEquiv, TopologicalSpace.Opens.overEquivalence] using hraw
  have hrawLeft' :
      αUG.inv.app Wleft lhsSection = sG.hom (pullφ z) := by
    exact hrawLeft.trans (by simpa [hsrc] using hmap_app)
  have hlhs_as_hom :
      lhsSection = αUG.hom.app Wleft (sG.hom (pullφ z)) := by
    have h := congrArg (αUG.hom.app Wleft) hrawLeft'
    simpa [αUG, lhsSection] using h
  have hlhs :
      αΩG.inv.app Wop lhsSection =
        ((leftComp.hom.app G).hom.app (op (subspace_open_of_le hW))) (pullφ z) := by
    rw [hlhs_as_hom]
    simpa [αΩG, αUG, Wop, Wleft, leftComp, sG] using
      left_target_endpoint (U := U) (V := V) (G := G) (hW := hW) (pullφ z)
  have hrawRight :
      αΩG.inv.app Wop rhsSection =
        ((leftComp.hom.app G).hom.app (op (subspace_open_of_le hW))) (pullφ z) := by
    have hraw := localHomSection_apply_raw (U := U ⊓ V) (F := F) (G := G)
      (φ := leftComp.inv.app F ≫
        (TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionLeftInclusion U V)).map φ ≫
        leftComp.hom.app G)
      (W := Wop) (x := x)
    simpa [rhsSection, Wop, αΩF, αΩG, yO, z, pullφ, leftComp,
      hobjΩ', overEquiv, TopologicalSpace.Opens.overEquivalence, Category.assoc] using hraw
  apply (show Function.Injective (αΩG.inv.app Wop) from by
    intro a b h
    simpa [αΩG] using congrArg (αΩG.hom.app Wop) h)
  dsimp only [lhsSection, rhsSection]
  rw [hlhs, hrawRight]

private theorem localHomSection_map_infLERight
    (U V : Opens X) (F G : X.Sheaf (Type u))
    (ψ : F ↾ V ⟶ G ↾ V) :
    (sheafHom F G).1.map (infLERight U V).op
        (localHomSection V F G ψ) =
      localHomSection (U ⊓ V) F G
        ((TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetIntersectionRightInclusion U V)
          (openSubsetInclusion V)).inv.app F ≫
          (TopCat.Sheaf.pullback (Type u)
            (openSubsetIntersectionRightInclusion U V)).map ψ ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetIntersectionRightInclusion U V)
            (openSubsetInclusion V)).hom.app G) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply CategoryTheory.NatTrans.ext
  funext W
  cases W using Opposite.rec
  rename_i Wover
  let W₀ : Opens X := Wover.left
  let hW : W₀ ≤ U ⊓ V := leOfHom Wover.hom
  have hWover : Wover = Over.mk (homOfLE hW) := by
    simpa [W₀, hW] using over_obj_eq_mk (U ⊓ V) Wover
  cases hWover
  funext x
  let Wop : (Over (U ⊓ V))ᵒᵖ := op Wover
  let Wright : (Over V)ᵒᵖ := op ((Over.map (infLERight U V)).obj (Over.mk (homOfLE hW)))
  let αΩF := restrictOpenToOverPullbackIso (U ⊓ V) F
  let αΩG := restrictOpenToOverPullbackIso (U ⊓ V) G
  let αVF := restrictOpenToOverPullbackIso V F
  let αVG := restrictOpenToOverPullbackIso V G
  let rightComp := TopCat.Sheaf.pullbackComp (A := Type u)
    (openSubsetIntersectionRightInclusion U V) (openSubsetInclusion V)
  let yO := αΩF.inv.app Wop x
  let z := (rightComp.inv.app F).hom.app (op (subspace_open_of_le hW)) yO
  let sF := openSubsetHomOfLE_section_iso hW inf_le_right
    ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion V)).obj F)
  let sG := openSubsetHomOfLE_section_iso hW inf_le_right
    ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion V)).obj G)
  let pullψ :=
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetIntersectionRightInclusion U V)).map ψ).hom.app
      (op (subspace_open_of_le hW))
  let lhsSection :=
    (((sheafHom F G).1.map (infLERight U V).op
      (localHomSection V F G ψ)).hom.app Wop x)
  let rhsSection :=
    ((localHomSection (U ⊓ V) F G
      (rightComp.inv.app F ≫
        (TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionRightInclusion U V)).map ψ ≫
        rightComp.hom.app G)).hom.app Wop x)
  have hobjΩ' :
      (overEquiv (U ⊓ V)).functor.obj (Over.mk (homOfLE hW)) =
        subspace_open_of_le hW := rfl
  have hobjV' :
      (overEquiv V).functor.obj ((Over.map (infLERight U V)).obj (Over.mk (homOfLE hW))) =
        subspace_open_of_le (hW.trans inf_le_right) := rfl
  have hsrc :
      αVF.inv.app Wright x = sF.hom z := by
    simpa [αVF, αΩF, Wop, Wright, yO, z, rightComp, sF] using
      right_source_endpoint (U := U) (V := V) (F := F) (hW := hW) x
  have hmap_app :
      ψ.hom.app (op (subspace_open_of_le (hW.trans inf_le_right))) (sF.hom z) =
        sG.hom (pullψ z) := by
    have hmap := openSubsetHomOfLE_section_iso_map_compare
      (hAB := hW) (hBC := inf_le_right) (η := ψ)
    have hz := congrFun hmap z
    have hz' := congrArg sG.hom hz
    simpa [sF, sG, pullψ, Category.assoc] using hz'
  have hrawLeft :
      αVG.inv.app Wright lhsSection =
        ψ.hom.app (op (subspace_open_of_le (hW.trans inf_le_right)))
          (αVF.inv.app Wright x) := by
    have hraw := localHomSection_apply_raw (U := V) (F := F) (G := G) (φ := ψ)
      (W := Wright) (x := x)
    simpa [lhsSection, Wop, Wright, αVF, αVG, sheafHom, sheafHom',
      CategoryTheory.GrothendieckTopology.overMapPullback,
      hobjV', overEquiv, TopologicalSpace.Opens.overEquivalence] using hraw
  have hrawLeft' :
      αVG.inv.app Wright lhsSection = sG.hom (pullψ z) := by
    exact hrawLeft.trans (by simpa [hsrc] using hmap_app)
  have hlhs_as_hom :
      lhsSection = αVG.hom.app Wright (sG.hom (pullψ z)) := by
    have h := congrArg (αVG.hom.app Wright) hrawLeft'
    simpa [αVG, lhsSection] using h
  have hlhs :
      αΩG.inv.app Wop lhsSection =
        ((rightComp.hom.app G).hom.app (op (subspace_open_of_le hW))) (pullψ z) := by
    rw [hlhs_as_hom]
    simpa [αΩG, αVG, Wop, Wright, rightComp, sG] using
      right_target_endpoint (U := U) (V := V) (G := G) (hW := hW) (pullψ z)
  have hrawRight :
      αΩG.inv.app Wop rhsSection =
        ((rightComp.hom.app G).hom.app (op (subspace_open_of_le hW))) (pullψ z) := by
    have hraw := localHomSection_apply_raw (U := U ⊓ V) (F := F) (G := G)
      (φ := rightComp.inv.app F ≫
        (TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionRightInclusion U V)).map ψ ≫
        rightComp.hom.app G)
      (W := Wop) (x := x)
    simpa [rhsSection, Wop, αΩF, αΩG, yO, z, pullψ, rightComp,
      hobjΩ', overEquiv, TopologicalSpace.Opens.overEquivalence, Category.assoc] using hraw
  apply (show Function.Injective (αΩG.inv.app Wop) from by
    intro a b h
    simpa [αΩG] using congrArg (αΩG.hom.app Wop) h)
  dsimp only [lhsSection, rhsSection]
  rw [hlhs, hrawRight]

private theorem restricted_localHomSection_eq_of_conj
    (U V : Opens X) (F G : X.Sheaf (Type u))
    (φ : F ↾ U ⟶ G ↾ U) (ψ : F ↾ V ⟶ G ↾ V)
    (h :
      (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetIntersectionLeftInclusion U V)
          (openSubsetInclusion U)).inv.app F ≫
        (TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionLeftInclusion U V)).map φ ≫
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetIntersectionLeftInclusion U V)
          (openSubsetInclusion U)).hom.app G =
      (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetIntersectionRightInclusion U V)
          (openSubsetInclusion V)).inv.app F ≫
        (TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionRightInclusion U V)).map ψ ≫
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetIntersectionRightInclusion U V)
          (openSubsetInclusion V)).hom.app G) :
    (sheafHom F G).1.map (infLELeft U V).op (localHomSection U F G φ) =
      (sheafHom F G).1.map (infLERight U V).op (localHomSection V F G ψ) := by
  rw [localHomSection_map_infLELeft, localHomSection_map_infLERight]
  exact (localHomSection_eq_iff (U ⊓ V) F G).2 h

/- Domain-style sampling for Lemma 6.33.4:
- primary domain: sheaf descent along an open cover, expressed through gluing data;
- sampled owner declarations:
  `SheafOpenCoverGlueing`,
  `SheafOpenCoverGlueing.ofSheafFunctor`,
  `exists_unique_hom_of_open_cover`,
  `exists_sheaf_realizing_open_cover_glueing`;
- owner abstraction: the canonical project owner is `SheafOpenCoverGlueing U`, and the bridge from
  global sheaves to that owner is `SheafOpenCoverGlueing.ofSheafFunctor U hU`;
- primitive data: an open cover `U : ι → Opens X` with `TopologicalSpace.IsOpenCover U`;
- derived API: unique gluing of local morphisms and existence of a realizing sheaf.

Source/core/bridge triage:
- `source-facing`: the textbook equivalence between sheaves on `X` and gluing data on the open
  cover `U`;
- `core/canonical`: the owner `SheafOpenCoverGlueing U`;
- `bridge/view`: the restriction functor `SheafOpenCoverGlueing.ofSheafFunctor U hU`. -/

-- Proof sketch: use `exists_unique_hom_of_open_cover` to identify the restriction functor as full
-- and faithful, and `exists_sheaf_realizing_open_cover_glueing` to show essential surjectivity.
/-- Helper for Lemma 6.33.4: a morphism between the restricted gluing data of two sheaves gives a
family of local morphisms compatible on pairwise overlaps. -/
private theorem ofSheafFunctorHomCompatible
    (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U)
    (F G : X.Sheaf (Type u))
    (f : (SheafOpenCoverGlueing.ofSheafFunctor U hU).obj F ⟶
      (SheafOpenCoverGlueing.ofSheafFunctor U hU).obj G) :
    IsCompatibleOnOverlaps U F G (fun i ↦ f.hom i) := by
  rw [isCompatibleOnOverlaps_iff]
  intro i j
  let leftComp := TopCat.Sheaf.pullbackComp
    (A := Type u)
    (openSubsetIntersectionLeftInclusion (U i) (U j))
    (openSubsetInclusion (U i))
  let rightComp := TopCat.Sheaf.pullbackComp
    (A := Type u)
    (openSubsetIntersectionRightInclusion (U i) (U j))
    (openSubsetInclusion (U j))
  have hcomm :
      (TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionLeftInclusion (U i) (U j))).map (f.hom i) ≫
        leftComp.hom.app G ≫ rightComp.inv.app G =
      leftComp.hom.app F ≫ rightComp.inv.app F ≫
        (TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionRightInclusion (U i) (U j))).map (f.hom j) := by
    simpa [leftComp, rightComp, SheafOpenCoverGlueing.ofSheafFunctor,
      SheafOpenCoverGlueing.ofSheaf, Category.assoc] using f.comm i j
  have hlocal :
      leftComp.inv.app F ≫
        (TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionLeftInclusion (U i) (U j))).map (f.hom i) ≫
        leftComp.hom.app G =
      rightComp.inv.app F ≫
        (TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionRightInclusion (U i) (U j))).map (f.hom j) ≫
        rightComp.hom.app G := by
    have h1 :
        leftComp.inv.app F ≫
            (TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionLeftInclusion (U i) (U j))).map (f.hom i) ≫
            leftComp.hom.app G =
          leftComp.inv.app F ≫
            ((TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionLeftInclusion (U i) (U j))).map (f.hom i) ≫
              leftComp.hom.app G ≫ rightComp.inv.app G) ≫
            rightComp.hom.app G := by
      rw [← Category.comp_id (leftComp.inv.app F ≫
        (TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionLeftInclusion (U i) (U j))).map (f.hom i) ≫
        leftComp.hom.app G)]
      erw [← rightComp.inv_hom_id_app G]
      rfl
    have h2 :
        leftComp.inv.app F ≫
            ((TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionLeftInclusion (U i) (U j))).map (f.hom i) ≫
              leftComp.hom.app G ≫ rightComp.inv.app G) ≫
            rightComp.hom.app G =
          leftComp.inv.app F ≫
            (leftComp.hom.app F ≫ rightComp.inv.app F ≫
              (TopCat.Sheaf.pullback (Type u)
                (openSubsetIntersectionRightInclusion (U i) (U j))).map (f.hom j)) ≫
            rightComp.hom.app G := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ leftComp.inv.app F ≫ k ≫ rightComp.hom.app G) hcomm
    have h3 :
        leftComp.inv.app F ≫
            (leftComp.hom.app F ≫ rightComp.inv.app F ≫
              (TopCat.Sheaf.pullback (Type u)
                (openSubsetIntersectionRightInclusion (U i) (U j))).map (f.hom j)) ≫
            rightComp.hom.app G =
          rightComp.inv.app F ≫
            (TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionRightInclusion (U i) (U j))).map (f.hom j) ≫
            rightComp.hom.app G := by
      simpa only [Category.assoc] using
        (leftComp.inv_hom_id_app_assoc F
          (rightComp.inv.app F ≫
            (TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionRightInclusion (U i) (U j))).map (f.hom j) ≫
            rightComp.hom.app G))
    exact h1.trans (h2.trans h3)
  exact restricted_localHomSection_eq_of_conj (U i) (U j) F G (f.hom i) (f.hom j) hlocal

/-- Helper for Lemma 6.33.4: restricting global morphisms to an open cover is bijective on
hom-sets. -/
private theorem ofSheafFunctorMapBijective
    (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U)
    (F G : X.Sheaf (Type u)) :
    Function.Bijective
      ((SheafOpenCoverGlueing.ofSheafFunctor U hU).map :
        (F ⟶ G) →
          ((SheafOpenCoverGlueing.ofSheafFunctor U hU).obj F ⟶
            (SheafOpenCoverGlueing.ofSheafFunctor U hU).obj G)) := by
  constructor
  · intro α β hmap
    -- Uniqueness in Lemma 6.33.1 turns equality of the restricted local components back into
    -- equality of global morphisms.
    obtain ⟨γ, -, huniq⟩ :=
      exists_unique_hom_of_open_cover U hU F G
        (fun i ↦ ((SheafOpenCoverGlueing.ofSheafFunctor U hU).map α).hom i)
        (ofSheafFunctorHomCompatible U hU F G
          ((SheafOpenCoverGlueing.ofSheafFunctor U hU).map α))
    have hαγ : α = γ := huniq α (by
      intro i
      rfl)
    have hβγ : β = γ := huniq β (by
      intro i
      simpa using (congrArg (fun k ↦ k.hom i) hmap).symm)
    exact hαγ.trans hβγ.symm
  · intro f
    -- Existence in Lemma 6.33.1 reconstructs the unique global morphism whose restrictions are
    -- the given compatible local components.
    obtain ⟨α, hα, -⟩ :=
      exists_unique_hom_of_open_cover U hU F G (fun i ↦ f.hom i)
        (ofSheafFunctorHomCompatible U hU F G f)
    refine ⟨α, ?_⟩
    apply SheafOpenCoverGlueing.Hom.ext
    funext i
    simpa using hα i

/-- Helper for Lemma 6.33.4: a realizing sheaf yields an actual isomorphism from the restricted
gluing datum of that sheaf to the chosen gluing datum. -/
private theorem realizesIsoOfSheafFunctorObj
    (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U)
    (data : SheafOpenCoverGlueing U) (F : X.Sheaf (Type u))
    (hreal : data.Realizes F) :
    Nonempty ((SheafOpenCoverGlueing.ofSheafFunctor U hU).obj F ≅ data) := by
  classical
  -- First rewrite the realization witness into the public comparison shape needed for the local
  -- component isomorphisms and their overlap equation.
  change ∃ φ : ∀ i : ι,
      ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F) ≅ data.localSheaf i,
      ∀ i j : ι,
        (TopCat.Sheaf.pullbackComp
          (openSubsetIntersectionLeftInclusion (U i) (U j))
          (openSubsetInclusion (U i))).symm.hom.app F ≫
            ((TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionLeftInclusion (U i) (U j))).mapIso (φ i)).hom ≫
              (data.overlapIso i j).hom =
          (TopCat.Sheaf.pullbackComp
            (openSubsetIntersectionRightInclusion (U i) (U j))
            (openSubsetInclusion (U j))).symm.hom.app F ≫
              ((TopCat.Sheaf.pullback (Type u)
                (openSubsetIntersectionRightInclusion (U i) (U j))).mapIso (φ j)).hom at hreal
  let φ := Classical.choose hreal
  let hφ := Classical.choose_spec hreal
  -- The forward morphism is the componentwise realization isomorphism.
  let forward : (SheafOpenCoverGlueing.ofSheafFunctor U hU).obj F ⟶ data := by
    refine ⟨fun i ↦ (φ i).hom, ?_⟩
    intro i j
    let leftComp := TopCat.Sheaf.pullbackComp
      (A := Type u)
      (openSubsetIntersectionLeftInclusion (U i) (U j))
      (openSubsetInclusion (U i))
    let rightComp := TopCat.Sheaf.pullbackComp
      (A := Type u)
      (openSubsetIntersectionRightInclusion (U i) (U j))
      (openSubsetInclusion (U j))
    have hcomm := congrArg (fun k ↦ leftComp.hom.app F ≫ k) (hφ i j)
    have h1 :
        (TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionLeftInclusion (U i) (U j))).map (φ i).hom ≫
          (data.overlapIso i j).hom =
        leftComp.hom.app F ≫
          (leftComp.inv.app F ≫
            (TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionLeftInclusion (U i) (U j))).map (φ i).hom ≫
            (data.overlapIso i j).hom) := by
      -- Insert the left comparison isomorphism so the realization equation can be used verbatim.
      symm
      simpa [leftComp, Category.assoc] using
        leftComp.hom_inv_id_app_assoc F
          ((TopCat.Sheaf.pullback (Type u)
            (openSubsetIntersectionLeftInclusion (U i) (U j))).map (φ i).hom ≫
            (data.overlapIso i j).hom)
    have h2 :
        leftComp.hom.app F ≫
          (leftComp.inv.app F ≫
            (TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionLeftInclusion (U i) (U j))).map (φ i).hom ≫
            (data.overlapIso i j).hom) =
        leftComp.hom.app F ≫
          (rightComp.inv.app F ≫
            (TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionRightInclusion (U i) (U j))).map (φ j).hom) := by
      simpa [leftComp, rightComp, φ, Category.assoc] using hcomm
    have h3 :
        leftComp.hom.app F ≫
          (rightComp.inv.app F ≫
            (TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionRightInclusion (U i) (U j))).map (φ j).hom) =
        ((SheafOpenCoverGlueing.ofSheaf U hU F).overlapIso i j).hom ≫
          (TopCat.Sheaf.pullback (Type u)
            (openSubsetIntersectionRightInclusion (U i) (U j))).map (φ j).hom := by
      -- The canonical overlap isomorphism of the restricted sheaf is exactly this comparison.
      change leftComp.hom.app F ≫
          rightComp.inv.app F ≫
            (TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionRightInclusion (U i) (U j))).map (φ j).hom =
        leftComp.hom.app F ≫
          rightComp.inv.app F ≫
            (TopCat.Sheaf.pullback (Type u)
              (openSubsetIntersectionRightInclusion (U i) (U j))).map (φ j).hom
      simp
    exact h1.trans (h2.trans h3)
  -- The inverse morphism is obtained from the inverse component isomorphisms and the same
  -- realization equation, now solved for the canonical overlap map of the restricted sheaf.
  let inverse : data ⟶ (SheafOpenCoverGlueing.ofSheafFunctor U hU).obj F := by
    refine ⟨fun i ↦ (φ i).inv, ?_⟩
    intro i j
    let leftComp := TopCat.Sheaf.pullbackComp
      (A := Type u)
      (openSubsetIntersectionLeftInclusion (U i) (U j))
      (openSubsetInclusion (U i))
    let rightComp := TopCat.Sheaf.pullbackComp
      (A := Type u)
      (openSubsetIntersectionRightInclusion (U i) (U j))
      (openSubsetInclusion (U j))
    let leftIso := (TopCat.Sheaf.pullback (Type u)
      (openSubsetIntersectionLeftInclusion (U i) (U j))).mapIso (φ i)
    let rightIso := (TopCat.Sheaf.pullback (Type u)
      (openSubsetIntersectionRightInclusion (U i) (U j))).mapIso (φ j)
    let leftBridge := leftIso.inv ≫ leftComp.hom.app F
    let rightBridge := rightComp.inv.app F ≫ rightIso.hom
    have hcomm := congrArg (fun k ↦ leftBridge ≫ k) (hφ i j)
    have h1 :
        (data.overlapIso i j).hom =
        leftBridge ≫
          (leftComp.inv.app F ≫ leftIso.hom ≫ (data.overlapIso i j).hom) := by
      -- Cancel the left realization isomorphism and the left comparison isomorphism.
      symm
      have hleft :
          leftComp.hom.app F ≫ leftComp.inv.app F ≫ leftIso.hom ≫ (data.overlapIso i j).hom =
            leftIso.hom ≫ (data.overlapIso i j).hom := by
        simpa [leftComp, Category.assoc] using
          leftComp.hom_inv_id_app_assoc F (leftIso.hom ≫ (data.overlapIso i j).hom)
      have hleft' := congrArg (fun k ↦ leftIso.inv ≫ k) hleft
      simpa [leftBridge, leftIso, Category.assoc] using hleft'
    have h2 :
        leftBridge ≫
          (leftComp.inv.app F ≫ leftIso.hom ≫ (data.overlapIso i j).hom) =
        leftBridge ≫ rightBridge := by
      simpa [leftBridge, rightBridge, leftComp, rightComp, leftIso, rightIso, φ,
        Category.assoc] using hcomm
    have h3 :
        leftBridge ≫ rightBridge =
        (leftBridge ≫ rightComp.inv.app F) ≫ rightIso.hom := by
      simp [leftBridge, rightBridge, Category.assoc]
    have hbase :
        (data.overlapIso i j).hom =
        (leftBridge ≫ rightComp.inv.app F) ≫ rightIso.hom := by
      exact h1.trans (h2.trans h3)
    -- Postcompose by the inverse right realization isomorphism to isolate the desired equality.
    have hfinal := congrArg (fun k ↦ k ≫ rightIso.inv) hbase
    change leftBridge ≫ rightComp.inv.app F =
      (data.overlapIso i j).hom ≫ rightIso.inv
    simpa [leftBridge, rightIso, Category.assoc] using hfinal.symm
  -- Componentwise inverse identities are enough because gluing-data morphisms are determined by
  -- their local components.
  let homInvId : forward ≫ inverse = 𝟙 _ := by
    apply SheafOpenCoverGlueing.Hom.ext
    funext i
    change (φ i).hom ≫ (φ i).inv = 𝟙 _
    simp
  let invHomId : inverse ≫ forward = 𝟙 _ := by
    apply SheafOpenCoverGlueing.Hom.ext
    funext i
    change (φ i).inv ≫ (φ i).hom = 𝟙 _
    simp
  exact
    ⟨{ hom := forward
       inv := inverse
       hom_inv_id := homInvId
       inv_hom_id := invHomId }⟩

/-- Helper for Lemma 6.33.4: essential surjectivity follows abstractly once every gluing datum is
realized by some sheaf. -/
private theorem ofSheafFunctorEssSurjOfRealizesExists
    (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U)
    (hrealExists : ∀ data : SheafOpenCoverGlueing U, ∃ F : X.Sheaf (Type u), data.Realizes F) :
    (SheafOpenCoverGlueing.ofSheafFunctor U hU).EssSurj := by
  classical
  -- Choose a realizing sheaf for each datum and reverse its realization isomorphism.
  exact
    (SheafOpenCoverGlueing.ofSheafFunctor U hU).essSurj_of_objwise_iso
      (fun data ↦ Classical.choose (hrealExists data))
      (fun data ↦
        (Classical.choice
          (realizesIsoOfSheafFunctorObj U hU data
            (Classical.choose (hrealExists data))
            (Classical.choose_spec (hrealExists data)))).symm)

/-- Helper for Lemma 6.33.4: the restriction functor is essentially surjective once the realizing
sheaf from Lemma 6.33.2 is available again. -/
private theorem ofSheafFunctorEssSurj
    (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U) :
    (SheafOpenCoverGlueing.ofSheafFunctor U hU).EssSurj := by
  -- Lemma 6.33.2 supplies a realizing sheaf for every datum, which is exactly the objectwise
  -- essential-image witness needed here.
  exact ofSheafFunctorEssSurjOfRealizesExists U hU
    (fun data ↦ exists_sheaf_realizing_open_cover_glueing data)

/-- Lemma 6.33.4: for an open cover `X = ⋃ i, U i`, restricting a sheaf of sets on `X` to the
members of the cover and their pairwise identifications yields an equivalence between sheaves on
`X` and the category of open-cover gluing data for `U`. -/
theorem sheafRestrictionToOpenCover_isEquivalence
    (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U) :
    Functor.IsEquivalence (SheafOpenCoverGlueing.ofSheafFunctor U hU) := by
  -- Route correction: the imported realization theorem from Lemma 6.33.2 is currently unavailable
  -- in this target-file run, so isolate essential surjectivity as the only missing premise and
  -- prove the full-faithful half locally via Lemma 6.33.1.
  let hff : Nonempty (SheafOpenCoverGlueing.ofSheafFunctor U hU).FullyFaithful := by
    -- Full faithfulness is exactly bijectivity on every hom-set.
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
    intro F G
    exact ofSheafFunctorMapBijective U hU F G
  letI : (SheafOpenCoverGlueing.ofSheafFunctor U hU).Faithful :=
    (Classical.choice hff).faithful
  letI : (SheafOpenCoverGlueing.ofSheafFunctor U hU).Full :=
    (Classical.choice hff).full
  letI : (SheafOpenCoverGlueing.ofSheafFunctor U hU).EssSurj :=
    ofSheafFunctorEssSurj U hU
  -- The equivalence structure is now assembled from the full, faithful, and essentially
  -- surjective instances.
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

end
