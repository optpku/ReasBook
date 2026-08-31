module

public import stacks_project.Chap06.Lemma_6_33_3_Part9

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe w u

section

variable {X : TopCat.{w}} {ι : Type u} {U : ι → Opens X}

/-- Helper for Lemma 6.33.3: the scalar transported from the right endpoint of an overlap agrees
with the scalar obtained by restricting the ambient section directly to the overlap. -/
theorem moduleOpenCoverRightEndpoint_scalar
    (𝒪 : TopCat.Sheaf RingCat.{w} X) {W : Opens X} {i j : ι}
    (hWi : W ≤ U i) (hWj : W ≤ U j)
    (r : 𝒪.obj.obj (op W)) :
    let hWij := subset_overlap_le (U := U) hWi hWj
    let hPair : U i ⊓ U j ≤ U j := inf_le_right
    let hOpen : ((openSubsetHomOfLE_isOpenEmbedding hPair).functor.obj
          (subspaceOpenOfLE hWij)) = subspaceOpenOfLE hWj := by
      simp [openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE]
    ((𝒪 |_ U j).obj.map (eqToHom hOpen).op).hom
      ((moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWj).inv.hom r) =
    ((moduleSheafRestrictionOpenPushRingIso 𝒪 hPair).hom.hom.app
      (op (subspaceOpenOfLE hWij))).hom
      ((moduleOpenCoverRingSectionIsoOfLE
        (U := fun _ : PUnit.{u+1} => U i ⊓ U j) (𝒪 := 𝒪)
        (i := PUnit.unit.{u+1}) hWij).inv.hom r) := by
  let hWij := subset_overlap_le (U := U) hWi hWj
  let hPair : U i ⊓ U j ≤ U j := inf_le_right
  let hOpen : ((openSubsetHomOfLE_isOpenEmbedding hPair).functor.obj
        (subspaceOpenOfLE hWij)) = subspaceOpenOfLE hWj := by
    simp [openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE]
  change ((𝒪 |_ U j).obj.map (eqToHom hOpen).op).hom
      ((moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWj).inv.hom r) =
    ((moduleSheafRestrictionOpenPushRingIso 𝒪 hPair).hom.hom.app
      (op (subspaceOpenOfLE hWij))).hom
      ((moduleOpenCoverRingSectionIsoOfLE
        (U := fun _ : PUnit.{u+1} => U i ⊓ U j) (𝒪 := 𝒪)
        (i := PUnit.unit.{u+1}) hWij).inv.hom r)
  rw [moduleOpenCoverRingSectionIsoOfLE_inv_eq_unit (U := U) (𝒪 := 𝒪) hWj]
  rw [moduleOpenCoverRingSectionIsoOfLE_inv_eq_unit
    (U := fun _ : PUnit.{u+1} => U i ⊓ U j) (𝒪 := 𝒪)
    (i := PUnit.unit.{u+1}) hWij]
  let hf := openSubsetHomOfLE_isOpenEmbedding hPair
  haveI := hf.functor_isContinuous
  let adjNaive :
      hf.sheafPullback RingCat ⊣ TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE hPair) :=
    hf.isOpenMap.adjunction.sheafPushforwardContinuous
      (Opens.grothendieckTopology (openSubsetSpace (U i ⊓ U j)))
      (Opens.grothendieckTopology (openSubsetSpace (U j)))
  let μ := moduleSheafRestrictionOpenPushRingIso 𝒪 hPair
  let x : (𝒪 |_ U j).obj.obj (op (subspaceOpenOfLE hWj)) :=
    (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
      (openSubsetInclusion (U j))).unit.app 𝒪).hom.app (op W)).hom r
  change ((𝒪 |_ U j).obj.map (eqToHom hOpen).op).hom x =
    ((μ.hom.hom.app (op (subspaceOpenOfLE hWij))).hom
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
        (openSubsetInclusion (U i ⊓ U j))).unit.app 𝒪).hom.app (op W)).hom r))
  have hNaive := openSubsetHomOfLE_naiveUnit_app_eq_map (𝒪 := 𝒪) hPair hWij hWj hOpen x
  have hPush := moduleSheafRestrictionOpenPushRingIso_unit (𝒪 := 𝒪) hPair
  have hPushApp := congrArg (fun η => η.hom.app (op (subspaceOpenOfLE hWj))) hPush
  have hPush_x := congrArg (fun f => f.hom x) hPushApp
  have hPush_x' :
      ((μ.hom.hom.app (op (subspaceOpenOfLE hWij))).hom
        (((restrictedRingSheafToPushforward 𝒪 hPair).hom.app
          (op (subspaceOpenOfLE hWj))).hom x)) =
      ((adjNaive.unit.app (𝒪 |_ U j)).hom.app (op (subspaceOpenOfLE hWj))).hom x := by
    change
      (((restrictedRingSheafToPushforward 𝒪 hPair).hom.app
          (op (subspaceOpenOfLE hWj)) ≫
        (μ.hom.hom.app (op (subspaceOpenOfLE hWij)))).hom x) =
      ((adjNaive.unit.app (𝒪 |_ U j)).hom.app (op (subspaceOpenOfLE hWj))).hom x at hPush_x
    simpa using hPush_x
  have hComp := restrictedRingSheafToOpenComp_eq 𝒪 hPair
  have hCompApp := congrArg (fun η => η.hom.app (op W)) hComp
  have hComp_r := congrArg (fun f => f.hom r) hCompApp
  have hComp_r' :
      (((restrictedRingSheafToPushforward 𝒪 hPair).hom.app
          (op (subspaceOpenOfLE hWj))).hom x) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
        (openSubsetInclusion (U i ⊓ U j))).unit.app 𝒪).hom.app (op W)).hom r) := by
    change
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
          (openSubsetInclusion (U j))).unit.app 𝒪).hom.app (op W) ≫
        (restrictedRingSheafToPushforward 𝒪 hPair).hom.app (op (subspaceOpenOfLE hWj))).hom r) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
        (openSubsetInclusion (U i ⊓ U j))).unit.app 𝒪).hom.app (op W)).hom r) at hComp_r
    simpa [x] using hComp_r
  have hNaive' :
      ((adjNaive.unit.app (𝒪 |_ U j)).hom.app (op (subspaceOpenOfLE hWj))).hom x =
        ((𝒪 |_ U j).obj.map (eqToHom hOpen).op).hom x := by
    simpa [adjNaive, hf] using hNaive
  exact hNaive'.symm.trans (hPush_x'.symm.trans (by
    rw [hComp_r']))

/-- Helper for Lemma 6.33.3: the right endpoint transport from a local module sheaf to an overlap
is semilinear for ambient sections. -/
theorem moduleOpenCoverRightEndpoint_smul
    (𝒪 : TopCat.Sheaf RingCat.{w} X)
    (localSheaf : ∀ i : ι, SheafOfModules.{w} (𝒪 |_ U i))
    {W : Opens X} {i j : ι} (hWi : W ≤ U i) (hWj : W ≤ U j)
    (r : 𝒪.obj.obj (op W))
    (m : (localSheaf j).val.obj (op (subspaceOpenOfLE hWj))) :
    let hWij := subset_overlap_le (U := U) hWi hWj
    let eRj := openSubsetHomOfLEOpenEmbeddingSectionIso hWij inf_le_right
      ((SheafOfModules.toSheaf (𝒪 |_ U j)).obj (localSheaf j))
    (show ((moduleSheafRestrictionOpenPush 𝒪 inf_le_right).obj (localSheaf j)).val.obj
        (op (subspaceOpenOfLE hWij)) from
      eRj.inv (((moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hWj).inv.hom r) • m)) =
      ((moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hWij).inv.hom r) •
        (show ((moduleSheafRestrictionOpenPush 𝒪 inf_le_right).obj (localSheaf j)).val.obj
          (op (subspaceOpenOfLE hWij)) from eRj.inv m) := by
  let hWij := subset_overlap_le (U := U) hWi hWj
  let hPair : U i ⊓ U j ≤ U j := inf_le_right
  let hOpen : ((openSubsetHomOfLE_isOpenEmbedding hPair).functor.obj
        (subspaceOpenOfLE hWij)) = subspaceOpenOfLE hWj := by
    simp [openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE]
  let μ := moduleSheafRestrictionOpenPushRingIso 𝒪 hPair
  let F := ((SheafOfModules.toSheaf (𝒪 |_ U j)).obj (localSheaf j))
  let eRj := openSubsetHomOfLEOpenEmbeddingSectionIso hWij hPair F
  have heRj : eRj.inv = F.obj.map (eqToHom hOpen).op := by
    have hmap := CategoryTheory.eqToHom_map F.obj (congrArg Opposite.op hOpen.symm)
    simpa [eRj, F, openSubsetHomOfLEOpenEmbeddingSectionIso, hOpen] using hmap.symm
  change (show ((moduleSheafRestrictionOpenPush 𝒪 hPair).obj (localSheaf j)).val.obj
        (op (subspaceOpenOfLE hWij)) from
      eRj.inv (((moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWj).inv.hom r) • m)) =
      ((moduleOpenCoverRingSectionIsoOfLE
        (U := fun _ : PUnit.{u+1} => U i ⊓ U j) (𝒪 := 𝒪)
        (i := PUnit.unit.{u+1}) hWij).inv.hom r) •
        (show ((moduleSheafRestrictionOpenPush 𝒪 hPair).obj (localSheaf j)).val.obj
          (op (subspaceOpenOfLE hWij)) from eRj.inv m)
  rw [heRj]
  change
    (show (localSheaf j).val.obj
        (op ((openSubsetHomOfLE_isOpenEmbedding hPair).functor.obj (subspaceOpenOfLE hWij))) from
      ((localSheaf j).val.map (eqToHom hOpen).op)
        (((moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWj).inv.hom r) • m)) =
    (show (𝒪 |_ U j).obj.obj
        (op ((openSubsetHomOfLE_isOpenEmbedding hPair).functor.obj (subspaceOpenOfLE hWij))) from
      ((μ.hom.hom.app (op (subspaceOpenOfLE hWij))).hom
        ((moduleOpenCoverRingSectionIsoOfLE
          (U := fun _ : PUnit.{u+1} => U i ⊓ U j) (𝒪 := 𝒪)
          (i := PUnit.unit.{u+1}) hWij).inv.hom r))) •
      (show (localSheaf j).val.obj
        (op ((openSubsetHomOfLE_isOpenEmbedding hPair).functor.obj (subspaceOpenOfLE hWij))) from
        ((localSheaf j).val.map (eqToHom hOpen).op) m)
  rw [(localSheaf j).val.map_smul]
  have hscalar := moduleOpenCoverRightEndpoint_scalar (U := U) (𝒪 := 𝒪) hWi hWj r
  change
    ((𝒪 |_ U j).obj.map (eqToHom hOpen).op).hom
      ((moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWj).inv.hom r) =
    ((μ.hom.hom.app (op (subspaceOpenOfLE hWij))).hom
      ((moduleOpenCoverRingSectionIsoOfLE
        (U := fun _ : PUnit.{u+1} => U i ⊓ U j) (𝒪 := 𝒪)
        (i := PUnit.unit.{u+1}) hWij).inv.hom r)) at hscalar
  rw [hscalar]
  rfl

/-- Helper for Lemma 6.33.3: the right endpoint comparison from an overlap back to the local
module sheaf is semilinear for ambient sections. -/
theorem moduleOpenCoverRightEndpoint_hom_smul
    (𝒪 : TopCat.Sheaf RingCat.{w} X)
    (localSheaf : ∀ i : ι, SheafOfModules.{w} (𝒪 |_ U i))
    {W : Opens X} {i j : ι} (hWi : W ≤ U i) (hWj : W ≤ U j)
    (r : 𝒪.obj.obj (op W))
    (m : ((moduleSheafRestrictionOpenPush 𝒪 inf_le_right).obj (localSheaf j)).val.obj
      (op (subspaceOpenOfLE (subset_overlap_le (U := U) hWi hWj)))) :
    let hWij := subset_overlap_le (U := U) hWi hWj
    let eRj := openSubsetHomOfLEOpenEmbeddingSectionIso hWij inf_le_right
      ((SheafOfModules.toSheaf (𝒪 |_ U j)).obj (localSheaf j))
    (show (localSheaf j).val.obj (op (subspaceOpenOfLE hWj)) from
      eRj.hom (((moduleOpenCoverRingSectionIsoOfLE
        (U := fun _ : PUnit.{u+1} => U i ⊓ U j) (𝒪 := 𝒪)
        (i := PUnit.unit.{u+1}) hWij).inv.hom r) • m)) =
      ((moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hWj).inv.hom r) •
        (show (localSheaf j).val.obj (op (subspaceOpenOfLE hWj)) from eRj.hom m) := by
  let hWij := subset_overlap_le (U := U) hWi hWj
  let eRj := openSubsetHomOfLEOpenEmbeddingSectionIso hWij inf_le_right
      ((SheafOfModules.toSheaf (𝒪 |_ U j)).obj (localSheaf j))
  have hinv := moduleOpenCoverRightEndpoint_smul
    (U := U) (𝒪 := 𝒪) localSheaf hWi hWj r
    (show (localSheaf j).val.obj (op (subspaceOpenOfLE hWj)) from eRj.hom m)
  change
    (show (localSheaf j).val.obj (op (subspaceOpenOfLE hWj)) from
      eRj.hom (((moduleOpenCoverRingSectionIsoOfLE
        (U := fun _ : PUnit.{u+1} => U i ⊓ U j) (𝒪 := 𝒪)
        (i := PUnit.unit.{u+1}) hWij).inv.hom r) • m)) =
      ((moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWj).inv.hom r) •
        (show (localSheaf j).val.obj (op (subspaceOpenOfLE hWj)) from eRj.hom m)
  have hcancel :
      (show ((moduleSheafRestrictionOpenPush 𝒪 inf_le_right).obj (localSheaf j)).val.obj
          (op (subspaceOpenOfLE hWij)) from
        eRj.inv (show (localSheaf j).val.obj (op (subspaceOpenOfLE hWj)) from eRj.hom m)) =
        m := by
    exact CategoryTheory.congr_fun eRj.hom_inv_id m
  have hinv' :
      (show ((moduleSheafRestrictionOpenPush 𝒪 inf_le_right).obj (localSheaf j)).val.obj
          (op (subspaceOpenOfLE hWij)) from
        eRj.inv (((moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWj).inv.hom r) •
          (show (localSheaf j).val.obj (op (subspaceOpenOfLE hWj)) from eRj.hom m))) =
        ((moduleOpenCoverRingSectionIsoOfLE
          (U := fun _ : PUnit.{u+1} => U i ⊓ U j) (𝒪 := 𝒪)
          (i := PUnit.unit.{u+1}) hWij).inv.hom r) •
          m := by
    have h := hinv
    change
      (show ((moduleSheafRestrictionOpenPush 𝒪 inf_le_right).obj (localSheaf j)).val.obj
          (op (subspaceOpenOfLE hWij)) from
        eRj.inv (((moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWj).inv.hom r) •
          (show (localSheaf j).val.obj (op (subspaceOpenOfLE hWj)) from eRj.hom m))) =
        ((moduleOpenCoverRingSectionIsoOfLE
          (U := fun _ : PUnit.{u+1} => U i ⊓ U j) (𝒪 := 𝒪)
          (i := PUnit.unit.{u+1}) hWij).inv.hom r) •
          (show ((moduleSheafRestrictionOpenPush 𝒪 inf_le_right).obj (localSheaf j)).val.obj
            (op (subspaceOpenOfLE hWij)) from
            eRj.inv (show (localSheaf j).val.obj (op (subspaceOpenOfLE hWj)) from eRj.hom m)) at h
    rw [hcancel] at h
    exact h
  rw [← hinv']
  exact CategoryTheory.congr_fun eRj.inv_hom_id
    (((moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWj).inv.hom r) •
      (show (localSheaf j).val.obj (op (subspaceOpenOfLE hWj)) from eRj.hom m))

/-- Helper for Lemma 6.33.3: the additive overlap comparison induced by a module overlap
isomorphism is linear after converting the open-push restriction owners to the internal module
restriction owners. -/
theorem moduleOpenCoverOverlapComposite_hom_smul
    (𝒪 : TopCat.Sheaf RingCat.{w} X)
    (localSheaf : ∀ i : ι, SheafOfModules.{w} (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (i j : ι) (V : (Opens (openSubsetSpace (U i ⊓ U j)))ᵒᵖ)
    (a : (𝒪 |_ (U i ⊓ U j)).obj.obj V)
    (m : ((moduleSheafRestrictionOpenPush 𝒪
      (show U i ⊓ U j ≤ U i from inf_le_left)).obj (localSheaf i)).val.obj V) :
    let L := moduleToAddCommGrpRestrictionIso 𝒪
      (show U i ⊓ U j ≤ U i from inf_le_left) (localSheaf i)
    let R := moduleToAddCommGrpRestrictionIso 𝒪
      (show U i ⊓ U j ≤ U j from inf_le_right) (localSheaf j)
    (show ((moduleSheafRestrictionOpenPush 𝒪
        (show U i ⊓ U j ≤ U j from inf_le_right)).obj (localSheaf j)).val.obj V from
      (R.inv.hom.app V).hom
        (((overlapIso i j).hom.val.app V).hom
          (show ((moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj
              (localSheaf i)).val.obj V from
            (L.hom.hom.app V).hom (a • m)))) =
      a •
        (show ((moduleSheafRestrictionOpenPush 𝒪
          (show U i ⊓ U j ≤ U j from inf_le_right)).obj (localSheaf j)).val.obj V from
          (R.inv.hom.app V).hom
            (((overlapIso i j).hom.val.app V).hom
              (show ((moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj
                  (localSheaf i)).val.obj V from
                (L.hom.hom.app V).hom m))) := by
  intro L R
  calc
    (show ((moduleSheafRestrictionOpenPush 𝒪
        (show U i ⊓ U j ≤ U j from inf_le_right)).obj (localSheaf j)).val.obj V from
      (R.inv.hom.app V).hom
        (((overlapIso i j).hom.val.app V).hom
          (show ((moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj
              (localSheaf i)).val.obj V from
            (L.hom.hom.app V).hom (a • m))))
        =
      (show ((moduleSheafRestrictionOpenPush 𝒪
        (show U i ⊓ U j ≤ U j from inf_le_right)).obj (localSheaf j)).val.obj V from
        (R.inv.hom.app V).hom
          (((overlapIso i j).hom.val.app V).hom
            (a • (show ((moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj
                (localSheaf i)).val.obj V from
              (L.hom.hom.app V).hom m)))) := by
          have hL := moduleToAddCommGrpRestrictionIso_hom_smul
            (𝒪 := 𝒪) (show U i ⊓ U j ≤ U i from inf_le_left) (localSheaf i) V a m
          simpa [L] using congrArg
            (fun z =>
              (show ((moduleSheafRestrictionOpenPush 𝒪
                (show U i ⊓ U j ≤ U j from inf_le_right)).obj
                  (localSheaf j)).val.obj V from
                (R.inv.hom.app V).hom (((overlapIso i j).hom.val.app V).hom z)))
            hL
    _ =
      (show ((moduleSheafRestrictionOpenPush 𝒪
        (show U i ⊓ U j ≤ U j from inf_le_right)).obj (localSheaf j)).val.obj V from
        (R.inv.hom.app V).hom
          (a • (show ((moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj
              (localSheaf j)).val.obj V from
            ((overlapIso i j).hom.val.app V).hom
              (show ((moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj
                  (localSheaf i)).val.obj V from
                (L.hom.hom.app V).hom m)))) := by
          have hβ := ((overlapIso i j).hom.val.app V).hom.map_smul a
            (show ((moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj
                (localSheaf i)).val.obj V from
              (L.hom.hom.app V).hom m)
          simpa using congrArg
            (fun z =>
              (show ((moduleSheafRestrictionOpenPush 𝒪
                (show U i ⊓ U j ≤ U j from inf_le_right)).obj
                  (localSheaf j)).val.obj V from
                (R.inv.hom.app V).hom z))
            hβ
    _ =
      a •
        (show ((moduleSheafRestrictionOpenPush 𝒪
          (show U i ⊓ U j ≤ U j from inf_le_right)).obj (localSheaf j)).val.obj V from
          (R.inv.hom.app V).hom
            (((overlapIso i j).hom.val.app V).hom
              (show ((moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj
                  (localSheaf i)).val.obj V from
                (L.hom.hom.app V).hom m))) := by
          have hR := moduleToAddCommGrpRestrictionIso_inv_smul
            (𝒪 := 𝒪) (show U i ⊓ U j ≤ U j from inf_le_right) (localSheaf j) V a
            (show ((moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj
                (localSheaf j)).val.obj V from
              ((overlapIso i j).hom.val.app V).hom
                (show ((moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj
                    (localSheaf i)).val.obj V from
                  (L.hom.hom.app V).hom m))
          simpa [R] using hR

/-- Helper for Lemma 6.33.3: after applying the left endpoint comparison, any surrounding
overlap-comparison context sees the transported scalar on the pair overlap. -/
theorem moduleOpenCoverChartLeftStep_smul
    (𝒪 : TopCat.Sheaf RingCat.{w} X)
    (localSheaf : ∀ i : ι, SheafOfModules.{w} (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    {W : Opens X} {i j : ι} (hWi : W ≤ U i) (hWj : W ≤ U j)
    (r : 𝒪.obj.obj (op W))
    (m : (localSheaf i).val.obj (op (subspaceOpenOfLE hWi))) :
    let hWij := subset_overlap_le (U := U) hWi hWj
    let V : (Opens (openSubsetSpace (U i ⊓ U j)))ᵒᵖ := op (subspaceOpenOfLE hWij)
    let hL : U i ⊓ U j ≤ U i := inf_le_left
    let hR : U i ⊓ U j ≤ U j := inf_le_right
    let eLi := openSubsetHomOfLEOpenEmbeddingSectionIso hWij hL
      ((SheafOfModules.toSheaf (𝒪 |_ U i)).obj (localSheaf i))
    let eRj := openSubsetHomOfLEOpenEmbeddingSectionIso hWij hR
      ((SheafOfModules.toSheaf (𝒪 |_ U j)).obj (localSheaf j))
    let L := moduleToAddCommGrpRestrictionIso 𝒪 hL (localSheaf i)
    let R := moduleToAddCommGrpRestrictionIso 𝒪 hR (localSheaf j)
    let sI := (moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWi).inv.hom r
    let sPair : (𝒪 |_ (U i ⊓ U j)).obj.obj V :=
      (moduleOpenCoverRingSectionIsoOfLE
        (U := fun _ : PUnit.{u+1} => U i ⊓ U j) (𝒪 := 𝒪)
        (i := PUnit.unit.{u+1}) hWij).inv.hom r
    eRj.hom
        ((R.inv.hom.app V).hom
          (((overlapIso i j).hom.val.app V).hom
            ((L.hom.hom.app V).hom
              (show ↑(((moduleSheafRestrictionOpenPush 𝒪 hL).obj
                  (localSheaf i)).val.obj V) from
                eLi.inv (sI • m))))) =
      eRj.hom
        ((R.inv.hom.app V).hom
          (((overlapIso i j).hom.val.app V).hom
            ((L.hom.hom.app V).hom
              (sPair •
                (show ↑(((moduleSheafRestrictionOpenPush 𝒪 hL).obj
                    (localSheaf i)).val.obj V) from
                  eLi.inv m))))) := by
  intro hWij V hL hR eLi eRj L R sI sPair
  have hleft := moduleOpenCoverLeftEndpoint_smul
    (U := U) (𝒪 := 𝒪) localSheaf hWi hWj r m
  change
      (show ↑(((moduleSheafRestrictionOpenPush 𝒪 hL).obj (localSheaf i)).val.obj V) from
        eLi.inv (sI • m)) =
      sPair •
        (show ↑(((moduleSheafRestrictionOpenPush 𝒪 hL).obj (localSheaf i)).val.obj V) from
          eLi.inv m) at hleft
  exact congrArg
    (fun z =>
      eRj.hom
        ((R.inv.hom.app V).hom
          (((overlapIso i j).hom.val.app V).hom
            ((L.hom.hom.app V).hom z))))
    hleft

/-- Helper for Lemma 6.33.3: the additive chart-change isomorphism attached to a module gluing
datum, exposed under a module-specific name so public statements need not unfold the additive
overlap package. -/
noncomputable def moduleOpenCoverSubsetChartIso
    (𝒪 : TopCat.Sheaf RingCat.{w} X)
    (localSheaf : ∀ i : ι, SheafOfModules.{w} (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    {W : Opens X} {i j : ι} (hWi : W ≤ U i) (hWj : W ≤ U j) :
    ((SheafOfModules.toSheaf (𝒪 |_ U i)).obj (localSheaf i)).obj.obj
        (op (subspaceOpenOfLE hWi)) ≅
      ((SheafOfModules.toSheaf (𝒪 |_ U j)).obj (localSheaf j)).obj.obj
        (op (subspaceOpenOfLE hWj)) :=
  algebraicSubsetChartIso
    (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
    (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
    hWi hWj

/-- Helper for `moduleOpenCoverSubsetChartIso_hom_smul`: the additive overlap comparison morphism
underlying `moduleOpenCoverAddOverlap` factors as the left module-restriction comparison, the
underlying overlap morphism, and the inverse right module-restriction comparison. -/
private theorem moduleOpenCoverSubsetChartIsoOverlapFactor
    (𝒪 : TopCat.Sheaf RingCat.{w} X)
    (localSheaf : ∀ i : ι, SheafOfModules.{w} (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (i j : ι)
    (V : (Opens (openSubsetSpace (U i ⊓ U j)))ᵒᵖ) :
    ((Sheaf.forget AddCommGrpCat (openSubsetSpace (U i ⊓ U j))).mapIso
          (moduleOpenCoverAddOverlap 𝒪 localSheaf overlapIso i j)).hom.app V =
      (moduleToAddCommGrpRestrictionIso 𝒪 (show U i ⊓ U j ≤ U i from inf_le_left)
            (localSheaf i)).hom.hom.app V ≫
        ((SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).map (overlapIso i j).hom).hom.app V ≫
        (moduleToAddCommGrpRestrictionIso 𝒪 (show U i ⊓ U j ≤ U j from inf_le_right)
          (localSheaf j)).inv.hom.app V := by
  simp only [moduleOpenCoverAddOverlap, moduleOpenCoverAddLocal,
    moduleToAddCommGrpPairLeftRestrictionIso, moduleToAddCommGrpPairRightRestrictionIso,
    Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
    TopCat.Sheaf.forget, ObjectProperty.ι_map, TopCat.Sheaf.comp_app]

/-- Helper for `moduleOpenCoverSubsetChartIso_hom_smul`: explicit nested form of the chart-change
isomorphism applied to an element, in the shape used by the right-endpoint building-block lemmas. -/
private theorem moduleOpenCoverSubsetChartIsoHomApply
    (𝒪 : TopCat.Sheaf RingCat.{w} X)
    (localSheaf : ∀ i : ι, SheafOfModules.{w} (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    {W : Opens X} {i j : ι} (hWi : W ≤ U i) (hWj : W ≤ U j)
    (X0 : (localSheaf i).val.obj (op (subspaceOpenOfLE hWi))) :
    (moduleOpenCoverSubsetChartIso 𝒪 localSheaf overlapIso hWi hWj).hom X0 =
      (openSubsetHomOfLEOpenEmbeddingSectionIso (subset_overlap_le (U := U) hWi hWj) inf_le_right
          ((SheafOfModules.toSheaf (𝒪 |_ U j)).obj (localSheaf j))).hom
        ((moduleToAddCommGrpRestrictionIso 𝒪 (show U i ⊓ U j ≤ U j from inf_le_right)
              (localSheaf j)).inv.hom.app
            (op (subspaceOpenOfLE (subset_overlap_le (U := U) hWi hWj)))
          (((overlapIso i j).hom.val.app
              (op (subspaceOpenOfLE (subset_overlap_le (U := U) hWi hWj))))
            ((moduleToAddCommGrpRestrictionIso 𝒪 (show U i ⊓ U j ≤ U i from inf_le_left)
                  (localSheaf i)).hom.hom.app
                (op (subspaceOpenOfLE (subset_overlap_le (U := U) hWi hWj)))
              ((openSubsetHomOfLEOpenEmbeddingSectionIso (subset_overlap_le (U := U) hWi hWj)
                  inf_le_left
                  ((SheafOfModules.toSheaf (𝒪 |_ U i)).obj (localSheaf i))).inv X0)))) := by
  rw [show moduleOpenCoverSubsetChartIso 𝒪 localSheaf overlapIso hWi hWj =
      algebraicSubsetChartIso (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
        (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso) hWi hWj from rfl]
  rw [algebraicSubsetChartIso_hom, moduleOpenCoverSubsetChartIsoOverlapFactor]
  simp only [AddCommGrpCat.comp_apply]
  erw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply,
    PresheafOfModules.toPresheaf_map_app_apply]

/-- (#1) The module chart-change isomorphism is semilinear: the scalar on the source side is
transported from `𝒪(W)` along the `i`-chart ring comparison, and on the target side along the
`j`-chart ring comparison.

PROOF PLAN: `moduleOpenCoverSubsetChartIso 𝒪 localSheaf overlapIso hWi hWj` is *definitionally*
`algebraicSubsetChartIso (moduleOpenCoverAddLocal localSheaf) (moduleOpenCoverAddOverlap localSheaf
overlapIso) hWi hWj`.  By `algebraicSubsetChartIso_hom` its `.hom` is
`eLi.inv ≫ ((TopCat.Sheaf.forget _ _).mapIso (moduleOpenCoverAddOverlap ... i j)).hom.app V ≫ eRj.hom`
where `eLi := openSubsetHomOfLEOpenEmbeddingSectionIso hWij inf_le_left (toSheaf (localSheaf i))`,
`eRj := openSubsetHomOfLEOpenEmbeddingSectionIso hWij inf_le_right (toSheaf (localSheaf j))`,
`V := op (subspaceOpenOfLE hWij)`, `hWij := subset_overlap_le hWi hWj`.
Applied to an element, `(f ≫ g) x = g (f x)` via `CategoryTheory.comp_apply`.
The middle `((forget).mapIso (moduleOpenCoverAddOverlap ... i j)).hom.app V` unfolds (using
`moduleOpenCoverAddOverlap = moduleToAddCommGrpPairLeftRestrictionIso ≪≫ toSheaf.mapIso(overlapIso)
≪≫ (moduleToAddCommGrpPairRightRestrictionIso).symm`, and `..PairLeft.. = moduleToAddCommGrpRestrictionIso 𝒪 inf_le_left`, `..PairRight.. = moduleToAddCommGrpRestrictionIso 𝒪 inf_le_right`)
to `(R.inv.hom.app V) ∘ ((overlapIso i j).hom.val.app V) ∘ (L.hom.hom.app V)` where
`L := moduleToAddCommGrpRestrictionIso 𝒪 inf_le_left (localSheaf i)`,
`R := moduleToAddCommGrpRestrictionIso 𝒪 inf_le_right (localSheaf j)`.
So `(moduleOpenCoverSubsetChartIso ...).hom y = eRj.hom (R.inv.hom.app V (overlapIso.val.app V
(L.hom.hom.app V (eLi.inv y))))`.  Then the three pre-built lemmas chain EXACTLY:
  * `moduleOpenCoverChartLeftStep_smul` pushes the source scalar `sI := (moduleOpenCoverRingSectionIsoOfLE hWi).inv r` through `eLi.inv`, turning it into the pair scalar `sPair := (moduleOpenCoverRingSectionIsoOfLE hWij).inv r` inside `eRj.hom(R.inv(overlap(L.hom(·))))`;
  * `moduleOpenCoverOverlapComposite_hom_smul` pulls `sPair` out of `R.inv(overlap(L.hom(sPair • ·)))`;
  * `moduleOpenCoverRightEndpoint_hom_smul` pulls `sPair` through `eRj.hom`, turning it into the target scalar `sWj := (moduleOpenCoverRingSectionIsoOfLE hWj).inv r`.
WARNING: do NOT use plain `rfl`/`change`/`congr` to identify `(moduleOpenCoverSubsetChartIso ...).hom`
with the explicit nested composite — that forces `whnf` through `eqToIso`/sheaf-pullback terms and
times out at 200000 heartbeats. You MUST NOT raise `maxHeartbeats`. Stay at the morphism level with
`algebraicSubsetChartIso_hom` (a cheap `simp`-proved morphism equation) + `CategoryTheory.comp_apply`,
and rewrite the middle `forget.mapIso` factor with targeted `simp only [...]` lemmas
(`Functor.mapIso_hom`, `Iso.trans_hom`, `Iso.symm_hom`, `Functor.map_comp`, `TopCat.Sheaf.comp_app`,
and whatever `SheafOfModules.toSheaf`/`sheafToPresheaf` map-app simp lemmas are needed) BEFORE applying
to the element. A good strategy: prove a separate `have hmid : ∀ z, ((forget).mapIso (moduleOpenCoverAddOverlap
...)).hom.app V z = R.inv.hom.app V (((overlapIso i j).hom.val.app V).hom (L.hom.hom.app V z))` by simp,
then chain. -/

theorem moduleOpenCoverSubsetChartIso_hom_smul
    (𝒪 : TopCat.Sheaf RingCat.{w} X)
    (localSheaf : ∀ i : ι, SheafOfModules.{w} (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    {W : Opens X} {i j : ι} (hWi : W ≤ U i) (hWj : W ≤ U j)
    (r : 𝒪.obj.obj (op W))
    (m : (localSheaf i).val.obj (op (subspaceOpenOfLE hWi))) :
    (show (localSheaf j).val.obj (op (subspaceOpenOfLE hWj)) from
      (moduleOpenCoverSubsetChartIso 𝒪 localSheaf overlapIso hWi hWj).hom
        (((moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hWi).inv.hom r) • m)) =
      ((moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hWj).inv.hom r) •
        (show (localSheaf j).val.obj (op (subspaceOpenOfLE hWj)) from
          (moduleOpenCoverSubsetChartIso 𝒪 localSheaf overlapIso hWi hWj).hom m) := by
  rw [moduleOpenCoverSubsetChartIsoHomApply,
    moduleOpenCoverSubsetChartIsoHomApply]
  have hstep := moduleOpenCoverChartLeftStep_smul 𝒪 localSheaf overlapIso hWi hWj r m
  have hcomp := moduleOpenCoverOverlapComposite_hom_smul 𝒪 localSheaf overlapIso i j
    (op (subspaceOpenOfLE (subset_overlap_le (U := U) hWi hWj)))
    ((moduleOpenCoverRingSectionIsoOfLE
        (U := fun _ : PUnit.{u+1} => U i ⊓ U j) (𝒪 := 𝒪)
        (i := PUnit.unit.{u+1}) (subset_overlap_le (U := U) hWi hWj)).inv.hom r)
    ((openSubsetHomOfLEOpenEmbeddingSectionIso (subset_overlap_le (U := U) hWi hWj) inf_le_left
        ((SheafOfModules.toSheaf (𝒪 |_ U i)).obj (localSheaf i))).inv m)
  have hend := moduleOpenCoverRightEndpoint_hom_smul 𝒪 localSheaf hWi hWj r
  rw [hstep]
  dsimp only [] at hcomp hend ⊢
  rw [hcomp, hend]

end
