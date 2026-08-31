module

public import stacks_project.Chap06.Lemma_6_33_3_Part9_RightEndpoint

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe w u

section

variable {X : TopCat.{w}} {ι : Type u} {𝒪 : TopCat.Sheaf RingCat X} {U : ι → Opens X}

/-- Helper for Lemma 6.33.3: extending the ambient ring sheaf restricted to the
cover-subordinate basis recovers the original ambient ring sheaf. -/
noncomputable def moduleOpenCoverRestrictedRingExtensionIso
    (hU : IsOpenCover U) :
    (moduleOpenCoverBasisRingSheaf (𝒪 := 𝒪) hU).extend ≅ 𝒪 := by
  let B := coverSubordinateOpens (U := U)
  let hB := cover_subordinate_opens_isBasis hU
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  let e : BasisSiteSheaf RingCat B hB ≌ TopCat.Sheaf RingCat X :=
    (basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense
      (Opens.grothendieckTopology X) RingCat
  simpa [moduleOpenCoverBasisRingSheaf, B, hB, BasisSiteSheaf.extend] using
    e.counitIso.app 𝒪

/-- Helper for Lemma 6.33.3: a sheaf of modules on the cover-subordinate basis extends to a
global `𝒪`-module by Lemma 6.30.12, then transports scalars along the ring-extension counit. -/
noncomputable def moduleOpenCoverGlobalModuleFromBasis
    (hU : IsOpenCover U)
    (ℬℱ : SheafOfModules (moduleOpenCoverBasisRingSheaf (𝒪 := 𝒪) hU)) :
    SheafOfModules 𝒪 :=
  (SheafOfModules.restrictScalars
    (moduleOpenCoverRestrictedRingExtensionIso (𝒪 := 𝒪) hU).inv).obj
    (basisModuleSheafExtension (moduleOpenCoverBasisRingSheaf (𝒪 := 𝒪) hU) ℬℱ)

end

section
variable {Y : TopCat.{w}}

/-- An additive presheaf morphism between sheaves of `R`-modules that is `R`-linear on a basis is
`R`-linear at every open: linearity of a sheaf-of-modules morphism is a local property. -/
theorem sheafOfModules_linear_of_basis_linear
    {R : TopCat.Sheaf RingCat.{w} Y} (M N : SheafOfModules.{w} R)
    (ψ : M.val.presheaf ⟶ N.val.presheaf)
    {B : Set (Opens Y)} (hB : Opens.IsBasis B)
    (hlin : ∀ (W : Opens Y), W ∈ B → ∀ (r : R.val.obj (op W)) (m : M.val.presheaf.obj (op W)),
      ψ.app (op W) (r • m) = r • ψ.app (op W) m)
    (V : Opens Y) (r : R.val.obj (op V)) (m : M.val.presheaf.obj (op V)) :
    ψ.app (op V) (r • m) = r • ψ.app (op V) m := by
  apply Presheaf.IsSheaf.section_ext N.isSheaf
  intro x hx
  obtain ⟨W, hWB, hxW, hWV⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  refine ⟨W, hWV, hxW, ?_⟩
  have hψV := ψ.naturality (homOfLE hWV).op
  have hψapp : ∀ z, (N.val.presheaf.map (homOfLE hWV).op) (ψ.app (op V) z) =
      ψ.app (op W) ((M.val.presheaf.map (homOfLE hWV).op) z) := by
    intro z
    have h := congrArg (fun g => (ConcreteCategory.hom g) z) hψV
    simp only [CategoryTheory.comp_apply] at h
    exact h.symm
  have hM : (M.val.presheaf.map (homOfLE hWV).op) (r • m) =
      (R.val.map (homOfLE hWV).op r) • (M.val.presheaf.map (homOfLE hWV).op) m :=
    M.val.map_smul (homOfLE hWV).op r m
  have hN : (N.val.presheaf.map (homOfLE hWV).op) (r • ψ.app (op V) m) =
      (R.val.map (homOfLE hWV).op r) • (N.val.presheaf.map (homOfLE hWV).op) (ψ.app (op V) m) :=
    N.val.map_smul (homOfLE hWV).op r (ψ.app (op V) m)
  calc (N.val.presheaf.map (homOfLE hWV).op) (ψ.app (op V) (r • m))
      = ψ.app (op W) ((M.val.presheaf.map (homOfLE hWV).op) (r • m)) := hψapp (r • m)
    _ = ψ.app (op W) ((R.val.map (homOfLE hWV).op r) • (M.val.presheaf.map (homOfLE hWV).op) m) := by
        rw [hM]
    _ = (R.val.map (homOfLE hWV).op r) • ψ.app (op W) ((M.val.presheaf.map (homOfLE hWV).op) m) :=
        hlin W hWB _ _
    _ = (R.val.map (homOfLE hWV).op r) • (N.val.presheaf.map (homOfLE hWV).op) (ψ.app (op V) m) := by
        rw [hψapp m]
    _ = (N.val.presheaf.map (homOfLE hWV).op) (r • ψ.app (op V) m) := hN.symm

/-- Build a morphism of sheaves of modules from an additive presheaf morphism that is linear on a
basis (using `sheafOfModules_linear_of_basis_linear` to upgrade to linearity everywhere). -/
def moduleHomOfBasisLinear
    {R : TopCat.Sheaf RingCat.{w} Y} (M N : SheafOfModules.{w} R)
    (ψ : M.val.presheaf ⟶ N.val.presheaf)
    {B : Set (Opens Y)} (hB : Opens.IsBasis B)
    (hlin : ∀ (W : Opens Y), W ∈ B → ∀ (r : R.val.obj (op W)) (m : M.val.presheaf.obj (op W)),
      ψ.app (op W) (r • m) = r • ψ.app (op W) m) :
    M ⟶ N :=
  ⟨PresheafOfModules.homMk ψ
    (fun X => sheafOfModules_linear_of_basis_linear M N ψ hB hlin X.unop)⟩

/-- Lift a basis-linear additive presheaf isomorphism between the underlying presheaves of two
sheaves of modules to an isomorphism of sheaves of modules. -/
def moduleIsoOfBasisLinear
    {R : TopCat.Sheaf RingCat.{w} Y} (M N : SheafOfModules.{w} R)
    (α : M.val.presheaf ≅ N.val.presheaf)
    {B : Set (Opens Y)} (hB : Opens.IsBasis B)
    (hhom : ∀ (W : Opens Y), W ∈ B → ∀ (r : R.val.obj (op W)) (m : M.val.presheaf.obj (op W)),
      α.hom.app (op W) (r • m) = r • α.hom.app (op W) m)
    (hinv : ∀ (W : Opens Y), W ∈ B → ∀ (r : R.val.obj (op W)) (m : N.val.presheaf.obj (op W)),
      α.inv.app (op W) (r • m) = r • α.inv.app (op W) m) :
    M ≅ N where
  hom := moduleHomOfBasisLinear M N α.hom hB hhom
  inv := moduleHomOfBasisLinear N M α.inv hB hinv
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    rw [SheafOfModules.comp_val, SheafOfModules.id_val]
    apply (PresheafOfModules.toPresheaf R.val).map_injective
    rw [Functor.map_comp, CategoryTheory.Functor.map_id]
    show (PresheafOfModules.toPresheaf R.val).map (PresheafOfModules.homMk α.hom _) ≫
        (PresheafOfModules.toPresheaf R.val).map (PresheafOfModules.homMk α.inv _) = 𝟙 _
    rw [show (PresheafOfModules.toPresheaf R.val).map (PresheafOfModules.homMk α.hom
        (fun X => sheafOfModules_linear_of_basis_linear M N α.hom hB hhom X.unop)) = α.hom from rfl,
      show (PresheafOfModules.toPresheaf R.val).map (PresheafOfModules.homMk α.inv
        (fun X => sheafOfModules_linear_of_basis_linear N M α.inv hB hinv X.unop)) = α.inv from rfl]
    exact α.hom_inv_id
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    rw [SheafOfModules.comp_val, SheafOfModules.id_val]
    apply (PresheafOfModules.toPresheaf R.val).map_injective
    rw [Functor.map_comp, CategoryTheory.Functor.map_id]
    show (PresheafOfModules.toPresheaf R.val).map (PresheafOfModules.homMk α.inv _) ≫
        (PresheafOfModules.toPresheaf R.val).map (PresheafOfModules.homMk α.hom _) = 𝟙 _
    rw [show (PresheafOfModules.toPresheaf R.val).map (PresheafOfModules.homMk α.inv
        (fun X => sheafOfModules_linear_of_basis_linear N M α.inv hB hinv X.unop)) = α.inv from rfl,
      show (PresheafOfModules.toPresheaf R.val).map (PresheafOfModules.homMk α.hom
        (fun X => sheafOfModules_linear_of_basis_linear M N α.hom hB hhom X.unop)) = α.hom from rfl]
    exact α.inv_hom_id

end

section Construct

variable {X : TopCat.{w}} {ι : Type u} {U : ι → Opens X}

variable (𝒪 : TopCat.Sheaf RingCat.{w} X)
  (localSheaf : ∀ i : ι, SheafOfModules.{w} (𝒪 |_ U i))
  (overlapIso : ∀ i j : ι,
    (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
      (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
  (cocycle : ModuleSheafOpenCover.CocycleCondition 𝒪 U localSheaf overlapIso)
  (hU : IsOpenCover U)

/-- (#2 + #3) The basis presheaf of `𝒪|_B`-modules realizing the gluing datum on the
cover-subordinate basis.  Underlying additive presheaf is `moduleOpenCoverBasisAddPresheaf`; the
module structure on each section group is `moduleOpenCoverBasisObjModule`.

PROOF PLAN for the `ofPresheaf` `map_smul` goal (after `intro V W f r m`, goal is
`M.map f (r • m) = (R.map f) r • M.map f m` with `M = moduleOpenCoverBasisAddPresheaf`,
`R = (moduleOpenCoverBasisRingSheaf 𝒪 hU).presheaf`, `•` via `moduleOpenCoverBasisObjModule`):
`moduleOpenCoverBasisObjModule W` is `Module.compHom _ (moduleOpenCoverRingSectionIsoOfLE
(chosen_chart_le W.unop)).inv.hom`, so `r • m` means `((moduleOpenCoverRingSectionIsoOfLE
(chosen_chart_le V.unop)).inv.hom r) • m` (genuine module action).  `M.map f` is by definition
`algebraicOpenCoverBasisPresheafMap (moduleOpenCoverAddLocal localSheaf) (moduleOpenCoverAddOverlap
localSheaf overlapIso) f = (localSheaf (chosen_chart V.unop)).1.map (subspaceOpenHom hWcV
(chosen_chart_le V.unop) hWV).op ≫ (algebraicSubsetChartIso ... hWcV (chosen_chart_le W.unop)).hom`
where `hWV := f.unop.hom.le`, `hWcV := hWV.trans (chosen_chart_le V.unop)`, and `R.map f r =
𝒪.obj.map (homOfLE hWV).op r`.  Chain (use `CategoryTheory.comp_apply` to split the composite):
  (1) first factor: `moduleOpenCoverBasisLocalMap_smul` gives
      `(localSheaf chartV).1.map(..)((eV.inv r) • m) = (e_{hWcV}.inv s) • (localSheaf chartV).1.map(..) m`
      with `s := 𝒪.obj.map (homOfLE hWV).op r`, `e_{hWcV} := moduleOpenCoverRingSectionIsoOfLE hWcV`;
  (2) chart factor: `moduleOpenCoverSubsetChartIso_hom_smul` (lemma #1 above) with `i := chosen_chart V.unop`,
      `j := chosen_chart W.unop`, `hWi := hWcV`, `hWj := chosen_chart_le W.unop`, `r := s`, gives
      `chartIso.hom ((e_{hWcV}.inv s) • x) = (e_{chosen_chart_le W.unop}.inv s) • chartIso.hom x`.
  Note `moduleOpenCoverSubsetChartIso 𝒪 localSheaf overlapIso hWcV (chosen_chart_le W.unop)` is defeq
  to `algebraicSubsetChartIso (moduleOpenCoverAddLocal ..) (moduleOpenCoverAddOverlap ..) hWcV
  (chosen_chart_le W.unop)`, which is the chart factor of `M.map f`.  The result's scalar
  `(moduleOpenCoverRingSectionIsoOfLE (chosen_chart_le W.unop)).inv s` is exactly the target `•`.
Same heartbeat warnings as #1. -/
noncomputable def moduleOpenCoverBasisModulePresheaf :
    PresheafOfModules.{w} (moduleOpenCoverBasisRingSheaf (𝒪 := 𝒪) hU).presheaf :=
  letI : ∀ W, Module ((moduleOpenCoverBasisRingSheaf (𝒪 := 𝒪) hU).obj.obj W)
      ((moduleOpenCoverBasisAddPresheaf (𝒪 := 𝒪) localSheaf overlapIso cocycle).obj W) :=
    fun W => moduleOpenCoverBasisObjModule (𝒪 := 𝒪) hU localSheaf overlapIso cocycle W
  PresheafOfModules.ofPresheaf
    (moduleOpenCoverBasisAddPresheaf (𝒪 := 𝒪) localSheaf overlapIso cocycle)
    (R := (moduleOpenCoverBasisRingSheaf (𝒪 := 𝒪) hU).presheaf)
    (by
      intro V W f r m
      rw [show (moduleOpenCoverBasisAddPresheaf (𝒪 := 𝒪) localSheaf overlapIso cocycle).map f =
          algebraicOpenCoverBasisPresheafMap (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
            (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso) f from rfl]
      rw [algebraicOpenCoverBasisPresheafMap]
      erw [AddCommGrpCat.comp_apply]
      erw [moduleOpenCoverBasisLocalMap_smul (𝒪 := 𝒪) localSheaf f r m]
      rw [show algebraicSubsetChartIso (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
          (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
          (f.unop.hom.le.trans (chosen_chart_le V.unop)) (chosen_chart_le W.unop) =
          moduleOpenCoverSubsetChartIso 𝒪 localSheaf overlapIso
            (f.unop.hom.le.trans (chosen_chart_le V.unop)) (chosen_chart_le W.unop) from rfl]
      set_option maxRecDepth 4000 in
      exact moduleOpenCoverSubsetChartIso_hom_smul 𝒪 localSheaf overlapIso
        (i := chosen_chart V.unop) (j := chosen_chart W.unop)
        (hWi := f.unop.hom.le.trans (chosen_chart_le V.unop)) (hWj := chosen_chart_le W.unop)
        ((𝒪.obj.map (homOfLE f.unop.hom.le).op).hom r)
        ((localSheaf (chosen_chart V.unop)).val.map
          (subspaceOpenHom (f.unop.hom.le.trans (chosen_chart_le V.unop))
            (chosen_chart_le V.unop) f.unop.hom.le).op m))

/-- (#3) The basis `SheafOfModules`: package the presheaf of modules with the additive sheaf
condition `algebraicOpenCoverBasisPresheaf_isSheaf` (the underlying additive presheaf of
`moduleOpenCoverBasisModulePresheaf` is `moduleOpenCoverBasisAddPresheaf` by `ofPresheaf_presheaf`,
i.e. `algebraicOpenCoverBasisPresheaf (forget AddCommGrpCat) (moduleOpenCoverAddLocal localSheaf)
(moduleOpenCoverAddOverlap localSheaf overlapIso) (moduleOpenCoverAddCocycle localSheaf overlapIso
cocycle)`). -/
noncomputable def moduleOpenCoverBasisModuleSheaf :
    SheafOfModules.{w} (moduleOpenCoverBasisRingSheaf (𝒪 := 𝒪) hU) where
  val := moduleOpenCoverBasisModulePresheaf 𝒪 localSheaf overlapIso cocycle hU
  isSheaf := by
    exact algebraicOpenCoverBasisPresheaf_isSheaf (F := forget AddCommGrpCat)
      (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
      (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
      (moduleOpenCoverAddCocycle (𝒪 := 𝒪) localSheaf overlapIso cocycle) hU

/-- (#3) The global sheaf of `𝒪`-modules realizing the gluing datum. -/
noncomputable def moduleOpenCoverGlobalModule : SheafOfModules.{w} 𝒪 :=
  moduleOpenCoverGlobalModuleFromBasis (𝒪 := 𝒪) hU
    (moduleOpenCoverBasisModuleSheaf 𝒪 localSheaf overlapIso cocycle hU)

end Construct
