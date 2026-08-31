module

public import stacks_project.Chap06.Lemma_6_33_3_Part10_RealizationAux
public import stacks_project.Chap06.Lemma_6_33_3_Part10_BridgeKeystone

@[expose] public section

/-!
# Lemma 6.33.3 (module case): the via-left / via-right `toSheaf`-bridge coherences

This file proves the two `toSheaf`-coherence squares `hSq1` (via-left) and `hSq2`
(via-right) for the realization of the module gluing datum.  They are the
Beck–Chevalley coherences between the module composition isomorphism
`moduleSheafRestrictionToOpenCompIso` and the additive composition isomorphism
`algebraicGlobalRestrictionCompIso`, conjugated by the L2 bridge isomorphisms.

Both squares are instances of a single general coherence
`comp_bridge_coherence` for an arbitrary open inclusion `h : W ≤ U`.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe w u

section General

variable {X : TopCat.{w}}

/-- Section formula for the inverse of the additive composition isomorphism on a represented open.
This is the general-`h` analogue of the pair-indexed computation `hleftGlobal` in
`Lemma_6_33_3_Part7`. -/
theorem algebraicGlobalRestrictionCompIso_inv_section
    {C : Type (w + 1)} [Category.{w} C] {W U : Opens X} (h : W ≤ U)
    (G : TopCat.Sheaf C X) {W₀ : Opens X} (hW₀W : W₀ ≤ W) :
    ((algebraicGlobalRestrictionCompIso (C := C) h).inv.app G).hom.app
        (op (subspaceOpenOfLE hW₀W)) =
      (eqToIso (show ((W.isOpenEmbedding.sheafPullback C).obj G).1.obj
              (op (subspaceOpenOfLE hW₀W)) =
            G.1.obj (op W₀) from by
          change G.1.obj (op ((subspaceInclusionFunctor W).obj (subspaceOpenOfLE hW₀W))) =
            G.1.obj (op W₀)
          simp [subspaceOpenOfLEImageEq])).hom ≫
        (eqToIso (show ((U.isOpenEmbedding.sheafPullback C).obj G).1.obj
              (op (subspaceOpenOfLE (hW₀W.trans h))) =
            G.1.obj (op W₀) from by
          change G.1.obj (op ((subspaceInclusionFunctor U).obj
              (subspaceOpenOfLE (hW₀W.trans h)))) = G.1.obj (op W₀)
          simp [subspaceOpenOfLEImageEq])).inv ≫
        (openSubsetHomOfLEOpenEmbeddingSectionIso hW₀W h
          ((U.isOpenEmbedding.sheafPullback C).obj G)).inv := by
  simp [algebraicGlobalRestrictionCompIso,
    openSubsetHomOfLEOpenEmbeddingSectionIso,
    Topology.IsOpenEmbedding.sheafPullback, eqToHom_map]

end General

section Construct

variable {X : TopCat.{w}} {ι : Type u} {U : ι → Opens X}
variable (𝒪 : TopCat.Sheaf RingCat.{w} X)
  (localSheaf : ∀ i : ι, SheafOfModules.{w} (𝒪 |_ U i))
  (overlapIso : ∀ i j : ι,
    (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
      (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
  (cocycle : ModuleSheafOpenCover.CocycleCondition 𝒪 U localSheaf overlapIso)
  (hU : IsOpenCover U)

local notation "ℱmod" => moduleOpenCoverGlobalModule 𝒪 localSheaf overlapIso cocycle hU

/-- `hSq1`: the via-left `toSheaf`-bridge coherence at the realized global module `ℱmod`. -/
theorem hSq1 (i j : ι) :
    (SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).map
        ((moduleRestrictionToPairViaLeftIso 𝒪 (U i) (U j)).hom.app ℱmod) =
      (moduleToAddCommGrpOpenRestrictionIso 𝒪 (U i ⊓ U j) ℱmod).hom ≫
        (algebraicGlobalRestrictionToPairViaLeftIso (C := AddCommGrpCat.{w}) (U i) (U j)).hom.app
          ((SheafOfModules.toSheaf 𝒪).obj ℱmod) ≫
        (algebraicRestrictToPairLeft (C := AddCommGrpCat.{w}) (U i) (U j)).map
          (moduleToAddCommGrpOpenRestrictionIso 𝒪 (U i) ℱmod).inv ≫
        (moduleToAddCommGrpPairLeftRestrictionIso 𝒪 (U i) (U j)
          ((moduleSheafRestrictionToOpen (U i) 𝒪).obj ℱmod)).hom := by
  rw [moduleRestrictionToPairViaLeftIso, Iso.symm_hom,
    algebraicGlobalRestrictionToPairViaLeftIso, Iso.symm_hom,
    moduleToAddCommGrpPairLeftRestrictionIso]
  exact comp_bridge_coherence 𝒪 (inf_le_left : U i ⊓ U j ≤ U i) ℱmod

/-- `hSq2`: the via-right `toSheaf`-bridge coherence at the realized global module `ℱmod`. -/
theorem hSq2 (i j : ι) :
    (SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).map
        ((moduleRestrictionToPairViaRightIso 𝒪 (U i) (U j)).hom.app ℱmod) =
      (moduleToAddCommGrpOpenRestrictionIso 𝒪 (U i ⊓ U j) ℱmod).hom ≫
        (algebraicGlobalRestrictionToPairViaRightIso (C := AddCommGrpCat.{w}) (U i) (U j)).hom.app
          ((SheafOfModules.toSheaf 𝒪).obj ℱmod) ≫
        (algebraicRestrictToPairRight (C := AddCommGrpCat.{w}) (U i) (U j)).map
          (moduleToAddCommGrpOpenRestrictionIso 𝒪 (U j) ℱmod).inv ≫
        (moduleToAddCommGrpPairRightRestrictionIso 𝒪 (U i) (U j)
          ((moduleSheafRestrictionToOpen (U j) 𝒪).obj ℱmod)).hom := by
  rw [moduleRestrictionToPairViaRightIso, Iso.symm_hom,
    algebraicGlobalRestrictionToPairViaRightIso, Iso.symm_hom,
    moduleToAddCommGrpPairRightRestrictionIso]
  exact comp_bridge_coherence 𝒪 (inf_le_right : U i ⊓ U j ≤ U j) ℱmod

end Construct
