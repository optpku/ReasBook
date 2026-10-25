module

public import stacks_project.Chap06.Lemma_6_33_3_Part10_RealizationAux

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section
universe w u
section
variable {X : TopCat.{w}} {ι : Type u} {U : ι → Opens X}
variable (𝒪 : TopCat.Sheaf RingCat.{w} X)
  (localSheaf : ∀ i : ι, SheafOfModules.{w} (𝒪 |_ U i))
  (overlapIso : ∀ i j : ι,
    (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
      (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
  (cocycle : ModuleSheafOpenCover.CocycleCondition 𝒪 U localSheaf overlapIso)
  (hU : IsOpenCover U)

local notation "ℱmod" =>
  moduleOpenCoverGlobalModule 𝒪 localSheaf overlapIso cocycle hU

example (i : ι) {W₀ : Opens X} (hW₀i : W₀ ≤ U i) : True := by
  have h := (algebraicCoverBasisRestrictExtendComponentIso (forget AddCommGrpCat.{w})
        (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
        (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
        (moduleOpenCoverAddCocycle (𝒪 := 𝒪) localSheaf overlapIso cocycle) hU
        (⟨W₀, ⟨i, hW₀i⟩⟩ : BasisOpen (coverSubordinateOpens (U := U)))).hom
  trace_state
  trivial

end
end
