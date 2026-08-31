module

public import stacks_project.Chap06.Lemma_6_33_3_Part10_BasisExtension
public import stacks_project.Chap06.Lemma_6_33_3_Part10_Cocycle
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe w u

section

variable {X : TopCat.{w}} {ι : Type u} {𝒪 : TopCat.Sheaf RingCat X} {U : ι → Opens X}

-- Proof sketch: the equalizer construction from Lemma 6.33.2 inherits the module structure over
-- each ring of sections, and the resulting sheaf of modules restricts back to the given local
-- module sheaves.
/-- Lemma 6.33.3 for modules: a gluing datum of sheaves of `𝒪`-modules on an open cover is
realized by a sheaf of `𝒪`-modules on the ambient space. -/
theorem exists_module_sheaf_of_open_cover_glueing
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (cocycle : ModuleSheafOpenCover.CocycleCondition 𝒪 U localSheaf overlapIso)
    (hU : IsOpenCover U) :
    ∃ ℱ : SheafOfModules 𝒪, ModuleSheafOpenCover.Realizes U localSheaf overlapIso ℱ :=
  -- The construction in the proof of Lemma 6.33.2 (the additive equalizer/glueing) inherits the
  -- `𝒪`-module structure: the global module sheaf is `moduleOpenCoverGlobalModule`, and it realizes
  -- the gluing datum by `moduleOpenCoverGlobalModule_realizes`.
  ⟨moduleOpenCoverGlobalModule 𝒪 localSheaf overlapIso cocycle hU,
    moduleOpenCoverGlobalModule_realizes 𝒪 localSheaf overlapIso cocycle hU⟩

end
