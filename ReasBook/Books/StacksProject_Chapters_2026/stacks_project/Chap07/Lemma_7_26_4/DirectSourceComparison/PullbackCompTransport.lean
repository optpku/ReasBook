module

public import stacks_project.Chap07.Lemma_7_26_4.DirectSourceComparison.DirectSourceReindexing
public import stacks_project.Chap07.Lemma_7_26_4.DirectSourceComparison.GlueRestrictionPresheaf

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}

/-- Helper for Lemma 7.26.4: the inverse `Cover.pullbackComp` reindexing of an iterated
pullback-cover arrow has the terminal side equation needed by the reindexed pullFunctor. -/
theorem localized_cover_descent_pullbackComp_reindex_w
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow) :
    (𝟙 K.Y) ≫ (K.map (Cover.pullbackComp 𝒰 T.hom I.f).inv).f =
      K.f ≫ 𝟙 T.left := by
  -- Unfold the cover-composition equivalence once; the result is the terminal identity law.
  cases T
  cases K
  dsimp [Cover.pullbackComp, Cover.Arrow.map]
  rw [Category.id_comp, Category.comp_id]

end

end GrothendieckTopology
end CategoryTheory
