module

import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Definition_4_35_6
public import stacks_project.Chap04.Lemma_4_42_6
public import stacks_project.Chap08.Definition_8_5_5
public import stacks_project.Chap08.Definition_8_6_5
public import stacks_project.Chap08.Lemma_8_13_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace CategoryTheory

open AlgebraicGeometry
open Bicategory
open Bicategory.InducedBicategory
open FibredInGroupoidsOver
open FibredInGroupoidsMor
open ObjectProperty
open scoped Bicategory

/- Domain-style sampling for Remark 4.29.3:
- primary domain: canonical owner-level examples of strict `2`-categories;
- sampled declarations:
  `InducedBicategory Cat Grpd.forgetToCat.obj`,
  `fibredInGroupoidsOverSubTwoCategory`,
  `stackInGroupoidsOverSubTwoCategory`,
  `StackInGroupoidsOver.ofProjection`;
- best owner abstraction: each example should be stated through its ambient owner `2`-category
  rather than through parallel local wrappers. For groupoids this owner is the induced
  bicategory inside `Cat`; for fibred categories and stacks it is the relevant chapter-level full
  sub-`2`-category owner.
- primitive data: the ambient owner objects themselves;
- derived API: the inherited object types, owner homs, the diagonal representability predicate,
  the atlas predicate `p.LocallyEssentiallySurjectiveOnObjects`, and the representable stack
  bridge `StackInGroupoidsOver.ofProjection J_fppf (Over.forget U)`.

Source/core/bridge triage:
- `source-facing`: the textbook list of strict `2`-category examples;
- `core/canonical`: `Cat`, `InducedBicategory Cat Grpd.forgetToCat.obj`,
  `fibredCategoryOverSubTwoCategory C`, `fibredInGroupoidsOverSubTwoCategory C`,
  `stackOverSubTwoCategory J`, `stackInGroupoidsOverSubTwoCategory J`,
  `stackInSetoidsOverSubTwoCategory J`, and `StackInGroupoidsOver J_fppf`;
- `bridge/view`: the inherited object types together with
  `StackInGroupoidsOver.ofProjection J_fppf (Over.forget U)` and
  `representable_diagonal_iff_all_slice_morphisms_representable`. -/

variable {A B : Cat}

/- Remark 4.29.3 (Stacks tag `003J`): the ambient strict `2`-category of categories is the
canonical large category `Cat`, and its hom-categories are the ordinary functor categories. -/
recall Cat
#check (A ⥤ B)

variable {G₁ G₂ : Grpd}

/- Another listed example is the full sub-`2`-category of groupoids inside `Cat`. Its
owner-level strict `2`-category surface is the induced bicategory on `Grpd` through
`Grpd.forgetToCat.obj`, while the bundled category `Grpd` remains the companion object/
`1`-morphism view. -/
#check InducedBicategory Cat Grpd.forgetToCat.obj
#check (inferInstance : Strict (InducedBicategory Cat Grpd.forgetToCat.obj))
recall Grpd
#check (G₁ ⥤ G₂)
#check Grpd.forgetToCat

variable {C : Type u} [Category.{v} C]
variable {X Y : FibredCategoryOver C}

/- Over a fixed base `C`, categories fibred over `C` are formalized by the full sub-`2`-category
owner `fibredCategoryOverSubTwoCategory C`; its object type is `FibredCategoryOver C`, with
ambient hom-categories `X ⟶ Y`. -/
#check fibredCategoryOverSubTwoCategory C
#check FibredCategoryOver C
#check (X ⟶ Y)

variable {Xg Yg : FibredInGroupoidsOver C}

/- Categories fibred in groupoids over `C` are formalized by the full sub-`2`-category owner
`fibredInGroupoidsOverSubTwoCategory C`; its object type is `FibredInGroupoidsOver C`, and the
ambient owner homs are `Xg ⟶ Yg`. -/
#check fibredInGroupoidsOverSubTwoCategory C
#check FibredInGroupoidsOver C
#check (Xg ⟶ Yg)

variable (J : GrothendieckTopology C)
variable {S T : StackOver J}

/- Over a fixed site `(C, J)`, stacks are formalized by the full sub-`2`-category owner
`stackOverSubTwoCategory J`; its object type is `StackOver J`, with ambient hom-categories
`S ⟶ T`. -/
#check stackOverSubTwoCategory J
#check StackOver J
#check (S ⟶ T)

variable {Sg Tg : StackInGroupoidsOver J}

/- Stacks in groupoids over `(C, J)` are already packaged by the canonical owner
`stackInGroupoidsOverSubTwoCategory J`; their object type is `StackInGroupoidsOver J`. -/
#check stackInGroupoidsOverSubTwoCategory J
#check StackInGroupoidsOver J
#check (Sg ⟶ Tg)

variable {Ss Ts : StackInSetoidsOver J}

/- Likewise, stacks in setoids over `(C, J)` are the canonical full sub-`2`-category
`stackInSetoidsOverSubTwoCategory J` of stacks in groupoids, with object type
`StackInSetoidsOver J`. -/
#check stackInSetoidsOverSubTwoCategory J
#check StackInSetoidsOver J
#check (Ss ⟶ Ts)

section AlgebraicStacks

open StackInGroupoidsOver.Hom

variable (Xscheme : Scheme.{w})
variable {U : Over Xscheme}
local notation "J_fppf" => Scheme.fppfTopology.over Xscheme
variable (𝒳 : StackInGroupoidsOver J_fppf)

local instance overForget_isStackInGroupoids (U : Over Xscheme) :
    IsStackInGroupoids J_fppf (Over.forget U) := by
  refine
    { toIsStackOnSite := by
        rw [over_forget_isStackOnSite_iff_representable_isSheaf]
        exact
          (isSheaf_iff_isSheaf_of_type J_fppf (yoneda.obj U)).2
            (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj U))
      toIsFibredInGroupoids := inferInstance }

/- The fixed-site ambient owner for the algebraic-stack example is the `2`-category of stacks in
groupoids on the fppf site over `Xscheme`. Representable objects in this owner are the canonical
stacks `X/U` obtained from the slice projections `Over.forget U`. -/
#check J_fppf
#check StackInGroupoidsOver J_fppf

/- The slice projection over an object of `Over Xscheme` is a stack in groupoids for the induced
fppf topology on `Over Xscheme`, so the canonical representable stack `X/U` is obtained directly
from `StackInGroupoidsOver.ofProjection`; no extra named instance is part of the public API. -/
#check StackInGroupoidsOver.ofProjection J_fppf (Over.forget U)

/- For a stack in groupoids `𝒳` on the fppf site over `Xscheme`, the source-facing algebraic-stack
conditions live directly on the owner surface: the base projection has representable diagonal,
and some representable stack `X/U` admits an atlas morphism that is locally essentially
surjective on objects. -/
#check 𝒳.toFibredInGroupoidsOver.baseProjection.diagonalMor.IsRepresentable
#check ∃ (U : Over Xscheme)
    (p : StackInGroupoidsOver.ofProjection J_fppf (Over.forget U) ⟶ 𝒳),
      p.LocallyEssentiallySurjectiveOnObjects

/- The slice criterion from Lemma 4.42.6 remains the companion reformulation of the diagonal
condition, rather than the main owner-level algebraic-stack surface. -/
#check representable_diagonal_iff_all_slice_morphisms_representable

end AlgebraicStacks

end CategoryTheory
