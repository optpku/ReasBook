module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_12_4
public import stacks_project.Chap07.Definition_7_14_1
public import stacks_project.Chap07.Lemma_7_25_2
public import stacks_project.Chap07.Lemma_7_25_9
public import stacks_project.Chap07.Lemma_7_25_8
public import stacks_project.Chap07.Remark_7_25_10

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open Opposite

universe w u₁ u₂ v₁ v₂ v₃

noncomputable section

namespace CategoryTheory

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/- Domain-style sampling for Lemma 7.28.1:
- primary domain: the slice functor `Over.post u : D/V ⥤ C/u(V)` attached to a morphism of sites
  and the induced comparison on direct images;
- sampled owner API:
  `Over.post`,
  `Functor.IsContinuous`,
  `RepresentablyFlat`,
  `IsMorphismOfSites`,
  `Functor.sheafPushforwardContinuousComp'`;
- source/core/bridge triage:
  `source-facing`: the localized morphism of sites `(D/V, JD.over V) ⟶ (C/u(V), JC.over u(V))`
  induced by `u`;
  `core/canonical`: the owner predicates `Functor.IsContinuous`, `RepresentablyFlat`,
  `IsMorphismOfSites`, and the pushforward comparison
  `Functor.sheafPushforwardContinuousComp'`;
  `bridge/view`: the slice specialization of those owner declarations.

Primitive data are only the functor `u`, the object `V`, and the site structures. The remaining
source-faithful blocker is the localization proof that `Over.post u` is continuous; once that is
supplied, the site-morphism and pushforward-comparison statements are owner-level corollaries.
-/

/- The flatness proof follows the source route: identify the slice structured-arrow category of
`Over.post u` with an over-category in the ambient structured-arrow category of `u`, then transport
cofilteredness across that equivalence. -/
/-- Helper for Lemma 7.28.1: send an object of `StructuredArrow Y (Over.post u)` to the
corresponding object of `Over (StructuredArrow.mk Y.hom)`. -/
abbrev structuredArrow_overPost_to_over_obj
    (u : D ⥤ C) (V : D) (Y : Over (u.obj V))
    (A : StructuredArrow Y (show Over V ⥤ Over (u.obj V) from Over.post u)) :
    Over (StructuredArrow.mk Y.hom : StructuredArrow Y.left u) := by
  -- The map `Y ⟶ u(A.right.left)/u(V)` is exactly a map into the ambient structured arrow
  -- `StructuredArrow.mk Y.hom`.
  let Z : StructuredArrow Y.left u := StructuredArrow.mk A.hom.left
  exact CostructuredArrow.mk
    (StructuredArrow.homMk (f := Z) (f' := StructuredArrow.mk Y.hom) A.right.hom (by
      simpa using A.hom.w))

/-- Helper for Lemma 7.28.1: send a morphism in `StructuredArrow Y (Over.post u)` to the
corresponding morphism in `Over (StructuredArrow.mk Y.hom)`. -/
abbrev structuredArrow_overPost_to_over_hom
    (u : D ⥤ C) (V : D) (Y : Over (u.obj V))
    {A B : StructuredArrow Y (show Over V ⥤ Over (u.obj V) from Over.post u)}
    (f : A ⟶ B) :
    structuredArrow_overPost_to_over_obj u V Y A ⟶
      structuredArrow_overPost_to_over_obj u V Y B := by
  -- The underlying map in `Over V` already satisfies the required compatibility over `u`.
  exact Over.homMk
    (StructuredArrow.homMk f.right.left (by
      simpa using (congrArg CommaMorphism.left f.w).symm))
    (by
      simpa using Over.w f.right)

/-- Helper for Lemma 7.28.1: recover an object of `StructuredArrow Y (Over.post u)` from an
object of `Over (StructuredArrow.mk Y.hom)`. -/
abbrev over_to_structuredArrow_overPost_obj
    (u : D ⥤ C) (V : D) (Y : Over (u.obj V))
    (A : Over (StructuredArrow.mk Y.hom : StructuredArrow Y.left u)) :
    StructuredArrow Y (show Over V ⥤ Over (u.obj V) from Over.post u) := by
  -- The right leg of the over-object is the corresponding object of `Over V`.
  let Z : Over V := CostructuredArrow.mk A.hom.right
  exact StructuredArrow.mk
    (Over.homMk (U := Y) (V := (Over.post u).obj Z) A.left.hom (by
      simpa using A.hom.w.symm))

/-- Helper for Lemma 7.28.1: recover a morphism in `StructuredArrow Y (Over.post u)` from a
morphism in `Over (StructuredArrow.mk Y.hom)`. -/
abbrev over_to_structuredArrow_overPost_hom
    (u : D ⥤ C) (V : D) (Y : Over (u.obj V))
    {A B : Over (StructuredArrow.mk Y.hom : StructuredArrow Y.left u)}
    (f : A ⟶ B) :
    over_to_structuredArrow_overPost_obj u V Y A ⟶
      over_to_structuredArrow_overPost_obj u V Y B := by
  -- The left component gives the structured-arrow compatibility, and the right component is the
  -- desired map in `Over V`.
  refine StructuredArrow.homMk ?_ ?_
  · exact Over.homMk f.left.right (by
      simpa using congrArg CommaMorphism.right (Over.w f))
  · ext
    simpa using f.left.w.symm

/-- Helper for Lemma 7.28.1: translating a structured-arrow morphism to the over-side and back
recovers the original morphism. -/
theorem over_to_structuredArrow_overPost_hom_structuredArrow_overPost_to_over_hom
    (u : D ⥤ C) (V : D) (Y : Over (u.obj V))
    {A B : StructuredArrow Y (show Over V ⥤ Over (u.obj V) from Over.post u)}
    (f : A ⟶ B) :
    over_to_structuredArrow_overPost_hom u V Y
        (structuredArrow_overPost_to_over_hom u V Y f) = f := by
  -- Both comma morphisms have the same right component in `Over V`.
  ext
  rfl

/-- Helper for Lemma 7.28.1: translating an over-side morphism to the structured-arrow side and
back recovers the original morphism. -/
theorem structuredArrow_overPost_to_over_hom_over_to_structuredArrow_overPost_hom
    (u : D ⥤ C) (V : D) (Y : Over (u.obj V))
    {A B : Over (StructuredArrow.mk Y.hom : StructuredArrow Y.left u)}
    (f : A ⟶ B) :
    structuredArrow_overPost_to_over_hom u V Y
        (over_to_structuredArrow_overPost_hom u V Y f) = f := by
  -- Both over-morphisms have the same left component in `StructuredArrow Y.left u`.
  ext
  rfl

/-- Helper for Lemma 7.28.1: the structured-arrow category governing slice flatness is
equivalent to the over-category on the corresponding ambient structured arrow. -/
noncomputable def structuredArrow_overPost_equiv_over_structuredArrow
    (u : D ⥤ C) (V : D) (Y : Over (u.obj V)) :
    StructuredArrow Y (show Over V ⥤ Over (u.obj V) from Over.post u) ≌
      Over (StructuredArrow.mk Y.hom : StructuredArrow Y.left u) where
  functor :=
    { obj := structuredArrow_overPost_to_over_obj u V Y
      map := fun f ↦ structuredArrow_overPost_to_over_hom u V Y f }
  inverse :=
    { obj := over_to_structuredArrow_overPost_obj u V Y
      map := fun f ↦ over_to_structuredArrow_overPost_hom u V Y f }
  unitIso := NatIso.ofComponents
    (fun A ↦
      -- The round-trip only repackages the same object of `Over V`.
      StructuredArrow.isoMk (Over.isoMk (Iso.refl _)))
    (by
      intro A B f
      ext
      simp)
  counitIso := NatIso.ofComponents
    (fun A ↦
      -- The reverse round-trip only repackages the same object of the ambient over-category.
      Over.isoMk (StructuredArrow.isoMk (Iso.refl _)))
    (by
      intro A B f
      ext
      simp)

/-- Helper for Lemma 7.28.1: forgetting the target slice after `Over.post u` recovers the base
functor `u`. -/
theorem overPost_comp_forget_eq
    (u : D ⥤ C) (V : D) :
    Over.post u ⋙ Over.forget (u.obj V) = Over.forget V ⋙ u := by
  -- This is the strict specialization of the definition of `Over.post`.
  rfl

/-- Helper for Lemma 7.28.1: after transporting a slice sieve back to the base category, pushing
it forward along `Over.post u` is the same as pushing the transported sieve forward along `u`. -/
theorem overEquiv_functorPushforward_post
    (u : D ⥤ C) {V : D} {Y : Over V} (S : Sieve Y) :
    Sieve.overEquiv ((Over.post u).obj Y) (S.functorPushforward (Over.post u)) =
      (Sieve.overEquiv Y S).functorPushforward u := by
  -- Both sides are the pushforward of `S` along the same composite
  -- `Over.forget V ⋙ u = Over.post u ⋙ Over.forget (u.obj V)`.
  change
      Sieve.functorPushforward (Over.forget (u.obj V))
          (S.functorPushforward (Over.post u)) =
        Sieve.functorPushforward u (Sieve.functorPushforward (Over.forget V) S)
  rw [← Sieve.functorPushforward_comp, ← Sieve.functorPushforward_comp]
  rfl


end

end CategoryTheory
