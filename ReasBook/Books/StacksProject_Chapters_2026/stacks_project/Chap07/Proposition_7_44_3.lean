module

public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Lemma_6_15_2
public import stacks_project.Chap07.Definition_7_14_1
public import stacks_project.Chap07.Remark_7_15_4
public import stacks_project.Chap07.Lemma_7_44_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v w

namespace CategoryTheory

open scoped MorphismOfTopoiIn

/-
Domain-style sampling for Proposition 7.44.3:
- primary domain: morphisms of topoi and the induced inverse-image and direct-image functors on
  sheaves of
  algebraic structures;
- sampled owner API:
  `MorphismOfTopoiIn.presentationFunctor_pushforwardIso`,
  `Functor.sheafAdjunctionContinuous`,
  `sheaf_pushforward_forget`,
  `sheaf_pullback_forget`;
- source/core/bridge triage:
  `source-facing`: the Stacks comparison between a presented morphism of topoi and the induced
  inverse-image and direct-image functors on sheaves of algebraic structures;
  `core/canonical`: the topoi-presentation comparison isomorphisms from `Remark_7_15_4` and the
  forget-compatibility owners from `Lemma_7_44_2`;
  `bridge/view`: the two whiskered comparison expressions below.

Primitive data are only the morphism-of-sites presentation and the algebraic-structure owner
`IsAlgebraicStructure A (forget A)`. The comparison isomorphisms are derived bridge API, so this
file should recall the upstream owners directly and keep only the thin whiskered comparison
expressions below.
-/

section MorphismOfTopoi

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Proposition 7.44.3: for a morphism of topoi `f : Sh(K) ⟶ Sh(J)`, the canonical presentation
`U ↦ f⁻¹(h_U^#)` from `Remark_7_15_4` recovers the original direct-image functor on underlying
sheaves of sets. -/
recall MorphismOfTopoiIn.presentationFunctor_pushforwardIso

end MorphismOfTopoi

section AlgebraicStructures

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Proposition 7.44.3: the additional Stacks examples of sheaves of algebraic structures are
obtained by applying the general sheaf-theoretic constructions to the standard algebraic-structure
categories already recorded in Lemma 6.15.2. The listed categories are therefore reused directly,
rather than repackaged into a new conjunction theorem. -/
recall pointed_sets_algebraic_structure_type
recall abelian_groups_algebraic_structure_type
recall groups_algebraic_structure_type
recall monoids_algebraic_structure_type
recall rings_algebraic_structure_type
recall modules_algebraic_structure_type (R : Type w) [Ring R] :
  IsAlgebraicStructure (ModuleCat.{w} R) (forget (ModuleCat.{w} R))
recall lie_algebras_algebraic_structure_type (R : Type w) [CommRing R] :
  IsAlgebraicStructure (LieAlgebraCat R) (forget (LieAlgebraCat R))

variable (A : Type w) [Category.{max u₁ u₂ v} A]
variable {FA : A → A → Type (max u₁ u₂ v)} {CA : A → Type (max u₁ u₂ v)}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
variable [IsAlgebraicStructure A (forget A)]
variable (u : C ⥤ D)

variable [IsMorphismOfSites J K u]
variable [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
variable [HasWeakSheafify K A]

/- Proposition 7.44.3: on sheaves of algebraic structures, the induced inverse-image and
direct-image functors are the canonical adjoint pair `u.sheafPullback A J K ⊣
u.sheafPushforwardContinuous A J K`. -/
recall Functor.sheafAdjunctionContinuous

variable [J.HasSheafCompose (forget A)] [K.HasSheafCompose (forget A)]
variable {f : MorphismOfTopoiIn J K}
variable (ePush : u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K ≅ f _*)

/- Proposition 7.44.3: if the direct-image functor of a morphism of topoi
`f : Sh(K) ⟶ Sh(J)` is presented on underlying sheaves of sets by the continuous functor `u`,
then the induced direct image on sheaves of `A`-valued algebraic structures forgets to the direct
image of `f`; this is exactly the canonical forget-comparison from `Lemma_7_44_2`, whiskered with
the presentation isomorphism `ePush`. -/
#check
  (eqToIso (sheaf_pushforward_forget J K u) ≪≫
      (sheafCompose K (forget A)).isoWhiskerLeft ePush :
    u.sheafPushforwardContinuous A J K ⋙ sheafCompose J (forget A) ≅
      sheafCompose K (forget A) ⋙ f _*)

/- Proposition 7.44.3: the induced direct-image functor on sheaves of algebraic structures
commutes with forgetting to sheaves of sets. -/
recall sheaf_pushforward_forget

variable [∀ P : Cᵒᵖ ⥤ Type (max u₁ u₂ v), u.op.HasLeftKanExtension P]
variable [(forget A).PreservesLeftKanExtensions u.op]
variable [HasWeakSheafify K (Type (max u₁ u₂ v))]
variable [K.PreservesSheafification (forget A)]
variable (eInv : u.sheafPullback (Type (max u₁ u₂ v)) J K ≅ f⁻¹)

/- Proposition 7.44.3: if the inverse-image functor of a morphism of topoi
`f : Sh(K) ⟶ Sh(J)` is presented on underlying sheaves of sets by the continuous functor `u`,
then the induced inverse image on sheaves of `A`-valued algebraic structures forgets to the
inverse image of `f`; this is exactly the canonical forget-comparison from `Lemma_7_44_2`,
whiskered with the presentation isomorphism `eInv`. -/
#check
  (sheaf_pullback_forget J K u ≪≫
      (sheafCompose J (forget A)).isoWhiskerLeft eInv :
    u.sheafPullback A J K ⋙ sheafCompose K (forget A) ≅
      sheafCompose J (forget A) ⋙ f⁻¹)

/- Proposition 7.44.3: the induced inverse-image functor on sheaves of algebraic structures
commutes with forgetting to sheaves of sets. -/
recall sheaf_pullback_forget

end AlgebraicStructures

end CategoryTheory
