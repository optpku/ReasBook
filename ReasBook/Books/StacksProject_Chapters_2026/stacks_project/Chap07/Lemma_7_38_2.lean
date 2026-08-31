module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import stacks_project.Chap07.Definition_7_38_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe w v u w' w''

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C] [LocallySmall.{max u v w'} C]
variable {J : GrothendieckTopology C}
variable {I : Type w} (p : I → Point.{max u v w'} J)

/- Layering for Lemma 7.38.2:
- primary domain: conservative families of site points and their stalk functors on sheaves;
- sampled owner declarations:
  `ObjectProperty.IsConservativeFamilyOfPoints`,
  `ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectMonomorphisms`,
  `ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectEpimorphisms`,
  `ObjectProperty.IsConservativeFamilyOfPoints.jointlyFaithful`,
  `JointlyReflectIsomorphisms.jointlyReflectsLimit`,
  `JointlyReflectIsomorphisms.jointlyReflectsColimit`;
- source/core/bridge triage:
  `source-facing`: the stalkwise mono/epi/equality and finite limit/colimit detection statements
    for sheaves of sets;
  `core/canonical`: `(ofObj p).IsConservativeFamilyOfPoints`;
  `bridge/view`: these theorems are thin source-facing specializations of the owner-level jointly
    reflective API to indexed families of stalk functors on `Sheaf J (Type (max u v w'))`;
- core/canonical owner: `(ofObj p).IsConservativeFamilyOfPoints`;
- primitive data: only the indexed family `p` and the conservativity hypothesis `hp`;
- derived API here: the set-valued stalkwise mono/epi/equality criteria and finite
  (co)limit detection consequences.
-/

variable {ℱ 𝒢 : Sheaf J (Type (max u v w'))}

omit [LocallySmall.{max u v w'} C] in
/-- Helper for Lemma 7.38.2: the stalk functors indexed by a conservative family of points jointly
reflect isomorphisms of sheaves of sets. -/
private theorem stalkJointlyReflectsIsomorphisms
    (hp : (ofObj p).IsConservativeFamilyOfPoints) :
    JointlyReflectIsomorphisms
      (fun i : I ↦
        ((p i).sheafFiber :
          Sheaf J (Type (max u v w')) ⥤ Type (max u v w'))) := by
  refine ⟨?_⟩
  intro X Y f hf
  let h := hp.jointlyReflectIsomorphisms (Type (max u v w'))
  let _ : ∀ Φ : (ofObj p).FullSubcategory, IsIso (Φ.obj.sheafFiber.map f) := fun Φ ↦ by
    rcases (ofObj_iff p Φ.obj).1 Φ.property with ⟨i, hi⟩
    have hΦ : Φ = ⟨p i, ofObj_apply p i⟩ := by
      cases Φ
      simp only [FullSubcategory.mk.injEq] at hi ⊢
      cases hi
      rfl
    cases hΦ
    exact hf i
  exact h.isIso f

/-- Helper for Lemma 7.38.2: each stalk functor preserves the limit of a finite sheaf diagram. -/
private theorem preservesLimit_fiberFunctor
    {K : Type w''} [Category K] [FinCategory K]
    (q : Point.{max u v w'} J) (F : K ⥤ Sheaf J (Type (max u v w'))) :
    PreservesLimit F q.sheafFiber := by
  let _ :
      PreservesFiniteLimits (q.sheafFiber : Sheaf J (Type (max u v w')) ⥤ Type (max u v w')) :=
    by
      infer_instance
  infer_instance

omit [LocallySmall.{max u v w'} C] in
/-- Helper for Lemma 7.38.2: each stalk functor preserves the colimit of a finite sheaf diagram. -/
private theorem preservesColimit_fiberFunctor
    {K : Type w''} [Category K] [FinCategory K]
    (q : Point.{max u v w'} J) (F : K ⥤ Sheaf J (Type (max u v w'))) :
    PreservesColimit F q.sheafFiber := by
  let _ : PreservesFiniteColimits
      (q.sheafFiber : Sheaf J (Type (max u v w')) ⥤ Type (max u v w')) := by infer_instance
  infer_instance

-- Proof sketch: convert stalkwise injectivity into stalkwise monomorphisms in `Type`, then apply
-- the canonical owner theorem `hp.jointlyReflectMonomorphisms (Type _)`.
omit [LocallySmall.{max u v w'} C] in
/-- Lemma 7.38.2 (1): a morphism of sheaves of sets is a monomorphism if all induced maps on the
fibers at a conservative family of points are injective. -/
theorem sheaf_mono_of_stalkwise_injective
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ i, Function.Injective ((p i).sheafFiber.map φ)) :
    Mono φ := by
  rw [(hp.jointlyReflectMonomorphisms (Type (max u v w'))).mono_iff]
  intro Φ
  rcases Φ with ⟨q, hq⟩
  rcases (ofObj_iff p q).1 hq with ⟨i, rfl⟩
  exact (mono_iff_injective ((p i).sheafFiber.map φ)).2 (hφ i)

-- Proof sketch: convert stalkwise surjectivity into stalkwise epimorphisms in `Type`, then apply
-- the canonical owner theorem `hp.jointlyReflectEpimorphisms (Type _)`.
omit [LocallySmall.{max u v w'} C] in
/-- Lemma 7.38.2 (2): a morphism of sheaves of sets is an epimorphism if all induced maps on the
fibers at a conservative family of points are surjective. -/
theorem sheaf_epi_of_stalkwise_surjective
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ i, Function.Surjective ((p i).sheafFiber.map φ)) :
    Epi φ := by
  rw [(hp.jointlyReflectEpimorphisms (Type (max u v w'))).epi_iff]
  intro Φ
  rcases Φ with ⟨q, hq⟩
  rcases (ofObj_iff p q).1 hq with ⟨i, rfl⟩
  exact (epi_iff_surjective ((p i).sheafFiber.map φ)).2 (hφ i)

-- Proof sketch: this is the canonical joint-faithfulness consequence
-- `hp.jointlyFaithful (Type _)`, specialized back to the indexed family `p`.
omit [LocallySmall.{max u v w'} C] in
/-- Lemma 7.38.2 (3): two morphisms of sheaves of sets are equal if they induce the same map on the
fibers at every point of a conservative family. -/
theorem sheaf_hom_ext_of_stalkwise
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    {φ₁ φ₂ : ℱ ⟶ 𝒢}
    (hφ : ∀ i,
      (p i).sheafFiber.map φ₁ =
        (p i).sheafFiber.map φ₂) :
    φ₁ = φ₂ := by
  exact (hp.jointlyFaithful (Type (max u v w'))).map_injective fun Φ ↦ by
    rcases Φ with ⟨q, hq⟩
    rcases (ofObj_iff p q).1 hq with ⟨i, rfl⟩
    exact hφ i

variable {K : Type w''} [Category K] [FinCategory K]
variable {F : K ⥤ Sheaf J (Type (max u v w'))}

-- Proof sketch: each stalk functor preserves finite limits, so a limiting cone stays limiting
-- stalkwise. Conversely, if every mapped cone is limiting, equip `F` with the limit structure
-- coming from `c` and apply the generic owner theorem
-- `JointlyReflectIsomorphisms.jointlyReflectsLimit` to the conservative family of stalk functors.
omit [LocallySmall.{max u v w'} C] in
/-- Lemma 7.38.2 (4): for a finite diagram of sheaves of sets, a cone is limiting if and only if
each induced cone on the fibers at a conservative family of points is limiting. -/
theorem sheaf_isLimit_iff_stalkwise_isLimit
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    (c : Cone F) :
    Nonempty (IsLimit c) ↔
      ∀ i, Nonempty (IsLimit (((p i).sheafFiber).mapCone c)) := by
  constructor
  · rintro ⟨hc⟩ i
    let _ : PreservesLimit F (p i).sheafFiber :=
      preservesLimit_fiberFunctor (p i) F
    exact ⟨isLimitOfPreserves (p i).sheafFiber hc⟩
  · intro hc
    let h := stalkJointlyReflectsIsomorphisms p hp
    let _ : HasLimit F := by infer_instance
    let _ : ∀ i : I, PreservesLimit F (p i).sheafFiber := fun i ↦
      preservesLimit_fiberFunctor (p i) F
    refine ⟨h.jointlyReflectsLimit ?_⟩
    intro i
    exact Classical.choice (hc i)

-- Proof sketch: each stalk functor preserves finite colimits, so a colimiting cocone stays
-- colimiting stalkwise. Conversely, if every mapped cocone is colimiting, equip `F` with the
-- colimit structure coming from `c` and apply the generic owner theorem
-- `JointlyReflectIsomorphisms.jointlyReflectsColimit` to the conservative family of stalk
-- functors.
omit [LocallySmall.{max u v w'} C] in
/-- Lemma 7.38.2 (5): for a finite diagram of sheaves of sets, a cocone is colimiting if and only
if each induced cocone on the fibers at a conservative family of points is colimiting. -/
theorem sheaf_isColimit_iff_stalkwise_isColimit
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    (c : Cocone F) :
    Nonempty (IsColimit c) ↔
      ∀ i, Nonempty (IsColimit (((p i).sheafFiber).mapCocone c)) := by
  constructor
  · rintro ⟨hc⟩ i
    let _ : PreservesColimit F (p i).sheafFiber :=
      preservesColimit_fiberFunctor (p i) F
    exact ⟨isColimitOfPreserves (p i).sheafFiber hc⟩
  · intro hc
    let h := stalkJointlyReflectsIsomorphisms p hp
    let _ : HasColimit F := by infer_instance
    let _ : ∀ i : I, PreservesColimit F (p i).sheafFiber := fun i ↦
      preservesColimit_fiberFunctor (p i) F
    refine ⟨h.jointlyReflectsColimit ?_⟩
    intro i
    exact Classical.choice (hc i)

end

end GrothendieckTopology
end CategoryTheory
