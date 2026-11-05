module

public import stacks_project.Chap04.Example_4_2_12
public import stacks_project.Chap04.Definition_4_33_5
public import stacks_project.Chap04.Lemma_4_35_2

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor IsHomLift Functor.Fiber
open CategoryTheory.SingleObj

universe u v

namespace MonoidHom

variable {G : Type u} {H : Type v} [Group G] [Monoid H]

/- Domain-style sampling for Example 4.35.4:
- primary domain: fibered categories attached to `MonoidHom.toFunctor` from a one-object
  groupoid to a one-object category;
- inspected owner-level declarations:
  `MonoidHom.toFunctor`,
  `Functor.IsFibered`,
  `CategoryTheory.IsFibredInGroupoids`,
  `Functor.Fiber`.
- best owner abstraction: the canonical owner is `p.toFunctor`, with fibredness expressed by
  `Functor.IsFibered` and the groupoid upgrade expressed by `IsFibredInGroupoids`.
- primitive data: the monoid homomorphism `p : G →* H`.
- derived API: the induced equivalence from the standard fiber of `p.toFunctor` to
  `SingleObj ↥(p.ker)`, together with the characterization of
  `IsFibredInGroupoids p.toFunctor` via surjectivity.

Source/core/bridge triage:
- `source-facing`: the two textbook clauses specialized to `p.toFunctor`.
- `core/canonical`: `Functor.IsFibered`, `IsFibredInGroupoids`, and `Functor.Fiber`.
- `bridge/view`: the canonical lift of `p.ker.subtype.toFunctor` into the standard fiber of
  `p.toFunctor`, the induced equivalence with `SingleObj ↥(p.ker)`, and the surjectivity
  criterion for the owner predicate. -/

/-- A vertical morphism in the fiber corresponds to an element of `ker p`. -/
-- Proof sketch: a morphism in `p.toFunctor.Fiber (SingleObj.star H)` lies over the identity of
-- the unique base object, so the defining equation `IsHomLift.fac'` forces its image under `p`
-- to be `1`.
private theorem fiberHom_mem_ker (p : G →* H) {x y : p.toFunctor.Fiber (star H)}
    (φ : x ⟶ y) : (φ.1 : G) ∈ p.ker := by
  letI : p.toFunctor.IsHomLift (𝟙 (star H)) φ.1 := φ.2
  change p φ.1 = 1
  simpa [toFunctor, mapHom, x.2, y.2] using
    (IsHomLift.fac' p.toFunctor (𝟙 (star H)) φ.1)

/-- For a homomorphism `p : G →* H` from a group to a monoid, the induced one-object-category
functor is fibered exactly when `p` is surjective. -/
-- Proof sketch: fibredness for `p.toFunctor` is the strongly-cartesian lift criterion from
-- `isFibered_iff_exists_isStronglyCartesian`. In a one-object source and base, such a lift is
-- exactly a preimage of the given element of `H`, so the criterion reduces to surjectivity.
theorem toFunctor_isFibered_iff_surjective (p : G →* H) :
    p.toFunctor.IsFibered ↔ Function.Surjective p := by
  constructor
  · intro hp h
    obtain ⟨⟨⟩, φ, hφ⟩ :=
      (isFibered_iff_exists_isStronglyCartesian p.toFunctor).1 hp
        (star G) (star H) h
    have hEq : h = p.toFunctor.map φ := by
      have hLift : p.toFunctor.IsHomLift h φ := hφ.toIsHomLift
      cases hLift
      rfl
    exact ⟨φ, by simpa using hEq.symm⟩
  · intro hp
    exact (isFibered_iff_exists_isStronglyCartesian p.toFunctor).2 fun x V f ↦ by
      cases x
      cases V
      obtain ⟨g, rfl⟩ := hp f
      let φ : star G ⟶ star G := g
      refine ⟨star G, φ, ?_⟩
      change p.toFunctor.IsStronglyCartesian (p.toFunctor.map φ) φ
      infer_instance

/- Internal bridge: the kernel inclusion `ker p ↪ G` induces a canonical functor from the
one-object groupoid `SingleObj ↥(p.ker)` into the standard fiber of `p.toFunctor` over the unique
object of `SingleObj H`. -/
theorem kernelToFiberCompConst (p : G →* H) :
    (Subgroup.subtype p.ker).toFunctor ⋙ p.toFunctor =
      (const (SingleObj ↥(p.ker))).obj (star H) := by
  fapply CategoryTheory.Functor.ext
  · intro X
    cases X
    rfl
  · intro X Y g
    cases X
    cases Y
    simpa using p.mem_ker.mp g.2

def kernelToFiberFunctor (p : G →* H) :
    SingleObj ↥(p.ker) ⥤ p.toFunctor.Fiber (star H) :=
  inducedFunctor (kernelToFiberCompConst p)

instance kernelSubtype_toFunctor_faithful (p : G →* H) :
    (Subgroup.subtype p.ker).toFunctor.Faithful :=
  (toFunctor_faithful_iff_injective (Subgroup.subtype p.ker)).2 Subtype.val_injective

instance kernelToFiberFunctor_faithful (p : G →* H) :
    (kernelToFiberFunctor p).Faithful :=
  Functor.Faithful.of_comp_eq <| by
    simpa [kernelToFiberFunctor] using inducedFunctor_comp (kernelToFiberCompConst p)

instance kernelToFiberFunctor_full (p : G →* H) :
    (kernelToFiberFunctor p).Full where
  map_surjective := by
    intro X Y φ
    cases X
    cases Y
    refine ⟨⟨φ.1, fiberHom_mem_ker p φ⟩, ?_⟩
    apply hom_ext
    rfl

instance kernelToFiberFunctor_essSurj (p : G →* H) :
    (kernelToFiberFunctor p).EssSurj := by
  apply essSurj_of_surj
  intro X
  cases X
  refine ⟨star ↥(p.ker), ?_⟩
  apply Subtype.ext
  rfl

instance kernelToFiberFunctor_isEquivalence (p : G →* H) :
    (kernelToFiberFunctor p).IsEquivalence :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem fiber_isGroupoid (p : G →* H) :
    IsGroupoid (p.toFunctor.Fiber (star H)) := by
  let e := (kernelToFiberFunctor p).asEquivalence.symm
  exact isGroupoid_of_reflects_iso e.functor

/-- Example 4.35.4 (2): the fiber category of `p.toFunctor` over the unique object of
`SingleObj H` is the one-object groupoid attached to the kernel of `p`. -/
noncomputable def toFunctorFiberEquivalenceKer (p : G →* H) :
    p.toFunctor.Fiber (star H) ≌ SingleObj ↥(p.ker) :=
  (kernelToFiberFunctor p).asEquivalence.symm

/-- The equivalence from the fiber of `p.toFunctor` to the one-object category of `ker p`
has an equivalence of categories as its forward functor. -/
-- Proof sketch: this is the standard `IsEquivalence` instance carried by the functor part of
-- any categorical equivalence.
theorem toFunctorFiberEquivalenceKer_functor_isEquivalence (p : G →* H) :
    (toFunctorFiberEquivalenceKer p).functor.IsEquivalence := by
  -- The forward functor of any equivalence carries the standard `IsEquivalence` instance.
  simpa using
    (CategoryTheory.Equivalence.isEquivalence_functor (toFunctorFiberEquivalenceKer p))

/-- Example 4.35.4 (1): for a homomorphism `p : G →* H` from a group to a monoid, the induced
functor `SingleObj G ⥤ SingleObj H` is fibred in groupoids exactly when `p` is surjective. -/
-- Proof sketch: if `p` is surjective, every arrow of the base category lifts to an arrow in
-- `SingleObj G`, and Lemma `4.35.2` reduces fibredness in groupoids to fibredness together with
-- the fact that the unique fiber is a groupoid; the latter follows from the kernel equivalence
-- above.
-- Conversely, fibredness over the unique object forces every element of `H` to have a lift in
-- `G`.
theorem toFunctor_isFibredInGroupoids_iff_surjective (p : G →* H) :
    IsFibredInGroupoids p.toFunctor ↔ Function.Surjective p := by
  constructor
  · intro hp
    exact (toFunctor_isFibered_iff_surjective p).1 hp.toIsFibered
  · intro hp
    refine
      isFibredInGroupoids_of_isFibered_and_fiber_groupoid p.toFunctor
        ((toFunctor_isFibered_iff_surjective p).2 hp) ?_
    intro U
    cases U
    exact fiber_isGroupoid p

end MonoidHom
