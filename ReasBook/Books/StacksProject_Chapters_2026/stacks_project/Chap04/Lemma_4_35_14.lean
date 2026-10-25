module

public import stacks_project.Chap04.Definition_4_35_1
public import stacks_project.Chap04.Lemma_4_33_2
public import stacks_project.Chap04.Lemma_4_33_12
public import stacks_project.Chap04.Lemma_4_35_2
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe uA uB uC vA vB vC

namespace CategoryTheory.Functor

open CategoryTheory.IsHomLift

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]

/- Domain-style sampling for Lemma 4.35.14:
- primary domain: fibered categories in groupoids and stability under functor composition;
- inspected owner-level declarations:
  `CategoryTheory.IsFibredInGroupoids`,
  `Functor.isFibered_comp`,
  `CategoryTheory.isFibredInGroupoids_of_isFibered_and_fiber_groupoid`,
  `Functor.IsStronglyCartesian.isIso_of_base_isIso`;
- best owner abstraction: the source-facing notion remains `IsFibredInGroupoids`, and the proof
  should pass through the fiberwise criterion of Lemma 4.35.2 rather than a direct composition
  argument for strongly cartesian morphisms;
- primitive data: the two input `IsFibredInGroupoids` instances on `F` and `G`;
- derived API: the induced `IsFibredInGroupoids` instance on the composite functor `F ⋙ G`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that a composite of functors fibred in groupoids is
  again fibred in groupoids;
- `core/canonical`: `Functor.IsFibered`, `Functor.IsStronglyCartesian`, `Functor.Fiber`;
- `bridge/view`: the helper lemmas below, which implement the textbook sentence that a morphism in
  a composite fiber maps to an isomorphism in the intermediate fiber. -/

/-- Helper for Lemma 4.35.14: a morphism in the fiber of `F ⋙ G` over `U` maps under `F` to a
morphism in the fiber of `G` over `U`. -/
private theorem mapped_hom_in_target_fiber
    (F : A ⥤ B) (G : B ⥤ C)
    [IsFibredInGroupoids F] [IsFibredInGroupoids G]
    (U : C) {X Y : (F ⋙ G).Fiber U} (φ : X ⟶ Y) :
    G.IsHomLift (𝟙 U) (F.map φ.1) := by
  letI : (F ⋙ G).IsHomLift (𝟙 U) φ.1 := φ.2
  -- The underlying morphism of `φ` already lies over `𝟙 U` for the composite functor.
  -- Rewriting that lift equation for `F ⋙ G` exposes the needed lift condition for `G`.
  refine IsHomLift.of_fac' G (𝟙 U) (F.map φ.1) X.2 Y.2 ?_
  simpa [Functor.comp_map] using IsHomLift.fac' (p := F ⋙ G) (𝟙 U) φ.1

/-- Helper for Lemma 4.35.14: the underlying morphism of a morphism in the composite fiber is an
isomorphism in `A`. -/
private theorem composite_fiber_underlying_hom_isIso
    (F : A ⥤ B) (G : B ⥤ C)
    [IsFibredInGroupoids F] [IsFibredInGroupoids G]
    (U : C) {X Y : (F ⋙ G).Fiber U} (φ : X ⟶ Y) :
    IsIso φ.1 := by
  letI : G.IsHomLift (𝟙 U) (F.map φ.1) := mapped_hom_in_target_fiber F G U φ
  -- Inside the fiber `G_U`, every morphism is invertible because `G` is fibred in groupoids.
  haveI : IsIso (Functor.Fiber.homMk G U (F.map φ.1)) :=
    CategoryTheory.IsFibredInGroupoids.hom_isIso (p := G) U
      (Functor.Fiber.homMk G U (F.map φ.1))
  haveI : IsIso (F.map φ.1) := by
    simpa using
      (inferInstance :
        IsIso
          ((Functor.Fiber.fiberInclusion : G.Fiber U ⥤ B).map
            (Functor.Fiber.homMk G U (F.map φ.1))))
  -- The morphism `φ.1` is strongly cartesian for `F`, so Lemma 4.33.2 upgrades the base
  -- isomorphism `F.map φ.1` to an isomorphism upstairs in `A`.
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso F (F.map φ.1) φ.1

/-- Helper for Lemma 4.35.14: a morphism in the fiber of `F ⋙ G` over `U` is an isomorphism in the
fiber category itself. -/
private theorem composite_fiber_hom_isIso
    (F : A ⥤ B) (G : B ⥤ C)
    [IsFibredInGroupoids F] [IsFibredInGroupoids G]
    (U : C) {X Y : (F ⋙ G).Fiber U} (φ : X ⟶ Y) :
    IsIso φ := by
  letI : (F ⋙ G).IsHomLift (𝟙 U) φ.1 := φ.2
  haveI : IsIso φ.1 := composite_fiber_underlying_hom_isIso F G U φ
  let e := asIso φ.1
  -- The inverse of the ambient vertical isomorphism still lies over `𝟙 U`, so it defines the
  -- inverse morphism in the composite fiber.
  refine ⟨⟨⟨e.inv, ?_⟩, ?_, ?_⟩⟩
  · simpa [e] using IsHomLift.lift_id_inv_isIso (p := F ⋙ G) U φ.1
  · apply Functor.Fiber.hom_ext
    change φ.1 ≫ e.inv = 𝟙 X.1
    simp [e]
  · apply Functor.Fiber.hom_ext
    change e.inv ≫ φ.1 = 𝟙 Y.1
    simp [e]

/-- Helper for Lemma 4.35.14: every standard fiber of the composite functor `F ⋙ G` is a
groupoid. -/
private theorem composite_fiber_isGroupoid
    (F : A ⥤ B) (G : B ⥤ C)
    [IsFibredInGroupoids F] [IsFibredInGroupoids G]
    (U : C) :
    IsGroupoid ((F ⋙ G).Fiber U) := by
  -- Each morphism in the composite fiber is invertible by the previous helper.
  exact
    { all_isIso := fun φ ↦ composite_fiber_hom_isIso F G U φ }

-- Proof sketch: use Lemma 4.33.12 to obtain that `F ⋙ G` is fibred, then apply the criterion of
-- Lemma 4.35.2. A morphism in the composite fiber over `U` maps to a morphism in `G.Fiber U`,
-- hence is invertible there because `G` is fibred in groupoids. Since every morphism in `A` is
-- strongly cartesian for `F`, Lemma 4.33.2 upgrades that base isomorphism to an isomorphism in
-- `A`, and therefore the composite fiber is a groupoid.
/-- Lemma 4.35.14: if `F : A ⥤ B` is fibred in groupoids over `B` and `G : B ⥤ C` is fibred in
groupoids over `C`, then the composite functor `F ⋙ G : A ⥤ C` is fibred in groupoids over
`C`. -/
instance isFibredInGroupoids_comp
    (F : A ⥤ B) (G : B ⥤ C)
    [IsFibredInGroupoids F] [IsFibredInGroupoids G] :
    IsFibredInGroupoids (F ⋙ G) := by
  -- Route correction: follow the source proof through Lemma 4.35.2 instead of the direct
  -- strongly-cartesian composition argument.
  have hFibered : (F ⋙ G).IsFibered := inferInstance
  -- The fiberwise groupoid condition comes from the intermediate fiber `G_U` and Lemma 4.33.2.
  have hFiberGroupoid : ∀ U : C, IsGroupoid ((F ⋙ G).Fiber U) :=
    fun U ↦ composite_fiber_isGroupoid F G U
  -- Lemma 4.35.2 packages fiberedness plus groupoid fibers into the desired structure.
  exact
    CategoryTheory.isFibredInGroupoids_of_isFibered_and_fiber_groupoid
      (F ⋙ G) hFibered hFiberGroupoid

end CategoryTheory.Functor
