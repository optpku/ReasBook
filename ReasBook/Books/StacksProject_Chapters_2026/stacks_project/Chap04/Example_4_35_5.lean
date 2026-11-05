module

public import stacks_project.Chap04.Definition_4_33_5
public import stacks_project.Chap04.Definition_4_35_1
public import stacks_project.Chap04.Lemma_4_35_2

@[expose] public section

/- Domain-style sampling for Example 4.35.5:
- primary domain: fibred categories and fibred-in-groupoids counterexamples.
- inspected owner-level declarations:
  `Functor.IsHomLift`,
  `Functor.IsFibered`,
  `IsFibredInGroupoids`,
  `Functor.isFibered_iff_exists_isStronglyCartesian`,
  `isFibredInGroupoids_iff_isFibered_and_fiber_groupoid`.
- best owner abstraction: the canonical owner is `Functor.IsFibered`, with the chapter's
  source-facing predicate `IsFibredInGroupoids` built on top of it.
- primitive data: the explicit small categories `Base`, `NoLift`, `TwoLift`, and their projection
  functors to `Base`.
- derived API: the lift/nonlift facts for `Base.Hom.f`, the fiberwise groupoid facts, and the
  counterexample conclusions `¬ projection.IsFibered` and `¬ IsFibredInGroupoids projection`.

Source/core/bridge triage:
- `source-facing`: the two counterexample projections in Example 4.35.5.
- `core/canonical`: `Functor.IsHomLift`, `Functor.IsCartesian`, `Functor.IsFibered`,
  `Functor.Fiber`.
- `bridge/view`: `Functor.isFibered_iff_exists_isStronglyCartesian` together with
  `isFibredInGroupoids_iff_isFibered_and_fiber_groupoid`. -/

namespace CategoryTheory
open Functor IsHomLift IsCartesian

namespace Example4355

/-- Objects of the base category used in Example 4.35.5. -/
inductive Base where
  | A | B | T
  deriving DecidableEq, Repr

namespace Base

/-- Morphisms of the base category used in Example 4.35.5. -/
inductive Hom : Base → Base → Type where
  | id : (X : Base) → Hom X X
  | f : Hom .A .B
  | g : Hom .B .T
  | h : Hom .A .T
  deriving DecidableEq, Repr

namespace Hom

/-- Composition law on the base category of Example 4.35.5. -/
def comp : {X Y Z : Base} → Hom X Y → Hom Y Z → Hom X Z
  | _, _, _, id _, k => k
  | _, _, _, k, id _ => k
  | _, _, _, f, g => h

/-- Left identity for the base category composition. -/
-- Proof sketch: enumerate the finitely many well-typed morphisms in the base category.
theorem id_comp {X Y : Base} (k : Hom X Y) : comp (id X) k = k := by
  -- Enumerate the only well-typed morphism constructors in the finite base category.
  cases k <;> rfl

/-- Right identity for the base category composition. -/
-- Proof sketch: enumerate the finitely many well-typed morphisms in the base category.
theorem comp_id {X Y : Base} (k : Hom X Y) : comp k (id Y) = k := by
  -- Enumerate the only well-typed morphism constructors in the finite base category.
  cases k <;> rfl

/-- Associativity for the base category composition. -/
-- Proof sketch: case split on the only composable triples of non-identity arrows.
theorem assoc {W X Y Z : Base} (k : Hom W X) (l : Hom X Y) (m : Hom Y Z) :
    comp (comp k l) m = comp k (comp l m) := by
  -- The dependent types remove impossible triples, so a finite case split closes the proof.
  cases k <;> cases l <;> cases m <;> rfl

end Hom

/-- The explicit category structure on the base of Example 4.35.5. -/
instance : Category Base where
  Hom := Hom
  id := Hom.id
  comp := fun k l ↦ Hom.comp k l
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

end Base

/-- Objects of the source category where the arrow `f : A ⟶ B` has no lift. -/
inductive NoLift where
  | A' | B' | T'
  deriving DecidableEq, Repr

namespace NoLift

/-- Morphisms of the source category where the arrow `f : A ⟶ B` has no lift. -/
inductive Hom : NoLift → NoLift → Type where
  | id : (X : NoLift) → Hom X X
  | g : Hom .B' .T'
  | h : Hom .A' .T'
  deriving DecidableEq, Repr

namespace Hom

/-- Composition law on the source category with no lift of `f`. -/
def comp : {X Y Z : NoLift} → Hom X Y → Hom Y Z → Hom X Z
  | _, _, _, id _, k => k
  | _, _, _, k, id _ => k

/-- Left identity for the source category with no lift of `f`. -/
-- Proof sketch: enumerate the finitely many well-typed morphisms in the source category.
theorem id_comp {X Y : NoLift} (k : Hom X Y) : comp (id X) k = k := by
  -- Enumerate the only well-typed morphism constructors in the finite source category.
  cases k <;> rfl

/-- Right identity for the source category with no lift of `f`. -/
-- Proof sketch: enumerate the finitely many well-typed morphisms in the source category.
theorem comp_id {X Y : NoLift} (k : Hom X Y) : comp k (id Y) = k := by
  -- Enumerate the only well-typed morphism constructors in the finite source category.
  cases k <;> rfl

/-- Associativity for the source category with no lift of `f`. -/
-- Proof sketch: all nontrivial composites factor through identities, so the finite case split is immediate.
theorem assoc {W X Y Z : NoLift} (k : Hom W X) (l : Hom X Y) (m : Hom Y Z) :
    comp (comp k l) m = comp k (comp l m) := by
  -- Every composable triple reduces to identities in this category.
  cases k <;> cases l <;> cases m <;> rfl

end Hom

/-- The category structure on the first source category of Example 4.35.5. -/
instance : Category NoLift where
  Hom := Hom
  id := Hom.id
  comp := fun k l ↦ Hom.comp k l
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The object map of the first source projection in Example 4.35.5. -/
def objMap : NoLift → Base
  | .A' => .A
  | .B' => .B
  | .T' => .T

/-- The morphism map of the first source projection in Example 4.35.5. -/
def homMap :
    {X Y : NoLift} → Hom X Y → (objMap X ⟶ objMap Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, Hom.g => Base.Hom.g
  | _, _, Hom.h => Base.Hom.h

/-- The first source projection preserves identities. -/
-- Proof sketch: check the three objects of the source category directly.
theorem projection_map_id (X : NoLift) : homMap (𝟙 X) = 𝟙 (objMap X) := by
  -- The object map is explicit, so each identity is preserved by reflexivity.
  cases X <;> rfl

/-- The first source projection preserves composition. -/
-- Proof sketch: inspect the finitely many composable pairs of source morphisms.
private theorem projection_map_comp {X Y Z : NoLift} (k : Hom X Y) (l : Hom Y Z) :
    homMap (Hom.comp k l) = Base.Hom.comp (homMap k) (homMap l) := by
  -- The projection is defined by explicit images of the finitely many generators.
  cases k <;> cases l <;> rfl

/-- The projection from the first source category to the base category. -/
def projection : NoLift ⥤ Base where
  obj := objMap
  map := fun {_ _} k ↦ homMap k
  map_id := projection_map_id
  map_comp := by
    intro X Y Z k l
    -- Route correction: state preservation of composition using the explicit finite `comp`.
    simpa using projection_map_comp k l

/-- Helper for Example 4.35.5: every hom-set in a standard fiber of the first projection is a
singleton. -/
private abbrev fiber_hom_unique (U : Base) {X Y : projection.Fiber U} : Unique (X ⟶ Y) := by
  cases U with
  | A =>
      cases X with
      | mk X hX =>
          cases X with
          | A' =>
              cases hX
              cases Y with
              | mk Y hY =>
                  cases Y with
                  | A' =>
                      cases hY
                      refine { default := 𝟙 _, uniq := ?_ }
                      intro φ
                      -- Over `A`, the only possible source morphism is the identity on `A'`.
                      apply Functor.Fiber.hom_ext
                      have hφ : (show Hom A' A' from φ.1) = Hom.id A' := by
                        cases (show Hom A' A' from φ.1) <;> rfl
                      simpa using hφ
                  | B' => cases hY
                  | T' => cases hY
          | B' => cases hX
          | T' => cases hX
  | B =>
      cases X with
      | mk X hX =>
          cases X with
          | A' => cases hX
          | B' =>
              cases hX
              cases Y with
              | mk Y hY =>
                  cases Y with
                  | A' => cases hY
                  | B' =>
                      cases hY
                      refine { default := 𝟙 _, uniq := ?_ }
                      intro φ
                      -- Over `B`, the only possible source morphism is the identity on `B'`.
                      apply Functor.Fiber.hom_ext
                      have hφ : (show Hom B' B' from φ.1) = Hom.id B' := by
                        cases (show Hom B' B' from φ.1) <;> rfl
                      simpa using hφ
                  | T' => cases hY
          | T' => cases hX
  | T =>
      cases X with
      | mk X hX =>
          cases X with
          | A' => cases hX
          | B' => cases hX
          | T' =>
              cases hX
              cases Y with
              | mk Y hY =>
                  cases Y with
                  | A' => cases hY
                  | B' => cases hY
                  | T' =>
                      cases hY
                      refine { default := 𝟙 _, uniq := ?_ }
                      intro φ
                      -- Over `T`, the only possible source morphism is the identity on `T'`.
                      apply Functor.Fiber.hom_ext
                      have hφ : (show Hom T' T' from φ.1) = Hom.id T' := by
                        cases (show Hom T' T' from φ.1) <;> rfl
                      simpa using hφ

/-- Example 4.35.5 (1): every standard fiber of the first projection is a groupoid. -/
-- Proof sketch: for each `U : Base`, the fiber `projection.Fiber U` has exactly one object by
-- inspection of `objMap`, and its only endomorphism is the identity.
instance fiber_isGroupoid (U : Base) :
    IsGroupoid (projection.Fiber U) := by
  -- The fiber is a thin category, so every morphism is automatically invertible.
  letI : Groupoid (projection.Fiber U) :=
    Groupoid.ofHomUnique (fun {X Y} ↦ fiber_hom_unique U (X := X) (Y := Y))
  infer_instance

/-- Example 4.35.5 (2): for the first projection, the arrow `f : A ⟶ B` has no lift from `A'` to
`B'`. -/
-- Proof sketch: inspect the morphisms in `Hom`; there is no arrow from `A'` to `B'`, so no
-- morphism can map to `f`.
theorem projection_not_isHomLift_f :
    ¬ ∃ φ : Hom A' B', projection.IsHomLift Base.Hom.f φ := by
  rintro ⟨φ, -⟩
  -- There is no constructor for a morphism `A' ⟶ B'` in `NoLift`.
  cases φ

private theorem homLift_f_domain_eq {X : NoLift} (φ : X ⟶ B')
    [projection.IsHomLift Base.Hom.f φ] : X = A' := by
  have hX : objMap X = Base.A := IsHomLift.domain_eq projection Base.Hom.f φ
  cases X with
  | A' => rfl
  | B' => simp [objMap] at hX
  | T' => simp [objMap] at hX

/-- The first projection in Example 4.35.5 is not fibred in groupoids. -/
-- Proof sketch: use the canonical strongly-cartesian lift criterion for fibredness. A lift of
-- `f : A ⟶ B` with codomain `B'` would have domain `A'`, contradicting
-- `projection_not_isHomLift_f`.
private theorem projection_not_isFibered :
    ¬ projection.IsFibered := by
  intro hp
  obtain ⟨X, φ, hφ⟩ :=
    (isFibered_iff_exists_isStronglyCartesian projection).1 hp B' Base.A Base.Hom.f
  letI : projection.IsStronglyCartesian Base.Hom.f φ := hφ
  have hX : X = A' := homLift_f_domain_eq φ
  subst hX
  exact projection_not_isHomLift_f ⟨φ, inferInstance⟩

theorem projection_not_isFibredInGroupoids :
    ¬ IsFibredInGroupoids projection := by
  rw [isFibredInGroupoids_iff_isFibered_and_fiber_groupoid]
  rintro ⟨hp, -⟩
  exact projection_not_isFibered hp

end NoLift

/-- Objects of the source category where the arrow `f : A ⟶ B` has two lifts. -/
inductive TwoLift where
  | A' | B' | T'
  deriving DecidableEq, Repr

namespace TwoLift

/-- Morphisms of the source category where the arrow `f : A ⟶ B` has two distinct lifts. -/
inductive Hom : TwoLift → TwoLift → Type where
  | id : (X : TwoLift) → Hom X X
  | f1 : Hom .A' .B'
  | f2 : Hom .A' .B'
  | g : Hom .B' .T'
  | h : Hom .A' .T'
  deriving DecidableEq, Repr

namespace Hom

/-- Composition law on the source category with two lifts of `f`. -/
def comp : {X Y Z : TwoLift} → Hom X Y → Hom Y Z → Hom X Z
  | _, _, _, id _, k => k
  | _, _, _, k, id _ => k
  | _, _, _, f1, g => h
  | _, _, _, f2, g => h

/-- Left identity for the source category with two lifts of `f`. -/
-- Proof sketch: enumerate the finitely many well-typed morphisms in the source category.
theorem id_comp {X Y : TwoLift} (k : Hom X Y) : comp (id X) k = k := by
  -- Enumerate the only well-typed morphism constructors in the finite source category.
  cases k <;> rfl

/-- Right identity for the source category with two lifts of `f`. -/
-- Proof sketch: enumerate the finitely many well-typed morphisms in the source category.
theorem comp_id {X Y : TwoLift} (k : Hom X Y) : comp k (id Y) = k := by
  -- Enumerate the only well-typed morphism constructors in the finite source category.
  cases k <;> rfl

/-- Associativity for the source category with two lifts of `f`. -/
-- Proof sketch: check the only non-identity composites, namely `f1 ≫ g` and `f2 ≫ g`.
theorem assoc {W X Y Z : TwoLift} (k : Hom W X) (l : Hom X Y) (m : Hom Y Z) :
    comp (comp k l) m = comp k (comp l m) := by
  -- The dependent typing again removes impossible triples of generators.
  cases k <;> cases l <;> cases m <;> rfl

end Hom

/-- The category structure on the second source category of Example 4.35.5. -/
instance : Category TwoLift where
  Hom := Hom
  id := Hom.id
  comp := fun k l ↦ Hom.comp k l
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The object map of the second source projection in Example 4.35.5. -/
def objMap : TwoLift → Base
  | .A' => .A
  | .B' => .B
  | .T' => .T

/-- The morphism map of the second source projection in Example 4.35.5. -/
def homMap :
    {X Y : TwoLift} → Hom X Y → (objMap X ⟶ objMap Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, Hom.f1 => Base.Hom.f
  | _, _, Hom.f2 => Base.Hom.f
  | _, _, Hom.g => Base.Hom.g
  | _, _, Hom.h => Base.Hom.h

/-- The second source projection preserves identities. -/
-- Proof sketch: check the three objects of the source category directly.
theorem projection_map_id (X : TwoLift) : homMap (𝟙 X) = 𝟙 (objMap X) := by
  -- The object map is explicit, so each identity is preserved by reflexivity.
  cases X <;> rfl

/-- The second source projection preserves composition. -/
-- Proof sketch: inspect the finitely many composable pairs of source morphisms and use that both lifts map to `f`.
private theorem projection_map_comp {X Y Z : TwoLift} (k : Hom X Y) (l : Hom Y Z) :
    homMap (Hom.comp k l) = Base.Hom.comp (homMap k) (homMap l) := by
  -- The only non-identity composites are `f1 ≫ g` and `f2 ≫ g`, both mapping to `h = f ≫ g`.
  cases k <;> cases l <;> rfl

/-- The projection from the second source category to the base category. -/
def projection : TwoLift ⥤ Base where
  obj := objMap
  map := fun {_ _} k ↦ homMap k
  map_id := projection_map_id
  map_comp := by
    intro X Y Z k l
    -- Route correction: state preservation of composition using the explicit finite `comp`.
    simpa using projection_map_comp k l

/-- Helper for Example 4.35.5: every hom-set in a standard fiber of the second projection is a
singleton. -/
private abbrev fiber_hom_unique (U : Base) {X Y : projection.Fiber U} : Unique (X ⟶ Y) := by
  cases U with
  | A =>
      cases X with
      | mk X hX =>
          cases X with
          | A' =>
              cases hX
              cases Y with
              | mk Y hY =>
                  cases Y with
                  | A' =>
                      cases hY
                      refine { default := 𝟙 _, uniq := ?_ }
                      intro φ
                      -- In the fiber over `A`, the lifts `f1` and `f2` disappear: only `id A'` remains.
                      apply Functor.Fiber.hom_ext
                      have hφ : (show Hom A' A' from φ.1) = Hom.id A' := by
                        cases (show Hom A' A' from φ.1) <;> rfl
                      simpa using hφ
                  | B' => cases hY
                  | T' => cases hY
          | B' => cases hX
          | T' => cases hX
  | B =>
      cases X with
      | mk X hX =>
          cases X with
          | A' => cases hX
          | B' =>
              cases hX
              cases Y with
              | mk Y hY =>
                  cases Y with
                  | A' => cases hY
                  | B' =>
                      cases hY
                      refine { default := 𝟙 _, uniq := ?_ }
                      intro φ
                      -- Over `B`, the only possible source morphism is `id B'`.
                      apply Functor.Fiber.hom_ext
                      have hφ : (show Hom B' B' from φ.1) = Hom.id B' := by
                        cases (show Hom B' B' from φ.1) <;> rfl
                      simpa using hφ
                  | T' => cases hY
          | T' => cases hX
  | T =>
      cases X with
      | mk X hX =>
          cases X with
          | A' => cases hX
          | B' => cases hX
          | T' =>
              cases hX
              cases Y with
              | mk Y hY =>
                  cases Y with
                  | A' => cases hY
                  | B' => cases hY
                  | T' =>
                      cases hY
                      refine { default := 𝟙 _, uniq := ?_ }
                      intro φ
                      -- Over `T`, the only possible source morphism is `id T'`.
                      apply Functor.Fiber.hom_ext
                      have hφ : (show Hom T' T' from φ.1) = Hom.id T' := by
                        cases (show Hom T' T' from φ.1) <;> rfl
                      simpa using hφ

/-- Example 4.35.5 (3): every standard fiber of the second projection is a groupoid. -/
-- Proof sketch: for each `U : Base`, the fiber `projection.Fiber U` again has exactly one object
-- by inspection of `objMap`, and its only endomorphism is the identity.
instance fiber_isGroupoid (U : Base) :
    IsGroupoid (projection.Fiber U) := by
  -- The fiber is a thin category, so every morphism is automatically invertible.
  letI : Groupoid (projection.Fiber U) :=
    Groupoid.ofHomUnique (fun {X Y} ↦ fiber_hom_unique U (X := X) (Y := Y))
  infer_instance

private theorem f1_ne_f2 : (Hom.f1 : A' ⟶ B') ≠ Hom.f2 := by
  intro h
  cases h

/-- Example 4.35.5 (4): for the second projection, the arrow `f : A ⟶ B` has two distinct lifts
from `A'` to `B'`. -/
-- Proof sketch: the arrows `f1` and `f2` are distinct morphisms `A' ⟶ B'`, and both map to
-- `Base.Hom.f` under `homMap`.
theorem projection_exists_two_distinct_isHomLift_f :
    ∃ φ₁ φ₂ : {φ : A' ⟶ B' // projection.IsHomLift Base.Hom.f φ}, φ₁ ≠ φ₂ := by
  have hf1 : projection.IsHomLift Base.Hom.f Hom.f1 := by
    -- The first explicit lift maps to `Base.Hom.f` by definition of `projection`.
    change projection.IsHomLift (projection.map Hom.f1) Hom.f1
    infer_instance
  have hf2 : projection.IsHomLift Base.Hom.f Hom.f2 := by
    -- The second explicit lift also maps to `Base.Hom.f`.
    change projection.IsHomLift (projection.map Hom.f2) Hom.f2
    infer_instance
  refine ⟨⟨Hom.f1, hf1⟩, ⟨Hom.f2, hf2⟩, ?_⟩
  intro h
  apply f1_ne_f2
  exact congrArg Subtype.val h

private theorem homLift_f_domain_eq {X : TwoLift} (φ : X ⟶ B')
    [projection.IsHomLift Base.Hom.f φ] : X = A' := by
  have hX : objMap X = Base.A := IsHomLift.domain_eq projection Base.Hom.f φ
  cases X with
  | A' => rfl
  | B' => simp [objMap] at hX
  | T' => simp [objMap] at hX

/-- The second projection in Example 4.35.5 is not fibred in groupoids. -/
-- Proof sketch: a functor fibred in groupoids is in particular fibered. Any cartesian lift of
-- `f : A ⟶ B` with codomain `B'` must be either `f1` or `f2`, and the other lift contradicts
-- cartesianness.
private theorem projection_not_isCartesian
    (φ ψ : A' ⟶ B') (hφψ : φ ≠ ψ) [projection.IsHomLift Base.Hom.f ψ] :
    ¬ projection.IsCartesian Base.Hom.f φ := by
  intro hφ
  letI : projection.IsCartesian Base.Hom.f φ := hφ
  have hχ :
      ∃! χ : A' ⟶ A', projection.IsHomLift (𝟙 Base.A) χ ∧ χ ≫ φ = ψ := by
    simpa using IsCartesian.universal_property
      (show Base.A ⟶ Base.B from Base.Hom.f) ψ
  obtain ⟨χ, hχ, -⟩ := hχ
  have hχ_id : χ = Hom.id A' := by
    refine match χ with
    | .id .A' => rfl
  apply hφψ
  simpa [hχ_id] using hχ.2

private theorem projection_not_isFibered :
    ¬ projection.IsFibered := by
  intro hp
  obtain ⟨X, φ, hφ⟩ :=
    (isFibered_iff_exists_isStronglyCartesian projection).1 hp B' Base.A Base.Hom.f
  have hX : X = A' := by
    letI : projection.IsStronglyCartesian Base.Hom.f φ := hφ
    exact homLift_f_domain_eq φ
  subst hX
  refine match φ, hφ with
  | .f1, hφ => by
      letI : projection.IsStronglyCartesian Base.Hom.f Hom.f1 := hφ
      haveI : projection.IsHomLift Base.Hom.f Hom.f2 := by
        change projection.IsHomLift (projection.map Hom.f2) Hom.f2
        infer_instance
      exact projection_not_isCartesian Hom.f1 Hom.f2
        f1_ne_f2 inferInstance
  | .f2, hφ => by
      letI : projection.IsStronglyCartesian Base.Hom.f Hom.f2 := hφ
      haveI : projection.IsHomLift Base.Hom.f Hom.f1 := by
        change projection.IsHomLift (projection.map Hom.f1) Hom.f1
        infer_instance
      exact projection_not_isCartesian Hom.f2 Hom.f1
        f1_ne_f2.symm inferInstance

theorem projection_not_isFibredInGroupoids :
    ¬ IsFibredInGroupoids projection := by
  rw [isFibredInGroupoids_iff_isFibered_and_fiber_groupoid]
  rintro ⟨hp, -⟩
  exact projection_not_isFibered hp

end TwoLift

end Example4355
end CategoryTheory
