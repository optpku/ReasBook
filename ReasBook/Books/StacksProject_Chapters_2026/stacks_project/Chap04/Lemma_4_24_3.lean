module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

/- Domain-style sampling for Lemma 4.24.3:
- primary domain: adjunction criteria for full, faithful, and fully faithful functors;
- sampled owner API:
  `Functor.FullyFaithful`,
  `Functor.FullyFaithful.ofCompFaithful`,
  `Adjunction.fullyFaithfulLOfIsIsoUnit`,
  `Adjunction.fullyFaithfulROfIsIsoCounit`,
  `Adjunction.homEquiv`;
- source-facing layer: the Stacks criterion that if the composite endofunctor `u ⋙ v` or `v ⋙ u`
  is fully faithful, then the corresponding adjoint `u` or `v` is fully faithful;
- core/canonical owner: `CategoryTheory.Adjunction`;
- bridge/view: this file upgrades fully faithfulness of the composite endofunctor to the owner
  criteria on the adjunction hom-set equivalence. The nearest upstream composition theorem is
  `Functor.FullyFaithful.ofCompFaithful`, but it needs an independent faithfulness hypothesis on
  the second functor, so it does not subsume the adjunction-specific Stacks lemma here.

Primitive data are the adjunction `adj : u ⊣ v` and the bundled `FullyFaithful` structure on the
composite endofunctor. The final `FullyFaithful` structures on `u` and `v` are derived API and
should be built directly from the adjunction owner `homEquiv`, rather than by introducing
intermediate local `Full`, `Faithful`, or `IsIso` wrappers.
-/

/- Source/core/bridge triage for Lemma 4.24.3:
- `source-facing`: the Stacks lemma is stated for a chosen adjunction `u ⊣ v` and a chosen
  fully faithful composite endofunctor `u ⋙ v` or `v ⋙ u`;
- `core/canonical`: the owner abstractions `Adjunction.homEquiv`,
  `Adjunction.fullyFaithfulLOfIsIsoUnit`, and `Adjunction.fullyFaithfulROfIsIsoCounit`;
- `bridge/view`: the two declarations below are thin source-facing bridges from full faithfulness
  of the composite endofunctor to full faithfulness of the corresponding adjoint. This file
  cannot be reduced to a pure `recall`: the nearest generic composition theorem
  `Functor.FullyFaithful.ofCompFaithful` still needs an independent faithfulness hypothesis on the
  second functor, so the adjunction-specific argument remains necessary here.
-/

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {u : C ⥤ D} {v : D ⥤ C}

attribute [local simp] Adjunction.homEquiv_unit Adjunction.homEquiv_counit

/-- Lemma 4.24.3 (1): source-facing bridge from full faithfulness of `u ⋙ v` to full faithfulness
of the left adjoint `u`. -/
noncomputable def fullyFaithfulLOfCompFullyFaithful
    (adj : u ⊣ v) (hcomp : (u ⋙ v).FullyFaithful) : u.FullyFaithful where
  preimage f := hcomp.preimage (v.map f)
  map_preimage {X Y} f := by
    apply (adj.homEquiv X (u.obj Y)).injective
    simpa [Functor.comp_map] using
      congrArg (fun k ↦ adj.unit.app X ≫ k) (hcomp.map_preimage (v.map f))
  preimage_map f := by
    simpa [Functor.comp_map] using hcomp.preimage_map f

/-- Full faithfulness of `u ⋙ v` makes the map on `Hom`-sets induced by the left adjoint `u`
bijective. -/
theorem fullyFaithfulLOfCompFullyFaithful_map_bijective
    (adj : u ⊣ v) (hcomp : (u ⋙ v).FullyFaithful) (X Y : C) :
    Function.Bijective (u.map : (X ⟶ Y) → (u.obj X ⟶ u.obj Y)) := by
  simpa using (fullyFaithfulLOfCompFullyFaithful adj hcomp).map_bijective X Y

/-- Lemma 4.24.3 (2): source-facing bridge from full faithfulness of `v ⋙ u` to full faithfulness
of the right adjoint `v`. -/
noncomputable def fullyFaithfulROfCompFullyFaithful
    (adj : u ⊣ v) (hcomp : (v ⋙ u).FullyFaithful) : v.FullyFaithful where
  preimage f := hcomp.preimage (u.map f)
  map_preimage {X Y} f := by
    apply (adj.homEquiv (v.obj X) Y).symm.injective
    simpa [Functor.comp_map, Category.assoc] using
      congrArg (fun k ↦ k ≫ adj.counit.app Y) (hcomp.map_preimage (u.map f))
  preimage_map f := by
    simpa [Functor.comp_map] using hcomp.preimage_map f

/-- Full faithfulness of `v ⋙ u` makes the map on `Hom`-sets induced by the right adjoint `v`
bijective. -/
theorem fullyFaithfulROfCompFullyFaithful_map_bijective
    (adj : u ⊣ v) (hcomp : (v ⋙ u).FullyFaithful) (X Y : D) :
    Function.Bijective (v.map : (X ⟶ Y) → (v.obj X ⟶ v.obj Y)) := by
  simpa using (fullyFaithfulROfCompFullyFaithful adj hcomp).map_bijective X Y

end

end CategoryTheory.Adjunction
