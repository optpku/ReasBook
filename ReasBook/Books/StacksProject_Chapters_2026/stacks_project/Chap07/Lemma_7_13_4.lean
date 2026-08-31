module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallyBijective
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.GrothendieckTopology

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsContinuous J K]

/- Domain-style sampling for Lemma 7.13.4:
- primary domain: sheafification and continuous functors between Grothendieck sites;
- sampled owner API:
  `GrothendieckTopology.toSheafify`,
  `GrothendieckTopology.sheafifyMap`,
  `CategoryTheory.plusPlusIsoSheafify`,
  `CategoryTheory.toSheafify_plusPlusIsoSheafify_hom`,
  `Functor.W_map_of_adjunction_of_isContinuous`,
  `GrothendieckTopology.W_iff`;
- source/core/bridge triage:
  `source-facing`: the Stacks comparison morphism `(u_p G)^# ⟶ (u_p (G^#))^#`;
  `core/canonical`: the localization class `J.W` and its transport to `K.W` along `u.op.lan`;
  `bridge/view`: `K.W_iff`, which turns the owner-level `K.W` statement into the desired
  sheaf-level `IsIso` for `K.sheafifyMap ((u.op.lan).map (J.toSheafify G))`.

Primitive data are the sheafification unit `J.toSheafify G` and continuity of `u`. The isomorphism
statement is derived API from the canonical localization owner `W`, so the proof should use
the bridge from the concrete `P⁺⁺` map `J.toSheafify G` to the generic localization unit
`CategoryTheory.toSheafify J G`, transport along `u.op.lan`, and then convert back by `K.W_iff`.
-/

/-- Lemma 7.13.4: for a continuous functor of sites, the canonical comparison morphism
`(u_p G)^# ⟶ (u_p (G^#))^#`, namely the sheafification of the left Kan extension of
`J.toSheafify G`, is an isomorphism. -/
-- Proof sketch: compare the concrete `P⁺⁺` map `J.toSheafify G` with the generic localization
-- unit `CategoryTheory.toSheafify J G` via `plusPlusIsoSheafify`; the latter lies in `J.W` by
-- `J.W_toSheafify`. Transport that `W`-fact across `u.op.lan`, convert it back to a generic
-- sheafification isomorphism using `K.W_iff`, and finally conjugate by the `plusPlus`-to-generic
-- comparison on the target side to recover the concrete `K.sheafifyMap`.
theorem continuous_pullback_sheafification_comparison_isIso
    (G : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    IsIso (K.sheafifyMap ((u.op.lan).map (J.toSheafify G))) := by
  let A := Type (max u₁ u₂ v₁ v₂)
  let f := (u.op.lan).map (J.toSheafify G)
  have hJG : J.W (J.toSheafify G) := by
    refine (J.W.cancel_right_of_respectsIso (J.toSheafify G) (plusPlusIsoSheafify J A G).hom).1 ?_
    simpa [toSheafify_plusPlusIsoSheafify_hom J A G] using
      (J.W_toSheafify G : J.W (CategoryTheory.toSheafify J G))
  have hGeneric : IsIso ((presheafToSheaf K A).map f) := (K.W_iff _).1 <|
    u.W_map_of_adjunction_of_isContinuous J K (u.op.lan)
      (u.op.lanAdjunction A) (J.toSheafify G)
      hJG
  let e₁ := plusPlusIsoSheafify K A ((u.op.lan).obj G)
  let e₂ := plusPlusIsoSheafify K A ((u.op.lan).obj (J.sheafify G))
  have hConcreteToGeneric :
      K.sheafifyMap f ≫ e₂.hom = e₁.hom ≫ CategoryTheory.sheafifyMap K f := by
    simpa [A, f, GrothendieckTopology.sheafification, CategoryTheory.sheafification] using
      (plusPlusFunctorIsoSheafification K A).hom.naturality f
  have hEq :
      K.sheafifyMap f = e₁.hom ≫ CategoryTheory.sheafifyMap K f ≫ e₂.inv := by
    calc
      K.sheafifyMap f = (K.sheafifyMap f ≫ e₂.hom) ≫ e₂.inv := by
        simp [Category.assoc]
      _ = e₁.hom ≫ CategoryTheory.sheafifyMap K f ≫ e₂.inv := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ e₂.inv) hConcreteToGeneric
  rw [hEq]
  let eGeneric :
      (presheafToSheaf K A).obj ((u.op.lan).obj G) ≅
        (presheafToSheaf K A).obj ((u.op.lan).obj (J.sheafify G)) :=
    asIso ((presheafToSheaf K A).map f)
  have : IsIso (CategoryTheory.sheafifyMap K f) := by
    have hIsoPresheaf : IsIso ((sheafToPresheaf K A).map eGeneric.hom) := by infer_instance
    simpa [A, f, CategoryTheory.sheafifyMap] using hIsoPresheaf
  infer_instance

end
