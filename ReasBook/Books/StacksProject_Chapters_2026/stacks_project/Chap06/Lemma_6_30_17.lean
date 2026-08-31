module

public import stacks_project.Chap06.Definition_6_26_1
public import stacks_project.Chap06.Lemma_6_30_16
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable {BX : Set (Opens X)} {BY : Set (Opens Y)}
variable (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X)))
variable (𝒢 : SheafOfModules ((RingedSpace.ringCatSheaf Y)))

local notation "BasisOpenX" => ObjectProperty.FullSubcategory fun U : Opens X ↦ U ∈ BX
local notation "BasisOpenY" => ObjectProperty.FullSubcategory fun V : Opens Y ↦ V ∈ BY

/-
Domain-style sampling for Lemma 6.30.17:
- primary domain: pushforward of sheaves of modules on a morphism of ringed spaces, expressed via
  basis-indexed section families on the underlying sheaves of abelian groups;
- sampled owner declarations:
  `RingedSpace.Hom.pushforward`,
  `RingedSpace.Hom.toRingCatSheafHom`,
  `BasisContinuousMapSectionFamily`,
  `existsUnique_pushforward_hom_of_basis_section_family`,
  `SheafOfModules.toSheaf`;
- owner abstraction: the canonical target owner is `(f _*).obj ℱ`,
  while the source-facing basis data are already owned by
  `BasisContinuousMapSectionFamily f.hom.base BX BY`;
- primitive data: the only extra primitive input beyond the basis family is the
  `\mathcal O_Y(V)`-linearity condition on sections;
- derived API: the unique module morphism whose underlying sheaf morphism recovers the given basis
  family on basis opens.

Source/core/bridge triage:
- `source-facing`: the basis-pair family `η` and its linearity condition;
- `core/canonical`: the module pushforward owner `(f _*).obj ℱ`;
- `bridge/view`: `SheafOfModules.toSheaf`, used only to compare the source family with the
  underlying sheaf morphism of the resulting module map.
-/

-- Proof sketch: forget the module structure to obtain a compatible basis-indexed family of maps
-- of sheaves of abelian groups, apply Lemma `6.30.16` to extend it uniquely to the underlying
-- pushforward morphism, and then use the pointwise linearity hypothesis to view the resulting
-- morphism as a morphism of sheaves of modules.
/-- Helper for Lemma 6.30.17: once the additive sheaf lift is known, its section map on a basis
open `V` of `Y` is `\mathcal O_Y(V)`-linear because its restrictions to all basis opens of
`f^{-1}(V)` agree with the given linear basis-pair maps. -/
theorem underlying_basis_pair_lift_is_linear
    (hBX : Opens.IsBasis BX) (η :
      BasisContinuousMapSectionFamily f.hom.base BX BY
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢)
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (hη :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj)
        (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op V.obj)) (s : 𝒢.val.obj (op V.obj)),
        (show ℱ.val.obj (op U.obj) from η.app U V hUV (r • s)) =
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) ≫
              ((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hUV).op) r) •
            (show ℱ.val.obj (op U.obj) from η.app U V hUV s))
    {Φ :
      ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢) ⟶
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj ((f _*).obj ℱ))}
    (hΦ :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        Φ.hom.app (op V.obj) ≫ ℱ.val.presheaf.map (homOfLE hUV).op =
          η.app U V hUV) :
    ∀ (V : BasisOpenY)
      (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op V.obj))
      (s : 𝒢.val.obj (op V.obj)),
      (show ((f _*).obj ℱ).val.obj (op V.obj) from
          Φ.hom.app (op V.obj) (r • s)) =
        r • (show ((f _*).obj ℱ).val.obj (op V.obj) from Φ.hom.app (op V.obj) s) := by
  intro V r s
  change (show ℱ.val.obj (op ((Opens.map f.hom.base).obj V.obj)) from
      Φ.hom.app (op V.obj) (r • s)) =
    (show ((RingedSpace.ringCatSheaf X)).obj.obj
        (op ((Opens.map f.hom.base).obj V.obj)) from
      (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) r) •
      (show ℱ.val.obj (op ((Opens.map f.hom.base).obj V.obj)) from Φ.hom.app (op V.obj) s)
  -- Compare the two sections after restricting to basis neighborhoods of each point of `f⁻¹(V)`.
  apply TopCat.Presheaf.IsSheaf.section_ext ℱ.isSheaf
  intro x hx
  obtain ⟨_, ⟨W, hWB, rfl⟩, hxW, hWV⟩ :=
    hBX.exists_subset_of_mem_open hx ((Opens.map f.hom.base).obj V.obj).2
  let U : BasisOpenX := ⟨W, hWB⟩
  refine ⟨W, hWV, hxW, ?_⟩
  have hleft : ℱ.val.presheaf.map (homOfLE hWV).op
      (show ℱ.val.obj (op ((Opens.map f.hom.base).obj V.obj)) from Φ.hom.app (op V.obj) (r • s)) =
        (show ℱ.val.obj (op U.obj) from η.app U V hWV (r • s)) := by
    simpa using ConcreteCategory.congr_hom (hΦ U V hWV) (r • s)
  have hright : ℱ.val.presheaf.map (homOfLE hWV).op
      (show ℱ.val.obj (op ((Opens.map f.hom.base).obj V.obj)) from Φ.hom.app (op V.obj) s) =
        (show ℱ.val.obj (op U.obj) from η.app U V hWV s) := by
    simpa using ConcreteCategory.congr_hom (hΦ U V hWV) s
  have hmiddle :
      (show ℱ.val.obj (op U.obj) from η.app U V hWV (r • s)) =
        (((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hWV).op
            (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj)) r)) •
          (show ℱ.val.obj (op U.obj) from η.app U V hWV s) := by
    simpa using hη U V hWV r s
  have hrewrite :
      (((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hWV).op
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj)) r)) •
        (show ℱ.val.obj (op U.obj) from η.app U V hWV s) =
          (((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hWV).op
            (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj)) r)) •
            ℱ.val.presheaf.map (homOfLE hWV).op
              (show ℱ.val.obj (op ((Opens.map f.hom.base).obj V.obj)) from Φ.hom.app (op V.obj) s) := by
    exact congrArg
      (fun t ↦
        (((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hWV).op
            (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj)) r)) • t)
      hright.symm
  have hsmul :
      (((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hWV).op
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj)) r)) •
        ℱ.val.presheaf.map (homOfLE hWV).op
          (show ℱ.val.obj (op ((Opens.map f.hom.base).obj V.obj)) from Φ.hom.app (op V.obj) s) =
          ℱ.val.presheaf.map (homOfLE hWV).op
            ((show ((RingedSpace.ringCatSheaf X)).obj.obj
                (op ((Opens.map f.hom.base).obj V.obj)) from
              (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) r) •
              (show ℱ.val.obj (op ((Opens.map f.hom.base).obj V.obj)) from Φ.hom.app (op V.obj) s)) := by
    symm
    simpa using
      (ℱ.val.map_smul (homOfLE hWV).op
        (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj)) r)
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj V.obj)) from Φ.hom.app (op V.obj) s))
  exact hleft.trans (hmiddle.trans (hrewrite.trans hsmul))

/-- Helper for Lemma 6.30.17: the additive lift is linear on arbitrary opens of `Y` once one
refines both the source open and its preimage by basis neighborhoods and then applies the
basis-local linearity statement. -/
theorem basis_pair_lift_is_linear_on_opens
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η :
      BasisContinuousMapSectionFamily f.hom.base BX BY
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢)
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (hη :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj)
        (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op V.obj)) (s : 𝒢.val.obj (op V.obj)),
        (show ℱ.val.obj (op U.obj) from η.app U V hUV (r • s)) =
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) ≫
              ((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hUV).op) r) •
            (show ℱ.val.obj (op U.obj) from η.app U V hUV s))
    {Φ :
      ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢) ⟶
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj ((f _*).obj ℱ))}
    (hΦ :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        Φ.hom.app (op V.obj) ≫ ℱ.val.presheaf.map (homOfLE hUV).op =
          η.app U V hUV) :
    ∀ (W : Opens Y)
      (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op W))
      (s : 𝒢.val.obj (op W)),
      (show ((f _*).obj ℱ).val.obj (op W) from Φ.hom.app (op W) (r • s)) =
        r • (show ((f _*).obj ℱ).val.obj (op W) from Φ.hom.app (op W) s) := by
  intro W r s
  change (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) (r • s)) =
    (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj W)) from
      (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op W) r) •
      (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s)
  -- Route correction: localize from `W` to a basis open `V ⊆ W` in `Y`; after transport to
  -- `f⁻¹(V)`, the existing basis-open linearity theorem closes the argument directly.
  apply TopCat.Presheaf.IsSheaf.section_ext ℱ.isSheaf
  intro x hx
  have hyW : f.hom.base x ∈ W := hx
  obtain ⟨_, ⟨V, hVB, rfl⟩, hxV, hVW⟩ :=
    hBY.exists_subset_of_mem_open (a := f.hom.base x) hyW W.2
  let Vb : BasisOpenY := ⟨V, hVB⟩
  have hpre : (Opens.map f.hom.base).obj Vb.obj ≤ (Opens.map f.hom.base).obj W := by
    intro y hy
    exact hVW hy
  refine ⟨(Opens.map f.hom.base).obj Vb.obj, hpre, hxV, ?_⟩
  -- Transport the left-hand side from `W` down to the basis open `V`.
  have hleft_nat :
      ℱ.val.presheaf.map (homOfLE hpre).op
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) (r • s)) =
          (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
            Φ.hom.app (op Vb.obj) (𝒢.val.map (homOfLE hVW).op (r • s))) := by
    simpa [Vb] using
      (NatTrans.naturality_apply Φ.hom (homOfLE hVW).op (r • s)).symm
  have hleft_smul :
      (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          Φ.hom.app (op Vb.obj) (𝒢.val.map (homOfLE hVW).op (r • s))) =
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          Φ.hom.app (op Vb.obj)
            ((((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r) •
              (𝒢.val.map (homOfLE hVW).op s))) := by
    exact congrArg
      (fun t ↦
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          Φ.hom.app (op Vb.obj) t))
      (𝒢.val.map_smul (homOfLE hVW).op r s)
  have hleft :
      ℱ.val.presheaf.map (homOfLE hpre).op
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) (r • s)) =
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          Φ.hom.app (op Vb.obj)
            ((((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r) •
              (𝒢.val.map (homOfLE hVW).op s))) := by
    exact hleft_nat.trans hleft_smul
  -- Transport the scalar and the section on the right-hand side to `f⁻¹(V)`.
  have hring :
      ((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hpre).op
        (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj W)) from
          (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op W) r) =
        (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op Vb.obj)
            (((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r)) := by
    simpa [Vb] using
      (NatTrans.naturality_apply ((RingedSpace.Hom.toRingCatSheafHom f).hom)
        (homOfLE hVW).op r).symm
  have hsection :
      ℱ.val.presheaf.map (homOfLE hpre).op
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s) =
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          Φ.hom.app (op Vb.obj) (𝒢.val.map (homOfLE hVW).op s)) := by
    simpa [Vb] using
      (NatTrans.naturality_apply Φ.hom (homOfLE hVW).op s).symm
  have hright_smul :
      ℱ.val.presheaf.map (homOfLE hpre).op
        ((show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj W)) from
            (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op W) r) •
          (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s)) =
        (((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hpre).op
            (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj W)) from
              (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op W) r)) •
          ℱ.val.presheaf.map (homOfLE hpre).op
            (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s) := by
    simpa using
      (ℱ.val.map_smul (homOfLE hpre).op
        ((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op W) r)
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s))
  have hright :
      ℱ.val.presheaf.map (homOfLE hpre).op
        ((show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj W)) from
            (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op W) r) •
          (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s)) =
        (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op Vb.obj)
            (((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r)) •
          (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
            Φ.hom.app (op Vb.obj) (𝒢.val.map (homOfLE hVW).op s)) := by
    have hright_scalar :
        (((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hpre).op
            (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj W)) from
              (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op W) r)) •
          ℱ.val.presheaf.map (homOfLE hpre).op
            (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s) =
          (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
            (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op Vb.obj)
              (((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r)) •
            ℱ.val.presheaf.map (homOfLE hpre).op
              (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s) := by
      exact congrArg (fun t ↦ t • ℱ.val.presheaf.map (homOfLE hpre).op
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s)) hring
    have hright_section :
        (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op Vb.obj)
            (((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r)) •
          ℱ.val.presheaf.map (homOfLE hpre).op
            (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s) =
        (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op Vb.obj)
            (((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r)) •
          (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
            Φ.hom.app (op Vb.obj) (𝒢.val.map (homOfLE hVW).op s)) := by
      exact congrArg
        (fun t ↦
          (show ((RingedSpace.ringCatSheaf X)).obj.obj
              (op ((Opens.map f.hom.base).obj Vb.obj)) from
            (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op Vb.obj)
              (((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r)) • t)
        hsection
    exact hright_smul.trans (hright_scalar.trans hright_section)
  -- The localized equality is exactly the basis-open linearity statement already proved.
  have hlinear :
      (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          Φ.hom.app (op Vb.obj)
            ((((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r) •
              (𝒢.val.map (homOfLE hVW).op s))) =
        (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op Vb.obj)
            (((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r)) •
          (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
            Φ.hom.app (op Vb.obj) (𝒢.val.map (homOfLE hVW).op s)) := by
    simpa [Vb] using
      underlying_basis_pair_lift_is_linear (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
        hBX η hη hΦ Vb
        (((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r)
        (𝒢.val.map (homOfLE hVW).op s)
  exact hleft.trans (hlinear.trans hright.symm)

/-- Helper for Lemma 6.30.17: once the additive lift is linear on every open of `Y`, it upgrades
to a morphism of presheaves of modules. -/
noncomputable def basis_pair_lift_to_presheaf_module_hom
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η :
      BasisContinuousMapSectionFamily f.hom.base BX BY
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢)
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (hη :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj)
        (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op V.obj)) (s : 𝒢.val.obj (op V.obj)),
        (show ℱ.val.obj (op U.obj) from η.app U V hUV (r • s)) =
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) ≫
              ((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hUV).op) r) •
            (show ℱ.val.obj (op U.obj) from η.app U V hUV s))
    (Φ :
      ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢) ⟶
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj ((f _*).obj ℱ)))
    (hΦ :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        Φ.hom.app (op V.obj) ≫ ℱ.val.presheaf.map (homOfLE hUV).op =
          η.app U V hUV) :
    𝒢.val ⟶ ((f _*).obj ℱ).val :=
  PresheafOfModules.homMk Φ.hom
    (fun W r s ↦ basis_pair_lift_is_linear_on_opens (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
      hBX hBY η hη hΦ W.unop r s)

/-- Helper for Lemma 6.30.17: packaging the presheaf-level module morphism as a morphism of sheaves
of modules introduces no extra data. -/
noncomputable def basis_pair_lift_to_module_hom
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η :
      BasisContinuousMapSectionFamily f.hom.base BX BY
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢)
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (hη :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj)
        (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op V.obj)) (s : 𝒢.val.obj (op V.obj)),
        (show ℱ.val.obj (op U.obj) from η.app U V hUV (r • s)) =
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) ≫
              ((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hUV).op) r) •
            (show ℱ.val.obj (op U.obj) from η.app U V hUV s))
    (Φ :
      ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢) ⟶
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj ((f _*).obj ℱ)))
    (hΦ :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        Φ.hom.app (op V.obj) ≫ ℱ.val.presheaf.map (homOfLE hUV).op =
          η.app U V hUV) :
    𝒢 ⟶ (f _*).obj ℱ :=
  ⟨basis_pair_lift_to_presheaf_module_hom (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
    hBX hBY η hη Φ hΦ⟩

/-- Helper for Lemma 6.30.17: the packaged module morphism still recovers the original basis-pair
family after restricting from `f^{-1}(V)` to `U`. -/
theorem basis_pair_lift_restrict_eq_eta
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η :
      BasisContinuousMapSectionFamily f.hom.base BX BY
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢)
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (hη :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj)
        (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op V.obj)) (s : 𝒢.val.obj (op V.obj)),
        (show ℱ.val.obj (op U.obj) from η.app U V hUV (r • s)) =
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) ≫
              ((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hUV).op) r) •
            (show ℱ.val.obj (op U.obj) from η.app U V hUV s))
    (Φ :
      ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢) ⟶
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj ((f _*).obj ℱ)))
    (hΦ :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        Φ.hom.app (op V.obj) ≫ ℱ.val.presheaf.map (homOfLE hUV).op =
          η.app U V hUV) :
    ∀ (U : BasisOpenX) (V : BasisOpenY)
      (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
      (((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).map
          (basis_pair_lift_to_module_hom (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
            hBX hBY η hη Φ hΦ)).hom.app (op V.obj)) ≫
          ℱ.val.presheaf.map (homOfLE hUV).op =
        η.app U V hUV := by
  intro U V hUV
  -- The module lift was built from the additive lift `Φ`, so the recovery equation is unchanged.
  simpa [basis_pair_lift_to_module_hom, basis_pair_lift_to_presheaf_module_hom] using hΦ U V hUV

/-- Helper for Lemma 6.30.17: uniqueness of the module lift follows by forgetting to sheaves of
abelian groups and reusing the uniqueness from Lemma `6.30.16`. -/
theorem basis_pair_lift_unique
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η :
      BasisContinuousMapSectionFamily f.hom.base BX BY
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢)
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (hη :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj)
        (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op V.obj)) (s : 𝒢.val.obj (op V.obj)),
        (show ℱ.val.obj (op U.obj) from η.app U V hUV (r • s)) =
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) ≫
              ((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hUV).op) r) •
            (show ℱ.val.obj (op U.obj) from η.app U V hUV s))
    (Φ :
      ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢) ⟶
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj ((f _*).obj ℱ)))
    (hΦ :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        Φ.hom.app (op V.obj) ≫ ℱ.val.presheaf.map (homOfLE hUV).op =
          η.app U V hUV)
    (hΦ_unique :
      ∀ Ψ :
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢) ⟶
          ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj ((f _*).obj ℱ)),
        (∀ (U : BasisOpenX) (V : BasisOpenY)
          (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
          Ψ.hom.app (op V.obj) ≫ ℱ.val.presheaf.map (homOfLE hUV).op =
            η.app U V hUV) →
          Ψ = Φ)
    (ψ : 𝒢 ⟶ (f _*).obj ℱ)
    (hψ :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        (((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).map ψ).hom.app (op V.obj)) ≫
            ℱ.val.presheaf.map (homOfLE hUV).op =
          η.app U V hUV) :
    ψ = basis_pair_lift_to_module_hom (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
      hBX hBY η hη Φ hΦ := by
  have hψ_underlying :
      ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).map ψ) = Φ := by
    apply hΦ_unique
    intro U V hUV
    simpa using hψ U V hUV
  have hconstructed_underlying :
      ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).map
          (basis_pair_lift_to_module_hom (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
            hBX hBY η hη Φ hΦ)) = Φ := by
    apply hΦ_unique
    intro U V hUV
    simpa using
      basis_pair_lift_restrict_eq_eta (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
        hBX hBY η hη Φ hΦ U V hUV
  exact Functor.Faithful.map_injective
    (F := SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y)))
    (hψ_underlying.trans hconstructed_underlying.symm)

/-- Lemma 6.30.17: a compatible family of `\mathcal O_Y(V)`-linear maps
`\mathcal G(V) → \mathcal F(U)` for basis opens `V ∈ BY`, `U ∈ BX`, and `U ⊆ f⁻¹(V)` comes from
exactly one morphism of sheaves of `\mathcal O_Y`-modules `𝒢 ⟶ f_* ℱ`, and on basis opens it
recovers the given maps after restricting from `f⁻¹(V)` to `U`. -/
theorem existsUnique_module_pushforward_hom_of_basis_pair_sections
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η :
      BasisContinuousMapSectionFamily f.hom.base BX BY
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢)
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (hη :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj)
        (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op V.obj)) (s : 𝒢.val.obj (op V.obj)),
        (show ℱ.val.obj (op U.obj) from η.app U V hUV (r • s)) =
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) ≫
              ((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hUV).op) r) •
            (show ℱ.val.obj (op U.obj) from η.app U V hUV s)) :
    ∃! φ : 𝒢 ⟶ (f _*).obj ℱ,
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        (((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).map φ).hom.app (op V.obj)) ≫
            ℱ.val.presheaf.map (homOfLE hUV).op =
          η.app U V hUV := by
  -- First forget the module structures and apply the additive pushforward extension theorem.
  obtain ⟨Φ, hΦ, hΦ_unique⟩ :=
    existsUnique_pushforward_hom_of_basis_section_family
      (f := f.hom.base) (BX := BX) (BY := BY)
      (((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢))
      (((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
      hBX hBY η
  refine ⟨basis_pair_lift_to_module_hom (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
      hBX hBY η hη Φ hΦ, ?_, ?_⟩
  · -- The wrapped module morphism still restricts to the given basis-pair family.
    intro U V hUV
    exact basis_pair_lift_restrict_eq_eta (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
      hBX hBY η hη Φ hΦ U V hUV
  · -- Uniqueness is inherited from the additive uniqueness after forgetting module structures.
    intro ψ hψ
    exact basis_pair_lift_unique (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
      hBX hBY η hη Φ hΦ hΦ_unique ψ hψ

end AlgebraicGeometry
