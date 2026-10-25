module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import stacks_project.Chap07.Lemma_7_12_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

open scoped SheafifiedRepresentable

/- Domain-style sampling for Lemma 7.40.1:
- primary domain: Grothendieck-topology cover theory and locally surjective morphisms of sheaves of
  sets, expressed through the chapter's sheafified-representable owner layer;
- sampled owner declarations:
  `GrothendieckTopology.IsWeaklyContractible`,
  `GrothendieckTopology.sheafifiedRepresentableCoverMap`,
  `GrothendieckTopology.sheafifiedRepresentableCoverMap_isLocallySurjective`,
  `CategoryTheory.IsSplitEpi`;
- best owner abstraction: the source-facing predicate `J.IsWeaklyContractible U`, with the
  sheaf-side comparison maps supplied by the canonical owner `J.sheafifiedRepresentableCoverMap S`;
- primitive data: only the site `(C, J)` and the object `U : C`;
- derived API: the section-surjectivity characterization and the split-epimorphism criterion for
  canonical sheafified cover maps.

Source/core/bridge triage:
- `source-facing`: `J.IsWeaklyContractible U`;
- `core/canonical`: `J.sheafifiedRepresentableCoverMap S` and `CategoryTheory.IsSplitEpi`;
- `bridge/view`: the equivalence between the section-surjectivity formulation and the split-epi
  formulation for the canonical cover maps.

The weakly-contractible predicate is the owner abstraction in this file, so the public API should
define it once and derive its section-surjectivity interface canonically rather than carrying a
hand-written duplicate of the single-field-class unpacking theorem.
-/

/-- An object `U` of a site is weakly contractible when every locally surjective morphism of
sheaves of sets is surjective on sections over `U`. -/
@[mk_iff isWeaklyContractible_iff_surjective_sections]
class IsWeaklyContractible (U : C) : Prop where
  surjective_sections ⦃ℱ 𝒢 : Sheaf J (Type (max u v))⦄
      (π : ℱ ⟶ 𝒢) (_ : Sheaf.IsLocallySurjective π) :
      Function.Surjective (π.hom.app (op U))

section

variable [HasWeakSheafify J (Type (max u v))]

-- Source/core/bridge triage for 7.40.1:
-- * source-facing owner: `J.IsWeaklyContractible U`
-- * core/canonical sheaf-side owner: `J.sheafifiedRepresentableCoverMap S`
-- * derived API used by the proof: `sheafifiedRepresentableCoverMap_isLocallySurjective`
--
-- Proof sketch: for `(1) → (2)`, lift a section of `𝒢(U)` locally along a covering, view the
-- local lifts as morphisms from the sheafified representables of the cover, and precompose with
-- a chosen splitting `h_U^# ⟶ ∐ h_{U_i}^#` to obtain a global lift in `ℱ(U)`. For `(2) → (1)`,
-- apply the surjectivity-on-sections hypothesis to the locally surjective canonical map
-- `∐ h_{U_i}^# ⟶ h_U^#` attached to a covering, then lift `𝟙_U ∈ h_U^#(U)` to a section of the
-- coproduct and interpret it via the sheafified Yoneda correspondence as a right inverse.

/-- Lemma 7.40.1: an object `U` of a site is weakly contractible if and only if for every
covering family of `U`, the canonical sheafified coproduct map is split epic. -/
theorem isWeaklyContractible_iff_isSplitEpi_sheafifiedRepresentableCoverMap (U : C) :
    J.IsWeaklyContractible U ↔
      ∀ S : J.Cover U, IsSplitEpi (J.sheafifiedRepresentableCoverMap S) := by
  constructor
  · intro hU S
    let π : ∐ (fun I : S.Arrow ↦ h[I.Y]^#[J]) ⟶ h[U]^#[J] := J.sheafifiedRepresentableCoverMap S
    letI : Sheaf.IsLocallySurjective π := by
      simpa [π] using sheafifiedRepresentableCoverMap_isLocallySurjective S
    let eTarget := J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U
    let eSource := J.uliftSheafifiedRepresentableHomEquiv (∐ (fun I : S.Arrow ↦ h[I.Y]^#[J])) U
    have hsurj := hU.surjective_sections π inferInstance
    obtain ⟨x, hx⟩ := hsurj (eTarget (𝟙 _))
    refine IsSplitEpi.mk' ⟨eSource.symm x, ?_⟩
    apply eTarget.injective
    rw [J.uliftSheafifiedRepresentableHomEquiv_comp]
    change π.hom.app (op U) (eSource (eSource.symm x)) = eTarget (𝟙 _)
    simpa using hx
  · intro hU
    refine ⟨fun {ℱ 𝒢} π hπ y ↦ ?_⟩
    let S : J.Cover U := ⟨Presheaf.imageSieve π.hom y, Presheaf.imageSieve_mem J π.hom y⟩
    letI : IsSplitEpi (J.sheafifiedRepresentableCoverMap S) := hU S
    let β : h[U]^#[J] ⟶ 𝒢 := (J.uliftSheafifiedRepresentableHomEquiv 𝒢 U).symm y
    let αI : ∀ I : S.Arrow, h[I.Y]^#[J] ⟶ ℱ :=
      fun I ↦
        (J.uliftSheafifiedRepresentableHomEquiv ℱ I.Y).symm
          (Presheaf.localPreimage π.hom y I.f I.hf)
    let α : ∐ (fun I : S.Arrow ↦ h[I.Y]^#[J]) ⟶ ℱ := Limits.Sigma.desc αI
    have hy : (J.uliftSheafifiedRepresentableHomEquiv 𝒢 U) β = y :=
      Equiv.apply_symm_apply (J.uliftSheafifiedRepresentableHomEquiv 𝒢 U) y
    have hα :
        α ≫ π = J.sheafifiedRepresentableCoverMap S ≫ β := by
      apply Limits.Sigma.hom_ext
      intro I
      apply (J.uliftSheafifiedRepresentableHomEquiv 𝒢 I.Y).injective
      rw [← Category.assoc, Limits.Sigma.ι_desc, J.uliftSheafifiedRepresentableHomEquiv_comp]
      rw [← Category.assoc, sheafifiedRepresentableCoverMap, Limits.Sigma.ι_desc]
      have hβ :
          (J.uliftSheafifiedRepresentableHomEquiv 𝒢 I.Y)
              (J.sheafifiedRepresentableMap I.f ≫ β) =
            𝒢.obj.map I.f.op ((J.uliftSheafifiedRepresentableHomEquiv 𝒢 U) β) := by
        simpa [β, sheafifiedRepresentableMap, sheafifiedRepresentableFunctor,
          uliftSheafifiedRepresentableFunctor] using
          (J.uliftSheafifiedRepresentableHomEquiv_naturality I.f 𝒢 β)
      have hαI :
          (J.uliftSheafifiedRepresentableHomEquiv ℱ I.Y) (αI I) =
            Presheaf.localPreimage π.hom y I.f I.hf := by
        dsimp [αI]
        exact
          Equiv.apply_symm_apply (J.uliftSheafifiedRepresentableHomEquiv ℱ I.Y)
            (Presheaf.localPreimage π.hom y I.f I.hf)
      rw [hβ, hy]
      rw [hαI]
      simpa using Presheaf.app_localPreimage π.hom y I.f I.hf
    let σ : h[U]^#[J] ⟶ ℱ := section_ (J.sheafifiedRepresentableCoverMap S) ≫ α
    refine ⟨(J.uliftSheafifiedRepresentableHomEquiv ℱ U) σ, ?_⟩
    change π.hom.app (op U)
        ((J.uliftSheafifiedRepresentableHomEquiv ℱ U) σ) = y
    rw [← J.uliftSheafifiedRepresentableHomEquiv_comp]
    dsimp [σ]
    rw [Category.assoc, hα, IsSplitEpi.id_assoc]
    exact hy

/-- For a weakly contractible object `U`, every canonical sheafified cover map onto `h_U^#` is
split epic. -/
theorem IsWeaklyContractible.isSplitEpi_sheafifiedRepresentableCoverMap
    {U : C} [J.IsWeaklyContractible U] (S : J.Cover U) :
    IsSplitEpi (J.sheafifiedRepresentableCoverMap S) :=
  (J.isWeaklyContractible_iff_isSplitEpi_sheafifiedRepresentableCoverMap U).1 inferInstance S

/-- If every canonical sheafified cover map onto `h_U^#` is split epic, then `U` is weakly
contractible. -/
theorem isWeaklyContractible_of_isSplitEpi_sheafifiedRepresentableCoverMap
    {U : C} (hU : ∀ S : J.Cover U, IsSplitEpi (J.sheafifiedRepresentableCoverMap S)) :
    J.IsWeaklyContractible U :=
  (J.isWeaklyContractible_iff_isSplitEpi_sheafifiedRepresentableCoverMap U).2 hU

end

end CategoryTheory.GrothendieckTopology
