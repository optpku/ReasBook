module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_11_3
public import stacks_project.Chap07.Lemma_7_12_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open Opposite

noncomputable section

universe u v

namespace CategoryTheory

/-- A semi-representable family in `C` is a type-indexed family of objects of `C`. -/
structure SemiRepresentableFamily.{w} (C : Type u) [Category.{v} C] where
  /-- The indexing type of the family. -/
  index : Type w
  /-- The object attached to each index. -/
  obj : index → C

end CategoryTheory

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

/-- A site has enough objects with property `P` if every object admits a cover all of whose
members satisfy `P`. -/
def HasEnoughObjectsWithProperty (P : C → Prop) : Prop :=
  ∀ U : C, ∃ S : J.Cover U, ∀ I : S.Arrow, P I.Y

open scoped SheafifiedRepresentable

/- Domain-style sampling for Lemma 7.12.5:
- primary domain: sheafified representables, locally surjective cover maps, and coequalizers in
  the sheaf topos `Sh(C, J)`;
- sampled owner declarations:
  `GrothendieckTopology.sheafifiedRepresentable`,
  `GrothendieckTopology.sheafifiedRepresentableCoverMap_isLocallySurjective`,
  `CategoryTheory.Limits.Cofork.ofπ`,
  `CategoryTheory.Sheaf.isColimitCoforkOfIsLocallySurjective`,
  `GrothendieckTopology.HasEnoughObjectsWithProperty`;
- best owner abstraction: this source-facing existence theorem should expose the actual coequalizer
  diagram `ℱ₁ ⇉ ℱ₀ ⟶ ℱ` and use the canonical owner
  `IsColimit (Cofork.ofπ π hπ)` for its universal property;
- primitive data: covers by objects of `E`, the resulting semi-representable families, the induced
  parallel pair between their coproducts, and the comparison map `ℱ₀ ⟶ ℱ`;
- derived API: existence of the `IsColimit` witness for the resulting canonical cofork.

Source/core/bridge triage:
- `source-facing`: the existence of a coequalizer presentation of a sheaf by coproducts of
  sheafified representables attached to objects of `E`;
- `core/canonical`: `Cofork.ofπ`, `IsColimit`, `J.sheafifiedRepresentable`, and
  `Sheaf.isColimitCoforkOfIsLocallySurjective`;
- `bridge/view`: the chosen semi-representable families and the induced parallel pair between their
  coproducts.

This item should stay `source-facing`: it chooses coproducts of sheafified representables from
`E`, but the coequalizer clause itself should use the canonical cofork owner rather than a broader
parallel-pair colimit wrapper.
-/

-- Proof sketch: choose a coproduct of sheafified representables from `E` mapping epimorphically
-- to `ℱ`, apply the same construction to the kernel pair of that map, and use Lemma 7.11.3 to
-- identify the resulting cofork as a coequalizer. Since `IsColimit` is a structure, the
-- existence theorem records its universal-property witness through `Nonempty`.
/-- Helper for Lemma 7.12.5: evaluating a morphism out of `h[U]^#` on the canonical identity
section recovers the corresponding section of the target sheaf. -/
lemma sheafifiedRepresentable_component_eq_section
    {ℱ : Sheaf J (Type (max u v))} {U : C} (α : h[U]^#[J] ⟶ ℱ) :
    α.hom.app (op U)
        (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J]))) =
      J.uliftSheafifiedRepresentableHomEquiv ℱ U α := by
  -- Evaluate `α` on the canonical identity section by rewriting it as a composition with `𝟙`.
  have hcomp :=
    J.uliftSheafifiedRepresentableHomEquiv_comp
      (𝟙 (h[U]^#[J])) α
  -- The source-side equivalence sends `𝟙` to the identity section, so the composition formula
  -- becomes exactly the desired evaluation identity.
  simpa using hcomp.symm

/-- Helper for Lemma 7.12.5: every sheaf admits a locally surjective map from a coproduct of
sheafified representables attached to objects of `E`. -/
lemma exists_locally_surjective_map_from_basis_objects
    {E : Set C}
    (hE : J.HasEnoughObjectsWithProperty E)
    (ℱ : Sheaf J (Type (max u v))) :
    ∃ 𝒰 : {𝒰 : SemiRepresentableFamily C // ∀ i : 𝒰.index, 𝒰.obj i ∈ E},
      let _ : HasColimitsOfShape (Discrete 𝒰.1.index) (Sheaf J (Type (max u v))) :=
        Sheaf.instHasColimitsOfShape
      ∃ π : (∐ fun i : 𝒰.1.index ↦ h[𝒰.1.obj i]^#[J]) ⟶ ℱ,
        Sheaf.IsLocallySurjective π := by
  let 𝒰 : SemiRepresentableFamily C :=
    { index := Σ U : { U : C // U ∈ E }, (h[U.1]^#[J] ⟶ ℱ)
      obj := fun i ↦ i.1.1 }
  refine ⟨⟨𝒰, ?_⟩, ?_⟩
  · intro i
    exact i.1.2
  · let _ : HasColimitsOfShape (Discrete 𝒰.index) (Sheaf J (Type (max u v))) :=
      Sheaf.instHasColimitsOfShape
    let π : (∐ fun i : 𝒰.index ↦ h[𝒰.obj i]^#[J]) ⟶ ℱ :=
      Limits.Sigma.desc fun i : 𝒰.index ↦ i.2
    refine ⟨π, ?_⟩
    refine ⟨?_⟩
    intro U x
    obtain ⟨S, hS⟩ := hE U
    -- The chosen cover lies inside the image sieve by using, on each member, the component
    -- indexed by the restricted section of `x`.
    refine J.superset_covering ?_ S.2
    intro V f hf
    let I : S.Arrow := ⟨V, f, hf⟩
    let α :
        h[I.Y]^#[J] ⟶ ℱ :=
      (J.uliftSheafifiedRepresentableHomEquiv ℱ I.Y).symm
        (ℱ.obj.map I.f.op x)
    let i : 𝒰.index := ⟨⟨I.Y, hS I⟩, α⟩
    refine ⟨(Limits.Sigma.ι (fun j : 𝒰.index ↦ h[𝒰.obj j]^#[J]) i).hom.app (op I.Y)
      (J.uliftSheafifiedRepresentableHomEquiv (h[I.Y]^#[J]) I.Y (𝟙 (h[I.Y]^#[J]))), ?_⟩
    -- First isolate the coproduct component chosen by `i`.
    have hι : (Limits.Sigma.ι (fun j : 𝒰.index ↦ h[𝒰.obj j]^#[J]) i) ≫ π = α := by
      simpa [π, i] using
        (Limits.Sigma.ι_desc (fun j : 𝒰.index ↦ j.2) i)
    -- Then evaluate that component on the identity section and identify it with the restriction.
    calc
      π.hom.app (op I.Y)
          ((Limits.Sigma.ι (fun j : 𝒰.index ↦ h[𝒰.obj j]^#[J]) i).hom.app (op I.Y)
            (J.uliftSheafifiedRepresentableHomEquiv (h[I.Y]^#[J]) I.Y
              (𝟙 (h[I.Y]^#[J])))) =
        α.hom.app (op I.Y)
          (J.uliftSheafifiedRepresentableHomEquiv (h[I.Y]^#[J]) I.Y
            (𝟙 (h[I.Y]^#[J]))) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦
                    k.hom.app (op I.Y)
                      (J.uliftSheafifiedRepresentableHomEquiv (h[I.Y]^#[J]) I.Y
                        (𝟙 (h[I.Y]^#[J]))))
                  hι
      _ = J.uliftSheafifiedRepresentableHomEquiv ℱ I.Y α := by
        rw [sheafifiedRepresentable_component_eq_section (J := J) α]
      _ = ℱ.obj.map I.f.op x := by
        rw [(J.uliftSheafifiedRepresentableHomEquiv ℱ I.Y).apply_symm_apply]

/-- Helper for Lemma 7.12.5: precomposing the parallel pair by an epimorphism does not change the
coequalizer with the same cofork map. -/
theorem isColimit_of_epi_precompose
    {X A B T : Sheaf J (Type (max u v))}
    {e : X ⟶ A} [Epi e]
    {a b : A ⟶ B} {π : B ⟶ T}
    (h : a ≫ π = b ≫ π)
    (hcolim : IsColimit (Cofork.ofπ (f := a) (g := b) π h)) :
    Nonempty (IsColimit
      (Cofork.ofπ (f := e ≫ a) (g := e ≫ b) π
        (by simpa [Category.assoc] using congrArg (fun k ↦ e ≫ k) h))) := by
  refine ⟨Cofork.IsColimit.mk _ (fun s ↦ ?_) ?_ ?_⟩
  · exact hcolim.desc (Cofork.ofπ s.π ((cancel_epi e).1 s.condition))
  · intro s
    exact hcolim.fac (Cofork.ofπ s.π ((cancel_epi e).1 s.condition)) WalkingParallelPair.one
  · intro s m hm
    apply Cofork.IsColimit.hom_ext hcolim
    exact hm.trans (hcolim.fac (Cofork.ofπ s.π ((cancel_epi e).1 s.condition))
      WalkingParallelPair.one).symm

/-- Lemma 7.12.5: if every object is covered by objects of `E`, then every sheaf of sets admits a
coequalizer presentation by a parallel pair between coproducts of sheafified representables whose
indexing objects lie in `E`. -/
theorem exists_coequalizer_presentation_by_sheafified_representables
    {E : Set C}
    (hE : J.HasEnoughObjectsWithProperty E)
    (ℱ : Sheaf J (Type (max u v))) :
    ∃ 𝒰₀ : {𝒰 : SemiRepresentableFamily C // ∀ i : 𝒰.index, 𝒰.obj i ∈ E},
      ∃ 𝒰₁ : {𝒰 : SemiRepresentableFamily C // ∀ i : 𝒰.index, 𝒰.obj i ∈ E},
        let _ : HasColimitsOfShape (Discrete 𝒰₁.1.index) (Sheaf J (Type (max u v))) :=
          Sheaf.instHasColimitsOfShape
        let _ : HasColimitsOfShape (Discrete 𝒰₀.1.index) (Sheaf J (Type (max u v))) :=
          Sheaf.instHasColimitsOfShape
        ∃ (p q :
            (∐ fun i : 𝒰₁.1.index ↦ h[𝒰₁.1.obj i]^#[J]) ⟶
              (∐ fun i : 𝒰₀.1.index ↦ h[𝒰₀.1.obj i]^#[J]))
          (π :
            (∐ fun i : 𝒰₀.1.index ↦ h[𝒰₀.1.obj i]^#[J]) ⟶ ℱ)
          (hπ : p ≫ π = q ≫ π),
          Nonempty (IsColimit (Cofork.ofπ π hπ)) := by
  -- First follow the source proof and choose a locally surjective basis presentation of `ℱ`.
  obtain ⟨𝒰₀, π, hπ₀⟩ := exists_locally_surjective_map_from_basis_objects (J := J) hE ℱ
  let 𝒢 := Limits.pullback π π
  -- Next present the kernel pair by the same kind of locally surjective basis map.
  obtain ⟨𝒰₁, ψ, hψ⟩ :=
    exists_locally_surjective_map_from_basis_objects (J := J) hE 𝒢
  let _ : HasColimitsOfShape (Discrete 𝒰₀.1.index) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  let _ : HasColimitsOfShape (Discrete 𝒰₁.1.index) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  let p :
      (∐ fun i : 𝒰₁.1.index ↦ h[𝒰₁.1.obj i]^#[J]) ⟶
        (∐ fun i : 𝒰₀.1.index ↦ h[𝒰₀.1.obj i]^#[J]) :=
    ψ ≫ Limits.pullback.fst π π
  let q :
      (∐ fun i : 𝒰₁.1.index ↦ h[𝒰₁.1.obj i]^#[J]) ⟶
        (∐ fun i : 𝒰₀.1.index ↦ h[𝒰₀.1.obj i]^#[J]) :=
    ψ ≫ Limits.pullback.snd π π
  have hpq : p ≫ π = q ≫ π := by
    -- The two maps become equal after composing with `π` because they factor through the kernel
    -- pair projections.
    simpa [p, q, Category.assoc] using
      congrArg
        (fun k ↦ ψ ≫ k)
        (Limits.pullback.condition (f := π) (g := π))
  let _ : Sheaf.IsLocallySurjective ψ := hψ
  let _ : Epi ψ := inferInstance
  -- Lemma 7.11.3 gives the kernel-pair coequalizer, and the epi-precomposition helper transfers
  -- it to the chosen basis presentation of that kernel pair.
  refine ⟨𝒰₀, 𝒰₁, p, q, π, hpq, ?_⟩
  exact isColimit_of_epi_precompose (J := J) Limits.pullback.condition
    (Sheaf.isColimitCoforkOfIsLocallySurjective π hπ₀)

end CategoryTheory.GrothendieckTopology

end
