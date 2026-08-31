module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_8_1
public import stacks_project.Chap07.Definition_7_8_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe w u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 7.17.1:
- primary domain: Grothendieck-topology covers and explicit covering families;
- sampled owner abstractions:
  `GrothendieckTopology.Cover`,
  `Presieve.exists_eq_ofArrows`,
  `SemiRepresentableFamily.Over.toSieve`,
  `SemiRepresentableFamily.Over.toPresieve`;
- source-facing layer: quasi-compactness of an object in a site;
- core/canonical owner: `J.QuasiCompactObject U` as a universe-independent property of `U`;
- bridge/view layer: explicit covering families `SemiRepresentableFamily.Over U`.

Primitive data are only the topology `J`, the object `U`, and a covering sieve on `U`. Explicit
indexed families are a bridge/view presentation of that sieve, so the public owner should not
store the index universe as primitive data.
-/

/-- Definition 7.17.1: an object `U` of a site `(C, J)` is quasi-compact if every covering family
of maps with fixed target `U` admits a covering refinement whose refinement morphism has finite
image on indices. -/
def QuasiCompactObject (J : GrothendieckTopology C) (U : C) : Prop :=
  ∀ S : J.Cover U,
    ∃ (T : Set S.Arrow) (_ : T.Finite),
      Sieve.ofArrows (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f) ∈ J U

-- Proof sketch: transport a covering sieve across an isomorphism using pullback stability and
-- `GrothendieckTopology.pullback_mem_iff_of_isIso`, then apply the finite-subcover field on the
-- isomorphic source object and push the resulting finite family back across the same isomorphism.
/-- Quasi-compactness is closed under isomorphisms of site objects. -/
instance quasiCompactObject_isClosedUnderIsomorphisms (J : GrothendieckTopology C) :
    CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms (J.QuasiCompactObject) :=
  { of_iso := by
      intro U V e hU S
      classical
      -- Pull the target cover back along the isomorphism so that `hU` applies on the source.
      let S' : J.Cover U := S.pullback e.hom
      obtain ⟨T, hT, hTcover⟩ := hU S'
      -- Postcompose the finite family on `U` along the isomorphism and record only its image in
      -- the original covering family on `V`.
      let β : T → S.Arrow := fun I ↦ I.1.base
      let T' : Set S.Arrow := Set.range β
      have hT' : T'.Finite := by
        letI := hT.fintype
        simpa [T', β] using Set.finite_range β
      have hpush :
          Sieve.ofArrows (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f ≫ e.hom) ∈ J V := by
        have hpull :
            (Sieve.ofArrows (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f ≫ e.hom)).pullback e.hom ∈
              J U := by
          rw [Sieve.pullback_ofArrows_of_iso]
          simpa [Category.assoc] using hTcover
        exact (GrothendieckTopology.pullback_mem_iff_of_isIso (J := J) (i := e.hom)).1 hpull
      -- Reindex the transported family by its range so the witness is a finite subset of
      -- `S.Arrow`, exactly as required by the definition.
      have hT'presieve :
          Presieve.ofArrows (fun I : T' ↦ I.1.Y) (fun I ↦ I.1.f) =
            Presieve.ofArrows (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f ≫ e.hom) := by
        let a : T → T' := fun I ↦ ⟨β I, ⟨I, rfl⟩⟩
        have ha : Function.Surjective a := by
          rintro ⟨I, i, rfl⟩
          exact ⟨i, rfl⟩
        calc
          Presieve.ofArrows (fun I : T' ↦ I.1.Y) (fun I ↦ I.1.f)
              =
                Presieve.ofArrows
                  (fun I : T ↦ (a I).1.Y)
                  (fun I ↦ (a I).1.f) := by
            symm
            exact Presieve.ofArrows_comp_eq_of_surjective (fun I : T' ↦ I.1.f) ha
          _ = Presieve.ofArrows (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f ≫ e.hom) := by
            rfl
      refine ⟨T', hT', ?_⟩
      simpa [Sieve.ofArrows, hT'presieve] using hpush }

/-- The fixed `max u v`-small owner formulation of quasi-compactness refines any covering family,
regardless of the indexing universe used to present that family. -/
theorem QuasiCompactObject.finite_image_refinement_of_family
    {J : GrothendieckTopology C} {U : C} (hU : QuasiCompactObject J U)
    (𝒰 : SemiRepresentableFamily.Over.{w} U) (h𝒰 : 𝒰.toSieve ∈ J U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{w} U) (_ : 𝒱.toSieve ∈ J U) (φ : 𝒱 ⟶ 𝒰),
      Set.Finite (Set.range φ.α) := by
  let S : J.Cover U := ⟨𝒰.toSieve, h𝒰⟩
  obtain ⟨T, hT, hTcover⟩ := hU S
  let 𝒱₀ := SemiRepresentableFamily.Over.ofArrows (fun I : T ↦ I.1.Y) fun I ↦ I.1.f
  have h𝒱₀ : 𝒱₀.toSieve ∈ J U := hTcover
  have hfactor :
      ∀ I : T, ∃ i : 𝒰.index, ∃ g : I.1.Y ⟶ (𝒰.obj i).left, I.1.f = g ≫ (𝒰.obj i).hom := by
    intro I
    exact Sieve.ofArrows.exists I.1.hf
  choose α g hg using hfactor
  let R : Set 𝒰.index := Set.range α
  have hR : R.Finite := by
    letI := hT.fintype
    simpa [R] using Set.finite_range α
  let 𝒱 : SemiRepresentableFamily.Over.{w} U :=
    { index := R
      obj := fun i ↦ 𝒰.obj i.1 }
  have hle : 𝒱₀.toSieve ≤ 𝒱.toSieve := by
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro I
    let iR : R := ⟨α I, by exact ⟨I, rfl⟩⟩
    refine ⟨_, g I, _, Presieve.ofArrows.mk iR, ?_⟩
    simpa [𝒱₀, 𝒱, iR] using (hg I).symm
  have h𝒱 : 𝒱.toSieve ∈ J U := by
    exact J.superset_covering hle h𝒱₀
  refine ⟨𝒱, h𝒱, ?_, ?_⟩
  · exact
      { α := Subtype.val
        f := fun i ↦ 𝟙 (𝒰.obj i.1) }
  · change Set.Finite (Set.range (Subtype.val : R → 𝒰.index))
    simpa [Subtype.range_coe] using hR

/-- Companion formulation of Definition 7.17.1 for an explicitly indexed covering family. -/
theorem quasiCompactObject_finite_image_refinement_ofArrows
    {J : GrothendieckTopology C} {U : C} (hU : QuasiCompactObject J U)
    {ι : Type w} (Uᵢ : ι → C) (π : ∀ i : ι, Uᵢ i ⟶ U)
    (hcover : Sieve.ofArrows Uᵢ π ∈ J U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{w} U) (_ : 𝒱.toSieve ∈ J U)
      (φ : 𝒱 ⟶ SemiRepresentableFamily.Over.ofArrows Uᵢ π),
      Set.Finite (Set.range φ.α) := by
  have h𝒰 : (SemiRepresentableFamily.Over.ofArrows Uᵢ π).toSieve ∈ J U := by
    simpa [toSieve, toPresieve, ofArrows] using hcover
  simpa [toSieve, toPresieve, ofArrows] using
    hU.finite_image_refinement_of_family (SemiRepresentableFamily.Over.ofArrows Uᵢ π) h𝒰

end CategoryTheory.GrothendieckTopology
