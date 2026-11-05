module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import stacks_project.Chap07.Definition_7_15_1_Topoi
public import stacks_project.Chap07.Lemma_7_12_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [HasWeakSheafify J (Type (max u₂ v₂))]
variable [HasWeakSheafify K (Type (max u₂ v₂))]

/- Domain-style sampling for Lemma 7.24.1:
- primary domain: morphisms of topoi and sheaf-theoretic adjunctions controlled by site covers;
- sampled owner API:
  `MorphismOfTopoiIn`,
  `sheafSections`,
  `GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv`,
  `GrothendieckTopology.exists_coequalizer_presentation_by_sheafified_representables`,
  `Functor.IsCorepresentable`,
  `GrothendieckTopology.Cover`,
  `GrothendieckTopology.HasEnoughObjectsWithProperty`;
- source-facing layer: local corepresentability of the section functors `ℱ ↦ f⁻¹ ℱ (V)` on a
  covering family of objects in the target site;
- core/canonical owners: the inverse-image functor itself, the sheaf-sections owner
  `(sheafSections K (Type (max u₂ v₂))).obj (op V)`, the sheafified-representable owner
  `K.sheafifiedRepresentable V`, and the canonical cover owner
  `K.HasEnoughObjectsWithProperty E`;
- bridge/view: the sheafified-Yoneda equivalence
  `K.uliftSheafifiedRepresentableHomEquiv` identifying
  `Hom(K.sheafifiedRepresentable V, -)` with sections at `V`.

Primitive data are the inverse-image functor, the distinguished object property `E`, the local
corepresentability condition, and the covering condition. The indexed arrows presenting a cover are
derived data of `K.Cover U`, so the public hypothesis should use that owner abstraction rather than
an ad hoc `∃ ι, V, π, Sieve.ofArrows V π ∈ K U` package.

Source/core/bridge triage:
- source-facing: the Stacks hypothesis that `ℱ ↦ f⁻¹ ℱ (V)` is corepresentable for cover members
  `V ∈ E`;
- core/canonical: `Functor.leftAdjointObjIsDefined` for the inverse-image functor `f⁻¹`;
- bridge/view: the local sections hypothesis on a covering family, used to promote
  `f⁻¹.leftAdjointObjIsDefined` to `⊤` and then invoke the owner theorem
  `Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top`.
-/

/- Shared source-facing hypotheses for Lemma 7.24.1. The private theorem below converts them to
the owner predicate `f⁻¹.leftAdjointObjIsDefined = ⊤`, and the public theorem then reuses the
canonical right-adjoint criterion from `PartialAdjoint`. -/
variable (f : MorphismOfTopoiIn J K) (E : ObjectProperty D)

/-- Helper for Lemma 7.24.1: the Hom-functor from a sheafified representable is naturally
identified with the corresponding sections functor after applying `f⁻¹`. -/
private noncomputable def inverseImage_coyonedaSheafifiedRepresentableIsoSections (V : D) :
    (f⁻¹ ⋙ coyoneda.obj (op (K.sheafifiedRepresentable V))) ≅
      (f⁻¹ ⋙ (sheafSections K (Type (max u₂ v₂))).obj (op V)) :=
  NatIso.ofComponents
    (fun ℱ ↦ Equiv.toIso (K.uliftSheafifiedRepresentableHomEquiv ((f⁻¹).obj ℱ) V))
    (fun {ℱ 𝒢} η ↦ by
      -- Compare both natural transformations on a section and use naturality of the Yoneda-style
      -- identification `Hom(h_V^#, -) ≃ (-)(V)`.
      ext α
      exact K.uliftSheafifiedRepresentableHomEquiv_comp α ((f⁻¹).map η))

omit [HasWeakSheafify J (Type (max u₂ v₂))] in
/-- Helper for Lemma 7.24.1: on each basis object `h_V^#` with `E V`, the inverse-image functor
already satisfies the owner predicate needed for a left adjoint object. -/
private theorem inverseImage_leftAdjointObjIsDefined_sheafifiedRepresentable
    (hcorepr : ∀ V : D, E V →
      (f⁻¹ ⋙ (sheafSections K (Type (max u₂ v₂))).obj (op V)).IsCorepresentable)
    {V : D} (hV : E V) :
    (f⁻¹).leftAdjointObjIsDefined (K.sheafifiedRepresentable V) := by
  let _ : (f⁻¹ ⋙ (sheafSections K (Type (max u₂ v₂))).obj (op V)).IsCorepresentable :=
    hcorepr V hV
  -- Switch from the owner predicate to corepresentability of the relevant coyoneda composite.
  rw [Functor.leftAdjointObjIsDefined_iff]
  -- The previous helper turns that coyoneda composite into the assumed sections functor.
  exact corepresentable_of_natIso
    (f⁻¹ ⋙ (sheafSections K (Type (max u₂ v₂))).obj (op V))
    (inverseImage_coyonedaSheafifiedRepresentableIsoSections f V).symm

/-- Helper for Lemma 7.24.1: the basis result is stable under coproducts of sheafified
representables indexed by objects satisfying `E`. -/
private theorem inverseImage_leftAdjointObjIsDefined_coproduct
    (hcorepr : ∀ V : D, E V →
      (f⁻¹ ⋙ (sheafSections K (Type (max u₂ v₂))).obj (op V)).IsCorepresentable)
    (𝒰 : SemiRepresentableFamily.{u₂, v₂, max u₂ v₂} D)
    (h𝒰 : ∀ i : 𝒰.index, E (𝒰.obj i))
    [HasCoproduct (fun i : 𝒰.index ↦ K.sheafifiedRepresentable (𝒰.obj i))] :
    (f⁻¹).leftAdjointObjIsDefined (∐ fun i : 𝒰.index ↦ K.sheafifiedRepresentable (𝒰.obj i)) := by
  let _ : HasColimitsOfShape (Discrete 𝒰.index) (Type (max u₂ v₂)) := inferInstance
  let _ : HasColimitsOfShape (Discrete 𝒰.index) (Sheaf J (Type (max u₂ v₂))) :=
    Sheaf.instHasColimitsOfShape
  -- Apply the colimit-closure lemma to the discrete diagram of basis objects.
  simpa using
    (f⁻¹).leftAdjointObjIsDefined_colimit
      (Discrete.functor (fun i : 𝒰.index ↦ K.sheafifiedRepresentable (𝒰.obj i)))
      (fun i ↦ inverseImage_leftAdjointObjIsDefined_sheafifiedRepresentable f E hcorepr (h𝒰 i.as))

/-- Helper for Lemma 7.24.1: the covering-family hypothesis implies that every sheaf satisfies the
owner predicate `leftAdjointObjIsDefined` for the inverse-image functor. -/
private theorem inverseImage_leftAdjointObjIsDefined_eq_top_of_corepresentable_on_covering_family
    (hcorepr : ∀ V : D, E V →
      (f⁻¹ ⋙ (sheafSections K (Type (max u₂ v₂))).obj (op V)).IsCorepresentable)
    (hcover : K.HasEnoughObjectsWithProperty E) :
    (f⁻¹).leftAdjointObjIsDefined = ⊤ := by
  -- Proof sketch: use the source-facing sections hypothesis on a covering family together with
  -- the canonical coequalizer presentation from Lemma `7.12.5` to promote the owner predicate
  -- `leftAdjointObjIsDefined` to all sheaves, then apply the right-adjoint criterion from
  -- `PartialAdjoint`.
  ext ℱ
  constructor
  · intro _
    trivial
  · intro _
    -- Present the given sheaf as a coequalizer of coproducts of basis sheafified representables.
    obtain ⟨𝒰₀, 𝒰₁, p, q, π, hπ, hcolim⟩ :=
      K.exists_coequalizer_presentation_by_sheafified_representables hcover ℱ
    let 𝒱₀ := 𝒰₀.1
    let 𝒱₁ := 𝒰₁.1
    have h𝒱₀ : ∀ i : 𝒱₀.index, E (𝒱₀.obj i) := 𝒰₀.2
    have h𝒱₁ : ∀ i : 𝒱₁.index, E (𝒱₁.obj i) := 𝒰₁.2
    rcases hcolim with ⟨hc⟩
    let _ : HasColimitsOfShape WalkingParallelPair (Type (max u₂ v₂)) := inferInstance
    let _ : HasColimitsOfShape WalkingParallelPair (Sheaf J (Type (max u₂ v₂))) :=
      Sheaf.instHasColimitsOfShape
    -- It remains to prove the owner predicate on both objects of the parallel pair.
    have hpair :
        ∀ j : WalkingParallelPair,
          (f⁻¹).leftAdjointObjIsDefined ((parallelPair p q).obj j) := by
      refine WalkingParallelPair.rec ?_ ?_
      · let _ : HasColimitsOfShape (Discrete 𝒱₁.index) (Type (max u₂ v₂)) := inferInstance
        let hcolim : HasColimitsOfShape (Discrete 𝒱₁.index) (Sheaf K (Type (max u₂ v₂))) :=
          Sheaf.instHasColimitsOfShape
        let _ : HasCoproduct (fun i : 𝒱₁.index ↦ K.sheafifiedRepresentable (𝒱₁.obj i)) :=
          hcolim.has_colimit (Discrete.functor fun i : 𝒱₁.index ↦ K.sheafifiedRepresentable (𝒱₁.obj i))
        simpa [𝒱₁] using inverseImage_leftAdjointObjIsDefined_coproduct f E hcorepr 𝒱₁ h𝒱₁
      · let _ : HasColimitsOfShape (Discrete 𝒱₀.index) (Type (max u₂ v₂)) := inferInstance
        let hcolim : HasColimitsOfShape (Discrete 𝒱₀.index) (Sheaf K (Type (max u₂ v₂))) :=
          Sheaf.instHasColimitsOfShape
        let _ : HasCoproduct (fun i : 𝒱₀.index ↦ K.sheafifiedRepresentable (𝒱₀.obj i)) :=
          hcolim.has_colimit (Discrete.functor fun i : 𝒱₀.index ↦ K.sheafifiedRepresentable (𝒱₀.obj i))
        simpa [𝒱₀] using inverseImage_leftAdjointObjIsDefined_coproduct f E hcorepr 𝒱₀ h𝒱₀
    -- Closure under this coequalizer presentation promotes the basis result to the target sheaf.
    simpa using (f⁻¹).leftAdjointObjIsDefined_of_isColimit hc hpair

/-- Lemma 7.24.1: if every object of `(D, K)` admits a covering by objects of `E` and, for each
`V ∈ E`, the functor `ℱ ↦ f⁻¹ ℱ (V)` is corepresentable on `Sh(C)`, then the inverse-image
functor `f⁻¹` admits a left adjoint `f_!`. -/
theorem inverseImage_isRightAdjoint_of_corepresentable_on_covering_family
    (hcorepr : ∀ V : D, E V →
      (f⁻¹ ⋙ (sheafSections K (Type (max u₂ v₂))).obj (op V)).IsCorepresentable)
    (hcover : K.HasEnoughObjectsWithProperty E) :
    (f⁻¹).IsRightAdjoint := by
  -- Once the owner predicate holds for every sheaf, the standard partial-adjoint criterion
  -- produces the desired left adjoint to `f⁻¹`.
  exact Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (inverseImage_leftAdjointObjIsDefined_eq_top_of_corepresentable_on_covering_family
      f E hcorepr hcover)

end MorphismOfTopoiIn

end CategoryTheory
