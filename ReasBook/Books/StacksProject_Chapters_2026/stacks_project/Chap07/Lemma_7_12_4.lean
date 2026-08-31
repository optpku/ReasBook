module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open GrothendieckTopology.Cover

universe w u v

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

noncomputable section

namespace Cover

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}

/-- The family of arrows indexed by `S.Arrow` generates exactly the sieve underlying `S`. -/
theorem ofArrows_eq (S : J.Cover U) :
    Sieve.ofArrows Arrow.Y (fun I : S.Arrow ↦ I.f) = (S : Sieve U) := by
  ext Y f
  rw [Sieve.mem_ofArrows_iff]
  constructor
  · rintro ⟨I, g, rfl⟩
    exact S.1.downward_closed I.hf g
  · intro hf
    exact ⟨⟨Y, f, hf⟩, 𝟙 _, by simp⟩

end

end Cover

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Domain-style sampling for the 7.12 sheafified-representable owner layer:
- primary domain: sheafification of representable presheaves on a site, organized by the sheafified
  Yoneda functor and its induced morphisms;
- sampled owner declarations:
  `GrothendieckTopology.yoneda`,
  `sheafificationAdjunction`,
  `Presheaf.isLocallySurjective_presheafToSheaf_map_iff`,
  `GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map`;
- best owner abstraction: the functor `J.uliftSheafifiedRepresentableFunctor`, with the
  default-universe owner `J.sheafifiedRepresentableFunctor` and its induced maps;
- primitive data: the site `(C, J)` together with an object, morphism, or covering family in `C`;
- derived API: the objects `J.sheafifiedRepresentable U`, the morphisms
  `J.sheafifiedRepresentableMap f`, the Yoneda-style equivalence
  `J.uliftSheafifiedRepresentableHomEquiv`, and the covering coproduct map
  `J.sheafifiedRepresentableCoverMap S`.

Source/core/bridge triage:
- `core/canonical`: the sheafified-representable functor and its induced maps;
- `bridge/view`: the cover coproduct map `J.sheafifiedRepresentableCoverMap S`;
- `source-facing`: Lemma `7.12.4`, asserting that this canonical cover map is locally surjective.

This file owns the `core/canonical` sheafified-representable API for the 7.12 cluster, and the
later chapter files should import and reuse that owner layer rather than recreating it downstream.
-/

/-- The sheafified representable sheaf `h_U^#` on the site `(C, J)`. -/
abbrev uliftSheafifiedRepresentable [HasWeakSheafify J (Type (max w u v))] (U : C) :
    Sheaf J (Type (max w u v)) :=
  (presheafToSheaf J (Type (max w u v))).obj (CategoryTheory.uliftYoneda.{max w u v}.obj U)

/-- The default-universe sheafified representable sheaf `h_U^#` on the site `(C, J)`. -/
abbrev sheafifiedRepresentable [HasWeakSheafify J (Type (max u v))] (U : C) :
    Sheaf J (Type (max u v)) :=
  J.uliftSheafifiedRepresentable U

namespace SheafifiedRepresentable

/- Textbook notation for the sheafified representable `h_U^#`. Since Lean does not support the
subscripted binder directly as notation, we write this reusable surface form as `h[U]^#[J]`. -/
scoped notation:max "h[" U "]^#[" J "]" =>
  CategoryTheory.GrothendieckTopology.sheafifiedRepresentable J U

end SheafifiedRepresentable

open scoped SheafifiedRepresentable

/-- The sheafified-representable functor `U ↦ h_U^#` on the site `(C, J)`. -/
abbrev uliftSheafifiedRepresentableFunctor [HasWeakSheafify J (Type (max w u v))] :
    C ⥤ Sheaf J (Type (max w u v)) :=
  CategoryTheory.uliftYoneda.{max w u v} ⋙ presheafToSheaf J (Type (max w u v))

/-- The default-universe sheafified-representable functor `U ↦ h[U]^#[J]`. -/
abbrev sheafifiedRepresentableFunctor [HasWeakSheafify J (Type (max u v))] :
    C ⥤ Sheaf J (Type (max u v)) :=
  J.uliftSheafifiedRepresentableFunctor

/-- The morphism `h_V^# ⟶ h_U^#` induced by a morphism `V ⟶ U`. -/
abbrev sheafifiedRepresentableMap [HasWeakSheafify J (Type (max u v))] {U V : C} (f : V ⟶ U) :
    h[V]^#[J] ⟶ h[U]^#[J] :=
  (J.sheafifiedRepresentableFunctor).map f

/-- The canonical equivalence `Hom(h_U^#, ℱ) ≃ ℱ(U)` for the sheafified representable sheaf. -/
abbrev uliftSheafifiedRepresentableHomEquiv
    [HasWeakSheafify J (Type (max w u v))]
    (ℱ : Sheaf J (Type (max w u v))) (U : C) :
    (J.uliftSheafifiedRepresentable U ⟶ ℱ) ≃ ℱ.obj.obj (op U) :=
  (((sheafificationAdjunction J (Type (max w u v))).homEquiv
    (CategoryTheory.uliftYoneda.{max w u v}.obj U) ℱ).trans
      CategoryTheory.uliftYonedaEquiv.{max w u v})

/-- Naturality in `U` of the canonical equivalence `Hom(h_U^#, ℱ) ≃ ℱ(U)`. -/
theorem uliftSheafifiedRepresentableHomEquiv_naturality
    [HasWeakSheafify J (Type (max w u v))]
    {U V : C} (f : V ⟶ U) (ℱ : Sheaf J (Type (max w u v)))
    (α : J.uliftSheafifiedRepresentable U ⟶ ℱ) :
    J.uliftSheafifiedRepresentableHomEquiv ℱ V
        (J.uliftSheafifiedRepresentableFunctor.map f ≫ α) =
      ℱ.obj.map f.op (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) := by
  dsimp [uliftSheafifiedRepresentableHomEquiv]
  rw [CategoryTheory.uliftYonedaEquiv_naturality.{max w u v}]
  exact congrArg CategoryTheory.uliftYonedaEquiv.{max w u v}
    ((sheafificationAdjunction J (Type (max w u v))).homEquiv_naturality_left
      (CategoryTheory.uliftYoneda.{max w u v}.map f) α)

/-- Naturality in `ℱ` of the canonical equivalence `Hom(h_U^#, ℱ) ≃ ℱ(U)`. -/
theorem uliftSheafifiedRepresentableHomEquiv_comp
    [HasWeakSheafify J (Type (max w u v))]
    {U : C} {ℱ 𝒢 : Sheaf J (Type (max w u v))}
    (α : J.uliftSheafifiedRepresentable U ⟶ ℱ) (β : ℱ ⟶ 𝒢) :
    J.uliftSheafifiedRepresentableHomEquiv 𝒢 U (α ≫ β) =
      β.hom.app (op U) (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) := by
  dsimp [uliftSheafifiedRepresentableHomEquiv]
  calc
    CategoryTheory.uliftYonedaEquiv
        (((sheafificationAdjunction J (Type (max w u v))).homEquiv
          (CategoryTheory.uliftYoneda.{max w u v}.obj U) 𝒢) (α ≫ β)) =
      CategoryTheory.uliftYonedaEquiv
        ((((sheafificationAdjunction J (Type (max w u v))).homEquiv
          (CategoryTheory.uliftYoneda.{max w u v}.obj U) ℱ) α) ≫ β.hom) := by
          exact congrArg CategoryTheory.uliftYonedaEquiv
            ((sheafificationAdjunction J (Type (max w u v))).homEquiv_naturality_right α β)
    _ = β.hom.app (op U)
        (CategoryTheory.uliftYonedaEquiv
          (((sheafificationAdjunction J (Type (max w u v))).homEquiv
            (CategoryTheory.uliftYoneda.{max w u v}.obj U) ℱ) α)) := by
      rw [CategoryTheory.uliftYonedaEquiv_comp]
      rfl

/-- The canonical sheafified morphism from the coproduct of a covering family to `h_U^#`. -/
instance [HasWeakSheafify J (Type (max u v))] {U : C} (S : J.Cover U) :
    HasCoproduct (fun I : S.Arrow ↦ h[I.Y]^#[J]) := by
  let _ : HasColimitsOfShape (Discrete S.Arrow) (Type (max u v)) := inferInstance
  let _ : HasColimitsOfShape (Discrete S.Arrow) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  infer_instance

/-- The canonical sheafified morphism from the coproduct of a covering family to `h_U^#`. -/
abbrev sheafifiedRepresentableCoverMap
    [HasWeakSheafify J (Type (max u v))] {U : C} (S : J.Cover U) :
    ∐ (fun I : S.Arrow ↦ h[I.Y]^#[J]) ⟶ h[U]^#[J] :=
  Limits.Sigma.desc (fun I : S.Arrow ↦ J.sheafifiedRepresentableMap I.f)

/-- The sigma-desc map built from sheafified representable morphisms is locally surjective exactly
when the underlying sigma-desc map of representable presheaves is locally surjective before
sheafification. -/
theorem isLocallySurjective_sigmaDesc_sheafifiedRepresentableMap_iff
    [HasWeakSheafify J (Type (max u v))]
    {ι : Type*} [Small.{max u v} ι] {U : C} (Y : ι → C) (f : ∀ i : ι, Y i ⟶ U)
    [HasCoproduct (fun i : ι ↦ h[Y i]^#[J])] :
    Sheaf.IsLocallySurjective
        (Limits.Sigma.desc (fun i : ι ↦ J.sheafifiedRepresentableMap (f i))) ↔
      Presheaf.IsLocallySurjective J
        (Limits.Sigma.desc (fun i : ι ↦ CategoryTheory.uliftYoneda.{max u v}.map (f i))) := by
  let G := presheafToSheaf J (Type (max u v))
  let F : ι → Cᵒᵖ ⥤ Type (max u v) := fun i ↦ CategoryTheory.uliftYoneda.{max u v}.obj (Y i)
  let gPres :
      ∐ F ⟶ CategoryTheory.uliftYoneda.{max u v}.obj U :=
    Limits.Sigma.desc (fun i : ι ↦ CategoryTheory.uliftYoneda.{max u v}.map (f i))
  let _ : HasCoproduct F := inferInstance
  let _ : HasCoproduct (fun i : ι ↦ G.obj (F i)) := by
    simpa [F, G, sheafifiedRepresentable, uliftSheafifiedRepresentable] using
      (inferInstance : HasCoproduct (fun i : ι ↦ h[Y i]^#[J]))
  constructor
  · intro hdesc
    have hcomp :
        Sheaf.IsLocallySurjective (Limits.sigmaComparison G F ≫ G.map gPres) := by
      simpa [F, G, gPres, sheafifiedRepresentableMap, sheafifiedRepresentableFunctor,
        uliftSheafifiedRepresentableFunctor, Limits.sigmaComparison_map_desc] using hdesc
    have hmap :
        Sheaf.IsLocallySurjective (G.map gPres) := by
      rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
      have hcomp'' :
          Presheaf.IsLocallySurjective J
            ((sheafToPresheaf J (Type (max u v))).map
              (Limits.sigmaComparison G F ≫ G.map gPres)) := by
        exact hcomp
      have hcomp' :
          Presheaf.IsLocallySurjective J
            (((sheafToPresheaf J (Type (max u v))).map (Limits.sigmaComparison G F)) ≫
              (sheafToPresheaf J (Type (max u v))).map (G.map gPres)) := by
        rw [Functor.map_comp] at hcomp''
        exact hcomp''
      let _ :
          Presheaf.IsLocallySurjective J
            ((sheafToPresheaf J (Type (max u v))).map (Limits.sigmaComparison G F)) := by
        infer_instance
      let _ :
          Presheaf.IsLocallyInjective J
            ((sheafToPresheaf J (Type (max u v))).map (Limits.sigmaComparison G F)) := by
        infer_instance
      exact
        (Presheaf.comp_isLocallySurjective_iff J
          ((sheafToPresheaf J (Type (max u v))).map (Limits.sigmaComparison G F))
          ((sheafToPresheaf J (Type (max u v))).map (G.map gPres))).1 hcomp'
    rw [Presheaf.isLocallySurjective_presheafToSheaf_map_iff] at hmap
    exact hmap
  · intro hpres
    have hmap :
        Sheaf.IsLocallySurjective (G.map gPres) := by
      rw [Presheaf.isLocallySurjective_presheafToSheaf_map_iff]
      exact hpres
    let _ : Sheaf.IsLocallySurjective (G.map gPres) := hmap
    simpa [F, G, gPres, sheafifiedRepresentableMap, sheafifiedRepresentableFunctor,
      uliftSheafifiedRepresentableFunctor, Limits.sigmaComparison_map_desc] using
      (show Sheaf.IsLocallySurjective (Limits.sigmaComparison G F ≫ G.map gPres) by
        infer_instance)

end

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {U : C} (S : J.Cover U)

/- Domain-style sampling for Lemma 7.12.4:
- primary domain: local surjectivity of canonical coproduct maps in the sheaf topos `Sh(J)`,
  specialized to the coproduct of sheafified representables attached to a cover;
- sampled owner declarations:
  `GrothendieckTopology.sheafifiedRepresentableCoverMap`,
  `Presheaf.isLocallySurjective_presheafToSheaf_map_iff`,
  `GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map`,
  `Limits.sigmaComparison_map_desc`;
- best owner abstraction: the canonical sheaf morphism `J.sheafifiedRepresentableCoverMap S`;
- primitive data: a covering family `S : J.Cover U`;
- derived API: local surjectivity of the sheafified coproduct comparison map, proved by sheafifying
  the canonical presheaf coproduct map and composing with the coproduct comparison isomorphism.

Source/core/bridge triage:
- `source-facing`: the textbook map from the coproduct of the `h_{U_i}^#` to `h_U^#` attached to a
  covering family;
- `core/canonical`: the presheaf local-surjectivity owners
  `Presheaf.isLocallySurjective_presheafToSheaf_map_iff` and
  `J.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map`;
- `bridge/view`: `J.sheafifiedRepresentableCoverMap S`, obtained from the presheaf coproduct map by
  sheafification and the canonical coproduct comparison `sigmaComparison`.

This file targets the `bridge/view` layer: the public theorem should stay phrased for
`J.sheafifiedRepresentableCoverMap S`, while its proof reuses the upstream owner abstractions
instead of rebuilding a parallel local API.
-/
/-- Helper for Lemma 7.12.4: sections of a sheaf over `U` are determined by their restrictions
to the members of the covering family `S`. -/
lemma section_eq_of_cover_restrictions_eq
    (S : J.Cover U)
    {ℱ : Sheaf J (Type (max u v))} {s t : ℱ.obj.obj (op U)}
    (h : ∀ I : S.Arrow, ℱ.obj.map I.f.op s = ℱ.obj.map I.f.op t) :
    s = t := by
  let e₁ : PUnit ⟶ ℱ.obj.obj (op U) := fun _ ↦ s
  let e₂ : PUnit ⟶ ℱ.obj.obj (op U) := fun _ ↦ t
  -- Package the sections as constant maps so separatedness applies directly.
  have heq : e₁ = e₂ := by
    -- The sheaf property forces equality once all cover restrictions agree.
    apply ℱ.property.hom_ext S e₁ e₂
    intro I
    funext x
    cases x
    exact h I
  simpa [e₁, e₂] using congr_fun heq PUnit.unit

/-- Helper for Lemma 7.12.4: equality after precomposition with the canonical coproduct map
forces equality of the induced restricted sections on each member of the cover. -/
lemma cover_component_eq_of_coverMap_comp_eq
    [HasWeakSheafify J (Type (max u v))]
    (S : J.Cover U) {ℱ : Sheaf J (Type (max u v))} {α β : J.sheafifiedRepresentable U ⟶ ℱ}
    (hcomp : J.sheafifiedRepresentableCoverMap S ≫ α = J.sheafifiedRepresentableCoverMap S ≫ β) :
    ∀ I : S.Arrow,
      ℱ.obj.map I.f.op (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) =
        ℱ.obj.map I.f.op (J.uliftSheafifiedRepresentableHomEquiv ℱ U β) := by
  intro I
  have hI : J.sheafifiedRepresentableMap I.f ≫ α = J.sheafifiedRepresentableMap I.f ≫ β := by
    -- Precompose with the `I`-th coproduct inclusion to isolate the `I`-th component.
    have hι := congrArg
      (fun k => Limits.Sigma.ι (fun I : S.Arrow ↦ J.sheafifiedRepresentable I.Y) I ≫ k) hcomp
    have hι' :
        (Limits.Sigma.ι (fun I : S.Arrow ↦ J.sheafifiedRepresentable I.Y) I ≫
            J.sheafifiedRepresentableCoverMap S) ≫ α =
          (Limits.Sigma.ι (fun I : S.Arrow ↦ J.sheafifiedRepresentable I.Y) I ≫
            J.sheafifiedRepresentableCoverMap S) ≫ β := by
      simpa [Category.assoc] using hι
    rw [sheafifiedRepresentableCoverMap, Limits.Sigma.ι_desc] at hι'
    simpa [sheafifiedRepresentableMap, Category.assoc] using hι'
  -- Translate equality of morphisms out of `h[I.Y]^#` into equality of restricted sections.
  have hα :
      J.uliftSheafifiedRepresentableHomEquiv ℱ I.Y (J.sheafifiedRepresentableMap I.f ≫ α) =
        ℱ.obj.map I.f.op (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) := by
    simpa [sheafifiedRepresentableMap] using
      J.uliftSheafifiedRepresentableHomEquiv_naturality I.f ℱ α
  have hβ :
      J.uliftSheafifiedRepresentableHomEquiv ℱ I.Y (J.sheafifiedRepresentableMap I.f ≫ β) =
        ℱ.obj.map I.f.op (J.uliftSheafifiedRepresentableHomEquiv ℱ U β) := by
    simpa [sheafifiedRepresentableMap] using
      J.uliftSheafifiedRepresentableHomEquiv_naturality I.f ℱ β
  rw [← hα, ← hβ]
  exact congrArg (J.uliftSheafifiedRepresentableHomEquiv ℱ I.Y) hI

/-- Helper for Lemma 7.12.4: the canonical coproduct map attached to a covering family is epi
after sheafification. -/
lemma sheafifiedRepresentableCoverMap_epi
    [HasWeakSheafify J (Type (max u v))] (S : J.Cover U) :
    Epi (J.sheafifiedRepresentableCoverMap S) where
  left_cancellation {ℱ} α β h := by
    -- Compare the two morphisms by the corresponding sections of `ℱ` over `U`.
    apply (J.uliftSheafifiedRepresentableHomEquiv ℱ U).injective
    -- The sheaf property reduces equality to the coverwise restriction equalities.
    apply section_eq_of_cover_restrictions_eq S
    intro I
    exact cover_component_eq_of_coverMap_comp_eq S h I

/-- Lemma 7.12.4: if `S : J.Cover U` is a covering, then the canonical sheafified coproduct map
attached to `S` is locally surjective. -/
theorem sheafifiedRepresentableCoverMap_isLocallySurjective
    [HasWeakSheafify J (Type (max u v))] :
    Sheaf.IsLocallySurjective (J.sheafifiedRepresentableCoverMap S) := by
  -- Follow the source proof: first identify the cover map as an epimorphism of sheaves.
  rw [Sheaf.isLocallySurjective_iff_epi]
  exact sheafifiedRepresentableCoverMap_epi S

end

end

end CategoryTheory.GrothendieckTopology
