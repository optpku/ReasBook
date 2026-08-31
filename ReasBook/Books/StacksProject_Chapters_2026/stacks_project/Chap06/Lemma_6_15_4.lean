module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.Topology.Sheaves.Functors
public import stacks_project.Chap06.Definition_6_15_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.Types

universe w v u

/-
Domain-style sampling for Lemma 6.15.4:
- primary domain: factorization of morphisms in a type of algebraic structure through a mono,
  detected on underlying sets via pullbacks;
- inspected owner declarations:
  `Subobject.Factors`,
  `Subobject.factorThru`,
  `CategoryTheory.mono_iff_injective`,
  `PreservesPullback.iso_hom_fst`;
- best owner abstraction:
  the canonical factorization owner is `Subobject.Factors`, while the textbook existential
  factorization through `g` is the source-facing statement obtained from that owner by passing to
  the underlying object of `Subobject.mk g`;
- primitive data:
  the morphisms `f`, `g`, the mono structure on `g` or equivalently the injectivity of `F.map g`,
  the range inclusion `Set.range (F.map f) ⊆ Set.range (F.map g)`, and the ambient functor
  hypotheses actually used by the proof: `F.Faithful`, pullbacks in `𝒞`, preservation of
  pullbacks by `F`, and `F.ReflectsIsomorphisms`;
- derived API:
  the witness morphism from `Subobject.factorThru` and the comparison isomorphism
  `Subobject.underlyingIso g`.

Source/core/bridge triage:
- `source-facing`: `morphism_factors_through_of_range_subset_of_injective`;
- `core/canonical`: `Subobject.Factors`;
- `bridge/view`: `subobject_factors_of_range_subset`, which packages the source factorization in the
  canonical subobject owner.
-/

section

variable {𝒞 : Type u} [Category.{v} 𝒞] (F : 𝒞 ⥤ Type w)
  [HasLimitsOfShape WalkingCospan 𝒞] [PreservesLimitsOfShape WalkingCospan F]
  [F.ReflectsIsomorphisms]

-- Proof sketch: form the pullback `A ×_B C` of `f` and `g`. The injectivity of `F.map g` and the
-- range inclusion `range (F.map f) ⊆ range (F.map g)` make the set-theoretic pullback projection
-- to `F.obj A` bijective. Via the pullback comparison isomorphism for `F`, this shows that
-- `pullback.fst f g` becomes an isomorphism under `F`; since `F` reflects isomorphisms, it is
-- already an isomorphism in `𝒞`. The desired factorization is then the canonical morphism through
-- the subobject `Subobject.mk g`.
theorem subobject_factors_of_range_subset
    {A B C : 𝒞} (f : A ⟶ B) (g : C ⟶ B) [Mono g]
    (hfg : Set.range (F.map f) ⊆ Set.range (F.map g)) :
    (Subobject.mk g).Factors f := by
  have hg_injective : Function.Injective (F.map g) :=
    (mono_iff_injective _).1 inferInstance
  have hfst_bijective : Function.Bijective (pullback.fst (F.map f) (F.map g)) := by
    have hcond :
        pullback.fst (F.map f) (F.map g) ≫ F.map f =
          pullback.snd (F.map f) (F.map g) ≫ F.map g :=
      pullback.condition
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply ext_of_isPullback (IsPullback.of_hasPullback (F.map f) (F.map g)) hxy
      apply hg_injective
      calc
        F.map g (pullback.snd (F.map f) (F.map g) x)
            = F.map f (pullback.fst (F.map f) (F.map g) x) := by
                simpa using congr_fun hcond.symm x
        _ = F.map f (pullback.fst (F.map f) (F.map g) y) := by simp [hxy]
        _ = F.map g (pullback.snd (F.map f) (F.map g) y) := by
              simpa using congr_fun hcond y
    · intro a
      rcases hfg ⟨a, rfl⟩ with ⟨c, hc⟩
      rcases exists_of_isPullback (IsPullback.of_hasPullback (F.map f) (F.map g)) a c hc.symm with
        ⟨x, rfl, _⟩
      exact ⟨x, rfl⟩
  let hshape : HasLimitsOfShape WalkingCospan 𝒞 := inferInstance
  let hpres : PreservesLimitsOfShape WalkingCospan F := inferInstance
  letI : HasLimit (cospan f g) := hshape.has_limit (cospan f g)
  letI : PreservesLimit (cospan f g) F := hpres.preservesLimit
  have hcomparison_bijective :
      Function.Bijective ((PreservesPullback.iso F f g).hom ≫ pullback.fst (F.map f) (F.map g)) :=
    hfst_bijective.comp <| (isIso_iff_bijective _).1 inferInstance
  have hmap_fst_bijective : Function.Bijective (F.map (pullback.fst f g)) := by
    simpa [PreservesPullback.iso_hom_fst] using hcomparison_bijective
  haveI : IsIso (F.map (pullback.fst f g)) := (isIso_iff_bijective _).2 hmap_fst_bijective
  haveI : IsIso (pullback.fst f g) := by
    exact isIso_of_reflects_iso (pullback.fst f g) F
  refine (Subobject.mk_factors_iff g f).2 ?_
  refine ⟨inv (pullback.fst f g) ≫ pullback.snd f g, ?_⟩
  calc
    (inv (pullback.fst f g) ≫ pullback.snd f g) ≫ g
        = inv (pullback.fst f g) ≫ (pullback.snd f g ≫ g) := by simp [Category.assoc]
    _ = inv (pullback.fst f g) ≫ (pullback.fst f g ≫ f) := by rw [← pullback.condition]
    _ = f := by simp

/-- Lemma 6.15.4: under the faithful, pullback-preserving, and isomorphism-reflecting hypotheses
satisfied by a type of algebraic structure, if the underlying function of `g` is injective and the
image of the underlying function of `f` is contained in the image of the underlying function of
`g`, then `f` factors through `g`. -/
theorem morphism_factors_through_of_range_subset_of_injective
    {A B C : 𝒞} (f : A ⟶ B) (g : C ⟶ B)
    [F.Faithful]
    (hg_injective : Function.Injective (F.map g))
    (hfg : Set.range (F.map f) ⊆ Set.range (F.map g)) :
    ∃ t : A ⟶ C, f = t ≫ g := by
  have hmap_mono : Mono (F.map g) := (mono_iff_injective _).2 hg_injective
  letI : F.ReflectsMonomorphisms := Functor.reflectsMonomorphisms_of_faithful F
  letI : Mono g := F.mono_of_mono_map hmap_mono
  have hfactor : (Subobject.mk g).Factors f := subobject_factors_of_range_subset F f g hfg
  refine ⟨(Subobject.mk g).factorThru f hfactor ≫ (Subobject.underlyingIso g).hom, ?_⟩
  rw [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
  exact (Subobject.factorThru_arrow (Subobject.mk g) f hfactor).symm

end
