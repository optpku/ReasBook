module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Stalks


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopCat.Presheaf TopCat.Sheaf

universe u

section

variable {X : TopCat.{u}} {ℱ 𝒢 : X.Sheaf (Type u)}
variable (φ : ℱ ⟶ 𝒢)

/- Layering for Lemma 6.16.1:
- primary domain: morphisms of sheaves of sets on a topological space and their induced stalk maps;
- sampled owner declarations:
  `TopCat.Presheaf.mono_iff_stalk_mono`,
  `TopCat.Sheaf.isLocallySurjective_iff_epi`,
  `TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks`,
  `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`;
- core/canonical owners: `Mono φ`, `Epi φ`, `IsIso φ`, and the stalk functor `stalkFunctor`;
- primitive data: only the sheaf morphism `φ`;
- derived API here: the source-facing set-theoretic reformulations of the canonical stalkwise
  mono/epi/iso criteria as injective, surjective, and bijective stalk maps.
-/

/-- Helper for Lemma 6.16.1: a map on a `Type`-valued stalk is a monomorphism exactly when it is
injective as a function. -/
lemma stalk_map_mono_iff_injective (x : X) :
    Mono ((stalkFunctor (Type u) x).map φ.hom) ↔
      Function.Injective ((stalkFunctor (Type u) x).map φ.hom) := by
  -- Reduce the categorical mono condition in `Type` to ordinary injectivity.
  simp [CategoryTheory.mono_iff_injective]

/-- Lemma 6.16.1 (1): a morphism of sheaves of sets on `X` is a monomorphism if and only if each
stalk map `φ_x : ℱ_x → 𝒢_x` is injective. -/
-- Proof sketch: specialize `TopCat.Presheaf.mono_iff_stalk_mono` to `Type` and rewrite stalkwise
-- monomorphisms using `CategoryTheory.mono_iff_injective`.
theorem sheaf_mono_iff_stalk_injective :
    Mono φ ↔ ∀ x : X, Function.Injective ((stalkFunctor (Type u) x).map φ.hom) := by
  constructor
  · intro hφ x
    -- Pass from stalkwise monomorphisms to injective stalk maps one point at a time.
    exact (stalk_map_mono_iff_injective (φ := φ) x).1 ((mono_iff_stalk_mono φ).1 hφ x)
  · intro hφ
    -- Reassemble the categorical mono statement from the pointwise injective stalk maps.
    exact (mono_iff_stalk_mono φ).2 fun x ↦ (stalk_map_mono_iff_injective (φ := φ) x).2 (hφ x)

/-- Lemma 6.16.1 (2): a morphism of sheaves of sets on `X` is an epimorphism if and only if each
stalk map `φ_x : ℱ_x → 𝒢_x` is surjective. -/
-- Proof sketch: combine `TopCat.Sheaf.isLocallySurjective_iff_epi` with
-- `TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks`.
theorem sheaf_epi_iff_stalk_surjective :
    Epi φ ↔ ∀ x : X, Function.Surjective ((stalkFunctor (Type u) x).map φ.hom) := by
  rw [← isLocallySurjective_iff_epi φ]
  simpa using locally_surjective_iff_surjective_on_stalks φ.hom

/-- Lemma 6.16.1 (3): a morphism of sheaves of sets on `X` is an isomorphism if and only if each
stalk map `φ_x : ℱ_x → 𝒢_x` is bijective. -/
-- Proof sketch: specialize `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso` to `Type` and
-- rewrite stalkwise isomorphisms using `CategoryTheory.isIso_iff_bijective`.
theorem sheaf_isIso_iff_stalk_bijective :
    IsIso φ ↔ ∀ x : X, Function.Bijective ((stalkFunctor (Type u) x).map φ.hom) := by
  simpa [CategoryTheory.isIso_iff_bijective] using
    isIso_iff_stalkFunctor_map_iso φ

end
