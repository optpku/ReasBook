/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {X : Type u} {F : Type v} [Group F]

/- Lemma 1-7-3 belongs to the free-group automorphism theory of basis-triangular substitutions. -/
-- Layer triage:
-- `source-facing`: a partially ordered subset `X₀` of a chosen basis `basis : FreeGroupBasis X F`
-- with descending chain condition, together with auxiliary words `p x` and `q x` whose basis
-- letters from `X₀` all lie below `x`.
-- `core/canonical`: the owner abstraction `FreeGroupBasis X F` for the chosen basis and
-- `MulAut F` for automorphisms of the ambient free group.
-- `bridge/view`: the source phrase “contains elements of `X₀` only for predecessors of `x`” is
-- expressed through `basisLetterOccurs basis y g`, i.e. by reading support in the canonical word
-- `(basis.repr g).toWord`.
-- Domain sampling:
-- 1. `FreeGroupBasis X F` is the chapter and mathlib owner abstraction for a free group with a
--    chosen basis.
-- 2. `basis.repr : F ≃* FreeGroup X` is the canonical bridge from intrinsic basis-level elements
--    to the concrete reduced-word model.
-- 3. `basisLetterOccurs` from Proposition `1-7-4` is the chapter's owner-side support predicate
--    derived from `basis.repr`, so this file reuses it directly instead of restating support via
--    the concrete model `FreeGroup.of`.
-- 4. `FreeGroupBasis.ofFreeGroup X` is the specialization recovering the standard basis of the
--    concrete model `FreeGroup X`.
-- Primitive vs. derived:
-- the primitive source data are the basis `basis`, the ordered subset `X₀`, and the words `p x`,
-- `q x`; the support condition is derived canonically via `basis.repr`, and the concrete
-- `FreeGroup X` model is only a specialization.

namespace FreeGroupBasis

/-- A word has descending support over `X₀` at `x` when every basis letter occurring in it either
lies outside `X₀` or is a strict predecessor of `x`. -/
def HasDescendingSupport (basis : FreeGroupBasis X F) (X₀ : Set X) [PartialOrder X₀]
    (x : X₀) (g : F) : Prop :=
  ∀ y : X, basisLetterOccurs basis y g → y ∈ X₀ᶜ ∪ Subtype.val '' Set.Iio x

/-- Lemma 1-7-3: if `X₀` is a partially ordered subset of a chosen basis `basis : FreeGroupBasis X F`
satisfying the descending chain condition, and for each `x : X₀` the words `p x` and `q x` only
involve basis elements from `X₀` that are strictly smaller than `x`, then there is an
automorphism of `F` sending each basis element `x ∈ X₀` to `p x * x * q x` and fixing the basis
elements outside `X₀`. Specializing `basis := FreeGroupBasis.ofFreeGroup X` recovers the standard
free-group model statement. -/
-- Proof sketch: define an endomorphism `α` by sending each basis element `x ∈ X₀` to
-- `p x * basis x * q x` and fixing basis elements outside `X₀`. Construct its inverse
-- recursively using the well-founded order on `X₀`, defining
-- `β x = (p x β)⁻¹ * basis x * (q x β)⁻¹` on `X₀` and `β y = basis y` outside `X₀`, then use the
-- free-group universal property supplied by `basis` to show `α` and `β` are inverse
-- automorphisms.
theorem exists_automorphism_mul_generator_of_descending_support
    (basis : FreeGroupBasis X F) (X₀ : Set X) [PartialOrder X₀] [WellFoundedGT X₀]
    (p q : X₀ → F)
    (hp : ∀ x : X₀, basis.HasDescendingSupport X₀ x (p x))
    (hq : ∀ x : X₀, basis.HasDescendingSupport X₀ x (q x)) :
    ∃ α : MulAut F,
      (∀ x : X₀, α (basis x) = p x * basis x * q x) ∧
        ∀ x ∈ X₀ᶜ, α (basis x) = basis x := sorry

end FreeGroupBasis

end
