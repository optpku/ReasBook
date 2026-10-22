/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

universe u v

-- Declarations for this item will be appended below by the statement pipeline.

variable {F : Type u} [Group F] {X : Set F}

-- Layer triage:
-- `source-facing`: the textbook subset-style universal property for a basis of a free group.
-- `core/canonical`: `FreeGroupBasis X F` is the owner abstraction for a free group with chosen
-- basis indexed by `X`.
-- `bridge/view`: the inclusion `Subtype.val : X → F` identifies the source subset with that owner
-- basis data.
--
-- Domain sampling:
-- 1. `FreeGroupBasis.ofUniqueLift` is the canonical owner constructor from a unique-extension
--    universal property.
-- 2. `FreeGroupBasis.isFreeGroup` is the canonical owner theorem that a chosen basis makes the
--    ambient group free.
-- 3. `FreeGroupBasis.lift` and `FreeGroupBasis.ext_hom` are the owner APIs behind the reverse
--    bridge from a chosen basis to the textbook subset property.
--
-- Primitive vs. derived:
-- the primitive source data are only the subset `X` and its unique-extension universal property.
-- The chosen owner-side basis and the ambient `IsFreeGroup F` instance are derived from that
-- source-facing predicate.

/-- Definition 1-1-1: A subset `X` of a group `F` is a basis of a free group structure on `F`
when every function from `X` to any group extends uniquely to a homomorphism from `F`. -/
def IsFreeGroupBasis (X : Set F) : Prop :=
  ∀ {H : Type u} [Group H] (φ : X → H), ∃! φStar : F →* H, ∀ x : X, φStar x.1 = φ x

/-- A subset satisfying the textbook universal property makes the ambient group free. -/
-- Proof sketch: Apply `IsFreeGroup.ofUniqueLift` to the inclusion `Subtype.val : X → F`, and use
-- the canonical owner bridge `FreeGroupBasis.ofUniqueLift`; then use
-- `FreeGroupBasis.isFreeGroup`.
theorem IsFreeGroupBasis.isFreeGroup (hX : IsFreeGroupBasis X) : IsFreeGroup F :=
  (FreeGroupBasis.ofUniqueLift X Subtype.val hX).isFreeGroup

namespace FreeGroupBasis

/-- Reindex a free group basis by its image subset in the ambient group. -/
protected noncomputable def reindexRange {ι : Type v} (b : FreeGroupBasis ι F) :
    FreeGroupBasis (Set.range b) F :=
  b.reindex (Equiv.ofInjective b b.injective)

@[simp] theorem reindexRange_apply {ι : Type v} (b : FreeGroupBasis ι F) (x : Set.range b) :
    b.reindexRange x = x.1 := by
  simpa [FreeGroupBasis.reindexRange] using Equiv.apply_ofInjective_symm b.injective x

/-- A `FreeGroupBasis` indexed by the subtype `X` gives the source-style basis property when its
underlying map is the inclusion of `X` into `F`. -/
-- Proof sketch: Use the equivalence `b.lift` to obtain the extending homomorphism, then use the
-- hypothesis `hb` to identify the basis elements with the corresponding elements of the subset `X`
-- and conclude uniqueness from the inverse direction of `b.lift`.
theorem isFreeGroupBasis (b : FreeGroupBasis X F) (hb : ∀ x : X, b x = x.1) :
    IsFreeGroupBasis X :=
  fun {H} _ φ ↦ by
    refine ⟨b.lift φ, ?_, ?_⟩
    · intro x
      have hbx : (b.lift φ) (b x) = φ x := congr_fun (b.lift.symm_apply_apply φ) x
      simpa [hb x] using hbx
    · intro ψ hψ
      apply b.ext_hom
      intro x
      have hbx : (b.lift φ) (b x) = φ x := congr_fun (b.lift.symm_apply_apply φ) x
      calc
        ψ (b x) = ψ x.1 := by rw [hb x]
        _ = φ x := hψ x
        _ = (b.lift φ) (b x) := hbx.symm

/-- Any chosen free basis yields the source-style basis predicate on its image subset. -/
theorem isFreeGroupBasis_range {ι : Type v} (b : FreeGroupBasis ι F) :
    IsFreeGroupBasis (Set.range b) :=
  FreeGroupBasis.isFreeGroupBasis b.reindexRange b.reindexRange_apply

end FreeGroupBasis
