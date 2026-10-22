/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.Algebra.Group.ULift
import Mathlib.GroupTheory.CoprodI

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

set_option autoImplicit false

open Monoid.CoprodI

namespace Monoid.CoprodI

/- The canonical `Bool`-indexed two-factor bridge for reduced words. This mirrors the
`fun b ↦ cond b M N` family behind `Monoid.Coprod`, with the necessary `ULift`s to place the two
factors in a common universe and with `false` indexing the left factor. This bridge is reused
later for free products with amalgamation, so it belongs at the chapter's first reduced-word item
rather than as a repeated local helper. Since `Word` is a monoid-level notion, the bridge also
lives at the monoid level and later group-specific files specialize it. -/
abbrev twoFactorFamily (A : Type u) (B : Type v) : Bool → Type (max u v) :=
  fun b ↦ cond b (ULift.{max u v} B) (ULift.{max u v} A)

instance (priority := 50) twoFactorFamilyMonoid
    (A : Type u) (B : Type v) [Monoid A] [Monoid B] (b : Bool) :
    Monoid (twoFactorFamily A B b) := by
  cases b <;> dsimp [twoFactorFamily] <;> infer_instance

instance twoFactorFamilyGroup
    (A : Type u) (B : Type v) [Group A] [Group B] (b : Bool) :
    Group (twoFactorFamily A B b) := by
  cases b with
  | false =>
      dsimp [twoFactorFamily]
      let inst : Group (ULift.{max u v} A) := inferInstance
      exact { inst with toMonoid := twoFactorFamilyMonoid A B false }
  | true =>
      dsimp [twoFactorFamily]
      let inst : Group (ULift.{max u v} B) := inferInstance
      exact { inst with toMonoid := twoFactorFamilyMonoid A B true }

end Monoid.CoprodI

section

variable (A : Type u) (B : Type v) [Monoid A] [Monoid B]

-- Primary domain: reduced words for free products of monoids, later specialized to groups.
-- Layer triage:
-- `source-facing`: the textbook notion of a reduced normal form in the free product of two
-- factors `A` and `B`.
-- `core/canonical`: `Monoid.Coprod` is mathlib's two-factor free-product owner, and `Word` in
-- `Monoid.CoprodI` is mathlib's owner abstraction for reduced words in an indexed free product.
-- `bridge/view`: `Monoid.CoprodI.twoFactorFamily A B` is the chapter's shared `Bool`/`ULift`
-- specialization used to view the two-factor case through the indexed owner.
-- No separate public two-factor reduced-word owner is introduced.
-- Domain sampling:
-- 1. `Monoid.Coprod` is mathlib's canonical two-factor free product, implemented via a
--    `Bool`-indexed family of factor types behind the scenes.
-- 2. `Monoid.CoprodI.twoFactorFamily` is the chapter's minimal same-kind bridge from two factors
--    to the
--    indexed free-product word owner.
-- 3. `Word` is the canonical reduced-word owner for indexed free products.
-- 4. `Word.empty`, `Word.prod`, and `Word.equiv` are the canonical empty-word, evaluation, and
--    normal-form API.
-- Primitive vs. derived:
-- the primitive data remain the reduced list of nontrivial letters with adjacent-factor
-- inequality; the empty word, evaluation map, and normal-form equivalence are derived API from the
-- owner abstraction. The shared two-factor specialization is exposed only as the minimal bridge
-- needed to reuse that owner abstraction in later chapter files.

/- Definition 4-1-4: a reduced sequence (normal form) for the free product of `A` and `B` is
mathlib's canonical reduced-word object specialized to the two-factor free product.

This item keeps `Monoid.CoprodI.Word` as the public owner of reduced words. The only extra chapter
API introduced here is the reusable bridge `Monoid.CoprodI.twoFactorFamily`, which specializes the
indexed owner to the two-factor case without creating a second reduced-word wrapper. -/
#check (Word (twoFactorFamily A B))

end
