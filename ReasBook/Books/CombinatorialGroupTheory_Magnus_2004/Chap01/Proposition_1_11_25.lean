/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_2_1
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_2_3
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_9_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

open Monoid
open Monoid.CoprodI
open scoped Symmetrization

namespace Monoid.CoprodI

section

variable {ι : Type u} {factors : ι → Type v} [∀ i, Group (factors i)]

/-- An element of a free product is conjugate into a free factor if it is conjugate to some image
`of x` of one of the factors. -/
def IsConjugateIntoFactor (g : CoprodI factors) : Prop :=
  ∃ i, ∃ x : factors i, IsConj g (of x)

/-- Internal product of the contiguous block of entries of `w` from position `h` through position
`k`. The public API only uses it under the accompanying in-range hypotheses. -/
private def contiguousSubproduct {G : Type*} [Monoid G] (w : List G) (h k : ℕ) : G :=
  ((w.drop h).take (k + 1 - h)).prod

/-- Two finite subsets of a free product are related by a Nielsen transformation if some genuine
finite enumerations of them are related by the Chapter I owner relation `nielsen_transforms_to`.
The list/finite-set bridge is internal: the primitive public data are the finite subsets
themselves, not nodup witness lists. -/
def NielsenTransformsTo (X Y : Finset (CoprodI factors)) : Prop :=
  letI : DecidableEq (CoprodI factors) := Classical.decEq _
  ∃ U V : List (CoprodI factors),
    U.Nodup ∧
      V.Nodup ∧
      U.toFinset = X ∧
      V.toFinset = Y ∧
      nielsen_transforms_to U V

/-- A subset of a free product satisfies the length dichotomy of Proposition `1-11-25` if every
noncancelling product of letters from `Y^{±1}` either has total syllable length dominating each
factor, or contains a contiguous block of letters conjugate into the free factors whose product is
shorter than one of its letters. For `w = []`, the first alternative is vacuous. -/
class HasNielsenLengthDichotomy (Y : Set (CoprodI factors)) : Prop where
  dichotomy :
    ∀ (w : List (CoprodI factors)) (_ : ∀ g ∈ w, g ∈ Y^{±1})
      (_ : w.IsChain (fun a b ↦ a * b ≠ 1)),
      (∀ i : Fin w.length, syllableLength (w.get i) ≤ syllableLength w.prod) ∨
        ∃ h k : ℕ,
          h ≤ k ∧
            k < w.length ∧
            (∀ j : Fin w.length,
              h ≤ j.1 → j.1 ≤ k → IsConjugateIntoFactor (w.get j)) ∧
            ∃ i : Fin w.length,
              h ≤ i.1 ∧
                i.1 ≤ k ∧
                syllableLength (contiguousSubproduct w h k) < syllableLength (w.get i)

/-- Proposition 1-11-25: every finite subset of the indexed free product can be carried by a
Nielsen transformation to a finite subset satisfying the free-product length dichotomy from the
text. -/
-- Layer triage:
-- `source-facing`: a finite subset `X` of the free product and a Nielsen-equivalent finite subset
-- `Y` whose underlying subset satisfies the stated length alternative for noncancelling words in
-- `Y^{±1}`.
-- `core/canonical`: `Monoid.CoprodI` for the ambient free product, `Word.equiv`
-- for canonical reduced words, and `IsConj` for conjugacy.
-- `bridge/view`: `syllableLength`, `IsConjugateIntoFactor`, and the finite-set Nielsen relation
-- `NielsenTransformsTo`, which bridges the finite source data to the owner predicate
-- `HasNielsenLengthDichotomy` on subsets.
-- Domain sampling:
-- 1. `Monoid.CoprodI` is mathlib's owner abstraction for indexed free products.
-- 2. `Monoid.CoprodI.syllableLength` is the chapter owner for the canonical syllable length,
--    derived from the unique reduced-word normal form `Word.equiv`.
-- 3. `nielsen_transforms_to` from Definition `1-2-1` is the chapter owner abstraction for finite
--    Nielsen transformations on lists, while Proposition `1-2-23` and Definition `1-2-3` show
--    the chapter owner pattern: a reusable Nielsen property lives on `Set`, and finite lists or
--    finite sets only provide bridge data to that owner.
-- 4. `IsConj` is the canonical conjugacy relation, so conjugacy into a factor is stated directly
--    without adding a surrogate wrapper structure.
-- Primitive vs. derived:
-- the primitive owner data are only the subset `Y` and the dichotomy property on words in
-- `Y^{±1}`. The finite Nielsen relation on `X` and `Y` is the source-facing bridge witnessing
-- that the finite input can be carried to such a subset, and the contiguous-block product is only
-- a private implementation helper for the displayed in-range conclusion.
-- Proof sketch: choose a finite enumeration of `X`, run the Nielsen-reduction process for free
-- products from the textbook until all forbidden counterexamples to the displayed alternative have
-- been removed, and let `Y` be the resulting finite subset.
theorem exists_nielsen_image_with_length_dichotomy
    (X : Finset (CoprodI factors)) :
    ∃ Y : Finset (CoprodI factors),
      NielsenTransformsTo X Y ∧
        HasNielsenLengthDichotomy (Y : Set (CoprodI factors)) := sorry

end

end Monoid.CoprodI
