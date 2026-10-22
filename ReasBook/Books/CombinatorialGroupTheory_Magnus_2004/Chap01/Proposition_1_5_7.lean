/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_5_6
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open MulAction

section

variable {X : Type u} {F : Type u} [Group F]

namespace FreeGroupBasis

local instance instDecidableEqBasisSupport_157 : DecidableEq X := Classical.decEq X

/-- Owner-level formulation of Proposition 1-5-7: if an element `g` of a free group has minimal
reduced length among its automorphic images with respect to the chosen basis `basis`, and every
basis generator occurs in the canonical reduced word of `g`, then the stabilizer of `g` in
`Aut(F)` is torsion-free. -/
-- Layer triage:
-- `source-facing`: the proposition concerns a word whose reduced length is minimal in its
-- automorphic orbit and whose support contains every basis generator.
-- `core/canonical`: the ambient owner objects are `FreeGroupBasis X F`, the canonical reduced word
-- `(basis.repr g).toWord` of the represented element `g : F`, and the stabilizer subgroup
-- `stabilizer (MulAut F) g`.
-- `bridge/view`: `basisLetterOccurs basis x g` is the chapter owner-side occurrence predicate for
-- basis generators in the canonical reduced word of `g`, and a reduced ordinary word
-- `w : List (X × Bool)` gives the source presentation of the same element via
-- `basis.repr.symm (FreeGroup.mk w)`.
-- Domain sampling:
-- 1. `FreeGroupBasis X F` is the chapter and mathlib owner abstraction for a chosen basis of `F`.
-- 2. `basisLetterOccurs basis x g` from Proposition `1-7-4` is the chapter owner-side predicate
--    expressing that the basis generator `x` occurs in the canonical reduced word of `g`.
-- 3. `stabilizer (MulAut F) g` is the canonical owner subgroup for automorphisms fixing `g`.
-- 4. `FreeGroup.mk` and `FreeGroup.toWord` already read a raw list word through the canonical
--    reduced-word normal form, so ordinary-word occurrence and length conditions belong in the
--    bridge layer only through `FreeGroup.mk w`, not through an extra reducedness field.
-- Primitive vs. derived:
-- the primitive data are the basis `basis` and the group element `g`; the reduced word used to
-- read occurrence is derived canonically from `basis.repr g`, while any concrete list `w`
-- representing `g` belongs only to the bridge layer.
-- Proof sketch: let `α` be a finite-order element of the stabilizer. By Proposition 1-5-5, its
-- fixed subgroup is a free factor of `F`, and it contains `g` because `α` stabilizes `g`. The
-- minimal-length and full-support hypotheses imply, by the preceding proposition, that `g` lies in
-- no proper free factor. Hence the fixed subgroup is all of `F`, so `α = 1`.
theorem stabilizer_isMulTorsionFree_of_minimal_length_and_full_support
    (basis : FreeGroupBasis X F) (g : F)
    (hmin : ∀ α : MulAut F,
      (basis.repr g).toWord.length ≤ (basis.repr (α g)).toWord.length)
    (hcontains : ∀ x : X, basisLetterOccurs basis x g) :
    IsMulTorsionFree (stabilizer (MulAut F) g) := by
  sorry

/-- Source-facing ordinary-word bridge for Proposition 1-5-7: if the canonical reduced form of an
ordinary word `w` has minimal reduced length among its automorphic images and contains every basis
generator, then the stabilizer of the represented element is torsion-free. The hypotheses are read
directly on `FreeGroup.mk w`, so they already refer to the canonical normal form of the element
represented by `w`. -/
theorem ordinaryWord_stabilizer_isMulTorsionFree_of_minimal_length_and_full_support
    (basis : FreeGroupBasis X F) (w : List (X × Bool))
    (hmin : ∀ α : MulAut F,
      (FreeGroup.mk w).toWord.length ≤
        (basis.repr (α (basis.repr.symm (FreeGroup.mk w)))).toWord.length)
    (hcontains : ∀ x : X, basisLetterOccurs basis x (basis.repr.symm (FreeGroup.mk w))) :
    IsMulTorsionFree (stabilizer (MulAut F) (basis.repr.symm (FreeGroup.mk w))) := by
  refine
    stabilizer_isMulTorsionFree_of_minimal_length_and_full_support
      basis (basis.repr.symm (FreeGroup.mk w)) ?_ hcontains
  intro α
  simpa using hmin α

end FreeGroupBasis

end
