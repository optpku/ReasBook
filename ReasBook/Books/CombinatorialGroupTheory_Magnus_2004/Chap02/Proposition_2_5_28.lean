/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

section

variable {X : Type u} {F : Type v} [Group F]

local instance proposition_2_5_28_decidableEq : DecidableEq X := Classical.decEq X

open Subgroup (normalClosure)

namespace FreeGroupBasis

-- Layer triage:
-- `source-facing`: a chosen free basis `basis : FreeGroupBasis X F`, a cyclically reduced relator
-- `r : F`, and an element `s : F` whose canonical reduced word is a nonempty proper consecutive
-- subword of the reduced word of `r`.
-- `core/canonical`: the owner namespace `FreeGroupBasis`, together with
-- `FreeGroup.IsCyclicallyReduced`, `Subgroup.normalClosure`, the reduced-word map
-- `FreeGroup.toWord`, and `List.IsInfix`.
-- `bridge/view`: the textbook phrase “proper subword of `r`” is read directly through the owner
-- reduced-word map `(basis.repr ·).toWord`, so no parallel wrapper around reduced words or normal
-- closures is introduced.
--
-- Domain sampling:
-- 1. `FreeGroupBasis X F` is the canonical owner abstraction for a chosen basis of a free group,
--    and nearby Chapter II Magnus theorems with basis data already live in
--    `namespace FreeGroupBasis`.
-- 2. `FreeGroup.IsCyclicallyReduced` is the owner predicate for cyclically reduced reduced words.
-- 3. `Subgroup.normalClosure` is the canonical owner for the normal closure of a relator.
-- 4. `FreeGroup.toWord` is the owner reduced-word API on the canonical free-group model.
-- 5. `List.IsInfix` from mathlib is the canonical consecutive-subword predicate on reduced words.
--
-- Primitive vs. derived:
-- the primitive public data are the basis `basis`, the relator `r`, the candidate subword list
-- `part`, and the corresponding free-group element `s`; “proper subword of `r`” is expressed
-- directly through the owner reduced-word equality `(basis.repr s).toWord = part`,
-- `List.IsInfix`, and the strict length inequality, so no extra wrapper predicate is kept.

/-- Proposition 2-5-28: if `r` is cyclically reduced with respect to the chosen basis
`basis : FreeGroupBasis X F`, then any proper subword of `r` lying in its singleton normal
closure is trivial. -/
-- Proof sketch: transport the statement through `basis.repr : F ≃* FreeGroup X` to the canonical
-- free-group model on `X`. There, Magnus's subword theorem rules out every nonempty proper
-- consecutive subword of a cyclically reduced relator from lying in the normal closure of the
-- whole relator. Hence any such element in the normal closure must equal `1`.
theorem eq_one_of_mem_normalClosure_singleton_of_hasPart_of_isCyclicallyReduced
    (basis : FreeGroupBasis X F) {r s : F} {part : List (X × Bool)}
    (hr : FreeGroup.IsCyclicallyReduced (basis.repr r).toWord)
    (hs_word : (basis.repr s).toWord = part)
    (hpart : part <:+: (basis.repr r).toWord)
    (hpart_ne : part ≠ [])
    (hproper : part.length < (basis.repr r).toWord.length)
    (hs : s ∈ normalClosure ({r} : Set F)) :
    s = 1 := sorry

end FreeGroupBasis

end
