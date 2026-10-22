/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

section

open MonoidHom

variable {X : Type u} (rels : Set (FreeGroup X))

-- Layer triage:
-- `source-facing`: the textbook subgroup `L_H ⊆ F(X) × F(X)` attached to
-- `H = PresentedGroup rels`, together with the criterion that `(u, v) ∈ L_H` exactly when `u`
-- and `v` represent the same element of `H`.
-- `core/canonical`: `PresentedGroup.mk rels` is the canonical quotient map
-- `FreeGroup X → PresentedGroup rels`, and `eqLocus` is the canonical subgroup equalizer of two
-- homomorphisms.
-- `bridge/view`: `L_H` is rendered directly by the equalizer of the two coordinate composites
-- into `PresentedGroup rels`, and membership in that equalizer is the textbook equality of the
-- two quotient images.
-- Domain sampling:
-- 1. `PresentedGroup rels` is the chapter owner for the quotient by relators `rels`.
-- 2. `PresentedGroup.mk rels` is the canonical map sending a free-group word to its class in the
--    presented group.
-- 3. `eqLocus` is mathlib's owner subgroup of elements on which two homomorphisms agree.
-- 4. `fst` and `snd` are the canonical product projections used to compare the two coordinates
--    after applying `PresentedGroup.mk rels`.
-- Primitive vs. derived:
-- the primitive source data are the relator set `rels` and the words `u`, `v`; the textbook
-- subgroup `L_H` is a derived owner-side equalizer construction, so no separate public wrapper is
-- introduced for it.

local notation "F" => FreeGroup X
local notation "q" => PresentedGroup.mk rels
local notation "LH" =>
  eqLocus (comp (PresentedGroup.mk rels) (fst F F)) (comp (PresentedGroup.mk rels) (snd F F))

/-- Lemma 4-4-3: a pair of free-group words lies in the textbook subgroup `L_H` if and only if the
two words represent the same element of `H = PresentedGroup rels`. Here the local notation `LH`
is the owner-side rendering of the textbook subgroup `L_H` by the canonical equalizer subgroup
`eqLocus (q.comp (fst F F)) (q.comp (snd F F))`. -/
theorem mem_LH_iff (u v : F) : (u, v) ∈ LH ↔ q u = q v :=
  Iff.rfl

end
