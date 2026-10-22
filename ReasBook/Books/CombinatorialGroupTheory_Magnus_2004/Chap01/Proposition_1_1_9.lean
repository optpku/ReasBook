/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_1_1

universe u

open scoped Cardinal

-- Layer triage:
-- `source-facing`: the image in `FreeGroup X` of the canonical generators `FreeGroup.of x`.
-- `core/canonical`: the owner basis `FreeGroupBasis.ofFreeGroup X`.
-- `bridge/view`: `FreeGroupBasis.reindexRange`, which reindexes that owner basis by its image
-- subset in the ambient group.
--
-- Domain sampling:
-- 1. `FreeGroupBasis.ofFreeGroup X` is the canonical owner basis on `FreeGroup X`.
-- 2. `FreeGroupBasis.reindexRange` is the chapter owner bridge from a basis to its image subset.
-- 3. `FreeGroupBasis.reindexRange_apply` is the companion pointwise lemma for that bridge.
--
-- Primitive vs. derived:
-- the only primitive data here are the canonical basis `FreeGroupBasis.ofFreeGroup X` and its
-- generator map `FreeGroup.of`. The basis indexed by the generator-image subset is derived
-- canonically by `reindexRange`, so this file does not introduce a parallel owner declaration.

variable (X : Type u)

/- Proposition 1-1-9: the canonical free group on `X` has the basis on the textbook
generator-image subset `Set.range (FreeGroup.of : X → FreeGroup X)`, obtained by reindexing the
standard basis `FreeGroupBasis.ofFreeGroup X` along its range. -/
#check
  (show FreeGroupBasis (Set.range (FreeGroup.of : X → FreeGroup X)) (FreeGroup X) from
    (FreeGroupBasis.ofFreeGroup X).reindexRange)

/-- The generator image subset in the free group on `X` has the same cardinality as `X`. -/
-- Proof sketch: apply `Cardinal.mk_range_eq` to the injective map `FreeGroup.of : X → FreeGroup X`.
theorem free_group_generator_image_cardinal_eq :
    #(Set.range (FreeGroup.of : X → FreeGroup X)) = #X := by
  simpa using Cardinal.mk_range_eq (FreeGroup.of : X → FreeGroup X) FreeGroup.of_injective
