/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace GroupPresentation

section

variable {X : Type u} [Primcodable X]
variable (r : FreeGroup X)

-- Layer triage:
-- `source-facing`: a one-relator group `G = (X; r)` together with the decision problem of whether
-- a signed word on `X` represents an element of the center of `G`.
-- `core/canonical`: the owner quotient `PresentedGroup ({r} : Set (FreeGroup X))`, its center
-- `Subgroup.center (PresentedGroup ({r} : Set (FreeGroup X)))`, and the computability predicate
-- `ComputablePred` on signed words.
-- `bridge/view`: a signed word `L : List (X × Bool)` represents a central element exactly when
-- its image under the canonical quotient map `PresentedGroup.mk ({r} : Set (FreeGroup X))` lies
-- in `Subgroup.center (PresentedGroup ({r} : Set (FreeGroup X)))`.
-- Domain sampling:
-- 1. `PresentedGroup ({r} : Set (FreeGroup X))` is the canonical one-relator quotient attached to
--    the relator `r`.
-- 2. `Subgroup.center (PresentedGroup ({r} : Set (FreeGroup X)))` is mathlib's canonical owner of
--    the center of that quotient group.
-- 3. `FreeGroup.mk` is the canonical evaluation of a finite signed word in the free group.
-- 4. `ComputablePred` is the project's canonical interface for algorithmic decidability on coded
--    words.
-- Primitive vs. derived:
-- the primitive data are only the generator type `X` and the relator `r`; the center is a
-- derived canonical subgroup of the presented group, so the public statement is the computability
-- of center-membership for represented words rather than a new wrapper around one-relator groups.

-- Proof sketch: use the classical algorithm describing centralizers in one-relator groups. For a
-- signed word `L`, first pass to its image under
-- `PresentedGroup.mk ({r} : Set (FreeGroup X))` in the canonical one-relator quotient; then apply
-- the effective classification of centralizers in one-relator groups to decide whether that image
-- commutes with every generator, equivalently whether it lies in the center.
/-- Proposition 2-5-22: there is an algorithm deciding whether a signed word on the generators of a
one-relator group represents an element of the center of that group. -/
theorem computable_represents_central_element_singleton_relator :
    ComputablePred fun L : List (X × Bool) ↦
      PresentedGroup.mk ({r} : Set (FreeGroup X)) (FreeGroup.mk L) ∈
        Subgroup.center (PresentedGroup ({r} : Set (FreeGroup X))) := sorry

end

end GroupPresentation
