/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_6_4
import Mathlib.GroupTheory.PresentedGroup

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {ι : Type u}

/- The irreducibility rank of a relator set is written `Ir(W)`, read directly through the
canonical owner invariant `groupIr (PresentedGroup W)`. -/
namespace RelatorSetIr

scoped notation "Ir(" W ")" => groupIr (PresentedGroup W)

end RelatorSetIr

open scoped RelatorSetIr

-- Layer triage:
-- `source-facing`: the irreducibility rank `Ir(W)` of a relator set `W`, and its invariance under
-- automorphisms of the ambient finite-rank free group.
-- `core/canonical`: the chapter owner `groupIr (PresentedGroup W)`, the presented-group owner
-- `PresentedGroup W`, the owner automorphism group `MulAut (FreeGroup ι)`, and set image
-- `α '' W`.
-- `bridge/view`: the induced isomorphism
-- `PresentedGroup W ≃* PresentedGroup (α '' W)` is the canonical quotient transport supplied by
-- `QuotientGroup.congr` together with `Subgroup.map_normalClosure`, while the source-facing
-- textbook notation `Ir(W)` is a thin notation for the canonical owner value
-- `groupIr (PresentedGroup W)`.
-- Domain sampling:
-- 1. `groupIr` from Proposition `1-6-4` is the chapter owner abstraction for irreducibility rank.
-- 2. `PresentedGroup W` is the canonical owner object attached to a relator set `W`.
-- 3. `QuotientGroup.congr` is the canonical quotient-level transport induced by an ambient
--    automorphism preserving the distinguished normal subgroup.
-- 4. `Subgroup.map_normalClosure` is the canonical proof that the transported normal closure is
--    exactly the normal closure of the image relator set.
-- Primitive vs. derived:
-- the primitive source data are only the relator set `W`; the presented group, its
-- irreducibility invariant in `ℕ∞`, the transformed relator family `α '' W`, and the induced
-- presented-group isomorphism are all derived canonically from that data.

section

/-- Proposition 1-6-13: if `W'` is the image of a relator set `W` under an automorphism of the
ambient free group, then `Ir(W') = Ir(W)`. -/
-- Proof sketch: use the canonical quotient transport induced by `α` together with
-- `Subgroup.map_normalClosure`, then apply `groupIr_eq_of_equiv`.
theorem ir_image_eq (W : Set (FreeGroup ι)) (α : MulAut (FreeGroup ι)) :
    Ir(α '' W) = Ir(W) := by
  simpa using
    (groupIr_eq_of_equiv
      (QuotientGroup.congr (Subgroup.normalClosure W) (Subgroup.normalClosure (α '' W)) α
        (Subgroup.map_normalClosure W α.toMonoidHom α.surjective))).symm

end
