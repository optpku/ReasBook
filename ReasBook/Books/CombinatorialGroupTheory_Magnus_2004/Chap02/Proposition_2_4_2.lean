/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap02.Proposition_2_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {G : Type u} [Group G] (H : Subgroup G)

-- Primary domain: finite-index subgroups of finitely presented groups, expressed through the
-- canonical owner predicate `Group.IsFinitelyPresented`.
-- Layer triage:
-- `source-facing`: a finite-index subgroup `H` of a group `G`, together with the inheritance of
-- finite generation and finite presentability from `G` to `H`.
-- `core/canonical`: `H.FiniteIndex` and `Group.IsFinitelyPresented H`.
-- `bridge/view`: clause (1) is exactly mathlib's Schreier instance
-- `Subgroup.fg_of_index_ne_zero`; clause (2) passes through the chapter-owner
-- Reidemeister-Schreier presentation theorem from Proposition `2-4-1` and the owner theorem
-- `GroupPresentation.isFinitelyPresented_presentedGroup` for finite presentations, then
-- transports along the resulting equivalence via `Group.IsFinitelyPresented.equiv`.
-- Domain sampling:
-- 1. `Subgroup.fg_of_index_ne_zero` is mathlib's canonical Schreier theorem for finite
--    generation of finite-index subgroups.
-- 2. Proposition `2-4-1` is the chapter owner theorem producing the subgroup presentation from
--    a Schreier transversal.
-- 3. `GroupPresentation.isFinitelyPresented_presentedGroup` is the chapter owner bridge from a
--    finite presentation to `Group.IsFinitelyPresented`.
-- 4. `Group.IsFinitelyPresented.equiv` transports finite presentability across multiplicative
--    equivalences.
-- Primitive vs. derived:
-- the primitive source data are only `G`, `H`, the finite-index hypothesis on `H`, and the
-- finite-presentability hypothesis on `G`; the Schreier presentation of `H` is derived bridge
-- data supplied by Proposition `2-4-1`, so no parallel local presentation wrapper belongs here.

/- Background recall: a finite-index subgroup of a finitely generated group is finitely
generated. -/
#check Subgroup.fg_of_index_ne_zero

/- Background recall: Proposition `2-2-1` is the canonical bridge from a finite presentation to
`Group.IsFinitelyPresented`. -/
#check GroupPresentation.isFinitelyPresented_presentedGroup

-- Proof sketch: choose a finite presentation of `G`, apply
-- the Reidemeister-Schreier presentation theorem from Proposition `2-4-1` to a Schreier
-- transversal for the preimage of `H`, use finite index together with Schreier's theorem to show
-- that the Schreier generator type and rewritten relator set are finite, invoke
-- `GroupPresentation.isFinitelyPresented_presentedGroup` for that finite presentation, and
-- transport the result to `H` through the resulting multiplicative equivalence.
namespace Subgroup

/-- Proposition 2-4-2: a finite-index subgroup of a finitely presented group is finitely
presented. -/
instance isFinitelyPresented_of_finiteIndex [Group.IsFinitelyPresented G] [H.FiniteIndex] :
    Group.IsFinitelyPresented H := sorry

end Subgroup

end
