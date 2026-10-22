/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

-- Layer triage:
-- `source-facing`: a one-relator group `G = (X; r)` together with the hypothesis that the
-- quotient has a nontrivial finite-order element, and a chosen nontrivial element whose
-- centralizer is under study.
-- `core/canonical`: `PresentedGroup ({r} : Set (FreeGroup X))` for the one-relator quotient,
-- `Subgroup.centralizer {g}` for the centralizer of an element, and `IsCyclic` for the conclusion
-- that this centralizer is cyclic.
-- `bridge/view`: the textbook phrase “one-relator group with torsion” is rendered directly as the
-- existence of a nontrivial finite-order element in the canonical quotient; no extra wrapper
-- predicate for torsion one-relator groups is introduced.
-- Domain sampling:
-- 1. `PresentedGroup ({r} : Set (FreeGroup X))` is the established project owner for one-relator
--    groups in this chapter.
-- 2. `Subgroup.centralizer {g}` is mathlib's canonical subgroup-valued owner for the centralizer
--    of an element.
-- 3. `IsOfFinOrder` is mathlib's canonical predicate for a finite-order element.
-- 4. `IsCyclic` is mathlib's canonical predicate for cyclicity of a group or subgroup.
-- Primitive vs. derived:
-- the primitive public data are the relator `r`, the torsion witness `htorsion`, and the
-- nontrivial element `g`; the cyclicity of its centralizer is the derived conclusion.

variable {X : Type u}
variable (r : FreeGroup X)

local notation "rels" => (Set.singleton r : Set (FreeGroup X))
local notation "Q" => PresentedGroup rels

/-- Proposition 2-5-29: if a one-relator group has torsion, then the centralizer of every
nontrivial element is cyclic.
For the canonical quotient `Q := PresentedGroup ({r} : Set (FreeGroup X))`, torsion is expressed
by a nontrivial finite-order element of `Q`. -/
-- Proof sketch: this is Newman's centralizer theorem for one-relator groups with torsion.
-- Starting from a nontrivial finite-order element in the quotient, one uses the structure theory
-- of torsion one-relator groups to show that the centralizer of any nontrivial element is forced
-- into the unique maximal cyclic subgroup containing that element.
theorem centralizer_nontrivial_isCyclic_of_torsion_oneRelator
    (htorsion : ∃ t : Q, t ≠ 1 ∧ IsOfFinOrder t) (g : Q) (hg : g ≠ 1) :
    IsCyclic (Subgroup.centralizer {g}) := sorry

end
