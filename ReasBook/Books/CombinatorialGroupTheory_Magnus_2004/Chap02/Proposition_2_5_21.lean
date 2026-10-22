/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

-- Layer triage:
-- `source-facing`: a one-relator group `G = (X; r)` and the size of its generating set `X`,
-- together with the two centrality conclusions in the textbook.
-- `core/canonical`: `PresentedGroup ({r} : Set (FreeGroup X))` for the one-relator quotient,
-- `Subgroup.center` for the center, `⊥` for triviality, `IsMulCommutative` for the abelian
-- hypothesis in part (2), and `IsCyclic` / `Infinite` for the infinite-cyclic conclusion.
-- `bridge/view`: the textbook assertions about the center of `G` are stated directly on the
-- canonical quotient group attached to the relator `r`, so no extra presentation wrapper is
-- introduced.
-- Domain sampling:
-- 1. `PresentedGroup ({r} : Set (FreeGroup X))` is the chapter's canonical owner for the
--    one-relator group on generators `X` with defining relator `r`.
-- 2. `Subgroup.center G` is mathlib's canonical owner for the center of a group `G`.
-- 3. `IsMulCommutative G` is mathlib's canonical owner predicate for the group `G` being
--    abelian, replacing an ad hoc quantified commutativity hypothesis.
-- 4. `IsCyclic H` and `Infinite H` together express that a subgroup `H` is infinite cyclic.
-- Primitive vs. derived:
-- the primitive public data are the relator `r`, the cardinality hypotheses on `X`, and in part
-- (2) the nontriviality hypothesis on the canonical center `Z`; the center itself is the
-- canonical derived subgroup of the presented group.

variable {X : Type u}
variable (r : FreeGroup X)

local notation "rels" => (Set.singleton r : Set (FreeGroup X))
local notation "G" => PresentedGroup rels
local notation "Z" => Subgroup.center G

/-- Proposition 2-5-21 (1): if a one-relator group `G = (X; r)` has at least three generators,
then its center is trivial. -/
-- Proof sketch: apply the centralizer theorem for one-relator groups. A nontrivial central
-- element would have to commute with the images of at least three independent generators, but the
-- centralizer description in the one-relator setting forces such a situation to collapse to the
-- trivial element.
theorem center_eq_bot_of_oneRelator_card_ge_three
    (hX : 3 ≤ Cardinal.mk X) :
    Z = ⊥ := sorry

/-- Proposition 2-5-21 (2): if a one-relator group `G = (X; r)` has exactly two generators, is
nonabelian, and has nontrivial center, then its center is infinite cyclic. -/
-- Proof sketch: Murasugi's center theorem for one-relator groups shows that a nontrivial center
-- in the nonabelian two-generator case is cyclic. Proposition `2-5-20` supplies a torsion-free
-- finite-index normal subgroup, ruling out finite-order central elements and therefore forcing
-- that cyclic center to be infinite.
theorem center_isCyclic_and_infinite_of_oneRelator_card_eq_two_of_nonabelian_of_center_ne_bot
    (hX : Cardinal.mk X = 2) (hnab : ¬ IsMulCommutative G) (hZ : Z ≠ ⊥) :
    IsCyclic Z ∧ Infinite Z := sorry

end
