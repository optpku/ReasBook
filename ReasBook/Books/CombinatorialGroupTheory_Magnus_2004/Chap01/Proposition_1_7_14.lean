/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Classical
open scoped RelatorSetIr

universe u

noncomputable section

section

variable {X : Type u}

-- Layer triage:
-- `source-facing`: a finite set `S` of cyclic words, its minimality under regular
-- transformations, its strict quadraticity, and the associated irreducibility rank `Ir(S)`.
-- `core/canonical`: `Finset (CyclicWord X)` as the finite-set owner, `CyclicWord.Finset` from
-- Proposition `1-7-9`, `CyclicWord.toConjClasses` as the canonical passage from cyclic words to
-- conjugacy classes in `FreeGroup X`, `ConjClasses.carrier` as the canonical relator-set view of
-- one conjugacy class, and `Ir(W)` from Proposition `1-6-13`.
-- `bridge/view`: a finite set of cyclic words determines the relator set of all free-group
-- elements whose conjugacy classes are represented by members of the set; minimality is measured
-- by the total cyclic length along the canonical automorphism action on cyclic words.
-- Domain sampling:
-- 1. `Finset (CyclicWord X)` is the canonical owner abstraction for a finite set of cyclic words.
-- 2. `CyclicWord.Finset.totalLength` and `CyclicWord.Finset.IsStrictlyQuadratic` from
--    Proposition `1-7-9` are the finite-system owner invariants used here.
-- 3. `CyclicWord.toConjClasses` is the canonical bridge from a cyclic word to one conjugacy
--    class in `FreeGroup X`.
-- 4. `ConjClasses.carrier` with `ConjClasses.mem_carrier_iff_mk_eq` is the canonical owner API
--    for the represented relator set of one conjugacy class.
-- 5. `Ir(W)` from Proposition `1-6-13` is the existing owner abstraction for irreducibility rank.
-- Primitive vs. derived:
-- the primitive data are only the finite set `S` of cyclic words. The ambient relator set,
-- irreducibility rank, total cyclic length, strict quadraticity, and the orbitwise minimality
-- predicate are derived canonically from that data.

namespace CyclicWord
namespace Finset

/-- The relator set represented by a finite set of cyclic words, obtained by taking every
free-group element whose conjugacy class is represented by one of those cyclic words. -/
def relatorSet (S : Finset (CyclicWord X)) : Set (FreeGroup X) :=
  { g | ∃ w ∈ S, g ∈ (w.toConjClasses).carrier }

/-- Membership in the relator set attached to a finite set of cyclic words is exactly membership
in one of the represented conjugacy classes. -/
-- Proof sketch: unfold `relatorSet`; the statement is its defining predicate, and
-- then `ConjClasses.mem_carrier_iff_mk_eq` identifies membership in each represented conjugacy
-- class with the corresponding equality of conjugacy classes.
theorem mem_relatorSet_iff (S : Finset (CyclicWord X)) (g : FreeGroup X) :
    g ∈ relatorSet S ↔
      ∃ w ∈ S, ConjClasses.mk g = CyclicWord.toConjClasses w := sorry

/-- The irreducibility rank of a finite set of cyclic words is the irreducibility rank of the
associated relator set in the ambient free group. -/
noncomputable def ir (S : Finset (CyclicWord X)) : ℕ∞ :=
  Ir(relatorSet S)

/-- A finite set of cyclic words is minimal when its total cyclic length is minimal in its
automorphism orbit. -/
def IsMinimal (S : Finset (CyclicWord X)) : Prop :=
  letI : DecidableEq (CyclicWord X) := Classical.decEq _
  ∀ α : MulAut (FreeGroup X),
    totalLength S ≤ totalLength (S.image (CyclicWord.map α))

/-- Proposition 1-7-14: if `S` is a finite minimal strictly quadratic set of cyclic words, then
its irreducibility rank is one quarter of its total cyclic length, rounded down. -/
-- Proof sketch: by the regular-transformation reduction from Proposition `7.6`, replace `S` by an
-- equivalent minimal set of the form consisting of singleton generators together with one residual
-- minimal strictly quadratic cyclic word `q`. The associated irreducibility rank is then the same
-- as that residual word's irreducibility rank, and Proposition `7.13` identifies that value with
-- one quarter of the total cyclic length.
theorem ir_eq_totalLength_div_four_of_minimal_strictlyQuadratic
    (S : Finset (CyclicWord X)) (hminimal : IsMinimal S) (hstrict : IsStrictlyQuadratic S) :
    ir S = ((totalLength S / 4 : ℕ) : ℕ∞) := sorry

end Finset
end CyclicWord

end
