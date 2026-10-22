/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {X : Type u}

local instance proposition_1_7_7_decidableEq : DecidableEq X := Classical.decEq X
local notation "basis" => FreeGroupBasis.ofFreeGroup X

open FreeGroup.Finset

-- Layer triage:
-- `source-facing`: a finite strictly quadratic word system `S : Finset (FreeGroup X)` together
-- with the textbook connectedness, minimality, and full-support hypotheses.
-- `core/canonical`: `Finset (FreeGroup X)` together with `IsStrictlyQuadraticSet`,
-- `FreeGroup.Finset.sigmaGraph`, `FreeGroup.Finset.IsMinimal`,
-- `FreeGroup.Finset.ContainsAllGenerators`, and the owner connectedness predicate
-- `(wordIncidenceGraph basis (S : Set (FreeGroup X))).Connected` from the surrounding Section 7
-- files.
-- `bridge/view`: the Whitehead-move proof sketch is mediated by the canonical owner predicate
-- `FreeGroup.Finset.IsMinimal`, whose automorphic-orbit formulation is the chapter's stable
-- interface for
-- minimality.
--
-- Domain sampling:
-- 1. `IsStrictlyQuadraticSet` from Proposition `1-7-6` is the chapter owner predicate for the
--    strict quadraticity hypothesis of Section 7.
-- 2. `wordIncidenceGraph basis` from Proposition `1-7-4` is the owner graph construction for the
--    connectedness of a finite word system.
-- 3. `FreeGroup.Finset.sigmaGraph` from Proposition `1-7-8` is the owner construction for the
--    Whitehead graph attached to such a system.
-- 4. `FreeGroup.Finset.IsMinimal` and `FreeGroup.Finset.ContainsAllGenerators` from Proposition
--    `1-7-8` are the canonical owner predicates for minimality in the automorphic orbit and for
--    full generator support.
-- Best owner abstraction:
-- the Section 7 finite-word-system API on `Finset (FreeGroup X)` consisting of
-- `IsStrictlyQuadraticSet`, `sigmaGraph S`, `IsMinimal S`, `ContainsAllGenerators S`, and the
-- owner connectedness predicate `(wordIncidenceGraph basis (S : Set (FreeGroup X))).Connected`.
--
-- Primitive vs. derived:
-- the primitive data here are only the finite word system `S` and the source-facing hypotheses of
-- strict quadraticity, connectedness, minimality, and full support; the Whitehead graph is reused
-- from the existing owner API.

/-- Proposition 1-7-7: if a finite strictly quadratic word system `S` is connected, is minimal,
and contains every generator of `X`, then its Whitehead graph `Σ(S)` is connected. -/
-- Proof sketch: argue by contradiction. If `Σ(S)` is disconnected, partition its vertices into two
-- nonempty parts with no crossing edges. If both parts are inverse-stable, then the words of `S`
-- split into two nonempty subfamilies with disjoint generator supports, contradicting the
-- connectedness of `S`. Otherwise choose a letter `a` whose inverse lies in the opposite part; the
-- corresponding Whitehead move strictly decreases the total length, contradicting minimality.
theorem sigmaGraph_connected_of_connected_minimal_contains_all_generators
    [Finite X]
    (S : Finset (FreeGroup X))
    (hstrict : IsStrictlyQuadraticSet S)
    (hconnected : (wordIncidenceGraph basis (S : Set (FreeGroup X))).Connected)
    (hminimal : IsMinimal S)
    (hcontains : ContainsAllGenerators S) :
    (sigmaGraph S).Connected := sorry

end
