/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {X : Type u}

local instance proposition_2_5_27_decidableEq : DecidableEq X := Classical.decEq X
local notation "basis" => FreeGroupBasis.ofFreeGroup X

variable (s : FreeGroup X) (n : ℕ)

local notation "q" => PresentedGroup.mk (Set.singleton (s ^ n))

-- Layer triage:
-- `source-facing`: a one-relator quotient `G = (X; s ^ n)` with `s` cyclically reduced, together
-- with two free-group elements `u` and `v` that have the same image in `G`, and a basis letter
-- `x` that occurs in `u` but not in `v`.
-- `core/canonical`: `PresentedGroup (Set.singleton (s ^ n))` for the one-relator quotient, `q`
-- for the quotient
-- map, `List.IsInfix` for consecutive subwords of the canonical reduced words,
-- `basisLetterOccurs basis` for generator occurrence, and `FreeGroup.norm` for reduced-word
-- length.
-- `bridge/view`: the source phrase “the letter `x` occurs in `u` but not in `v`” is read through
-- the chapter's owner-side predicate `basisLetterOccurs` specialized to the canonical basis
-- `basis`, with no auxiliary presentation wrapper.
-- Domain sampling:
-- 1. `PresentedGroup (Set.singleton r)` is the chapter's canonical owner for the
--    one-relator group on generators `X`.
-- 2. `PresentedGroup.mk` is the canonical map identifying when two ambient free-group elements
--    represent the same element of the quotient.
-- 3. `List.IsInfix` from mathlib is the owner predicate for a consecutive subword of a reduced
--    word.
-- 4. `basisLetterOccurs basis` from Proposition `1-7-4` is the chapter's owner-side occurrence
--    predicate for generators in the concrete free-group model.
-- 5. `FreeGroup.IsCyclicallyReduced` is the chapter's owner predicate for the cyclically reduced
--    root hypothesis needed by the Newman--Greendlinger conclusion for the relator `s ^ n`.
-- 6. `FreeGroup.norm` is the canonical reduced-word length on `FreeGroup X`, so the textbook
--    quantity `|s|` is rendered directly as `FreeGroup.norm s`.
-- Primitive vs. derived:
-- the primitive source data are the root word `s`, the exponent `n`, the two representative words
-- `u` and `v`, the cyclically reduced root hypothesis on `s`, and the letter-occurrence
-- discrepancy for `x`. The quotient equality and the long common subword with the relator or its
-- inverse are the derived owner-level conclusions.

/-- Proposition 2-5-27: if `u` and `v` represent the same element of the one-relator group
`PresentedGroup (Set.singleton (s ^ n))`, where `n > 1` and the root `s` is cyclically
reduced, and some generator `x` occurs in `u` but not in `v`, then `u` contains a consecutive
subword that is also a consecutive subword of the relator `s ^ n` or of its inverse, and whose
length is greater than `(n - 1) * |s|`. -/
-- Proof sketch: from the equality of the images of `u` and `v` in the quotient by `s ^ n`, form
-- a van Kampen diagram for `u * v⁻¹` over the single relator `s ^ n`. The disappearance of the
-- letter `x` from `v` forces one 2-cell labeled by the relator to share a long boundary segment
-- with the `u`-side of the diagram. Greendlinger's lemma for the proper-power relator `s ^ n`
-- applies because the root `s` is cyclically reduced, and it yields a common part with `s ^ n`
-- or `(s ^ n)⁻¹` of length strictly greater than `(n - 1) * FreeGroup.norm s`.
theorem exists_long_common_part_with_relator_of_eq_in_power_relator_quotient
    (u v : FreeGroup X) {x : X} (hn : 1 < n)
    (hs : FreeGroup.IsCyclicallyReduced s.toWord)
    (heq : q u = q v)
    (hxu : basisLetterOccurs basis x u)
    (hxv : ¬ basisLetterOccurs basis x v) :
    ∃ part : List (X × Bool),
      part <:+: u.toWord ∧
        (part <:+: (s ^ n).toWord ∨ part <:+: ((s ^ n)⁻¹).toWord) ∧
          part.length > (n - 1) * s.norm := by
  sorry

end
