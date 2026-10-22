/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]

local notation "Γ" => Subgroup.lowerCentralSeries F

-- Layer triage:
-- `source-facing`: an element `w` of a free group which is both a product of two square elements
-- and a member of one textbook lower-central-series term `F_{n + 1}`, together with the induced
-- square class in the next textbook quotient `F_{n + 1} / F_{n + 2}`.
-- `core/canonical`: the owner lower central series `Γ`, the subgroup quotient
-- `Γ n ⧸ (Γ (n + 1)).subgroupOf (Γ n)`,
-- the canonical quotient coercion from `lowerCentralSeries F n`, and the canonical predicate
-- `IsSquare`.
-- `bridge/view`: mathlib indexes the lower central series one step earlier than the textbook
-- convention used in combinatorial group theory: `Γ 0 = F` and `Γ 1 = [F, F]`. Thus the
-- textbook term `F_{n + 1}` is realized by `Γ n`, with the Lean parameter `n` explicitly
-- recording this reindexing.
-- Domain sampling:
-- 1. `lowerCentralSeries F` in mathlib is the owner abstraction for the descending central series,
--    written locally here as `Γ`.
-- 2. `lowerCentralSeries_zero` and `lowerCentralSeries_one` show the indexing offset:
--    `lowerCentralSeries F 0 = F` and `lowerCentralSeries F 1 = [F, F]`.
-- 3. `IsSquare` together with `isSquare_iff_exists_sq` is the owner API for the square factors in
--    the source hypothesis.
-- 4. The quotient coercion from `Γ n` is the owner-derived image of `w`, and
--    `Subgroup.subgroupOf` is the canonical way to regard `Γ (n + 1)` as a subgroup of `Γ n`.
-- Primitive vs. derived:
-- the primitive source data are the element `w`, the hypothesis that `w` is a product of two
-- squares, and the membership hypothesis `w ∈ Γ n`; any chosen square factors witnessing that
-- decomposition are auxiliary bridge data, while the image class of `w` in the corresponding
-- lower-central-series quotient is derived canonically from the owner subgroup.

/-- Proposition 1-6-9, written with the explicit mathlib reindexing of the lower central series:
if `w` is a product of two square elements of a free group `F` and `w ∈ Γ n`, then the image of
`w` in the quotient `Γ n / Γ (n + 1)` is a square. Here the Lean index `n` corresponds to the
textbook index `n + 1`, since mathlib sets `lowerCentralSeries F 0 = F`. -/
-- Proof sketch: write `w = a * b` with `a = u²` and `b = v²`. Modulo the next lower-central-series
-- term, the quotient is abelian, so the image of `w` agrees with the square of the image of
-- `u * v`. In the source indexing, the key induction begins with the textbook case `F₁ = F`; in
-- mathlib this is the case `Γ 0 = F`. One then rewrites `v = u⁻¹ k` after showing
-- `u * v ∈ Γ 1`, and uses torsion-freeness of the successive lower-central-series quotients of a
-- free group to promote the error term into the required deeper term.
theorem isSquare_in_lowerCentralSeries_subquotient_of_product_two_squares
    (w : F) (n : ℕ)
    (hw_square : ∃ a b : F, IsSquare a ∧ IsSquare b ∧ w = a * b)
    (hw : w ∈ Γ n) :
    IsSquare
      ((⟨w, hw⟩ : Γ n) : Γ n ⧸ (Γ (n + 1)).subgroupOf (Γ n)) := sorry

end
