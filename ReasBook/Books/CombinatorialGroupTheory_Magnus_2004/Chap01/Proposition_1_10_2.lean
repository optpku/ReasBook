/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open QuotientGroup

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-10-2: the intersection of the terms of the descending central series of a free
group is trivial. In mathlib's indexing this is the infimum of `lowerCentralSeries F m`, since
`lowerCentralSeries F 0 = F` and `lowerCentralSeries F (m + 1) = ⁅lowerCentralSeries F m, ⊤⁆`.

The textbook finite-rank hypothesis and the choice of a basis are redundant for this statement, so
the theorem is stated directly under the owner assumption `[IsFreeGroup F]`. -/
-- Layer triage:
-- `source-facing`: the textbook descending central series `F₁ = F`, `F_{m + 1} = [F_m, F]` and
-- the assertion that its intersection is trivial.
-- `core/canonical`: mathlib's owner sequence `lowerCentralSeries F`.
-- `bridge/view`: Proposition `1-4-10` gives the owner separation theorem saying that every
-- nontrivial element of a free group survives in some lower-central-series quotient.
-- Domain sampling:
-- 1. `lowerCentralSeries F` is the canonical descending central series in mathlib.
-- 2. `exists_lowerCentralSeries_quotient_separating_nonconjugate` is the chapter's owner
--    separation theorem for lower-central quotients of a free group.
-- 3. `QuotientGroup.eq_one_iff` is the canonical membership test for the quotient map
--    `mk' (lowerCentralSeries F m)`.
-- 4. `Subgroup.eq_bot_iff_forall` and `Subgroup.mem_iInf` are the owner lattice lemmas for
--    converting subgroup infima into pointwise membership statements.
-- Primitive vs. derived:
-- the primitive datum is the free-group owner instance `[IsFreeGroup F]`; the subgroup
-- intersection `⨅ m, lowerCentralSeries F m` is the canonical derived owner encoding the textbook
-- intersection `⋂_m F_m`.
-- Proof sketch: let `g` lie in every `lowerCentralSeries F m`. If `g ≠ 1`, then `g` is not
-- conjugate to `1`, so Proposition `1-4-10` gives an index `m` such that the image of `g` in
-- `F ⧸ lowerCentralSeries F m` is not conjugate to `1`. But membership of `g` in
-- `lowerCentralSeries F m` forces that image to be `1`, contradiction.
theorem iInf_lowerCentralSeries_eq_bot_of_isFreeGroup :
    (⨅ m : ℕ, Subgroup.lowerCentralSeries F m) = (⊥ : Subgroup F) := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  by_contra hg1
  obtain ⟨m, hm⟩ :=
    exists_lowerCentralSeries_quotient_separating_nonconjugate g 1 <|
      by simpa [isConj_one_left] using hg1
  have hgq :
      (mk' (Subgroup.lowerCentralSeries F m) g :
        F ⧸ Subgroup.lowerCentralSeries F m) = 1 :=
    (QuotientGroup.eq_one_iff g).mpr <| Subgroup.mem_iInf.mp hg m
  exact hm <| by
    simpa using isConj_one_left.mpr hgq

end
