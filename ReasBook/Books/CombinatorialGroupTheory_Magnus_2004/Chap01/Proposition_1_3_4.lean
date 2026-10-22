/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_10_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Subgroup

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-3-4: the intersection of all terms in the derived series of a free group is
trivial. -/
-- Layer triage:
-- `source-facing`: the intersection statement for the derived series of a free group.
-- `core/canonical`: mathlib's owner sequence `derivedSeries F`.
-- `bridge/view`: the canonical comparison `derived_le_lower_central` identifies the derived-series
-- intersection as a subgroup of the lower-central-series intersection, whose triviality is already
-- the chapter owner theorem `iInf_lowerCentralSeries_eq_bot_of_isFreeGroup`.
-- Domain sampling:
-- 1. `derivedSeries F` is mathlib's owner declaration for the derived series.
-- 2. `lowerCentralSeries F` is mathlib's owner declaration for the descending central series.
-- 3. `derived_le_lower_central` is the canonical bridge from the derived series to the lower
--    central series.
-- 4. `iInf_lowerCentralSeries_eq_bot_of_isFreeGroup` is the project owner theorem for triviality
--    of the lower-central intersection in a free group.
-- Primitive vs. derived:
-- the only primitive datum is the free-group owner instance `[IsFreeGroup F]`; the subgroup infima
-- `⨅ n, derivedSeries F n` and `⨅ n, lowerCentralSeries F n` are the canonical derived lattice
-- objects encoding the source intersections.
theorem iInf_derivedSeries_eq_bot_of_isFreeGroup :
    (⨅ n : ℕ, derivedSeries F n) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have hg_lower : g ∈ ⨅ n : ℕ, Subgroup.lowerCentralSeries F n := by
    rw [Subgroup.mem_iInf]
    intro n
    exact Subgroup.derived_le_lower_central n <| Subgroup.mem_iInf.mp hg n
  simpa [iInf_lowerCentralSeries_eq_bot_of_isFreeGroup] using hg_lower

end
