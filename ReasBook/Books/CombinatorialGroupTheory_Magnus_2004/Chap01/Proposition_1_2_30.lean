/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_17

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open FreeGroup

noncomputable section

variable {ι : Type v} {F : Type u} [Group F]

local instance proposition_1_2_30_decidableEq : DecidableEq ι := Classical.decEq ι

/-!
Primary domain: conjugacy growth in free groups measured by reduced-word length.

Layer triage:
- `source-facing`: the basis-relative word-length statement for a free group with chosen basis.
- `core/canonical`: `FreeGroup.norm` on the canonical `FreeGroup ι` model.
- `bridge/view`: `FreeGroupBasis.repr` transports the source-facing formulation to that owner
  statement.

Domain sampling:
1. `FreeGroup.norm` is the owner reduced-word length function.
2. `FreeGroupBasis.repr` is the canonical equivalence from an abstract free group with chosen basis
   to the concrete `FreeGroup` model.
3. `commute_map_iff` is the owner transport lemma for commutation through the basis equivalence.

Primitive vs. derived:
- primitive public data: elements `u w` and the hypothesis `¬ Commute u w`;
- derived API: the basis-level formulation obtained by transporting the canonical `FreeGroup`
  statement through `b.repr`.
-/

namespace FreeGroup

/-- Proposition 1-2-30 on the canonical free-group model: if `u` and `w` do not commute, then
there is an integer from which onward the reduced-word lengths of the conjugates
`w^{-m} * u * w^m` form a strictly increasing sequence. -/
-- Layer: core/canonical owner statement on `FreeGroup ι`.
-- Proof sketch: first conjugate `w` to a cyclically reduced element, which does not change the
-- reduced-word lengths of the conjugates up to a bounded shift. For sufficiently large positive
-- powers, enough of the initial and terminal copies of `w` survive free reduction in
-- `w^{-m} * u * w^m`, so each successive conjugation by `w` strictly increases the reduced-word
-- length. If no such tail existed, the eventual periodicity argument from the textbook would force
-- `u` and `w` to commute, contradicting the hypothesis.
theorem exists_conjugate_power_tail_strictMono_norm_of_not_commute
    (u w : FreeGroup ι) (huw : ¬ Commute u w) :
    ∃ n : ℤ,
      StrictMono fun k : ℕ ↦
        norm (w ^ (-(n + k : ℤ)) * u * w ^ (n + k : ℤ)) := sorry

end FreeGroup

namespace FreeGroupBasis

/-- Proposition 1-2-30: if `u` and `w` do not commute in a free group, then there is an integer
from which onward the reduced-word lengths of the conjugates `w^{-m} * u * w^m` form a strictly
increasing sequence, relative to a chosen free basis. -/
-- Layer: source-facing bridge/view statement obtained from the canonical `FreeGroup` owner
-- theorem through `b.repr`.
theorem exists_conjugate_power_tail_strictMono_wordLength_of_not_commute
    (b : FreeGroupBasis ι F) (u w : F) (huw : ¬ Commute u w) :
    ∃ n : ℤ,
      StrictMono fun k : ℕ ↦
        norm (b.repr (w ^ (-(n + k : ℤ)) * u * w ^ (n + k : ℤ))) := by
  simpa [map_mul, map_zpow] using
    FreeGroup.exists_conjugate_power_tail_strictMono_norm_of_not_commute (b.repr u) (b.repr w)
      (by simpa [commute_map_iff b.repr.injective] using huw)

end FreeGroupBasis
