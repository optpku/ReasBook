/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

/- Internal bridge: the textbook existential statement is witnessed in the canonical free-group
model `FreeGroup (Fin n)`. -/
private theorem exists_freeGroup_mem_nthPowers_pow_not_mem_lower_powers
    (n N : ℕ) (hN : 1 < N) :
    ∃ w : FreeGroup (Fin n),
      w ∈ (Set.range fun g : FreeGroup (Fin n) ↦ g ^ N) ^ n ∧
        ∀ m < n, w ∉ (Set.range fun g : FreeGroup (Fin n) ↦ g ^ N) ^ m := sorry

/-- Corollary 1-6-7: for every `n ≥ 0` and `N > 1`, some group contains an element that is a
product of exactly `n` `N`th powers, in the sense that it lies in the `n`-fold pointwise product
of `Set.range (fun g ↦ g ^ N)` but in no smaller such product. -/
-- Layer triage:
-- `source-facing`: the textbook existence statement for an element that is a product of exactly
-- `n` `N`th powers.
-- `core/canonical`: mathlib's pointwise `Set` power API applied to the canonical set
-- `Set.range (fun g : G ↦ g ^ N)` of `N`th powers.
-- `bridge/view`: the source-facing existential statement is witnessed in the canonical free-group
-- model `FreeGroup (Fin n)` by the private bridge theorem
-- `exists_freeGroup_mem_nthPowers_pow_not_mem_lower_powers`.
-- Domain sampling:
-- 1. `Set.range (fun g : G ↦ g ^ N)` is the canonical set of `N`th powers, so a local wrapper
--    would duplicate the owner declaration.
-- 2. `Set.mem_pow` is mathlib's owner lemma for membership in an `n`-fold pointwise product.
-- 3. `Set.mem_pow_iff_prod` is the indexed-product reformulation of the same owner API.
-- 4. `rank_closure_range_le_half_of_prod_powers_eq_one` from Proposition `1-6-6` is the
--    chapter owner theorem controlling relations among finite products of `N`th powers in a free
--    group.
-- Primitive vs. derived:
-- the primitive public data are only `n` and `N`; the specific witness group and witness element
-- are derived, with the canonical free-group model `FreeGroup (Fin n)` supplying a bridge
-- witness. The pointwise powers of the set of `N`th powers are derived from the `Set` owner
-- abstraction.
-- Proof sketch: for `n = 0`, take the identity element. For `n > 0`, take
-- `G = FreeGroup (Fin n)` and the product of the `N`th powers of the free generators. If that
-- element also lay in `(Set.range fun g : G ↦ g ^ N) ^ m` with `m < n`, then after rewriting
-- both memberships as explicit products of `N`th powers and moving one side across, Proposition
-- `1-6-6` would give a relation among `n + m` `N`th powers whose generated subgroup has rank at
-- most `(n + m) / 2`.
-- Since that subgroup contains the `n` free generators, its rank is at least `n`, forcing
-- `n ≤ m`, a contradiction.
theorem exists_group_element_mem_nthPowerSet_pow_not_mem_lower_powers
    (n N : ℕ) (hN : 1 < N) :
    ∃ (G : Type) (_ : Group G) (w : G),
      w ∈ (Set.range fun g : G ↦ g ^ N) ^ n ∧
        ∀ m < n, w ∉ (Set.range fun g : G ↦ g ^ N) ^ m := by
  obtain ⟨w, hw, hlower⟩ := exists_freeGroup_mem_nthPowers_pow_not_mem_lower_powers n N hN
  exact ⟨FreeGroup (Fin n), inferInstance, w, hw, hlower⟩
