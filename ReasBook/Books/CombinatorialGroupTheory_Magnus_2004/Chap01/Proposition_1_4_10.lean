/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open QuotientGroup

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-4-10: if `u` and `v` are not conjugate in the free group `F`, then for some
index `n` their images in the quotient by the `n`th term of the lower central series are not
conjugate. -/
-- Layer triage:
-- this item is a `bridge/view` theorem: it keeps the textbook lower-central-series quotient
-- `F / F_n`, but its proof should pass through the quotient-owner theorem from Proposition 1-4-9.
-- `source-facing`: the free group `F`, elements `u v : F`, and the lower-central-series index
-- `n`.
-- `core/canonical`: `lowerCentralSeries F n`, the quotient map
-- `mk' (lowerCentralSeries F n) : F →* F ⧸ lowerCentralSeries F n`, and the quotient conjugacy
-- relation `IsConj`.
-- Domain sampling:
-- 1. `lowerCentralSeries F` in mathlib is the owner descending central series.
-- 2. `mk'` is the canonical quotient map attached to a normal subgroup, and the quotient-side
--    coercion `u : F ⧸ lowerCentralSeries F n` is its owner-derived view.
-- 3. `MonoidHom.map_isConj` is the owner transport for conjugacy along the factor map
--    `F ⧸ lowerCentralSeries F n →* F ⧸ N`.
-- 4. `IsPGroup.isNilpotent` and `nilpotent_iff_lowerCentralSeries` are the owner bridge from the
--    finite `p`-group quotient in Proposition 1-4-9 to a vanishing lower-central-series stage.
-- Primitive vs. derived:
-- the primitive datum is the canonical owner subgroup `lowerCentralSeries F n`; the quotient type
-- `F ⧸ lowerCentralSeries F n` and the induced quotient image `u : F ⧸ lowerCentralSeries F n`
-- are derived from it.
-- Proof sketch: apply Proposition 1-4-9 in its quotient-owner form to obtain a finite-index
-- normal subgroup owner `N` such that `F ⧸ N.toSubgroup` is a finite `p`-group and the images of
-- `u` and `v` in `F ⧸ N.toSubgroup` are not conjugate. Since finite `p`-groups are nilpotent,
-- some lower central term of `F ⧸ N.toSubgroup` is trivial; functoriality of the lower central
-- series for the canonical quotient map then shows `lowerCentralSeries F n ≤ N.toSubgroup`, so
-- the quotient map `F →* F ⧸ N.toSubgroup` factors through
-- `F ⧸ lowerCentralSeries F n`. If the images of `u` and `v` were conjugate in that lower-central
-- quotient, their further images in `F ⧸ N.toSubgroup` would also be conjugate.
theorem exists_lowerCentralSeries_quotient_separating_nonconjugate
    (u v : F) (huv : ¬ IsConj u v) :
    ∃ n : ℕ,
      ¬ IsConj ((u : F ⧸ Subgroup.lowerCentralSeries F n))
        (v : F ⧸ Subgroup.lowerCentralSeries F n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hNpq, huvN⟩ :=
    exists_finite_pGroup_quotient_separating_nonconjugate 2 u v huv
  letI : Group.IsNilpotent (F ⧸ N.toSubgroup) := hNpq.isNilpotent
  let n : ℕ := Group.nilpotencyClass (F ⧸ N.toSubgroup)
  have hle : Subgroup.lowerCentralSeries F n ≤ N.toSubgroup := by
    rw [← ker_mk' N.toSubgroup]
    exact (Subgroup.map_eq_bot_iff _).mp <| by
      apply eq_bot_iff.mpr
      calc
        Subgroup.map (mk' N.toSubgroup) (Subgroup.lowerCentralSeries F n) ≤
            Subgroup.lowerCentralSeries (F ⧸ N.toSubgroup) n :=
          Subgroup.lowerCentralSeries.map _ n
        _ = ⊥ := by
          dsimp [n]
          exact Subgroup.lowerCentralSeries_nilpotencyClass
  refine ⟨n, ?_⟩
  intro huvLower
  exact huvN <| by
    simpa using
      (QuotientGroup.map (Subgroup.lowerCentralSeries F n) N.toSubgroup (.id F) hle).map_isConj
        huvLower

end
