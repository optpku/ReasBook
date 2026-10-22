/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open QuotientGroup

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-4-9: if `u` and `v` are not conjugate in a free group `F`, then for every
prime `p` there is a finite `p`-group quotient of `F` in which the images of `u` and `v` are still
not conjugate. This is the quotient-owner form of the textbook surjective statement, recovered
canonically from the quotient-by-kernel presentation of a surjective homomorphism. -/
-- Layer triage:
-- `source-facing`: the ambient free group `F`, the two elements `u` and `v`, and a prime `p`.
-- `core/canonical`: the bundled owner `N : FiniteIndexNormalSubgroup F`, its underlying subgroup
-- `N.toSubgroup`, the quotient owner `F ⧸ N.toSubgroup`, the quotient-side coercions
-- `u : F ⧸ N.toSubgroup` and `v : F ⧸ N.toSubgroup`, and the quotient-side predicates
-- `IsPGroup p (F ⧸ N.toSubgroup)` and `IsConj`.
-- `bridge/view`: the textbook phrase “a surjective homomorphism onto a finite `p`-group” is the
-- quotient-by-kernel view of the owner datum `N.toSubgroup`, via
-- `QuotientGroup.quotientKerEquivOfSurjective`.
-- Domain sampling:
-- 1. `FiniteIndexNormalSubgroup` is the owner abstraction for normal subgroups of finite index.
-- 2. The quotient coercion `F → F ⧸ N.toSubgroup` is the canonical image map attached to a normal
--    subgroup.
-- 3. `QuotientGroup.quotientKerEquivOfSurjective` is the first-isomorphism owner bridge from an
--    arbitrary surjective homomorphism to its kernel quotient.
-- 4. `MonoidHom.map_isConj` is the canonical transport of conjugacy along homomorphisms.
-- 5. `IsPGroup.of_equiv` is the canonical way to move the `p`-group structure across the quotient
--    isomorphism induced by a surjection.
-- Primitive vs. derived:
-- the intrinsic primitive data is the finite-index normal subgroup owner `N`;
-- the quotient group, its quotient map, its `p`-group structure, and the source-facing surjective
-- homomorphism are derived API.
-- Proof sketch: argue by induction on the total reduced-word length after transporting `F` to its
-- canonical free-group model. If the images of `u` and `v` already differ in the abelianization,
-- reduce modulo a large `p`-power to separate them in a finite abelian `p`-group. Otherwise use
-- the Baumslag-Taylor reduction to pass to shorter nonconjugate words inside a suitable subgroup,
-- apply the induction hypothesis there, and then compose with the relevant finite `p`-group
-- quotient map back from `F`.
theorem exists_finite_pGroup_quotient_separating_nonconjugate
    (p : ℕ) [Fact p.Prime] (u v : F) (huv : ¬ IsConj u v) :
    ∃ N : FiniteIndexNormalSubgroup F,
      IsPGroup p (F ⧸ N.toSubgroup) ∧
        ¬ IsConj (u : F ⧸ N.toSubgroup) (v : F ⧸ N.toSubgroup) := sorry

end
