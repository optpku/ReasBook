/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap04.Theorem_4_8_1

universe u

set_option autoImplicit false

namespace IsAlgebraicallyClosedGroup

/-!
Primary domain: group-theoretic algebraic closure.

Layer triage:
- `source-facing`: the textbook notion of an algebraically closed group, meaning that every finite
  system of equations and inequations with coefficients in `G` that is solvable in some extension
  already has a solution in `G`, together with the two consequences in Theorem `4-8-2`.
- `core/canonical`: the owner predicate `IsAlgebraicallyClosedGroup` imported from Theorem
  `4-8-1`, together with the coefficient-word owner `G ∗ FreeGroup ι`,
  `Monoid.Coprod.lift`, `IsSimpleGroup`, and `Group.FG`.
- `bridge/view`: this file is a consequence layer over the owner from Theorem `4-8-1`; the
  source's finite systems of equations and inequations are already encoded there as finite sets of
  coefficient words in `G ∗ FreeGroup ι`.

Domain sampling:
1. `IsAlgebraicallyClosedGroup` from Theorem `4-8-1` is the chapter owner for the finite-system
   extension property.
2. `G ∗ FreeGroup ι` from Theorem `4-8-1` is the canonical owner for coefficient words with
   coefficients in `G` and variables in `ι`.
3. `Monoid.Coprod.lift` from Theorem `4-8-1` is the canonical evaluation map for such words in an
   extension group.
4. `IsSimpleGroup` and `Group.FG` are mathlib's owners for the two conclusions of Theorem `4-8-2`.

Primitive vs. derived:
- primitive public data in this file: the ambient group `G` and the imported owner hypothesis
  `IsAlgebraicallyClosedGroup G`;
- derived API: the induced owner instance `IsSimpleGroup G` and the theorem that `G` is not
  finitely generated.
-/

variable {G : Type u} [Group G]

/-- Theorem 4-8-2 (1): every algebraically closed group is simple. -/
-- Proof sketch: for nontrivial `w a : G`, consider in the free product `G ∗ FreeGroup PUnit` the
-- one-variable equation expressing that a stable letter conjugates the commutator
-- `w x w⁻¹ x⁻¹` to `a x w⁻¹ x⁻¹`. This equation is solvable in an HNN extension, hence by
-- algebraic closedness it is solvable already in `G`. Rearranging shows that `a` lies in the
-- normal closure of `w`, so every nontrivial element normally generates `G`.
instance isSimpleGroup [IsAlgebraicallyClosedGroup G] : IsSimpleGroup G := by
  sorry

/-- Theorem 4-8-2 (2): an algebraically closed group cannot be finitely generated. -/
-- Proof sketch: algebraic closedness lets one solve `a * x ≠ x * a` in `G`, so the center is
-- trivial. On the other hand, for any finite generating set `{a₁, ..., aₙ}` the finite system
-- `aᵢ * y = y * aᵢ` together with `y ≠ 1` has a solution in an extension and therefore already in
-- `G`. Thus every finitely generated subgroup has a nontrivial centralizer, so `G` itself cannot
-- be finitely generated.
theorem not_fg [IsAlgebraicallyClosedGroup G] : ¬ Group.FG G := by
  sorry

end IsAlgebraicallyClosedGroup
