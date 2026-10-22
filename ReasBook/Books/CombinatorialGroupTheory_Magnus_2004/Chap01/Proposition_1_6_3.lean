/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

universe u v

open scoped Monoid.Coprod
open Subgroup

section

variable {G : Type u} [Group G] [Finite G] [Nontrivial G]
variable {X : Type v} [Group X] [IsCyclic X] [Infinite X]

-- Layer triage:
-- `source-facing`: the quotient of the free product `G ∗ X` by the normal closure of one element.
-- `core/canonical`: `Monoid.Coprod` for the ambient free product,
-- `Subgroup.normalClosure` for the relator subgroup, and `QuotientGroup.nontrivial_iff` for the
-- quotient-side nontriviality criterion.
-- `bridge/view`: an explicit generator of the infinite cyclic factor would come from
-- `intCyclicMulEquiv X : Multiplicative ℤ ≃* X`, but the proposition itself only needs the
-- intrinsic owner assumptions `[IsCyclic X] [Infinite X]`.
-- Domain sampling:
-- 1. `Monoid.Coprod` with notation `G ∗ X` is mathlib's owner abstraction for the free product of
--    two groups.
-- 2. `Subgroup.normalClosure` is the owner construction for the normal closure of a subset, hence
--    of a singleton relator, so the relator subgroup is canonically `Subgroup.normalClosure {w}`.
-- 3. `QuotientGroup.mk'` and `QuotientGroup.nontrivial_iff` are the canonical quotient-group API
--    for passing from the ambient free product to the quotient and reading its nontriviality.
-- 4. `intCyclicMulEquiv` shows that an infinite cyclic group is canonically equivalent to
--    `Multiplicative ℤ`, so a separate chosen-generator wrapper for `X` would duplicate owner API.
-- Primitive vs. derived:
-- the primitive source data are the finite nontrivial group `G`, the infinite cyclic group `X`,
-- and the relator `w : G ∗ X`; the relator subgroup `Subgroup.normalClosure {w}` and the quotient
-- `((G ∗ X) ⧸ Subgroup.normalClosure {w})` are derived canonically from that data.

/-- Proposition 1-6-3: if `G` is a finite nontrivial group, `X` is an infinite cyclic group, and
`w` is an element of the free product `G ∗ X`, then the quotient of `G ∗ X` by the normal closure
of `w` is nontrivial. -/
-- Proof sketch: if the exponent sum of the `X`-letters in `w` is not `±1`, then the image of the
-- generator of `X` is already nontrivial in the quotient. In the remaining case, identify `X`
-- with `Multiplicative ℤ`, embed the finite group `G` into a unitary group, solve the resulting
-- one-relator equation there by a path-connectedness argument, and obtain a homomorphism from the
-- quotient back to that unitary group which is injective on the copy of `G`.
theorem freeProduct_quotient_normalClosure_singleton_nontrivial
    (w : G ∗ X) :
    Nontrivial ((G ∗ X) ⧸ normalClosure {w}) := sorry

end
