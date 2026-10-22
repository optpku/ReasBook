/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap02.Proposition_2_5_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x y

open scoped Monoid.Coprod

set_option autoImplicit false

section

variable {G : Type u} [Group G]

/-!
Primary domain: group theory, free products, direct products, and free indecomposability.

Layer triage:
- `source-facing`: a group `G` together with a nontrivial free-product decomposition
  `G ≃* A ∗ B` and a nontrivial direct-product decomposition `G ≃* D × E`.
- `core/canonical`: `Monoid.Coprod` is mathlib's owner for free products, the product type
  `D × E` is the canonical owner for direct products, and `IsFreelyIndecomposable` from
  Proposition `2-5-12` is the project's owner abstraction for excluding nontrivial free-product
  decompositions.
- `bridge/view`: the two source-facing equivalences are composed into
  `D × E ≃* A ∗ B`, and the textbook contradiction is then a short corollary of the owner field
  `of_mulEquiv_coprod`.

Domain sampling:
1. `Monoid.Coprod` with notation `A ∗ B` is mathlib's owner abstraction for free products.
2. `IsFreelyIndecomposable` from Proposition `2-5-12` is the chapter owner for the property
   “every free-product decomposition has a trivial factor”.
3. `IsFreelyIndecomposable.of_mulEquiv_coprod` is the owner field that turns a free-product
   equivalence into the conclusion `Subsingleton A ∨ Subsingleton B`.
4. `false_of_nontrivial_of_subsingleton` is the atomic mathlib contradiction used to pass from the
   owner conclusion `Subsingleton A ∨ Subsingleton B` back to the source wording with
   nontriviality hypotheses.

Best owner abstraction:
- the reusable mathematical core is `IsFreelyIndecomposable`, not a one-off theorem returning
  `False` from two decomposition witnesses.

Primitive vs. derived:
- primitive public data: the nontrivial direct-product factors `D`, `E` and, in the source-facing
  corollary, the nontrivial free-product factors `A`, `B`;
- derived API: free indecomposability of `D × E` and the resulting contradiction for a
  simultaneous nontrivial free-product decomposition of `G`.
-/

-- Proof sketch: a nontrivial direct product has enough commuting structure to force any
-- free-product decomposition to collapse to a trivial factor, so the correct reusable output is
-- the owner predicate `IsFreelyIndecomposable`. The source-facing remark then follows by applying
-- that owner predicate to the given free-product equivalence.
/-- A direct product of two nontrivial groups is freely indecomposable. -/
theorem isFreelyIndecomposable_prod
    (D : Type x) [Group D] (E : Type y) [Group E]
    (hD : Nontrivial D) (hE : Nontrivial E) :
    IsFreelyIndecomposable (D × E) := by
  sorry

/-- Remark 4-1-12: a group that is isomorphic to a free product `A ∗ B` with both factors
nontrivial cannot also be isomorphic to a direct product `D × E` with both factors nontrivial. -/
theorem not_nontrivial_directProduct_of_nontrivial_freeProduct
    {A : Type v} [Group A] {B : Type w} [Group B]
    {D : Type x} [Group D] {E : Type y} [Group E]
    (hA : Nontrivial A) (hB : Nontrivial B)
    (hfree : G ≃* A ∗ B)
    (hD : Nontrivial D) (hE : Nontrivial E)
    (hdirect : G ≃* D × E) : False := by
  rcases (isFreelyIndecomposable_prod D E hD hE).of_mulEquiv_coprod (hdirect.symm.trans hfree) with
    hA' | hB'
  · letI := hA
    letI := hA'
    exact false_of_nontrivial_of_subsingleton A
  · letI := hB
    letI := hB'
    exact false_of_nontrivial_of_subsingleton B

end
