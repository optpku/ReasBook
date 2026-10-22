/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.GroupTheory.OrderOfElement
import CombinatorialGroupTheory_Magnus_2004.Chap04.Theorem_4_2_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

open Monoid

section

variable {G H : Type u} [Group G] [Group H]
variable {A : Subgroup G} {B : Subgroup H} (e : A ≃* B)

open Subgroup.amalgamatedProductAlong

local notation "P" => Subgroup.amalgamatedProductAlong e

/-!
Primary domain: torsion in free products with amalgamation.

Layer triage:
- `source-facing`: the two-factor amalgamated product determined by `e : A ≃* B`, together with
  the claim that each torsion element is conjugate to a torsion element from the left factor `G`
  or the right factor `H`.
- `core/canonical`: `MulEquiv.amalgamatedProduct` for the underlying pushout construction,
  `IsOfFinOrder` for torsion, and `IsConj` for conjugacy.
- `bridge/view`: `Subgroup.amalgamatedProductAlong e` is the chapter-facing two-factor owner with
  named `left` and `right` embeddings, built as a thin source-facing wrapper over the canonical
  `MulEquiv` pushout API. The internal `Bool`-indexed presentation should not appear in the public
  theorem statement.

Domain sampling:
1. `Subgroup.amalgamatedProduct` from Proposition `3-12-5` is the chapter's owner pattern for a
   two-factor amalgamated product: a named owner type together with named `left` and `right`
   embeddings, not a public `Bool`-indexed interface.
2. `Subgroup.amalgamatedProductAlong` from Definition `4-2-9` is the matching owner specialization
   for an abstract identification `e : A ≃* B`.
3. `MulEquiv.amalgamatedProduct` and `MulEquiv.amalgamatedProductFactor` are the canonical core
   constructions underneath that source-facing owner.
4. `IsOfFinOrder` and `IsConj` are mathlib's canonical predicates for finite order and conjugacy.

Primitive vs. derived:
the primitive public data are the two factor groups `G` and `H`, the subgroups `A ≤ G` and
`B ≤ H`, and the identification `e : A ≃* B`. The internal `Bool`-indexed pushout diagram is
bridge data. The owner `Subgroup.amalgamatedProductAlong e` and its named left/right embeddings are
canonical derived objects, so the main public theorem should speak directly about that source-facing
interface and state the textbook finite-order witness in one factor. The weaker conjugacy-only
alternative is a derived forgetful consequence, not the main numbered entry.
-/

/-- Theorem 4-2-11: every finite-order element of the amalgamated product
`P = ⟨G * H; A = B, e⟩` is conjugate to a finite-order element of one of the two factors. -/
-- Proof sketch: choose a cyclically reduced conjugate of the given torsion element using the
-- normal-form theorem for amalgamated products. A cyclically reduced word of length at least two
-- cannot have finite order, because its nonzero powers remain reduced and nontrivial. Hence a
-- torsion element is conjugate to an element lying in one factor, and conjugacy together with
-- injectivity of the factor embeddings shows that the factor element itself has finite order.
theorem exists_factor_isConj_of_amalgamatedProduct_isOfFinOrder
    (x : P) (hx : IsOfFinOrder x) :
    (∃ g : G, IsOfFinOrder g ∧ IsConj (left e g) x) ∨
      ∃ h : H, IsOfFinOrder h ∧ IsConj (right e h) x := sorry

end
