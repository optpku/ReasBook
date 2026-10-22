/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap02.Proposition_2_5_31
import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_2_9
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_11_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

set_option autoImplicit false

section

variable {H : Type u} {K : Type v} [Group H] [Group K]

open Subgroup

/-!
Primary domain: small-cancellation theory over free products with amalgamation.

Layer triage:
- `source-facing`: proper subgroups `A ≤ H` and `B ≤ K`, an identification `e : A ≃* B`, and the
  existence of a blocking pair for `A` inside `H`.
- `core/canonical`: `Subgroup H` and `Subgroup K` are the owner abstractions for the amalgamated
  subgroups, `Subgroup.IsBlockingPair` is the source-facing predicate from Definition `5-11-8`,
  `Subgroup.amalgamatedProductAlong e` is the canonical owner for the amalgamated product, and
  `IsSQUniversal` is the project owner predicate for the conclusion.
- `bridge/view`: the textbook notation `P = ⟨H ∗ K, A = B⟩` is rendered directly by the canonical
  owner `Subgroup.amalgamatedProductAlong e`.

Domain sampling:
1. `Subgroup.IsBlockingPair` from Definition `5-11-8` already formalizes the source blocking-pair
   condition on the subgroup owner `A`.
2. `Subgroup.amalgamatedProductAlong e` from Definition `4-2-9` is the chapter owner for the free
   product of `H` and `K` amalgamating `A` with `B`.
3. `IsSQUniversal` from Proposition `2-5-31` is the existing owner predicate for `SQ`-universality.

Primitive vs. derived:
the primitive public data are the ambient groups, the subgroup pair `A ≤ H`, `B ≤ K`, the
identification `e : A ≃* B`, the properness of `B`, and the existence of a blocking pair for `A`.
Properness of `A` is derived from the blocking-pair hypothesis, so it is not repeated as a
separate public assumption.
-/

-- Proof sketch: apply the section-11 small-cancellation theorem for amalgamated products with a
-- blocking pair on one side. The blocking-pair hypothesis supplies the combinatorial separation
-- needed to build the required small-cancellation quotient, and the properness of `B` excludes
-- the degenerate amalgamation case. The conclusion is then stated on the canonical owner
-- `Subgroup.amalgamatedProductAlong e`.
/-- Theorem 5-11-9: if `P = ⟨H ∗ K, A = B⟩` is a free product with amalgamation, `B` is a proper
subgroup of `K`, and there is a blocking pair for `A` in `H`, then `P` is `SQ`-universal. -/
theorem isSQUniversal_amalgamatedProductAlong_of_exists_blockingPair
    (A : Subgroup H) (B : Subgroup K) (e : A ≃* B) (hB_proper : B < ⊤)
    (hblocking : ∃ x₁ x₂, A.IsBlockingPair x₁ x₂) :
    IsSQUniversal (amalgamatedProductAlong e) := sorry

end
