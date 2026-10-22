/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

open HNNExtension

section

variable {G : Type u} [Group G]
variable {A B : Subgroup G} {φ : A ≃* B}

local notation "E" => HNNExtension G A B φ
local notation "of" => (HNNExtension.of : G →* E)

/-!
Primary domain: torsion in HNN extensions of groups.

Layer triage:
- `source-facing`: an HNN extension `E = HNNExtension G A B φ` together with a finite-order
  element of `E` and the textbook conclusion that such an element is conjugate to one coming from
  the base group `G`.
- `core/canonical`: mathlib's owner `HNNExtension G A B φ`, the canonical embedding `of`,
  `IsOfFinOrder` and `orderOf` for torsion data, and `IsConj` for conjugacy.
- `bridge/view`: the phrase “an element of the base `G` viewed inside the HNN extension” is
  expressed directly by the canonical map `of`, so no extra wrapper API is needed.

Domain sampling:
1. `HNNExtension G A B φ` is mathlib's canonical owner abstraction for the source HNN extension.
2. `HNNExtension.of` is the canonical embedding of the base group into that HNN extension.
3. `IsOfFinOrder`, `orderOf`, and positive naturals `ℕ+` are the canonical owner APIs for finite
   order and exact positive order.
4. `IsConj` is mathlib's canonical relation for conjugacy in a group.

Primitive vs. derived:
- primitive public data: the base group `G`, the associated subgroups `A`, `B`, the isomorphism
  `φ`, and an element of `E`;
- derived API: the base-group witness whose image is conjugate to the given torsion element, the
  resulting finite-order statement for that base element, and the corresponding exact-order
  consequence for the existence of elements of order `n`.
-/

/-- Theorem 4-2-7 (1): every finite-order element of an HNN extension is conjugate to the image of
an element of the base group. The finite-order conclusion for that base element is derived from
conjugacy and injectivity of `of`. -/
-- Proof sketch: choose a cyclically reduced conjugate of the given torsion element. Britton's
-- lemma rules out any cyclically reduced representative containing the stable letter, because a
-- positive power of such a word would remain nontrivial. Hence the cyclically reduced conjugate
-- lies in the embedded base group, and conjugacy transports finite order back to a base element.
theorem exists_base_isConj_of_hnnExtension_isOfFinOrder (x : E) (hx : IsOfFinOrder x) :
    ∃ g : G, IsConj (of g) x := sorry

/-- Theorem 4-2-7 (2): if an HNN extension has an element of exact order `n`, then the base group
also has an element of exact order `n`. The positivity implicit in “exact order `n`” is recorded
by taking `n : ℕ+`. -/
-- Proof sketch: apply part `(1)` to a torsion element `x` of order `n`. Conjugate elements have
-- the same order, and the canonical embedding `HNNExtension.of` preserves order because it is
-- injective. Therefore the conjugate base element supplied by part `(1)` has order exactly `n`.
theorem exists_base_orderOf_eq_of_exists_hnnExtension_orderOf_eq (n : ℕ+)
    (hx : ∃ x : E, orderOf x = n) :
    ∃ g : G, orderOf g = n := by
  rcases hx with ⟨x, hx⟩
  have hfin : IsOfFinOrder x := by
    rw [← orderOf_pos_iff, hx]
    exact n.pos
  obtain ⟨g, hconj⟩ := exists_base_isConj_of_hnnExtension_isOfFinOrder x hfin
  refine ⟨g, ?_⟩
  calc
    orderOf g = orderOf (of g : E) := by
      symm
      simpa using orderOf_injective of (HNNExtension.of_injective φ) g
    _ = orderOf x := by
      rcases hconj with ⟨c, hc⟩
      simpa using SemiconjBy.orderOf_eq (↑c) hc
    _ = n := hx

end
