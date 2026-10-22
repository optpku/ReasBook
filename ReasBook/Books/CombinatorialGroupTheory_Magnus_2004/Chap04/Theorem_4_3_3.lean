/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

section

variable (C : Type u) [Group C] [Countable C]

/-!
Primary domain: countable groups and conjugacy-preserving embedding theorems.

Layer triage:
- `source-facing`: a countable group `C`, an embedding of `C` into a countable ambient group `G`,
  and the conclusion that every two elements of `G` with the same order are conjugate.
- `core/canonical`: `Countable` for countability, `C →* G` with `Function.Injective` for an
  embedding, `orderOf` for element order, and `IsConj` for conjugacy.
- `bridge/view`: the textbook phrase “`C` can be embedded in `G`” is expressed directly by an
  injective group homomorphism, so no auxiliary wrapper notion is needed.

Domain sampling:
1. `Countable` is the canonical owner for countability of a type in mathlib.
2. `MonoidHom` together with `Function.Injective` is the chapter owner for group embeddings, while
   `MonoidHom.ofInjective` is only the derived bridge to the image subgroup.
3. `orderOf` is the canonical owner API for exact order in a group, with infinite order recorded
   as `0`.
4. `IsConj` is mathlib's canonical relation for conjugacy in a group.

Primitive vs. derived:
- primitive public data: the source group `C`, the ambient group `G`, and an injective homomorphism
  `C →* G`;
- derived property: the ambient conclusion that equality of `orderOf` forces conjugacy in `G`.
-/

/-- Theorem 4-3-3: every countable group embeds in a countable group in which any two elements of
the same order are conjugate. -/
-- Proof sketch: first adjoin stable letters so that every ordered pair of elements of `C` with
-- the same order becomes conjugate inside a countable overgroup. Then iterate that construction
-- along the natural numbers, applying it at stage `i + 1` to the group built at stage `i`.
-- The union of the resulting countable chain is again countable, contains the original group by
-- the composite embedding, and ensures that any two elements with equal order are conjugate.
theorem countable_group_embeds_in_countable_group_with_orderOf_eq_isConj :
    ∃ (G : Type u) (_ : Group G) (_ : Countable G) (f : C →* G),
      Function.Injective f ∧ ∀ x y : G, orderOf x = orderOf y → IsConj x y := sorry

end
