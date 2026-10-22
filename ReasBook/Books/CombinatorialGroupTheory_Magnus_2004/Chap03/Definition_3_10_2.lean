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

namespace List

variable {G : Type u} [Group G]

/-!
Primary domain: finite list-valued Peiffer rewrites in a group.

Layer triage:
- `source-facing`: the first-kind Peiffer formula replacing an adjacent pair `(a, b)` by
  `(b, b⁻¹ * a * b)`.
- `core/canonical`: `List G` is the owner abstraction for a finite ordered sequence, and
  `List.IsAdjacentConjugatingSwap` is the chapter owner relation for the adjacent conjugating
  rewrite `(a, b) ↦ (a * b * a⁻¹, a)`.
- `bridge/view`: the first-kind source formula is exactly the converse relation
  `Function.swap IsAdjacentConjugatingSwap`, used downstream in the short form
  `IsAdjacentConjugatingSwap π' π`, so no parallel first-kind predicate is needed.

Domain sampling:
1. `List G` is the canonical owner for a finite sequence `(p₁, ..., pₙ)`.
2. `List.append` and list literals `[a, b]` give the cleanest source-faithful way to isolate an
   adjacent pair without separate index bookkeeping.
3. `List.prod` together with `List.prod_append` is the canonical aggregate API on a group-valued
   list.
4. `Function.swap` is the canonical owner-side operation for reversing a binary relation, so it
   captures the first-kind orientation without introducing a second predicate.
5. Group conjugation is represented directly by the standard term `a * b * a⁻¹`.

Primitive vs. derived:
- primitive data: the owner relation `IsAdjacentConjugatingSwap` on the two lists;
- derived API: the converse-owner recall `Function.swap IsAdjacentConjugatingSwap`, the
  source-facing bridge theorem below, and the owner invariants of length and total product.
-/

/-- The chapter owner relation for the adjacent conjugating rewrite used in Peiffer
transformations. -/
def IsAdjacentConjugatingSwap (π π' : List G) : Prop :=
  ∃ left right : List G, ∃ a b : G,
    π = left ++ [a, b] ++ right ∧
      π' = left ++ [a * b * a⁻¹, a] ++ right

/-- An adjacent conjugating swap preserves the length of the sequence. -/
theorem length_eq_of_isAdjacentConjugatingSwap {π π' : List G}
    (h : IsAdjacentConjugatingSwap π π') :
    π.length = π'.length := by
  rcases h with ⟨left, right, a, b, rfl, rfl⟩
  simp

/-- An adjacent conjugating swap preserves the total product of the sequence. -/
theorem prod_eq_of_isAdjacentConjugatingSwap {π π' : List G}
    (h : IsAdjacentConjugatingSwap π π') :
    π.prod = π'.prod := by
  rcases h with ⟨left, right, a, b, rfl, rfl⟩
  simp [List.prod_append, mul_assoc]

/- Definition 3-10-2: the textbook first-kind Peiffer transformation is the converse relation
`Function.swap List.IsAdjacentConjugatingSwap` of the chapter owner relation. -/
#check Function.swap IsAdjacentConjugatingSwap

/-- Definition 3-10-2 is canonically the converse orientation of the adjacent conjugating
swap. -/
theorem isPeifferTransformationFirstKind_iff (π π' : List G) :
    (∃ left right : List G, ∃ a b : G,
      π = left ++ [a, b] ++ right ∧
        π' = left ++ [b, b⁻¹ * a * b] ++ right) ↔
      IsAdjacentConjugatingSwap π' π := by
  constructor
  · rintro ⟨left, right, a, b, hπ, hπ'⟩
    refine ⟨left, right, b, b⁻¹ * a * b, hπ', ?_⟩
    simpa [mul_assoc] using hπ
  · rintro ⟨left, right, a, b, hπ', hπ⟩
    refine ⟨left, right, a * b * a⁻¹, a, hπ, ?_⟩
    simpa [mul_assoc] using hπ'

end List

end
