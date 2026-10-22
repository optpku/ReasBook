/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

open List
open HNNExtension
open HNNExtension.NormalWord

section

variable {G : Type u} [Group G]
variable {A B : Subgroup G} {φ : A ≃* B}

/-!
Primary domain: conjugacy theory for HNN extensions.

Layer triage:
- `source-facing`: cyclically reduced reduced words in an HNN extension and the conjugacy theorem
  describing conjugate such words by cyclic permutation and conjugation by an element of `A` or
  `B`.
- `core/canonical`: `HNNExtension.NormalWord.ReducedWord G B A`, its bridge evaluation map
  `ReducedWord.toHNNExtension`, and the group-theoretic conjugacy relation `IsConj`.
- `bridge/view`: the textbook cyclic sequence attached to a reduced HNN word is the derived list
  obtained by merging the initial base term into the terminal syllable. Cyclic permutation is
  then the canonical list-rotation relation `List.IsRotated` on that derived list, while
  conjugation by an element of the base group is expressed by the canonical embedding
  `HNNExtension.of`.

Domain sampling:
1. `HNNExtension.NormalWord.ReducedWord G B A` is mathlib's owner abstraction for reduced HNN
   words in the source stable-letter convention.
2. `ReducedWord.toHNNExtension φ` is the project bridge evaluating such a source word in
   `HNNExtension G A B φ`.
3. `IsConj` is the canonical conjugacy relation in a group.
4. `List.IsRotated` is the canonical list-level owner relation encoding cyclic permutation of the
   source-facing cyclic syllable list.

Primitive vs. derived:
- primitive public data: reduced HNN words `u` and `v`;
- derived bridge data: the private cyclic syllable list obtained by absorbing the initial base
  term into the terminal syllable;
- derived source-facing notions: cyclic permutation and cyclically reducedness, expressed directly
  in terms of reduced words, the canonical rotation relation on that cyclic syllable list, and the
  cyclic boundary no-pinch condition;
- derived conclusion: equality of stable-letter lengths together with the existence of a cyclic
  permutation of `v`, an explicit terminal stable-letter sign `ε`, and a conjugator
  `z : toSubgroup B A ε` whose image in the HNN extension conjugates that cyclic permutation to
  `u.toHNNExtension φ`.
-/

namespace HNNExtension.NormalWord

namespace ReducedWord

local notation "W" => ReducedWord G B A

private def cyclicData (w : W) : List (ℤˣ × G) :=
  match w.toList.getLast? with
  | none => []
  | some (ε, g) => w.toList.dropLast ++ [(ε, g * w.head)]

/-- One cyclically reduced HNN word is obtained from another by cyclic permutation when their
source-facing cyclic syllable lists differ by a list rotation; in the zero-syllable case this
reduces to equality of the base-group words. -/
def IsCyclicPermutation (u v : W) : Prop :=
  match u.toList.getLast?, v.toList.getLast? with
  | none, none => u.head = v.head
  | some _, some _ => cyclicData u ~r cyclicData v
  | _, _ => False

/-- A reduced HNN word is cyclically reduced when its cyclic syllable list has no boundary pinch.
For a word with no stable-letter syllables, this condition is vacuous. -/
def IsCyclicallyReduced (w : W) : Prop :=
  ∀ {a b : ℤˣ × G},
    (cyclicData w).head? = some a →
      (cyclicData w).getLast? = some b →
        b.2 ∈ toSubgroup B A b.1 →
          a.1 = b.1

/-- Theorem 4-2-8 (1): conjugate cyclically reduced reduced words in an HNN extension with at
least one stable-letter syllable have the same stable-letter length. -/
-- Proof sketch: use cyclic reducedness of `v` to choose a reduced cyclic permutation whose final
-- stable-letter sign matches that of `u`, then apply Britton normal-form uniqueness to the
-- resulting conjugacy relation to identify the stable-letter pattern and hence the length.
theorem conjugacy_length_eq_of_isCyclicallyReduced
    (u v : W) (hu_nonempty : u.toList ≠ [])
    (hu_cyclic : u.IsCyclicallyReduced) (hv_cyclic : v.IsCyclicallyReduced)
    (hconj : IsConj (u.toHNNExtension φ) (v.toHNNExtension φ)) :
    u.toList.length = v.toList.length := sorry

/-- Theorem 4-2-8 (2): under the same hypotheses, a suitable cyclic permutation of `v` is
conjugate to `u` by a base-group element lying in the subgroup determined by the final stable
letter of `u`. -/
-- Proof sketch: use cyclic reducedness of `v` to choose a reduced cyclic permutation `v'` whose
-- final stable-letter sign `ε` matches that of `u`; the conjugating element obtained from
-- Britton's analysis then lies directly in the canonical subgroup `toSubgroup B A ε`.
theorem exists_subgroupConjugator_of_isCyclicallyReduced
    (u v : W) (hu_nonempty : u.toList ≠ [])
    (hu_cyclic : u.IsCyclicallyReduced) (hv_cyclic : v.IsCyclicallyReduced)
    (hconj : IsConj (u.toHNNExtension φ) (v.toHNNExtension φ)) :
    ∃ ε : ℤˣ, ∃ z : toSubgroup B A ε, ∃ v' : W,
      v'.IsCyclicPermutation v ∧
        (∃ g : G, u.toList.getLast? = some (ε, g)) ∧
        (∃ g : G, v'.toList.getLast? = some (ε, g)) ∧
        u.toHNNExtension φ = of (z : G) * v'.toHNNExtension φ * (of (z : G))⁻¹ :=
  sorry

end ReducedWord

end HNNExtension.NormalWord

end
