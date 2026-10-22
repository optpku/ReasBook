/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_2_3
import CombinatorialGroupTheory_Magnus_2004.Chap04.Lemma_4_2_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

open HNNExtension
open HNNExtension.NormalWord
open HNNExtension.NormalWord.ReducedWord

section

variable {G : Type u} [Group G]
variable {A B : Subgroup G} {φ : A ≃* B}

/-!
Primary domain: HNN extensions and the normal form theorem.

Layer triage:
- `source-facing`: the textbook asserts three atomic facts for an HNN extension:
  the base group embeds, a reduced word with at least one stable letter is nontrivial,
  and every element has a unique normal form.
- `core/canonical`: `HNNExtension.of_injective`,
  `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`, and
  `HNNExtension.NormalWord.equiv φ.symm d`.
- `bridge/view`: the textbook phrase “normal form” depends on the chosen right-coset
  representatives from Definition `4-2-3`, so part `(II)` is expressed relative to a
  source-facing `TransversalPair G B A`, while part `(I)` is the source-convention consequence of
  Britton's lemma obtained through `ReducedWord.toHNNExtension`.

Domain sampling:
1. `HNNExtension.of_injective` is mathlib's canonical embedding theorem for the base group.
2. `reducedWord_toHNNExtension_ne_one_of_toList_ne_nil` from Lemma `4-2-2` is the chapter's
   source-facing Britton bridge in the original stable-letter convention.
3. `HNNExtension.NormalWord.equiv φ.symm d` is the canonical normal-form equivalence for the
   swapped convention, and `HNNExtension.swapEquiv φ` transports it back to the original HNN
   extension.

Primitive vs. derived:
- primitive source data: the base group `G`, the subgroups `A`, `B`, the isomorphism `φ`,
  and for part `(II)` a transversal pair `d`;
- derived API: the embedding statement, the Britton nontriviality statement, and the unique
  normal-form correspondence, with part `(I)`'s second sentence expressed as a thin
  source-facing consequence of Britton's lemma.
-/

/- The canonical embedding clause of the HNN normal-form theorem: the map `g ↦ g` embeds the base
group `G` into the HNN extension.

This clause is already exactly mathlib's theorem `HNNExtension.of_injective`. -/
#check ((of_injective φ : Function.Injective (of : G → HNNExtension G A B φ)))

/-- Theorem 4-2-4: part (I), if a reduced HNN word represents the identity, then it contains
no stable-letter syllables. Equivalently, a reduced sequence with `n ≥ 1` cannot equal `1`. -/
theorem reducedWord_toList_eq_nil_of_toHNNExtension_eq_one
    (w : ReducedWord G B A) (hprod : w.toHNNExtension φ = 1) :
    w.toList = [] := by
  by_contra hnil
  exact (reducedWord_toHNNExtension_ne_one_of_toList_ne_nil w hnil) hprod

variable (d : TransversalPair G B A)

/- The chosen-transversal clause of the HNN normal-form theorem: once a transversal pair of
right-coset representatives is chosen, every element of the HNN extension has a unique normal
form.

This clause is encoded by transporting the canonical equivalence
`HNNExtension.NormalWord.equiv φ.symm d` for the swapped convention along
`HNNExtension.swapEquiv φ`.
-/
#check (((swapEquiv φ).toEquiv.symm.trans (equiv φ.symm d)) :
  HNNExtension G A B φ ≃ HNNExtension.NormalWord d)

end
