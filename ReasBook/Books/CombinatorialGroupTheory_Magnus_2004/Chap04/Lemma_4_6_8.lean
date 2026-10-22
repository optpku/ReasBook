/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_1_4
import CombinatorialGroupTheory_Magnus_2004.Chap04.Theorem_4_2_8
import CombinatorialGroupTheory_Magnus_2004.Chap04.Theorem_4_2_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

open Monoid.CoprodI
open Monoid.CoprodI.Word
open HNNExtension
open HNNExtension.NormalWord
open scoped Pointwise

attribute [-instance] Monoid.CoprodI.twoFactorFamilyMonoid

/-!
Primary domain: subgroup structure of free products with amalgamation and HNN extensions.

Layer triage:
- `source-facing`: a finitely generated subgroup of an amalgamated free product or an HNN
  extension, together with the dichotomy that it either lies in a conjugate of a factor/base or a
  conjugate of it contains a cyclically reduced element of length at least `2`.
- `core/canonical`: `Subgroup.amalgamatedProductAlong` with its factor embeddings `left` and
  `right`, `HNNExtension` with its base embedding `of`, subgroup conjugation via `MulAut.conj •`,
  and the chapter's cyclically reduced word owners
  `Monoid.CoprodI.Word.IsCyclicallyReduced` and
  `HNNExtension.NormalWord.ReducedWord.IsCyclicallyReduced`.
- `bridge/view`: the textbook "cyclically reduced element of length at least two" is rendered by
  the existence of a cyclically reduced reduced word of syllable-list length at least `2` whose
  canonical evaluation lies in a conjugate of the subgroup.

Domain sampling:
1. `Subgroup.amalgamatedProductAlong`, together with
   `Subgroup.amalgamatedProductAlong.left`, `right`, and `ofWord`, is the chapter-facing owner for
   free products with amalgamation.
2. `Monoid.CoprodI.Word.IsCyclicallyReduced` from Theorem `4-2-12` is the project owner for
   cyclically reduced source words in an amalgamated product.
3. `HNNExtension.NormalWord.ReducedWord G B A` and `ReducedWord.toHNNExtension` are the source
   owner and evaluation bridge for HNN normal words, while `ReducedWord.IsCyclicallyReduced` from
   Theorem `4-2-8` is the project owner for cyclic reducedness.
4. `MulAut.conj p • K` is the canonical expression for a conjugate subgroup.

Primitive vs. derived:
the primitive public data are the ambient amalgamated product or HNN extension, the subgroup
`K`, and the finite-generation hypothesis `K.FG`. The conjugate factor/base subgroups and the
existence of a cyclically reduced element are stated directly in terms of the canonical owner-side
embeddings and reduced-word APIs, without introducing any extra package or surrogate notion.
-/

section AmalgamatedProduct

variable {G1 : Type u} {G2 : Type u} [Group G1] [Group G2]
variable {A : Subgroup G1} {B : Subgroup G2} (e : A ≃* B)

open Subgroup.amalgamatedProductAlong

local notation "P" => Subgroup.amalgamatedProductAlong e
local notation "Family" => Monoid.CoprodI.twoFactorFamily G1 G2
local notation "W" => Word Family
local notation "ιA" => A.subtype
local notation "ιB" => B.subtype.comp e.toMonoidHom

/-- Lemma 4-6-8 (1): a finitely generated subgroup of a nontrivial free product with amalgamation
is either contained in a conjugate of one of the two factor subgroups, or some conjugate of that
subgroup contains a cyclically reduced element represented by a reduced word of length at least
two. -/
-- Proof sketch: induct on the sum of the normal-form lengths of a finite generating set of the
-- subgroup. If every generator has length `1`, the subgroup lies in a conjugate of one factor.
-- Otherwise, after conjugating so that all generators begin and end in the same factor, one
-- shortens the total length by peeling off a common initial syllable. If this reduction process
-- ever fails, a product of two generators yields a cyclically reduced word of length at least `2`
-- inside a conjugate of the subgroup.
theorem subgroup_le_conjugate_factor_or_exists_cyclicallyReduced_conjugate_amalgamatedProductAlong
    (K : Subgroup P) (hK : K.FG) :
    (∃ p : P, K ≤ MulAut.conj p • (left e).range) ∨
      (∃ p : P, K ≤ MulAut.conj p • (right e).range) ∨
      ∃ p : P, ∃ w : W,
        w.IsCyclicallyReduced ιA ιB ∧
          2 ≤ w.toList.length ∧
          ofWord e w ∈ MulAut.conj p • K := sorry

end AmalgamatedProduct

section HNN

variable {G : Type u} [Group G]
variable {A B : Subgroup G} {φ : A ≃* B}

local notation "E" => HNNExtension G A B φ
local notation "of" => (HNNExtension.of : G →* E)

/-- Lemma 4-6-8 (2): a finitely generated subgroup of an HNN extension is either contained in a
conjugate of the embedded base group, or some conjugate of that subgroup contains a cyclically
reduced HNN word with at least two stable-letter syllables. -/
-- Proof sketch: repeat the amalgamated-product induction with Britton normal forms in place of
-- free-product normal forms. If every generator has no stable-letter syllable, the subgroup lies
-- in a conjugate of the base. Otherwise, conjugating by a suitable initial base syllable reduces
-- the total stable-letter length unless one already obtains a cyclically reduced HNN word of
-- length at least `2` in a conjugate of the subgroup.
theorem subgroup_le_conjugate_base_or_exists_cyclicallyReduced_conjugate_hnnExtension
    (K : Subgroup E) (hK : K.FG) :
    (∃ p : E, K ≤ MulAut.conj p • (of).range) ∨
      ∃ p : E, ∃ w : ReducedWord G B A,
        w.IsCyclicallyReduced ∧
          2 ≤ w.toList.length ∧
          w.toHNNExtension φ ∈ MulAut.conj p • K := sorry

end HNN
