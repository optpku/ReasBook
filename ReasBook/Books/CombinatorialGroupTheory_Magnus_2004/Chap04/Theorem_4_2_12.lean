/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.PushoutI
import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_1_4
import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_2_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

open List
open Monoid
open Monoid.CoprodI Monoid.PushoutI

attribute [-instance] Monoid.CoprodI.twoFactorFamilyMonoid

namespace Monoid.CoprodI.Word

section

variable {A : Type u} {G : Type u} {H : Type u}
variable [Group A] [Group G] [Group H]

local notation "Family" => Monoid.CoprodI.twoFactorFamily G H
local notation "W" => Word Family

/-- A reduced word in a two-factor amalgamated product is cyclically reduced when it is reduced in
the sense of Definition `4-2-9`, and whenever its first and last syllables lie in the same
factor, the word has at most one syllable. -/
def IsCyclicallyReduced (φG : A →* G) (φH : A →* H) (w : W) : Prop :=
  Monoid.PushoutI.TwoFactorReduced φG φH w ∧
    ∀ {x y : Σ b, Family b}
      (_hx : w.toList.head? = some x)
      (_hy : w.toList.getLast? = some y)
      (_hxy : x.1 = y.1),
        w.toList.length ≤ 1

/-- A cyclically reduced reduced word with at least two syllables begins and ends in different
factors. -/
-- Proof sketch: apply the defining boundary condition in `IsCyclicallyReduced`. If the first and
-- last syllables came from the same factor, that condition would force the word to have length at
-- most `1`, contradicting the hypothesis `2 ≤ w.toList.length`.
theorem firstFactor_ne_lastFactor_of_isCyclicallyReduced_of_two_le
    (φG : A →* G) (φH : A →* H) {w : W}
    (hw : w.IsCyclicallyReduced φG φH) (hwlen : 2 ≤ w.toList.length)
    {x y : Σ b, Family b}
    (hx : w.toList.head? = some x) (hy : w.toList.getLast? = some y) :
    x.1 ≠ y.1 := by
  intro hxy
  have hlen : w.toList.length ≤ 1 := hw.2 hx hy hxy
  omega

end

end Monoid.CoprodI.Word

section

variable {G H : Type u} [Group G] [Group H]
variable {A : Subgroup G} {B : Subgroup H}
variable (e : A ≃* B)

open Subgroup.amalgamatedProductAlong

local notation "Family" => Monoid.CoprodI.twoFactorFamily G H
local notation "W" => Word Family
local notation "ιA" => A.subtype
local notation "ιB" => B.subtype.comp e.toMonoidHom

/-!
Primary domain: conjugacy in free products with amalgamation.

Layer triage:
- `source-facing`: cyclically reduced reduced words in the two-factor amalgamated product
  `⟨G * H; A = B, e⟩`, together with the statement that cyclically reduced
  conjugates of length at least `2` differ by cyclic permutation and conjugation from the
  amalgamated subgroup.
- `core/canonical`: `Monoid.CoprodI.Word` for reduced alternating words,
  `Monoid.PushoutI` for the amalgamated product, `Subgroup.amalgamatedProductAlong e` for the
  chapter-facing two-factor owner with named `left`, `right`, `base`, and `ofWord`,
  `Monoid.PushoutI.Reduced` for owner-side reducedness, `List.IsRotated` for cyclic permutation,
  and `IsConj` for conjugacy in the ambient group.
- `bridge/view`: `Monoid.PushoutI.TwoFactorReduced` is the generic `Bool`/`ULift` bridge, while
  `Subgroup.amalgamatedProductAlong.Reduced` is the subgroup-specialized source-facing
  reduced-word predicate from Definition `4-2-9`. The map
  `Subgroup.amalgamatedProductAlong.ofWord e` is the derived conversion from that presentation to
  the owner object. Chosen transversals and `NormalWord` realizations remain proof-internal via
  `Monoid.PushoutI.Reduced.exists_normalWord_prod_eq`.

Domain sampling:
1. `Monoid.CoprodI.Word` is the chapter's intrinsic owner for source reduced words in free-product
   style normal forms.
2. `Subgroup.amalgamatedProductAlong.Reduced` is the upstream source-facing reducedness predicate
   for two-factor amalgamated products over identified subgroups.
3. Proposition `3-12-5` already fixes the chapter owner pattern for two-factor amalgamated
   products: a named `Subgroup` owner with named embeddings rather than a raw `Bool`-indexed
   pushout surface.
4. `List.IsRotated` is the canonical owner for cyclic permutation of syllable lists.

Primitive vs. derived:
the primitive public data are the two factors `G`, `H`, the amalgamating subgroups `A` and `B`,
the identification `e : A ≃* B`, and the source reduced words `u` and `v`. Reducedness and
cyclic reducedness are expressed directly on those words. The owner
`Subgroup.amalgamatedProductAlong e`, its canonical embeddings, and word evaluation are derived
operations.
-/

/-- Theorem 4-2-12: in the free product with amalgamation of `G` and `H`
over `A = B` via `e`, if a reduced word `u` is cyclically reduced and has at least two syllables,
then every cyclically reduced conjugate reduced word `v` is obtained by cyclically permuting the
syllables of `u` and then conjugating by an element of the amalgamated subgroup `A`. -/
-- Proof sketch: pass from the source reduced words to chosen normal forms only internally, using
-- the canonical existence theorem `Reduced.exists_normalWord_prod_eq`. The conjugacy theorem for
-- amalgamated products applied to those normal forms shows that a cyclically reduced conjugate of
-- a cyclically reduced word of length at least two can only arise from rotating the syllable list
-- and then conjugating by an element of the amalgamated subgroup. Translating back to the source
-- reduced-word layer yields the stated conclusion.
theorem exists_amalgamatedConjugator_and_cyclicPermutation_of_isConj_of_cyclicallyReduced
    {u v : W}
    (hu : u.IsCyclicallyReduced ιA ιB)
    (hu_len : 2 ≤ u.toList.length)
    (hv : v.IsCyclicallyReduced ιA ιB)
    (hconj : IsConj (ofWord e u) (ofWord e v)) :
    ∃ a : A, ∃ w : W,
      u.toList ~r w.toList ∧
        ofWord e v = (base e a)⁻¹ * ofWord e w * base e a := sorry

end
