/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_1_4
import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_2_9

-- Declarations for this item will be appended below by the statement pipeline.

universe uA uG uH

set_option autoImplicit false

open Monoid
open Monoid.CoprodI Monoid.PushoutI
open MulEquiv

attribute [-instance] Monoid.CoprodI.twoFactorFamilyMonoid

section

variable {A : Type uA} {G : Type uG} {H : Type uH}
variable [Group A] [Group G] [Group H]
variable (φG : A →* G) (φH : A →* H)

local notation "Family" => Monoid.CoprodI.twoFactorFamily G H
local notation "Maps" => Monoid.CoprodI.twoFactorAmalgamatingMaps φG φH
local notation "P" => PushoutI Maps
local notation "W" => Word Family

/-!
Primary domain: free products with amalgamation and their normal forms.

Layer triage:
- `source-facing`: a reduced alternating word in the two-factor amalgamated product together with
  the textbook conclusion that a nonempty reduced word represents a nontrivial element.
- `core/canonical`: `Monoid.PushoutI` for the amalgamated product, `Monoid.PushoutI.Reduced` for
  the owner-side reducedness predicate, `Monoid.PushoutI.ofCoprodI` for evaluating a coproduct word
  in the pushout, and `Monoid.PushoutI.of_injective` for the factor embeddings.
- `bridge/view`: `Monoid.PushoutI.TwoFactorReduced` from `Definition_4_2_9` is the generic
  `Bool`-indexed bridge from the textbook two-factor reduced-word condition to the canonical
  predicate `Monoid.PushoutI.Reduced`, while
  `Subgroup.amalgamatedProductAlong.Reduced` is the subgroup-specialized source-facing owner for
  Definition `4-2-9`.

Domain sampling:
1. `Monoid.PushoutI.Reduced.eq_empty_of_mem_range` is the canonical normal-form theorem saying a
   nonempty reduced coproduct word cannot lie in the image of the base group.
2. `Monoid.PushoutI.of_injective` is the canonical injectivity theorem for the factor maps into an
   amalgamated product when the amalgamating maps are injective.
3. `Monoid.CoprodI.twoFactorAmalgamatingMaps` from `Definition_4_2_9` is the project owner for the
   two-factor pushout diagram and should be reused here instead of rebuilt locally.
4. `Monoid.PushoutI.TwoFactorReduced` is the generic bridge predicate used away from the subgroup
   specialization.

Primitive vs. derived:
the primitive public inputs are the common group `A`, the two factor groups `G` and `H`, the maps
`φG : A →* G` and `φH : A →* H`, and a source-facing reduced word `w`. The pushout `P`, the
evaluation map of `w` in `P`, and the two factor embeddings are canonical derived objects, while
the generic reducedness bridge is imported from `Definition_4_2_9` rather than duplicated locally.
-/

/-- Theorem 4-2-10: a reduced sequence of positive length in a free product with amalgamation
represents a nontrivial element of the pushout. -/
-- Proof sketch: if the reduced word has length one, its unique letter is already nontrivial
-- because `Monoid.CoprodI.Word` stores only nonidentity syllables. If the length is greater than
-- one, the source-facing reducedness condition identifies with the canonical
-- predicate `Monoid.PushoutI.Reduced`, via
-- `Monoid.PushoutI.twoFactorReduced_iff_of_one_lt_length`, and the pushout normal-form theorem
-- `Reduced.eq_empty_of_mem_range` rules out the product being the identity.
theorem reduced_sequence_prod_ne_one
    (hφG : Function.Injective φG) (hφH : Function.Injective φH)
    {word : W}
    (hw : TwoFactorReduced φG φH word)
    (hn : 1 ≤ word.toList.length) :
    PushoutI.ofCoprodI word.prod ≠ (1 : P) := sorry

end

section

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
variable {A : Subgroup G} {B : Subgroup H}

namespace Subgroup.amalgamatedProductAlong

open Subgroup.amalgamatedProductAlong

variable (e : A ≃* B)

local notation "Family" => Monoid.CoprodI.twoFactorFamily G H
local notation "ιA" => A.subtype
local notation "ιB" => B.subtype.comp e.toMonoidHom
local notation "Maps" => Monoid.CoprodI.twoFactorAmalgamatingMaps ιA ιB

private theorem rightBaseMap_injective :
    Function.Injective (ιB : A →* H) := by
  intro a₁ a₂ h
  exact e.injective (Subtype.coe_injective h)

private theorem amalgamatingMaps_injective :
    ∀ b, Function.Injective (Maps b)
  | false => by
      change Function.Injective
        ((ulift.symm.toMonoidHom : G →* Family false).comp ιA)
      exact (ulift.symm : G ≃* Family false).injective.comp Subtype.coe_injective
  | true => by
      change Function.Injective
        ((ulift.symm.toMonoidHom : H →* Family true).comp ιB)
      exact (ulift.symm : H ≃* Family true).injective.comp (rightBaseMap_injective e)

/-- The canonical left embedding into `Subgroup.amalgamatedProductAlong e` is injective. -/
theorem left_injective :
    Function.Injective (left e : G →* Subgroup.amalgamatedProductAlong e) := by
  dsimp [left]
  exact (PushoutI.of_injective (amalgamatingMaps_injective e) false).comp
    (ulift.symm : G ≃* Family false).injective

/-- The canonical right embedding into `Subgroup.amalgamatedProductAlong e` is injective. -/
theorem right_injective :
    Function.Injective (right e : H →* Subgroup.amalgamatedProductAlong e) := by
  dsimp [right]
  exact (PushoutI.of_injective (amalgamatingMaps_injective e) true).comp
    (ulift.symm : H ≃* Family true).injective

end Subgroup.amalgamatedProductAlong

end
