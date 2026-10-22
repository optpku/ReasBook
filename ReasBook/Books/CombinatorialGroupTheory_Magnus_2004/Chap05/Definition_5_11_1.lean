/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_11_2
import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_1_4
import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_2_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

set_option autoImplicit false

open Monoid.CoprodI
open Monoid.PushoutI
open Monoid.PushoutI.NormalWord

attribute [-instance] Monoid.CoprodI.twoFactorFamilyMonoid

namespace Subgroup.amalgamatedProductAlong

section

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {A : Subgroup G} {B : Subgroup H} (e : A ≃* B)

local notation "Family" => Monoid.CoprodI.twoFactorFamily G H
local notation "Maps" =>
  Monoid.CoprodI.twoFactorAmalgamatingMaps A.subtype (B.subtype.comp e.toMonoidHom)
local notation "W" => Word Family
local notation "P" => Subgroup.amalgamatedProductAlong e

-- Primary domain: normal forms in free products with amalgamation.
-- Layer triage:
-- `source-facing`: a normal form of one fixed nontrivial element in the amalgamated product,
-- recorded as a reduced alternating word that evaluates to that element.
-- `core/canonical`: `Subgroup.amalgamatedProductAlong e` for the ambient amalgamated product,
-- `Subgroup.amalgamatedProductAlong.Reduced` for the source reduced-word predicate,
-- `Subgroup.amalgamatedProductAlong.ofWord e` for evaluation of a word in the amalgamated
-- product, and `Monoid.PushoutI.syllableLength` for the chosen-transversal owner length on the
-- ambient pushout.
-- `bridge/view`: the textbook phrase “normal form of `w`” is the conjunction that the source
-- reduced word represents the chosen element `w`; no second word owner is introduced.
--
-- Domain sampling:
-- 1. `Subgroup.amalgamatedProductAlong e` is the chapter-facing owner for a two-factor
--    amalgamated product.
-- 2. `Subgroup.amalgamatedProductAlong.Reduced e` already encodes exactly the source condition
--    that successive syllables come from different factors and that syllables from the
--    amalgamated subgroup are allowed only in the length-one case.
-- 3. `Subgroup.amalgamatedProductAlong.ofWord e` is the canonical evaluation map from a reduced
--    factor word to the represented element of the amalgamated product.
-- 4. `Monoid.PushoutI.syllableLength` is the chapter's canonical owner for the chosen-transversal
--    normal-form length, and the source length here differs from it only by the length-one
--    convention for nontrivial elements of the amalgamated subgroup.
--
-- Primitive vs. derived:
-- the primitive public inputs are the amalgamating identification `e`, the represented element
-- `w : P`, and the reduced word `u : W`. The textbook notion “`u` is a normal form of `w`” is the
-- derived conjunction that `u` is reduced and evaluates to `w`, together with the source
-- restriction `w ≠ 1`. The uniqueness-of-length statement is derived through the canonical owner
-- `syllableLength`, not by a second parallel length API.

/-- Definition 5-11-1: if `w ≠ 1` is an element of the free product of `G` and `H` with `A` and
`B` amalgamated along `e`, then a normal form of `w` is a reduced alternating word in the two
factors whose product is `w`. The length-one exception for letters lying in the amalgamated part
is already built into `Reduced e`. -/
def IsNormalForm (w : P) (u : W) : Prop :=
  w ≠ 1 ∧ Reduced e u ∧ ofWord e u = w

private theorem maps_injective : ∀ b, Function.Injective (Maps b)
  | false => by
      intro a₁ a₂ h
      exact Subtype.ext <| congrArg ULift.down h
  | true => by
      intro a₁ a₂ h
      exact e.injective <| Subtype.ext <| congrArg ULift.down h

/-- A source normal form has the canonical pushout syllable length, except that a nontrivial
element of the amalgamated subgroup is counted as one syllable in the source convention. -/
-- Proof sketch: choose a transversal for the amalgamated product and compare `u` with the
-- canonical `NormalWord` of `w`. Away from the amalgamated subgroup, `u` and the canonical normal
-- word have the same factor pattern, so they have the same syllable count. If `w` lies in the
-- amalgamated subgroup, the chosen normal word has syllable length `0`, while the source
-- convention records the unique nontrivial base syllable, producing `max 1 0 = 1`.
theorem length_eq_max_one_syllableLength
    (d : NormalWord.Transversal Maps)
    {w : P} {u : W}
    (hu : IsNormalForm e w u) :
    u.toList.length = max 1 (syllableLength d w) := sorry

/-- Any two normal forms of the same nontrivial element have the same syllable length. -/
theorem length_eq_of_isNormalForm
    {w : P} {u v : W}
    (hu : IsNormalForm e w u)
    (hv : IsNormalForm e w v) :
    u.toList.length = v.toList.length := by
  obtain ⟨d⟩ := transversal_nonempty Maps (maps_injective e)
  rw [length_eq_max_one_syllableLength e d hu, length_eq_max_one_syllableLength e d hv]

end

end Subgroup.amalgamatedProductAlong
