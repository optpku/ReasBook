/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Monoid.Coprod
open Monoid.Coprod

/-- A split retraction of `R` onto the infinite cyclic group. -/
structure SplitToInfiniteCyclic (R : Type u) [Group R] where
  hom : R →* Multiplicative ℤ
  section_ : Multiplicative ℤ →* R
  id : hom.comp section_ = MonoidHom.id (Multiplicative ℤ)

instance (R : Type u) [Group R] : CoeOut (SplitToInfiniteCyclic R) (R →* Multiplicative ℤ) :=
  ⟨SplitToInfiniteCyclic.hom⟩

section

variable {F : Type u} {R : Type v}
variable [Group F] [Group R]

-- Primary domain: Section `8` ambient words in the free product `F ∗ R` and the canonical induced
-- coproduct maps obtained from split retractions of the parameter group `R` onto the infinite
-- cyclic group.
-- Layer triage:
-- `source-facing`: a Section `8` ambient word `w : F ∗ R` together with the assertion that if all
-- its specializations along split retractions `R ⟶ Multiplicative ℤ` are trivial, then `w = 1`.
-- `core/canonical`: `F ∗ R` is the owner ambient object, `map (MonoidHom.id F)` is the canonical
-- induced coproduct map from a homomorphism on the parameter factor, and a split retraction is
-- recorded canonically by its homomorphism, section, and the identity `hom.comp section_ = id`.
-- `bridge/view`: later one-variable evaluation in Proposition `1-8-3` composes this canonical
-- induced map with `lift (MonoidHom.id F) (zpowersHom F x)`, but that evaluation layer is derived
-- from the coproduct owner map below.
-- Domain sampling:
-- 1. `F ∗ R` is the chapter/mathlib owner for Section `8` parametric words; compare Proposition
--    `1-8-3`.
-- 2. `map (MonoidHom.id F)` is the canonical induced map on a coproduct word when only the
--    parameter factor changes.
-- 3. The canonical algebraic content of a split retraction is a homomorphism with a specified
--    section and identity equation, avoiding the earlier existential witness packaging.
-- 4. Proposition `1-8-3` evaluates parametric words by first applying exactly this coproduct map
--    and then the one-variable evaluation homomorphism.
-- Primitive vs. derived:
-- the primitive source data are the ambient word `w : F ∗ R` and the split retractions of `R`
-- onto `Multiplicative ℤ`. The induced coproduct homomorphism is derived canonically by
-- `Monoid.Coprod.map`; there is no extra wrapper predicate in the public API beyond the
-- proposition's own statement.

/-- The canonical Section `8` coproduct homomorphism induced by a split retraction of the
parameter factor `R` onto the infinite cyclic group. -/
def inducedSplitRetraction (ρ : SplitToInfiniteCyclic R) : F ∗ R →* F ∗ Multiplicative ℤ :=
  map (MonoidHom.id F) ρ.hom

/-- The family of Section `8` induced maps obtained from split retractions of `R` onto the
infinite cyclic group. This is the canonical function family to which the separation hypothesis is
applied. -/
def inducedRetractionMaps (F : Type u) [Group F] (R : Type v) [Group R] :
    Set (F ∗ R → F ∗ Multiplicative ℤ) :=
  Set.range fun ρ : SplitToInfiniteCyclic R ↦
    (inducedSplitRetraction ρ : F ∗ R → F ∗ Multiplicative ℤ)

/-- Proposition 1-8-1: if a Section `8` ambient word maps to `1` under every induced homomorphism
coming from a split retraction of `R` onto the infinite cyclic group, and those induced maps
separate points of `F ∗ R`, then the word itself is `1`. -/
-- Proof sketch: if `w ≠ 1`, point separation for the family of induced maps provides one split
-- retraction whose induced map takes `w` away from the value at `1`. Since every monoid
-- homomorphism sends `1` to `1`, this contradicts the universal vanishing hypothesis.
theorem eq_one_of_forall_induced_retraction_eq_one
    (hsep : (inducedRetractionMaps F R).SeparatesPoints)
    (w : F ∗ R)
    (hw : ∀ ρ : SplitToInfiniteCyclic R, inducedSplitRetraction ρ w = 1) :
    w = 1 := by
  by_contra hw_ne
  rcases hsep hw_ne with ⟨f, ⟨ρ, rfl⟩, hf⟩
  exact hf (by simpa using hw ρ)

end
