/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.Algebra.Group.Conj

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

section

variable {F : Type u} [Group F]

/-!
Primary domain: small-cancellation relator conditions stated via group conjugacy.

Layer triage:
- `source-facing`: a relator set `R : Set F` satisfying the textbook condition that no relator
  `r ∈ R` is conjugate in `F` to its inverse.
- `core/canonical`: `IsConj` is mathlib's owner relation for group conjugacy, and
  `ConjClasses.mk_eq_mk_iff_isConj` is the canonical conjugacy-class reformulation.
- `bridge/view`: the set-level predicate `Set.SatisfiesConditionJ` packages the source condition on
  `R` without adding auxiliary witness data.

Domain sampling:
1. `IsConj` from `Mathlib.Algebra.Group.Conj` is the canonical owner relation for conjugacy.
2. `isConj_iff` is the canonical witness-level expansion of `IsConj`.
3. `ConjClasses.mk_eq_mk_iff_isConj` shows the equivalent conjugacy-class view, but the source
   sentence is most faithful when stated directly with `IsConj`.
4. Project files such as Proposition `2-5-7` and Proposition `2-5-14` already phrase
   “conjugate to the inverse” directly via `IsConj _ _⁻¹`, so the chapter's owner vocabulary is
   already aligned with `IsConj`.

Primitive vs. derived:
- primitive public data: the relator set `R`;
- derived API: the membership consequence `¬ IsConj r r⁻¹` for each `r ∈ R`.
-/

namespace Set

/-- Definition 5-9-7: Condition `J` for a relator set `R` says that no relator in `R` is
conjugate to its inverse. -/
def SatisfiesConditionJ (R : Set F) : Prop :=
  ∀ ⦃r : F⦄, r ∈ R → ¬ IsConj r r⁻¹

end Set

notation:55 "J[" R "]" => Set.SatisfiesConditionJ R

namespace Set.SatisfiesConditionJ

/-- Any relator in a set satisfying Condition `J` is not conjugate to its inverse. -/
theorem not_isConj_inv {R : Set F} (hR : J[R]) {r : F} (hr : r ∈ R) :
    ¬ IsConj r r⁻¹ :=
  hR hr

end Set.SatisfiesConditionJ

end
