module

import Mathlib.Tactic.Recall
public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

open Bicategory

/- Domain-style sampling for Definition 4.30.1:
- primary domain: bicategorical `(2,1)`-categories, i.e. locally groupoidal bicategories;
- sampled owner-level declarations:
  `Bicategory.IsLocallyGroupoid`,
  `CategoryTheory.IsGroupoid`,
  `CategoryTheory.IsGroupoid.all_isIso`,
  `CategoryTheory.Groupoid.ofIsGroupoid`;
- best owner abstraction: `Bicategory.IsLocallyGroupoid` is the canonical Prop-valued owner for
  the `(2,1)` condition on a bicategory;
- primitive data: for each pair of objects `a b : B`, the hom-category `a ⟶ b` carries the
  canonical owner predicate `IsGroupoid (a ⟶ b)`;
- derived API: the textbook reformulation saying every `2`-morphism is invertible via
  `IsGroupoid.all_isIso`, together with canonical downstream constructions such as `Pith`.

Source/core/bridge triage:
- `source-facing`: the textbook wording that every `2`-morphism is invertible;
- `core/canonical`: `Bicategory.IsLocallyGroupoid`;
- `bridge/view`: the pointwise consequence `IsGroupoid.all_isIso` on each hom-category. -/

/- Definition 4.30.1: the new content of a `(2,1)`-category, beyond the strictness condition from
Definition 4.29.1, is exactly the canonical mathlib predicate `IsLocallyGroupoid B`. Thus the
textbook notion is expressed by the pair of assumptions `[Strict B] [IsLocallyGroupoid B]`. -/
recall IsLocallyGroupoid

end CategoryTheory
