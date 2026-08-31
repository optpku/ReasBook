module

public import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Lemma 4.21.7:
- primary domain: cofiltered and inverse systems of finite nonempty types, expressed through
  sections of `Type`-valued diagrams;
- relevant owner declarations inspected:
  - `nonempty_sections_of_finite_cofiltered_system.init` in
    `Mathlib/CategoryTheory/CofilteredSystem.lean`,
  - `nonempty_sections_of_finite_cofiltered_system` in
    `Mathlib/CategoryTheory/CofilteredSystem.lean`,
  - `nonempty_sections_of_finite_inverse_system` in
    `Mathlib/CategoryTheory/CofilteredSystem.lean`,
  - the chapter-level inverse-system owner expression `Iᵒᵈ ⥤ C` in `Definition_4_21_4`.
- best owner abstraction:
  - `source-facing`: the inverse-limit nonemptiness statement for a directed inverse system,
  - `core/canonical`: `nonempty_sections_of_finite_inverse_system`,
  - `bridge/view`: `nonempty_sections_of_finite_cofiltered_system` as the more general cofiltered
    owner theorem specialized to thin categories of directed preorders.
- primitive data: a diagram `F : Jᵒᵖ ⥤ Type v` together with the instance assumptions that each
  stage is finite and nonempty;
- derived API: the proposition `F.sections.Nonempty` and the cofiltered generalization. -/

/-
Source/core/bridge triage for Lemma 4.21.7:
- `source-facing`: a directed inverse system of finite nonempty sets has a nonempty inverse limit.
- `core/canonical`: `nonempty_sections_of_finite_inverse_system`, with
  `nonempty_sections_of_finite_cofiltered_system` as the general cofiltered owner theorem.
- `bridge/view`: the inverse-system statement is the preorder-specialized companion of the
  cofiltered theorem from `Mathlib.CategoryTheory.CofilteredSystem`.
-/

/- Lemma 4.21.7: a directed inverse system of finite nonempty sets has a nonempty inverse limit.
This is exactly the canonical mathlib theorem `nonempty_sections_of_finite_inverse_system`. -/
recall nonempty_sections_of_finite_inverse_system

/- General companion: the same statement for an arbitrary cofiltered diagram of finite nonempty
sets is exactly the canonical theorem `nonempty_sections_of_finite_cofiltered_system`. -/
recall nonempty_sections_of_finite_cofiltered_system
