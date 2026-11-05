module

public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Presieve

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (F : Cᵒᵖ ⥤ Type v)

/- Domain-style sampling for Definition 7.47.10:
- primary domain: sheaf conditions for set-valued presheaves on a Grothendieck site, expressed via
  the Yoneda condition on covering sieves;
- sampled owner API:
  `CategoryTheory.Presheaf.IsSheaf`,
  `CategoryTheory.Presheaf.IsSheaf.isSheafFor`,
  `CategoryTheory.isSheaf_iff_isSheaf_of_type`,
  `CategoryTheory.Presieve.isSheaf_of_yoneda`;
- source/core/bridge triage:
  `source-facing`: the Stacks formulation that a presheaf on `(C, J)` is a sheaf iff every
  covering sieve satisfies the Yoneda sheaf condition;
  `core/canonical`: `CategoryTheory.Presheaf.IsSheaf J F`;
  `bridge/view`: the coverwise passage
  `Presheaf.IsSheaf.isSheafFor` + `isSheafFor_iff_yonedaSheafCondition`, and the converse bridge
  through `isSheaf_iff_isSheaf_of_type` + `Presieve.isSheaf_of_yoneda`.

Primitive data are only the site `(C, J)` and the set-valued presheaf `F`. The per-cover Yoneda
condition is derived API from the owner predicate `Presheaf.IsSheaf`, so this file should recall
that owner directly and keep the Yoneda formulation only as a thin companion theorem.
-/

/- Definition 7.47.10: for a set-valued presheaf `F` on the site `(C, J)`, the sheaf condition is
the canonical proposition `Presheaf.IsSheaf J F`. Equivalently, each covering sieve satisfies the
Yoneda sheaf condition, i.e. the canonical restriction map `Hom(h_U, F) → Hom(S, F)` is
bijective. -/
recall Presheaf.IsSheaf

/-- A set-valued presheaf on `(C, J)` is a sheaf exactly when every covering sieve satisfies the
Yoneda sheaf condition, equivalently when the canonical map `Hom(h_U, F) → Hom(S, F)` is
bijective. -/
theorem presheaf_isSheaf_iff_yonedaSheafCondition :
    Presheaf.IsSheaf J F ↔
      ∀ ⦃U : C⦄ (S : Sieve U) (_ : S ∈ J U), YonedaSheafCondition F S := by
  constructor
  · intro h U S hS
    exact isSheafFor_iff_yonedaSheafCondition.1 (h.isSheafFor S hS)
  · intro h
    rw [isSheaf_iff_isSheaf_of_type]
    exact isSheaf_of_yoneda J (fun {U} S hS ↦ h S hS)
