module

public import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v w

section

variable {C : Type u} [Category.{v} C]

/-
Source/core/bridge triage for Definition 7.3.3:
- source-facing notion: a subpresheaf of a set-valued presheaf
- core/canonical owner: `CategoryTheory.Subfunctor`
- primitive data: for each object `U`, a subset `𝒢.obj U : Set (ℱ.obj U)` of sections stable
  under restriction
- derived API: the older name `Subpresheaf` is only a deprecated compatibility alias and should not
  be used as a second public owner
-/
/-
Definition 7.3.3: a subpresheaf of a set-valued presheaf `ℱ` is the canonical mathlib structure
`CategoryTheory.Subfunctor ℱ`, consisting of subsets `𝒢.obj U : Set (ℱ.obj U)` for every object
`U`, compatible with the restriction maps of `ℱ`. The older name `Subpresheaf ℱ` is only a
deprecated alias, so downstream code should use `Subfunctor ℱ` directly.
-/
recall Subfunctor

end
