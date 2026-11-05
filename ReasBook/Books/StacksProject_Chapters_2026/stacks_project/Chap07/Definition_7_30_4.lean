module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (ℱ : Sheaf J (Type w))

/- Domain-style sampling for Definition 7.30.4:
- primary domain: localization of a sheaf topos at an object, expressed by the slice topos over
  that object;
- sampled owner API:
  `Over`,
  `Over.forgetAdjStar`,
  `Over.forget`,
  `Over.star`;
- source/core/bridge triage:
  `source-facing`: the localized topos `Sh(C, J) / ℱ`;
  `core/canonical`: the slice owner `Over ℱ`, together with the adjunction
  `Over.forget ℱ ⊣ Over.star ℱ`, packaged by `Over.forgetAdjStar ℱ`;
  `bridge/view`: the direct-image and inverse-image functors `Over.forget ℱ` and `Over.star ℱ`.

Primitive data are only the ambient site and the sheaf `ℱ`. The localization topos and its
geometric morphism are already owned canonically by `Over ℱ` and `Over.forgetAdjStar ℱ`, so this
file should stay at the `core/canonical` layer with direct recall rather than repeating the same
owner facts under parallel local names.
-/

/- Definition 7.30.4: the localization of the topos `Sh(C, J)` at a sheaf `ℱ` is the slice
topos `Sh(C, J) / ℱ`, represented in Lean by the over category `Over ℱ`. -/
#check Over ℱ

/- Companion recall: the localization morphism at `ℱ` is the canonical slice-topos adjunction
whose direct image is `Over.forget ℱ` and whose inverse image is `Over.star ℱ`. -/
recall Over.forgetAdjStar
