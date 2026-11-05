module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Functor

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Domain-style sampling:
- primary domain: presheaf right Kan extensions and their counits;
- sampled owner API:
  `HasRightKanExtension`,
  `Functor.rightKanExtensionCounit`,
  `Functor.ranCounit`,
  nearby chapter analogue `Lemma_7_5_3` for the left Kan extension unit;
- source/core/bridge triage:
  `source-facing`: Lemma 7.19.1 records, for one fixed presheaf `ℱ`, the canonical evaluation map
    and its restriction-map compatibility;
  `core/canonical`: `Functor.rightKanExtensionCounit`;
  `bridge/view`: the component at `U` and the naturality equation for `f : V ⟶ U`.

Primitive data are `u`, `ℱ`, and the existence of the right Kan extension along `u.op`. The
component map and its restriction compatibility are derived API from the counit natural
transformation, so this file should expose that owner projection directly rather than a parallel
local definition. The adjunction-level counit `Functor.ranCounit` is a stronger companion owner,
since it requires right Kan extensions for all presheaves; the source lemma only fixes one
presheaf, so `Functor.rightKanExtensionCounit` is the correct main entry here.
-/

/- Lemma 7.19.1: for a presheaf `ℱ` on `C` and `u : C ⥤ D`, the canonical map
`${}_p u \mathcal F (u(U)) \to \mathcal F(U)` is the component at `U` of the right Kan extension
counit `u.op.rightKanExtensionCounit ℱ`. -/
recall Functor.rightKanExtensionCounit

variable (u : C ⥤ D) (ℱ : Cᵒᵖ ⥤ Type w) [HasRightKanExtension u.op ℱ]
variable {U V : C} (f : V ⟶ U)

/- The source-facing map of Lemma 7.19.1 is the `U`-component of that counit. -/
#check (u.op.rightKanExtensionCounit ℱ).app (op U)

/- The restriction-map compatibility in Lemma 7.19.1 is exactly the naturality of the counit:
for `f : V ⟶ U`, this is `(u.op.rightKanExtensionCounit ℱ).naturality f.op`. -/
#check (u.op.rightKanExtensionCounit ℱ).naturality f.op

end CategoryTheory
