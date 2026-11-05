module

public import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Example_4_3_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open scoped RepresentablePresheaf

variable {C : Type u} [Category.{v} C]

/- Source/core/bridge triage for Definition 4.3.6:
- sampled owner-style declarations in this domain:
  `Presheaf C`,
  `Functor.RepresentableBy`,
  `Functor.RepresentableBy.toIso`,
  `Functor.IsRepresentable`
- `source-facing`: the textbook condition that a presheaf be isomorphic to some `h[U]`
- `core/canonical`: the mathlib owner predicate `Functor.IsRepresentable`
- `bridge/view`: the equivalence between a representing structure `F.RepresentableBy U` and a
  Yoneda isomorphism `h[U] ≅ F`
- primitive data: a representing object `U : C` together with `F.RepresentableBy U`
- derived API: the source-facing Yoneda isomorphism from `Functor.RepresentableBy.toIso`, and when
  later needed the chosen representing object `reprX` with its Yoneda isomorphism `reprW`
-/
/- Definition 4.3.6: representability of a presheaf is the canonical mathlib predicate
`CategoryTheory.Functor.IsRepresentable`. -/
recall Functor.IsRepresentable

/-- A presheaf is representable exactly when it is isomorphic to a representable Yoneda
presheaf `h[U]` for some `U : C`. -/
-- Proof sketch: use the canonical chosen representing object and Yoneda isomorphism from
-- `Functor.IsRepresentable` in one direction, and build representability from the exhibited
-- Yoneda isomorphism in the other direction.
theorem isRepresentable_iff_exists_yoneda_obj_iso (F : Presheaf C) :
    F.IsRepresentable ↔ Nonempty (Σ U : C, h[U] ≅ F) := by
  constructor
  · intro hF
    -- Use the canonical representing object attached to the representability witness.
    let _ : F.IsRepresentable := hF
    refine ⟨⟨F.reprX, ?_⟩⟩
    -- The canonical Yoneda comparison gives the required source-facing isomorphism.
    simpa using (F.reprW : yoneda.obj F.reprX ≅ F)
  · rintro ⟨⟨U, e⟩⟩
    -- An exhibited Yoneda isomorphism is exactly the canonical constructor for representability.
    simpa using (Functor.IsRepresentable.mk' e : F.IsRepresentable)

end CategoryTheory
