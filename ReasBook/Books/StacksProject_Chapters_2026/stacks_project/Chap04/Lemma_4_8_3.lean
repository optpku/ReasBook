module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap04.Definition_4_3_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {F G : Presheaf C}

/- Source/core/bridge triage for Lemma 4.8.3:
- source-facing statement: a representable morphism of presheaves with representable codomain has
  representable domain;
- domain-style sampling in the presheaf representability owner layer:
  `yoneda.relativelyRepresentable`,
  `Functor.IsRepresentable`,
  `Functor.reprW`,
  `isRepresentable_of_natIso`;
- core/canonical owners: `yoneda.relativelyRepresentable` and `Functor.IsRepresentable`, with the
  latter recalled in `Definition_4_3_6`;
- bridge/view: specialize relative representability to the canonical Yoneda presentation
  `G.reprW.hom : yoneda.obj G.reprX ⟶ G`;
- primitive data: the morphism `a`, the witness `ha`, and the explicit representability proof
  `hG : G.IsRepresentable`;
- derived API: the induced isomorphism `yoneda.obj (ha.pullback G.reprW.hom) ≅ F`, obtained from
  `ha.fst G.reprW.hom`, is fed to the canonical stability theorem `isRepresentable_of_natIso`.
-/
/-- Lemma 4.8.3: if `a : F ⟶ G` is a representable morphism of presheaves of sets on `C` and
`G` is representable, then `F` is representable. -/
-- Proof sketch: choose a Yoneda presentation `yoneda.obj (G.reprX) ≅ G`. Relative
-- representability of `a` applied to the canonical map `yoneda.obj (G.reprX) ⟶ G` yields a
-- pullback square with top-left corner again of the form `yoneda.obj X`. Since the right vertical
-- map is an isomorphism, the left vertical map is an isomorphism as well, so `F` is representable.
theorem isRepresentable_of_relativelyRepresentable_of_isRepresentable_codomain
    (a : F ⟶ G) (ha : yoneda.relativelyRepresentable a) (hG : G.IsRepresentable) :
    F.IsRepresentable := by
  letI : G.IsRepresentable := hG
  -- Specialize relative representability to the canonical Yoneda presentation of `G`.
  letI : IsIso (ha.fst G.reprW.hom) := (ha.isPullback G.reprW.hom).isIso_fst_of_isIso
  -- Transport representability across the resulting Yoneda isomorphism onto `F`.
  exact isRepresentable_of_natIso (yoneda.obj (ha.pullback G.reprW.hom))
    (asIso (ha.fst G.reprW.hom))

end CategoryTheory
