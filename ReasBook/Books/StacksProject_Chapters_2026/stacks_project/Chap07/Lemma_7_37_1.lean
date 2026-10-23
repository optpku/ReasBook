module

public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.«7_32_1_1»

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace GrothendieckTopology.Point

open Hom

variable {p p' : GrothendieckTopology.Point.{v} J}
variable (f : p ⟶ p')

/- Source/core/bridge triage for Lemma 7.37.1:
- source-facing statements: the formulas for the induced maps on sheaf fibers and on generators of
  presheaf fibers attached to a morphism of points
- core/canonical owner: `Point.Hom`
- derived owner API: `Point.Hom.presheafFiber` and `Point.Hom.sheafFiber`
- primitive data: points `p`, `p'` and a morphism of points `f : p ⟶ p'`
- bridge/view: `yoneda ⋙ p.presheafFiber ≅ p.fiber` from Lemma 7.32.3
- derived API: the induced fiber maps and their generator formulas via the generic natural-
  transformation theorem `NatTrans.toPresheafFiber_presheafFiber_app`, specialized to `f.hom`
-/

/-- Lemma 7.37.1: a morphism of points `f : p ⟶ p'` induces the canonical map on sheaf fibers,
whose component at a sheaf is
by definition the corresponding component of the induced map on the underlying presheaf fibers. -/
theorem sheafFiber_app_eq_presheafFiber_app
    (ℱ : Sheaf J (Type v)) :
    (f.sheafFiber).app ℱ =
      (f.presheafFiber).app ((sheafToPresheaf J (Type v)).obj ℱ) :=
  -- The sheaf-fiber map is defined by restricting the presheaf-fiber map along `sheafToPresheaf`.
  rfl

/-- On a representable presheaf, the induced canonical map on presheaf fibers sends a generator
map `p'.toPresheafFiber X x (yoneda.obj U)` to the corresponding generator built from the image
of `x` under `f.hom`. Via the identifications of Lemma 7.32.3, this is the statement that the
induced map agrees with `f.hom` on representables. -/
@[simp, reassoc]
theorem presheafFiber_app_toPresheafFiber
    (U X : C) (x : p'.fiber.obj X) :
    p'.toPresheafFiber X x (CategoryTheory.yoneda.obj U) ≫
        f.presheafFiber.app (CategoryTheory.yoneda.obj U) =
      p.toPresheafFiber X (f.hom.app X x) (CategoryTheory.yoneda.obj U) := by
  -- Specialize the generic naturality formula for `toPresheafFiber` to the map of fibers `f.hom`.
  simpa [Hom.presheafFiber] using
    NatTrans.toPresheafFiber_presheafFiber_app f.hom X x

end GrothendieckTopology.Point

end CategoryTheory
