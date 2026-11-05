module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

universe u v w u' v'

namespace CategoryTheory

open GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Definition 7.32.6:
- primary domain: skyscraper sheaves attached to points of a site;
- sampled owner declarations:
  `Point.skyscraperPresheaf`,
  `Point.skyscraperSheafFunctor`,
  `Point.skyscraperSheaf`,
  `Point.toToposPoint_pointPushforwardIso`;
- source/core/bridge triage:
  `source-facing`: the direct-image functor `p_*` of a site point and its objectwise set-valued
    description;
  `core/canonical`: `Point.skyscraperSheafFunctor`;
  `bridge/view`: the owner-level presheaf view `Φ.skyscraperPresheaf E`, the canonical
    `Type`-level product comparison `Types.productIso`, and later in the chapter the comparison
    `Point.toToposPoint_pointPushforwardIso` to the direct image of the induced topos point.

The primitive data are only the point `Φ` and the target object `E`. The objectwise identification
with maps `Φ.fiber.obj X → E` is derived API of the owner `Φ.skyscraperSheafFunctor`, best exposed
through the canonical view `Φ.skyscraperPresheaf E` rather than a parallel local wrapper or a
low-level underlying-sheaf expression.
-/

/- Definition 7.32.6: for a point `p` of the site `(C, J)`, the direct-image/skyscraper functor
`p_*` is the canonical mathlib functor `Point.skyscraperSheafFunctor`.
For sets, `Φ.skyscraperSheaf E` is the sheaf denoted `u^s E` in the Stacks Project. -/
recall Point.skyscraperSheafFunctor
  {C : Type u} [Category.{v, u} C] {J : GrothendieckTopology C}
  (Φ : J.Point) {A : Type u'} [Category.{v', u'} A] [HasProducts A] :
  A ⥤ Sheaf J A

variable (Φ : Point.{w} J) (E : Type w) (X : C)

/- For sets, the owner-level presheaf view `Φ.skyscraperPresheaf E` evaluates at `X` to the
product of copies of `E` indexed by `Φ.fiber.obj X`, so in `Type` it is canonically equivalent to
the set of maps `Φ.fiber.obj X → E` via `Types.productIso`. -/
#check
  (((Types.productIso (fun _ : Φ.fiber.obj X ↦ E)).toEquiv) :
    (Φ.skyscraperPresheaf E).obj (op X) ≃ (Φ.fiber.obj X → E))

end CategoryTheory
