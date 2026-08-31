module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory
namespace Pseudofunctor.CoGrothendieck

open Functor
open Opposite
open scoped Bicategory

variable {𝒞 : Type u} [Category.{v} 𝒞]
variable {F : 𝒞ᵒᵖ ⥤ Cat.{v, w}}

/- Domain-style sampling for Example 4.36.1:
- primary domain: split fibred categories arising from contravariant `Cat`-valued functors via the
  co-Grothendieck construction.
- sampled owner API:
  `Functor.toPseudofunctor'`,
  `forget`,
  `domainCartesianLift`,
  `cartesianLift`.
- best owner abstraction: the canonical owner remains the pseudofunctorial co-Grothendieck
  projection and its lift API, but the source-facing surface for this example is the ordinary
  functor `F : 𝒞ᵒᵖ ⥤ Cat` together with the bridge `F.toPseudofunctor'`.

Primitive-vs-derived split:
- primitive data: an object `a : F.obj (op S)` and a base morphism `f : R ⟶ S`.
- derived API: the projection `forget (F.toPseudofunctor')`, the lifted domain object, the
  morphism `(f, 𝟙)` over `f`, its strong-cartesian property, and the induced `IsFibered`
  instance.

Source/core/bridge triage:
- `source-facing`: the textbook explicit lift `(f, 𝟙)` in the category over `𝒞` attached to an
  ordinary contravariant functor `F : 𝒞ᵒᵖ ⥤ Cat`.
- `core/canonical`: `forget`, `domainCartesianLift`, `cartesianLift`,
  `isHomLift_cartesianLift`, and `isStronglyCartesian_homCartesianLift` for the induced
  pseudofunctor.
- `bridge/view`: `Functor.toPseudofunctor'`, which promotes the ordinary functor to the canonical
  pseudofunctor owner used by the co-Grothendieck construction. -/

/- Example 4.36.1 uses the canonical bridge from the ordinary contravariant functor `F` to the
underlying pseudofunctor needed by the co-Grothendieck construction. -/
recall toPseudofunctor'

/- Example 4.36.1: the category over `𝒞` associated to `F : 𝒞ᵒᵖ ⥤ Cat` is the canonical
projection `forget (F.toPseudofunctor') : ∫ᶜ F.toPseudofunctor' ⥤ 𝒞`. -/
example : ∫ᶜ F.toPseudofunctor' ⥤ 𝒞 :=
  forget F.toPseudofunctor'

section CartesianLift

variable {R S : 𝒞} (a : F.toPseudofunctor'.obj ⟨op S⟩) (f : R ⟶ S)

/- Example 4.36.1: the domain object of the textbook lift over `f` is the canonical
`domainCartesianLift` for `F.toPseudofunctor'`. Here `(F.toPseudofunctor').obj ⟨op S⟩` is
definitionally the same category as `F.obj (op S)`. -/
example : ∫ᶜ F.toPseudofunctor' :=
  domainCartesianLift a f

/- Example 4.36.1: the textbook lift `(f, 𝟙)` is the canonical morphism `cartesianLift` in the
associated category over `𝒞`. -/
example : domainCartesianLift a f ⟶ ⟨S, a⟩ :=
  cartesianLift a f

/- Example 4.36.1: the textbook lift `(f, 𝟙)` canonically lies over `f`; this is the
source-facing specialization of `isHomLift_cartesianLift` along `F.toPseudofunctor'`. -/
example : IsHomLift (forget F.toPseudofunctor') f (cartesianLift a f) :=
  isHomLift_cartesianLift a f

/- Example 4.36.1: the canonical morphism `(f, 𝟙) = cartesianLift a f` is strongly cartesian over
`f`; this is exactly the textbook lift in the split category associated to the ordinary functor
`F`. -/
example : IsStronglyCartesian (forget F.toPseudofunctor') f (cartesianLift a f) :=
  isStronglyCartesian_homCartesianLift a f

end CartesianLift

/- Companion example: the associated projection `forget (F.toPseudofunctor')` is fibred. -/
example : (forget F.toPseudofunctor').IsFibered := inferInstance

end Pseudofunctor.CoGrothendieck
end CategoryTheory
