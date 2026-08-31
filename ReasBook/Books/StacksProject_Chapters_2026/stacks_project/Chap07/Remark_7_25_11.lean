module

public import Mathlib.CategoryTheory.Sites.Over

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {U V : C} (h : U ⟶ V)

/- Domain-style sampling for Remark 7.25.11:
- primary domain: cocontinuity of localization and relocalization functors between slice sites;
- sampled owner API:
  `CategoryTheory.Functor.IsCocontinuous`,
  `CategoryTheory.Functor.cover_lift`,
  `(Over.forget U).IsCocontinuous (J.over U) J`,
  `(Over.map h).IsCocontinuous (J.over U) (J.over V)`;
- source/core/bridge triage:
  `source-facing`: the two covering-family pullback assertions in Remark 7.25.11;
  `core/canonical`: the cocontinuity owner instances for `Over.forget U` and `Over.map h`;
  `bridge/view`: `Functor.cover_lift`, whose `Sieve.ofArrows` specialization recovers the explicit
  family-level pullback language of the remark.

Primitive data are only the ambient topology `J`, the objects `U`, `V`, and the morphism `h`.
The pulled-back covering families are derived from the owner abstraction `Functor.IsCocontinuous`,
so this file should recall those canonical instances directly instead of keeping parallel local
theorems that restate the same semantics entrywise.
-/

/- Remark 7.25.11 (1): the localization functor `Over.forget U : C/U ⥤ C` is cocontinuous for
the localized topology. Equivalently, every covering family in `C` pulls back to a covering family
in `C/U` via the owner operation `Functor.cover_lift`. -/
#check (inferInstance : (Over.forget U).IsCocontinuous (J.over U) J)

/- Remark 7.25.11 (2): for `h : U ⟶ V`, the relocalization functor
`Over.map h : C/U ⥤ C/V` is cocontinuous. Equivalently, every covering family over an object of
`C/V` pulls back to a covering family over the source object in `C/U` via
`Functor.cover_lift`. -/
#check (inferInstance : (Over.map h).IsCocontinuous (J.over U) (J.over V))

end CategoryTheory
