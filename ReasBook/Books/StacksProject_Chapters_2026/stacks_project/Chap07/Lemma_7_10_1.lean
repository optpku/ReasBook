module

public import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (I : Type w) [Category I] [Small.{max u v} I]

/- Source/core/bridge triage for Lemma 7.10.1:
- sampled upstream declarations in the same domain:
  `sheafToPresheaf`, `Sheaf.createsLimitsOfShape`,
  `hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape`,
  `preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape`
- source-facing content: the forgetful functor from set-valued sheaves on `(C, J)` to presheaves
  creates `I`-shaped limits
- core/canonical owner: `Sheaf.createsLimitsOfShape`
- bridge/view: the `Type (max u v)` specialization and the induced `HasLimitsOfShape` instance on
  `Sheaf J (Type (max u v))`, together with the induced preservation statement for
  `sheafToPresheaf J (Type (max u v))`
- primitive data: the site `(C, J)` and the diagram shape `I`
- derived API: existence of `I`-shaped limits in the sheaf category, obtained from the owner
  instance together with limits in `Type`
-/
/- Lemma 7.10.1 targets the source-facing specialization of the canonical owner:
for set-valued sheaves on `(C, J)`, the forgetful functor to presheaves creates `I`-shaped
limits. -/
#check (inferInstance : CreatesLimitsOfShape I (sheafToPresheaf J (Type (max u v))))

/- Core/canonical owner recall behind the specialized statement above. -/
recall Sheaf.createsLimitsOfShape

/- Companion derived API: since `Type (max u v)` has `I`-shaped limits, the sheaf category
`Sheaf J (Type (max u v))` inherits them. -/
#check (inferInstance : HasLimitsOfShape I (Sheaf J (Type (max u v))))

/- The owner instance also implies that the forgetful functor computes these limits on underlying
presheaves. -/
#check (inferInstance : PreservesLimitsOfShape I (sheafToPresheaf J (Type (max u v))))
