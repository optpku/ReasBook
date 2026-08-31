module

public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

variable {X : TopCat.{u}} {ι : Type v} (F : ι → X.Presheaf (Type v))
variable (U : Opens X) (ℱ 𝒢 : X.Presheaf (Type v))

/- Domain-style sampling for Lemma 6.4.2:
- primary domain: products in the presheaf category `X.Presheaf (Type v)`, viewed as the
  functor category `(Opens X)ᵒᵖ ⥤ Type v`;
- inspected owner declarations:
  `functorCategoryHasLimitsOfShape`,
  `piObjIso`,
  `FunctorToTypes.binaryProductIso`,
  `FunctorToTypes.binaryProductEquiv`;
- best owner abstraction: the canonical functor-category product instance, specialized through the
  presheaf owner `X.Presheaf (Type v)`.

Primitive-vs-derived split:
- primitive data: limits in `Type v`, which induce products in the functor category of presheaves;
- derived API: the presheaf-level `HasLimitsOfShape` instance, the evaluation isomorphism
  `piObjIso`, and the binary product specializations
  `FunctorToTypes.binaryProductIso` and `FunctorToTypes.binaryProductEquiv`.

Source/core/bridge triage:
- `source-facing`: products of set-valued presheaves on a topological space;
- `core/canonical`: `functorCategoryHasLimitsOfShape` and the resulting product object `∏ᶜ F`;
- `bridge/view`: the pointwise identifications of those products with ordinary set-theoretic
  products. -/

/- Lemma 6.4.2: products of set-valued presheaves are the canonical functor-category products.
The owner is the general pointwise-limit instance for functor categories, specialized here to the
presheaf category on `X`. -/
recall functorCategoryHasLimitsOfShape

/- Companion specialization: the presheaf category `X.Presheaf (Type v)` therefore has products
indexed by any `v`-small type `ι`. -/
#check (inferInstance : HasLimitsOfShape (Discrete ι) (X.Presheaf (Type v)))

/- Evaluating the categorical product presheaf at an open `U` identifies it with the product of
the section sets of the family over `U`. -/
#check (piObjIso F (op U))

/- For a pair of set-valued presheaves on `X`, the categorical binary product is the objectwise
product presheaf. This is the binary specialization of the same pointwise product owner. -/
#check (FunctorToTypes.binaryProductIso ℱ 𝒢)

/- Over each open `U`, sections of the categorical binary product identify canonically with pairs
of sections of `ℱ` and `𝒢`. -/
#check (FunctorToTypes.binaryProductEquiv ℱ 𝒢 (op U))
