module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open CategoryTheory

/- Domain-style sampling for Definition 6.5.1:
- primary domain: `C`-valued presheaves on a topological space;
- sampled owner declarations:
  `CategoryTheory.Presheaf`,
  `TopCat.Presheaf`,
  `TopCat.Presheaf.restrict`,
  `TopCat.Presheaf.IsSheaf`;
- best owner abstraction: the topological specialization `TopCat.Presheaf`, with public surface
  `X.Presheaf C`.

Primitive-vs-derived split:
- primitive data: only the underlying contravariant functor `(Opens X)ᵒᵖ ⥤ C`;
- derived API: morphisms are natural transformations, and restriction compatibility is the
  canonical naturality identity.

Source/core/bridge triage:
- `source-facing`: a presheaf on `X` with values in `C`;
- `core/canonical`: `TopCat.Presheaf`;
- `bridge/view`: none needed, since the source notion is exactly the canonical owner. -/

/- Definition 6.5.1 (Tag 006N): a presheaf on a topological space `X` with values in a category
`C` is the canonical mathlib functor category `TopCat.Presheaf C X = (Opens X)ᵒᵖ ⥤ C`, whose
morphisms are natural transformations. -/
recall TopCat.Presheaf

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C]
variable {F G : X.Presheaf C} (φ : F ⟶ G)

/- A morphism of presheaves is a natural transformation, so compatibility with restriction along an
inclusion `i : V ⟶ U` is the canonical naturality identity `φ.naturality i.op`. -/
#check φ.naturality
