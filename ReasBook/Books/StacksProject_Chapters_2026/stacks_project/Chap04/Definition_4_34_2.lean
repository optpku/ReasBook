module

import Mathlib.Tactic.Recall
public import stacks_project.Chap04.«4_34_2_1»

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

namespace FibredCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FibredCategoryOver C}

/- Domain-style sampling for Definition 4.34.2:
- primary domain: categories fibred over a fixed base `C` and the relative/absolute inertia
  construction.
- inspected owner declarations:
  `CategoryTheory.relativeInertiaProjection` from `Lemma_4_34_1`,
  `FibredCategoryOver.relativeInertiaOver` and `CategoryOver.absoluteInertiaOver` from
  `4_34_2_1`,
  and `FibredCategoryOver.ofFunctor`.
- best owner abstraction: the source-facing owner is `FibredCategoryOver C`; the underlying
  `CategoryOver C` object is the bridge/view layer.
- primitive-vs-derived split: the owner objects and their projection functors are primitive at the
  fibred-category level; the `Cat/C` packaging is derived view data.
- layer classification here: recall of the canonical chapter owner declarations at their
  compiling owner layers. -/

/- Definition 4.34.2: for a morphism `F : X ⟶ Y` of categories fibred over `C`, the relative
inertia `\mathcal{I}_{\mathcal X / \mathcal Y}` is the fibred category
`relativeInertiaOver F`. -/
recall relativeInertiaOver

end FibredCategoryOver

namespace CategoryOver

variable {C : Type u} [Category.{v} C]
variable {X : CategoryOver C}

/- Definition 4.34.2: the absolute inertia `\mathcal{I}_{\mathcal X}` is the special case
`\mathcal{I}_{\mathcal X/\mathcal C}`, obtained by specializing the same generic inertia
construction to the structure morphism `X ⟶ (C, 𝟭 C)`, and implemented in `Cat/C` as
`absoluteInertiaOver X`. -/
recall absoluteInertiaOver

end CategoryOver

end CategoryTheory
