module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Definition_6_16_2
public import stacks_project.Chap06.Lemma_6_16_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 6.16.3:
- primary domain: mono/epi criteria for set-valued presheaves and sheaves on a topological space;
- inspected owner declarations:
  `presheaf_epi_iff_app_surjective`,
  `presheaf_mono_iff_app_injective`,
  `TopCat.Sheaf.isLocallySurjective_iff_epi`,
  `sheaf_epi_iff_stalk_surjective`.
- best owner abstraction: the categorical predicates `Mono φ` and `Epi φ` on morphisms of
  presheaves/sheaves, with sectionwise, local, and stalkwise injectivity/surjectivity criteria as
  derived API.

Primitive-vs-derived split:
- primitive data: the canonical categorical notions `Mono` and `Epi` for the morphism itself;
- derived API: objectwise injectivity/surjectivity on sections, local surjectivity, and stalkwise
  injectivity/surjectivity.

Source/core/bridge triage:
- `source-facing`: the textbook criteria for monomorphisms and epimorphisms of presheaves and
  sheaves of sets;
- `core/canonical`: the owner predicates `Mono`, `Epi`, and the mathlib owner
  `TopCat.Presheaf.IsLocallySurjective`;
- `bridge/view`: the equivalences between those owner predicates and sectionwise/local/stalkwise
  criteria. -/

/- Lemma 6.16.3, presheaf epimorphism clause: for set-valued presheaves on `X`, epimorphisms are
exactly the morphisms that are surjective on sections over every open set. This is the
source-facing bridge theorem recorded in Definition 6.16.2. -/
recall presheaf_epi_iff_app_surjective

/- Lemma 6.16.3, presheaf monomorphism clause: for set-valued presheaves on `X`, monomorphisms are
exactly the morphisms that are injective on sections over every open set. This is the
source-facing bridge theorem recorded in Definition 6.16.2. -/
recall presheaf_mono_iff_app_injective

/- Lemma 6.16.3, sheaf epimorphism clause in local form: for set-valued sheaves, the textbook
criterion `Epi φ ↔ IsLocallySurjective φ.hom` is the symmetric form of the canonical mathlib
theorem `TopCat.Sheaf.isLocallySurjective_iff_epi`. -/
recall TopCat.Sheaf.isLocallySurjective_iff_epi

/- Lemma 6.16.3, sheaf epimorphism clause in stalkwise form: for set-valued sheaves on `X`,
epimorphisms are exactly the morphisms that are surjective on all stalks. This is the exact
canonical theorem already recorded in Lemma 6.16.1. -/
recall sheaf_epi_iff_stalk_surjective

/- Lemma 6.16.3, sheaf monomorphism clause in sectionwise form: for set-valued sheaves on `X`,
monomorphisms are exactly the morphisms that are injective on sections over every open set. This
is the exact canonical theorem already recorded in Definition 6.16.2. -/
recall sheaf_mono_iff_app_injective

/- Lemma 6.16.3, sheaf monomorphism clause in stalkwise form: for set-valued sheaves on `X`,
monomorphisms are exactly the morphisms that are injective on all stalks. This is the exact
canonical theorem already recorded in Lemma 6.16.1. -/
recall sheaf_mono_iff_stalk_injective
