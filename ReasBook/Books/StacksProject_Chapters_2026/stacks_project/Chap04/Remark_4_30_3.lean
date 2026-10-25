module

import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Definition_4_35_6
public import stacks_project.Chap08.Definition_8_5_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open Bicategory

/- Domain-style sampling for Remark 4.30.3:
- primary domain: bicategorical `(2,1)`-category constructions obtained by restricting
  `2`-morphisms to isomorphisms;
- core/canonical owner abstraction: `CategoryTheory.Bicategory.Pith`;
- bridge/view declarations reused from the project: `FibredInGroupoidsOver`,
  `FibredInGroupoidsMor`, and `StackInGroupoidsOver`.

Primitive-vs-derived split:
- primitive data: the ambient bundled objects and `1`-morphisms from those owner declarations;
- derived API: the `2`-morphism types `(F ≅ G)` and `(M ≅ N)`, which are exactly the isomorphism
  spaces used by the pith construction. -/

/- Source/core/bridge triage for Remark 4.30.3:
- source-facing: the listed examples where one keeps the same objects and `1`-morphisms and
  restricts `2`-morphisms to isomorphisms;
- core/canonical: `Pith`;
- bridge/view: the chapter-level owners for fibred categories in groupoids and stacks in
  groupoids, together with their isomorphism-valued `2`-morphism types. -/

/- Remark 4.30.3: the construction of Example 4.30.2 is the canonical `Pith` construction,
which keeps the same objects and `1`-morphisms and restricts `2`-morphisms to isomorphisms. The
remark only lists further contexts where the same idea applies, so the main formal content here
is a recall of `Pith` and the corresponding canonical chapter-level examples. -/
recall Pith

/- The groupoid variant is the associated `(2,1)`-category `Pith Grpd`. -/
#check Pith Grpd

variable {C : Type u} [Category.{v} C]
variable {X Y : FibredInGroupoidsOver C}
variable {F G : FibredInGroupoidsMor X Y}

/- Over a fixed base `C`, categories fibred in groupoids are formalized by
`FibredInGroupoidsOver C`; the pith construction keeps the same objects and `1`-morphisms and
uses the isomorphisms `F ≅ G` in `FibredInGroupoidsMor X Y` as `2`-morphisms. -/
#check FibredInGroupoidsOver C
#check FibredInGroupoidsMor X Y
#check (F ≅ G)

variable (J : GrothendieckTopology C)
variable {S T : StackInGroupoidsOver J}
variable {M N : S ⟶ T}

/- Likewise, stacks in groupoids over a fixed site `(C, J)` are formalized by
`StackInGroupoidsOver J`; the associated pith keeps the same objects and `1`-morphisms and uses
the isomorphisms `M ≅ N` in `S ⟶ T` as `2`-morphisms. -/
#check StackInGroupoidsOver J
#check (S ⟶ T)
#check (M ≅ N)

end CategoryTheory
