module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Definition_4_3_3
public import stacks_project.Chapters.Chap23.section03

@[expose] public section

universe u

namespace CategoryTheory

/- Domain-style sampling for Remark 4.2.2:
- primary domain: the source-facing whitelist of ambient large categories used throughout the
  chapter, each expressed through its canonical owner declaration
- sampled canonical declarations:
  `LargeCategory`,
  `Action`,
  `ModuleCat`,
  `TopCat.Sheaf`
- best owner abstraction: this remark is not owned by a single new abstraction; its mathematical
  content is the chapter's explicit roster of allowed large categories, so each listed family
  should be presented directly through its existing canonical owner rather than collapsed to the
  generic size abbreviation alone
- primitive data: the owner categories themselves, together with the local mathematical inputs
  they actually depend on, such as a group `G`, a ring `R`, a small category `C`, a topology `J`,
  or a topological space `X`
- derived API: the inherited `LargeCategory` instances on those owner categories

Source/core/bridge triage for Remark 4.2.2:
- source-facing: the whitelist of ambient large categories explicitly allowed in the text
- core/canonical: the owner declarations for those categories, such as `Action`, `ModuleCat`,
  `Presheaf`, `Sheaf`, `TopCat.Presheaf`, `TopCat.Sheaf`, `TopCat`, and
  `AlgebraicGeometry.Scheme`
- bridge/view: the size-interface checks `LargeCategory (...)` showing that each owner category
  fits the ambient convention
-/

/- Remark 4.2.2 fixes the ambient size convention through the canonical abbreviation
`LargeCategory`, but its source-facing mathematical content is the explicit list of large
categories the chapter allows one to work with. The refined file therefore keeps the generic size
recall only as background and records the listed examples directly through their canonical owner
categories. -/
recall LargeCategory

/- Companion recall: when the source mentions functor, presheaf, and sheaf categories indexed by a
category `C`, the relevant input hypothesis is that `C` is small. -/
recall SmallCategory

/- The basic ambient examples named in the remark are already large through their canonical owner
category instances: sets, abelian groups, groups, rings, topological spaces, and schemes. -/
#check (inferInstance : LargeCategory (Type u))
#check (inferInstance : LargeCategory AddCommGrpCat)
#check (inferInstance : LargeCategory GrpCat)
#check (inferInstance : LargeCategory RingCat)
#check (inferInstance : LargeCategory TopCat)
#check (inferInstance : LargeCategory AlgebraicGeometry.Scheme)

section AlgebraicExamples

variable (G : Type u) [Group G]
variable (R : Type u) [Ring R]
variable (k : Type u) [Field k]

/- The algebraic families listed in the remark use their standard owners: `Action (Type u) G` for
`G`-sets, `ModuleCat R` for `R`-modules, `ModuleCat k` for vector spaces over `k`, and the
project's bundled owner `DividedPowerRing` for divided power rings. -/
#check Action
#check (inferInstance : LargeCategory (Action (Type u) G))
#check ModuleCat
#check (inferInstance : LargeCategory (ModuleCat.{u} R))
#check (inferInstance : LargeCategory (ModuleCat.{u} k))
#check DividedPowerRing
#check (inferInstance : LargeCategory DividedPowerRing)

end AlgebraicExamples

section PresheafAndFunctorExamples

variable (C : Type u) [SmallCategory C]
variable (X : TopCat.{u})

/- The remark also allows the standard large categories built from a small category `C` or a
topological space `X`: set-valued functors on `C`, presheaves of sets on `C`, and presheaves of
sets or abelian groups on `X`. -/
#check (inferInstance : LargeCategory (C ⥤ Type u))
#check Presheaf
#check (inferInstance : LargeCategory (Presheaf.{u, u, u} C))
#check TopCat.Presheaf
#check (inferInstance : LargeCategory (X.Presheaf (Type u)))
#check (inferInstance : LargeCategory (X.Presheaf AddCommGrpCat.{u}))

end PresheafAndFunctorExamples

section SheafExamples

variable (C : Type u) [SmallCategory C]
variable (J : GrothendieckTopology C)
variable (X : TopCat.{u})

/- Finally, the sheaf examples from the remark use the canonical site-level and topological-space
owners for sheaves of sets and of abelian groups. -/
#check Sheaf
#check TopCat.Sheaf
#check (inferInstance : LargeCategory (Sheaf J (Type u)))
#check (inferInstance : LargeCategory (X.Sheaf (Type u)))
#check (inferInstance : LargeCategory (X.Sheaf AddCommGrpCat.{u}))

end SheafExamples

end CategoryTheory
