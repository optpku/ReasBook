module

import Mathlib.Tactic.Recall
public import stacks_project.Chap07.PlusNotation
public import stacks_project.Chap07.Theorem_7_10_10

@[expose] public section

/- Domain-style sampling for Theorem 7.49.3:
- primary domain: the plus construction and sheafification for set-valued presheaves on a
  Grothendieck site;
- sampled owner API:
  `plusObj_isSeparated`,
  `plusObj_isSheaf_of_isSeparated`,
  `toPlus_injective_of_isSeparated`,
  `GrothendieckTopology.isIso_toPlus_of_isSheaf`,
  `GrothendieckTopology.Plus.isSheaf_plus_plus`;
- source-facing layer: the textbook assertions about `L F`, `F ⟶ L F`, and `L (L F)`;
- core/canonical owner: the plus-construction/sheafification API on `GrothendieckTopology`;
- bridge/view: the monomorphism reformulation `toPlus_mono_of_isSeparated`, obtained from the
  source-facing objectwise injectivity statement through `Presheaf.mono_iff_injective`.

Primitive data are only the site `J` and the presheaf `F`. The map `J.toPlus F`, the iterated plus
object, and sheafification are canonical constructions of the Grothendieck-topology owner, so this
file should recall those owners directly rather than keep parallel restatements.
-/

open CategoryTheory Opposite
open GrothendieckTopology
open scoped CategoryTheory.GrothendieckTopology.PlusNotation

universe u v

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (F : Cᵒᵖ ⥤ Type (max u v))

/- Theorem 7.49.3 (1): the plus construction `L F` is separated. This is the same statement as
Theorem 7.10.10 (1), already recorded in the chapter API. -/
recall plusObj_isSeparated :
  Presieve.IsSeparated J F⁺

/- Theorem 7.49.3 (2), first assertion: if `F` is separated, then `L F` is a sheaf. This is the
same statement as Theorem 7.10.10 (2), first assertion. -/
recall plusObj_isSheaf_of_isSeparated (hF : Presieve.IsSeparated J F) :
  Presheaf.IsSheaf J F⁺

/- Theorem 7.49.3 (2), second assertion: if `F` is separated, then the canonical map
`F ⟶ L F` is injective on sections over every object. This is the same statement as
Theorem 7.10.10 (2), second assertion. -/
recall toPlus_injective_of_isSeparated (hF : Presieve.IsSeparated J F) :
  ∀ U : C, Function.Injective ((J.toPlus F).app (op U))

/- Companion bridge for Theorem 7.49.3 (2), second assertion: via Definition 7.3.1 and
Lemma 7.3.2, the same map is a monomorphism. -/
recall toPlus_mono_of_isSeparated (hF : Presieve.IsSeparated J F) :
  Mono (J.toPlus F)

/- Theorem 7.49.3 (3): if `F` is a sheaf, then the canonical map `F ⟶ L F` is an isomorphism.
This is the same statement as Theorem 7.10.10 (3), now exposed by direct recall of the canonical
owner theorem. -/
recall isIso_toPlus_of_isSheaf

/- Theorem 7.49.3 (4): the iterated plus construction `L (L F)` is a sheaf. This is the same
statement as Theorem 7.10.10 (4), now exposed by direct recall of the canonical owner theorem. -/
recall Plus.isSheaf_plus_plus

/- Companion reformulation of Theorem 7.49.3 (4): since `J.sheafify F = F⁺⁺`,
the sheafification `J.sheafify F` is a sheaf. The canonical library-facing companion is the
theorem `sheafify_isSheaf`. -/
recall sheafify_isSheaf

end
