module

public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Whiskering
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open CategoryTheory.Functor
open CategoryTheory.Limits

universe u₁ u₂ v

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]
variable (u : C ⥤ D) (v' : D ⥤ C) (adj : u ⊣ v')

/- Domain-style sampling:
- primary domain: category-theoretic consequences of an adjunction on presheaf pullback,
  comma categories, and Kan extension comparisons;
- sampled owner API:
  `Adjunction.compYonedaIso`,
  `mkInitialOfLeftAdjoint`,
  `mkTerminalOfRightAdjoint`,
  `Adjunction.rightAdjointUniq`;
- source-facing: Lemma 7.19.3 records the five standard consequences of a functor `u`
  admitting a right adjoint `v'`;
- core/canonical: the adjunction owner declarations listed above;
- bridge/view: the objectwise representable comparison and the presheaf pullback/right- and
  left-Kan specializations.

Primitive data are the functors `u`, `v'`, the adjunction `adj`, and the existence of the
relevant Kan extensions in clauses `(4)` and `(5)`. The representable comparison, the
initial/terminal comma objects, and the Kan-extension identifications are derived API from those
owners, so this file should expose the owner projections directly rather than keep parallel local
wrappers. Clause `(5)` then uses the dual owner `Adjunction.leftAdjointUniq`. -/

/- Lemma 7.19.3 (1): the presheaf comparison underlying the representable pullback identity is the
canonical Yoneda comparison attached to an adjunction. -/
recall Adjunction.compYonedaIso

/- Lemma 7.19.3 (1): pulling back the representable presheaf `h_V` along `u` yields the
representable presheaf `h_{v'(V)}`. In mathlib this is the Yoneda comparison
`adj.compYonedaIso.symm.app V`, viewed objectwise. -/
#check
  (Iso.app (adj.compYonedaIso.symm) :
    ∀ V : D,
      ((whiskeringLeft Cᵒᵖ Dᵒᵖ (Type v)).obj u.op).obj (yoneda.obj V) ≅
        yoneda.obj (v'.obj V))

/- Lemma 7.19.3 (2): for `U : C`, the unit map `U ⟶ v'(u(U))` defines an initial object of
`StructuredArrow U v'`. -/
#check
  (mkInitialOfLeftAdjoint v' adj :
    ∀ U : C,
      IsInitial (StructuredArrow.mk (adj.unit.app U) : StructuredArrow U v'))

/- Lemma 7.19.3 (3): for `V : D`, the counit map `u(v'(V)) ⟶ V` defines a terminal object of
`CostructuredArrow u V`. -/
#check
  (mkTerminalOfRightAdjoint v' adj :
    ∀ V : D,
      IsTerminal (CostructuredArrow.mk (adj.counit.app V) : CostructuredArrow u V))

section RightKanExtensionComparison

variable [∀ P : Cᵒᵖ ⥤ Type v, u.op.HasRightKanExtension P]

/- Lemma 7.19.3 (4): the Stacks identity `${}_p u = v^p` is realized in the project API by the
canonical isomorphism from the chosen right Kan extension functor `u.op.ran` to pullback along
`v'`, obtained from uniqueness of right adjoints. -/
#check
  ((u.op.ranAdjunction (Type v)).rightAdjointUniq (adj.op.whiskerLeft (Type v)) :
    u.op.ran ≅ (whiskeringLeft Dᵒᵖ Cᵒᵖ (Type v)).obj v'.op)

end RightKanExtensionComparison

section LeftKanExtensionComparison

variable [∀ P : Dᵒᵖ ⥤ Type v, v'.op.HasLeftKanExtension P]

/- Lemma 7.19.3 (5): the Stacks identity `u^p = v'_p` is realized in the project API by the
canonical isomorphism from pullback along `u` to the chosen left Kan extension functor `v'.op.lan`,
obtained from uniqueness of left adjoints. -/
#check
  ((adj.op.whiskerLeft (Type v)).leftAdjointUniq (v'.op.lanAdjunction (Type v)) :
    (whiskeringLeft Cᵒᵖ Dᵒᵖ (Type v)).obj u.op ≅ v'.op.lan)

end LeftKanExtensionComparison

end

end CategoryTheory
