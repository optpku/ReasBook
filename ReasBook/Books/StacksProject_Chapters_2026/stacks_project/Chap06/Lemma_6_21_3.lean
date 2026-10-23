module

public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Functors
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TopCat.Presheaf

/- Domain-style sampling for Lemma 6.21.3:
- primary domain: inverse image of set-valued presheaves along a continuous map, organized as
  left Kan extension on the category of opens;
- sampled owner API:
  `TopCat.Presheaf.pullback`,
  `TopCat.Presheaf.pullbackPushforwardAdjunction`,
  `Functor.leftKanExtensionObjIsoColimit`,
  `IsFiltered (CostructuredArrow (Opens.map f).op (op U))`;
- source/core/bridge triage:
  `source-facing`: the Stacks description of `f⁻¹ 𝒢` and its objectwise colimit over neighborhoods
  of `f(U)`;
  `core/canonical`: the presheaf pullback owner `pullback (Type u) f` and its adjunction with
  pushforward;
  `bridge/view`: the specialization of `Functor.leftKanExtensionObjIsoColimit` to
  `(Opens.map f).op`, together with the filteredness instance for the indexing category.

Primitive data are only the continuous map `f`, the presheaf `𝒢`, and the open `U`. The pullback,
its adjunction, the objectwise colimit formula, and the filteredness of the costructured-arrow
indexing category are all derived from the canonical left-Kan-extension owner, so this file should
recall those owners directly rather than keep parallel wrapper declarations.
-/

/- Lemma 6.21.3: for a continuous map `f : X ⟶ Y`, the canonical presheaf pullback functor on
`Type`-valued presheaves is left adjoint to pushforward. In mathlib this is the canonical
adjunction `TopCat.Presheaf.pullbackPushforwardAdjunction`, specialized here to presheaves of
sets. -/
recall TopCat.Presheaf.pullbackPushforwardAdjunction

/- Companion owner recall: the pointwise description of a left Kan extension as a colimit is the
canonical declaration `Functor.leftKanExtensionObjIsoColimit`. -/
recall Functor.leftKanExtensionObjIsoColimit

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable (𝒢 : Y.Presheaf (Type u)) (U : Opens X)

/- Lemma 6.21.3, bridge/view recall: the value of the inverse-image presheaf on `U` is the
canonical colimit computing the left Kan extension along `(Opens.map f).op`; this is exactly
`Functor.leftKanExtensionObjIsoColimit` specialized to the opens functor. -/
#check
  ((Opens.map f).op.leftKanExtensionObjIsoColimit 𝒢 (op U) :
    (((pullback (Type u) f).obj 𝒢).obj (op U)) ≅
      colimit (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ 𝒢))

/- The same indexing category is filtered, expressing that neighborhoods of `f(U)` form a directed
system under reverse inclusion. This is direct instance recall, not a separate chapter-level
owner. -/
#check (inferInstance : IsFiltered (CostructuredArrow (Opens.map f).op (op U)))

end
