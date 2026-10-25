module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_26_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}
variable [UnivLE.{max u v, w}]

/- Domain-style sampling for Lemma 7.26.5:
- primary domain: effective descent for set-valued sheaves on slice sites over a fixed cover;
- sampled owner API:
  `Pseudofunctor.IsStackFor`,
  `Pseudofunctor.isStackFor_ofArrows_iff`,
  `Functor.IsEquivalence`;
- source-facing layer: the textbook equivalence between sheaves on `C / U` and coverwise glueing
  data on a fixed cover `𝒰`;
- core/canonical owner: the fixed-cover stack condition
  `(J.pseudofunctorOver (Type w)).IsStackFor (Presieve.ofArrows _ (fun I : 𝒰.Arrow ↦ I.f))`,
  already established in Lemma `7.26.4`;
- bridge/view: `isStackFor_ofArrows_iff`, which converts that owner-level theorem to the explicit
  equivalence of the descent-data functor.

Primitive data are only the topology `J`, the object `U`, and the cover `𝒰 : J.Cover U`. The
equivalence statement here is derived API of the owner theorem from Lemma `7.26.4`, so this file
should reuse that theorem directly instead of rebuilding the same fixed-cover stack proof.
-/

/-- Lemma 7.26.5, source-facing form: for a covering `𝒰` of `U`, the canonical functor from
sheaves on the localized site `C / U` to the category of coverwise glueing data on `𝒰` is an
equivalence of categories. -/
theorem localizedSheafToCoverDescentFunctor_isEquivalence
    (𝒰 : J.Cover U) :
    ((J.pseudofunctorOver (Type w)).toDescentData (fun I : 𝒰.Arrow ↦ I.f)).IsEquivalence := by
  simpa using
    ((J.pseudofunctorOver (Type w)).isStackFor_ofArrows_iff
      (fun I : 𝒰.Arrow ↦ I.f)).1
      (localizedSheafPseudofunctorOver_isStackFor_cover 𝒰)

end

end GrothendieckTopology
end CategoryTheory
