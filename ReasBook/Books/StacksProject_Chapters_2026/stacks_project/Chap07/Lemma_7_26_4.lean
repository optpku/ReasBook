module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_26_1
public import stacks_project.Chap07.Lemma_7_26_4.Index
public import stacks_project.Chap07.Lemma_7_26_4.DirectSourceComparison

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v w

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}

/- Domain-style sampling for Lemma 7.26.4:
- primary domain: effective descent for sheaves on slice sites, encoded by the pseudofunctor
  `J.pseudofunctorOver (Type (max u v))`;
- sampled owner API:
  `GrothendieckTopology.pseudofunctorOver`,
  `Pseudofunctor.IsStackFor`,
  `Pseudofunctor.isStackFor_ofArrows_iff`,
  `Pseudofunctor.IsStackFor.essSurj`,
  `Functor.EssSurj`,
  `GrothendieckTopology.Cover`;
- source-facing layer: the essential-surjectivity statement for descent data on a fixed cover
  `𝒰 : J.Cover U`;
- core/canonical owner: the fixed-cover stack condition
  `(J.pseudofunctorOver (Type (max u v))).IsStackFor (Presieve.ofArrows _ (fun I : 𝒰.Arrow ↦ I.f))`;
- bridge/view: the descent-data functor attached to the family of cover arrows
  `fun I : 𝒰.Arrow ↦ I.f`.

Primitive data are the site topology `J`, the object `U`, and the cover `𝒰 : J.Cover U`. The
fixed-cover stack condition is the canonical owner abstraction; the essential-surjectivity
statement for the descent-data functor is derived API of that owner. This file keeps the
source-facing `EssSurj` theorem and packages the same content once at the owner level so later
files can reuse it directly instead of rebuilding the stack proof.
-/

-- Proof sketch: view the family of slice-site sheaf categories as the pseudofunctor
-- `J.pseudofunctorOver (Type (max u v))`. Combine the prestack theorem from Lemma `7.26.1`
-- with essential surjectivity for the fixed cover to obtain the owner-level stack condition,
-- then recover the textbook `EssSurj` statement from that owner theorem.

variable [UnivLE.{max u v, w}]

/-- Lemma 7.26.4: for a covering `𝒰` of `U`, the canonical descent-data functor from sheaves on
the localized site `C / U` to coverwise glueing data on `𝒰` is essentially surjective. -/
theorem localizedSheafToCoverDescentFunctor_essSurj (𝒰 : J.Cover U) :
    ((J.pseudofunctorOver (Type w)).toDescentData fun I : 𝒰.Arrow ↦ I.f).EssSurj := by
  -- Read the source-facing statement directly from the fixed-cover essential-surjectivity witness.
  exact localized_cover_descent_essSurj (J := J) (U := U) 𝒰

#print axioms localizedSheafToCoverDescentFunctor_essSurj
end

end GrothendieckTopology
end CategoryTheory
