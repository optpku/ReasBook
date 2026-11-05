module

public import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X : C}

/- Domain-style sampling for 7.49.3.1:
- primary domain: iterated refinement of sieves on a category;
- sampled owner abstractions:
  `Presieve.bind`,
  `Presieve.BindStruct`,
  `Sieve.bind`,
  `Sieve.BindStruct`;
- source-facing layer: the sieve obtained by refining each arrow of a sieve by a further sieve on
  its domain;
- core/canonical owner: `Sieve.bind`, whose owner interface is slightly more general and takes an
  initial `Presieve`;
- bridge/view layer: `Sieve.BindStruct` together with the structural conversion
  `Presieve.BindStruct.bind`.

Primitive data are the source-facing sieve `S` on `X` and the sieve-valued refinement family `R`.
At the owner level mathlib packages the same construction for an arbitrary initial presieve, so the
source sieve case is handled by direct recall of that canonical owner. The factorization package
`BindStruct` and the structural map from factorization data to membership are derived API owned
upstream by mathlib, so this file recalls those owners directly. The noncomputable selector
`Presieve.bind.bindStruct` is intentionally not exposed here because it chooses one witness from an
existential statement and is not part of the canonical public surface.
-/

/- 7.49.3.1: the source-facing refinement of a sieve by sieve-valued refinements is the canonical
owner `Sieve.bind`. Mathlib defines this owner slightly more generally for an initial presieve
`S`, and the sieve case of the source is the intended specialization. -/
recall Sieve.bind (S : Presieve X)
    (R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y) : Sieve X

/- Companion recall: a morphism `h : Z ⟶ X` in `Sieve.bind S R` is equivalently encoded by the
structured factorization datum `Sieve.BindStruct S R h`. This is the canonical factorization
interface for membership in a bound sieve. -/
recall Sieve.BindStruct (S : Presieve X)
    (R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y)
    {Z : C} (h : Z ⟶ X) : Type (max u v)

/- Companion recall: a factorization datum in `BindStruct` canonically determines membership in the
corresponding bound presieve, hence also in the sieve `Sieve.bind S R` when `R` is sieve-valued. -/
recall Presieve.BindStruct.bind
    {S : Presieve X} {R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y}
    {Z : C} {h : Z ⟶ X} (b : S.BindStruct R h) : S.bind R h

end CategoryTheory
