module

public import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

/- Domain-style sampling for Definition 7.47.1:
- primary domain: sieves and their associated subpresheaves of representable presheaves;
- sampled owner abstractions:
  `CategoryTheory.Sieve`,
  `CategoryTheory.Sieve.functor`,
  `CategoryTheory.Sieve.functorInclusion`,
  `CategoryTheory.Subfunctor`;
- source-facing layer: a sieve on an object `U`;
- core/canonical owner: `Sieve U`;
- bridge/view layer: `S.functor` together with `S.functorInclusion`, exhibiting the sieve as a
  subfunctor of `yoneda.obj U`.

Primitive data are just the sieve itself, i.e. membership of arrows into `U` together with
downward closure under precomposition. The induced presheaf and its canonical mono into the
representable are derived API, so this file should recall the upstream owner and bridge
declarations directly rather than introduce a parallel local `subpresheaf-of-representable`
wrapper.
-/

/- Definition 7.47.1: a sieve on an object `U` of a category `C` is the canonical mathlib notion
`Sieve U`. For a sieve `S`, the associated subpresheaf of the representable
presheaf `h_U = yoneda.obj U` is the presheaf `S.functor`, equipped with its canonical inclusion
into `h_U`. -/
recall Sieve

/- Companion recall: a sieve `S` on `U` determines a presheaf `S.functor`, whose sections over
`T` are precisely the arrows `T ⟶ U` belonging to the sieve. -/
recall Sieve.functor

/- Companion recall: the presheaf attached to a sieve includes naturally into the representable
presheaf `yoneda.obj U`. -/
recall Sieve.functorInclusion

/- Companion recall: the canonical inclusion from the presheaf induced by a sieve to the Yoneda
presheaf is a monomorphism, so in the chapter's earlier `Subfunctor` language a sieve canonically
determines a subpresheaf of `h_U`. -/
recall Sieve.functorInclusion_is_mono
