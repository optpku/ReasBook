module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/- Domain sampling:
- Primary domain: rigid monoidal category theory in a braided/symmetric monoidal category.
- Core/canonical declarations inspected:
  - `CategoryTheory.ExactPairing`
  - `CategoryTheory.BraidedCategory.exactPairing_swap`
  - `CategoryTheory.SymmetricCategory`
- Owner abstraction: `ExactPairing X Y`, with `BraidedCategory.exactPairing_swap` as the canonical
  derived construction that swaps a dual pairing through the braiding.
- Layer triage:
  - `core/canonical`: `ExactPairing` and `BraidedCategory.exactPairing_swap`;
  - `bridge/view`: specializing the braided construction to the symmetric case via the instance
    `[SymmetricCategory C]`.
- Primitive vs. derived:
  - primitive data: an exact pairing `ExactPairing X Y`;
  - derived API: the swapped exact pairing supplied by `BraidedCategory.exactPairing_swap`.
-/

/- Lemma 4.43.10: in a symmetric monoidal category, the swapped coevaluation and evaluation again
form an exact pairing. This is exactly the symmetric special case of the canonical braided owner
declaration `BraidedCategory.exactPairing_swap`. -/
recall BraidedCategory.exactPairing_swap

end CategoryTheory
