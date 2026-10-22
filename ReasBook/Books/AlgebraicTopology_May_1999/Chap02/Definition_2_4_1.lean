/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

variable (X : TopCat)

/- Definition 2.4.1: the category `T` of based spaces is the under category of the terminal
topological space, so its objects are spaces equipped with chosen basepoints and its morphisms are
continuous maps preserving those basepoints. -/
#check Under (⊤_ TopCat)

/- A based space with underlying space `X` is given primitively by a map from the one-point space
into `X`, equivalently by a chosen basepoint of `X`. -/
#check (Under.mk : (⊤_ TopCat ⟶ X) → Under (⊤_ TopCat))

/- The categorical structure on based spaces is the inherited category structure on this under
category. -/
#check (inferInstance : Category (Under (⊤_ TopCat)))
