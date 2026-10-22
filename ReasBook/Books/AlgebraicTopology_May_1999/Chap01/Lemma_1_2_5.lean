/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Path.Homotopic.Quotient

variable {X : Type u} [TopologicalSpace X] {x y z : X}

/- Lemma 1.2.5: path composition is well defined on endpoint-fixed homotopy classes. For
`f : Path x y` and `g : Path y z`, the class of the concatenated path `f.trans g` depends only on
the classes of `f` and `g`, so `[g][f] = [g · f]`. -/
recall mk_trans (f : Path x y) (g : Path y z) :
  mk (f.trans g) = (mk f).trans (mk g)
