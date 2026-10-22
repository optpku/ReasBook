/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Path.Homotopic.Quotient

variable {X : Type u} [TopologicalSpace X] {w x y z : X}

/- Lemma 1.2.6: composition of path classes is associative; for endpoint-fixed homotopy classes
represented by composable paths `f`, `g`, and `h`, the classes of `h · (g · f)` and
`(h · g) · f` coincide. -/
recall trans_assoc (f : Path.Homotopic.Quotient w x) (g : Path.Homotopic.Quotient x y)
    (h : Path.Homotopic.Quotient y z) :
    trans (trans f g) h = trans f (trans g h)
