/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 2.3.3: the free abelian group functor is left adjoint to the forgetful functor
from abelian groups to sets, meaning that morphisms from the free abelian group on a set `S`
to an abelian group `A` are naturally identified with functions from `S` to the underlying set
of `A`. -/
#check AddCommGrpCat.adj
