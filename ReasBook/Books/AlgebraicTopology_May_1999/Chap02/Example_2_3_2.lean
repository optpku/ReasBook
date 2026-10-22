/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

/- Example 2.3.2: the inclusion of a set `S` into the underlying set of its free abelian group
is the unit natural transformation of the free-forgetful adjunction, hence is natural in `S`. -/
#check (AddCommGrpCat.adj).unit

/- The naturality of this inclusion is the standard naturality of the unit of an adjunction. -/
#check (AddCommGrpCat.adj).unit_naturality
