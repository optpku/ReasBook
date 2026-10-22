/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

/- Example 2.2.3: the forgetful functor from topological spaces to sets is a basic example of a
functor. -/
#check (forget TopCat)

/- The forgetful functor from abelian groups to sets is another basic example of a functor. -/
#check (forget AddCommGrpCat)

/- The free abelian group construction defines a functor from sets to abelian groups. -/
recall AddCommGrpCat.free : Type u ⥤ AddCommGrpCat.{u}
