/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

/- Example 2.1.3: standard examples of categories in mathlib include the category of types with
functions, the category of topological spaces with continuous maps, the category of groups with
homomorphisms, and the category of abelian groups with homomorphisms. For `Type u`, the canonical
owner is the large-category instance `CategoryTheory.types`. -/
#check (inferInstance : LargeCategory (Type u))

/- The bundled type `TopCat` carries the standard category of topological spaces and continuous
maps. -/
#check (inferInstance : Category TopCat)

/- The bundled type `GrpCat` carries the standard category of groups and group homomorphisms. -/
#check (inferInstance : Category GrpCat)

/- The bundled type `AddCommGrpCat` carries the standard category of abelian groups and
homomorphisms. -/
#check (inferInstance : Category AddCommGrpCat)
