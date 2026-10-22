/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory Limits

noncomputable instance : Coreflective (forget₂ GrpCat MonCat) :=
  Coreflective.mk MonCat.units GrpCat.forget₂MonAdj

/-- The category of groups is cocomplete because it is a coreflective subcategory of monoids. -/
noncomputable instance : HasColimits GrpCat :=
  hasColimits_of_coreflective (forget₂ GrpCat MonCat)

/- Remark 2.6.8: the category of sets is complete and cocomplete, via the canonical instances
`HasLimits (Type u)` and `HasColimits (Type u)`. -/
#check (inferInstance : HasLimits (Type u))
#check (inferInstance : HasColimits (Type u))

/- The category of topological spaces is complete and cocomplete. -/
#check (inferInstance : HasLimits TopCat)
#check (inferInstance : HasColimits TopCat)

/- The category of based spaces, realized as `Under (⊤_ TopCat)`, is complete and cocomplete. -/
#check (inferInstance : HasLimits (Under (⊤_ TopCat)))
#check (inferInstance : HasColimits (Under (⊤_ TopCat)))

/- The category of groups is complete and cocomplete. -/
#check (inferInstance : HasLimits GrpCat)
#check (inferInstance : HasColimits GrpCat)

/- The category of abelian groups is complete and cocomplete. -/
#check (inferInstance : HasLimits AddCommGrpCat)
#check (inferInstance : HasColimits AddCommGrpCat)
