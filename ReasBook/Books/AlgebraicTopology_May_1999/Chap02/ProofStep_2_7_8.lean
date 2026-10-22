/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap02.Theorem_2_7_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped FundamentalGroupoid

noncomputable section

variable {X : Type u} [TopologicalSpace X]
variable {ι : Type v}

variable
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hPi : IsColimit (fundamental_groupoid_cover_cocone O))
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    (x : X)

/- ProofStep 2.7.8 is the bridge/view obtained by applying the canonical owner
`CategoryTheory.Functor.mapEnd` to the universal colimit-desc functor `hPi.desc S` at the object
`FundamentalGroupoid.mk x`. This restricts the universal functor `Π(X) ⥤ S.pt` to the vertex
group `π₁(X, x)`. -/
#check (hPi.desc S).mapEnd (FundamentalGroupoid.mk x)
