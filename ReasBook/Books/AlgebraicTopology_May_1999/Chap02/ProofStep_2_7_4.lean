/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory FundamentalGroupoid
open Path.Homotopic.Quotient
open scoped FundamentalGroupoid

variable {X : Type u} [TopologicalSpace X]

/-- ProofStep 2.7.4: once a path homotopy square has been subdivided so that each small subsquare
lies inside a single cover member, the equality of the two boundary paths is reduced to the
endpoint-fixed homotopy relation already valid in that individual fundamental groupoid `Π(U)`.
Any functor out of `Π(U)` therefore identifies the two boundary paths, which is the local relation
used in the van Kampen subdivision argument. -/
-- Proof sketch: in a single open set `U`, endpoint-fixed homotopic paths define the same morphism
-- of `Π(U)` by the quotient relation on `Path.Homotopic.Quotient`. After rewriting the two arrows
-- with `FundamentalGroupoid.fromPath`, functoriality of `F` carries that equality into the target
-- category.
theorem functor_map_eq_of_homotopic_paths_in_open
    (U : TopologicalSpace.Opens (TopCat.of X))
    {C : Type v} [Category C]
    (F : πₓ (TopCat.of U) ⥤ C)
    {x y : U} {p q : Path x y}
    (h : Path.Homotopic p q) :
    F.map (fromPath ⟦p⟧) = F.map (fromPath ⟦q⟧) := by
  exact congrArg F.map ((fromPath_eq_iff_homotopic p q).2 h)
