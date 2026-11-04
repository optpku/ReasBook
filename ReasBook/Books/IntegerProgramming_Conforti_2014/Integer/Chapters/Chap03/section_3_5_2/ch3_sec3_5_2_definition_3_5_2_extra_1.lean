/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

namespace Set

variable (𝕜 : Type*) [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]

/-- Definition 3.5.2-extra-1. A subset `Q` of a `𝕜`-module is a polytope if `Q` is the
convex hull of a finite set of vectors. -/
def IsPolytope (Q : Set E) : Prop :=
  ∃ V : Set E, V.Finite ∧ Q = convexHull 𝕜 V

end Set
