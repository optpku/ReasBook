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
