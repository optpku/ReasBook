/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

universe u

variable {E : Type u}

section ContinuousConstSMul

variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E]

/-- Proposition 3.45 (1): the closure of a convex subset of a real topological vector space is
convex. -/
theorem convex_closure_of_convex {C : Set E} (hC : Convex ℝ C) :
    Convex ℝ (closure C) := by
  simpa using hC.closure

/-- Proposition 3.45 (2): the interior of a convex subset of a real topological vector space is
convex. -/
theorem convex_interior_of_convex {C : Set E} (hC : Convex ℝ C) :
    Convex ℝ (interior C) := by
  simpa using hC.interior

end ContinuousConstSMul

section ContinuousSMul

variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Proposition 3.45 (3): if a convex set has nonempty interior, then taking the closure does not
change its interior. -/
theorem interior_closure_eq_interior_of_convex_nonempty_interior {C : Set E}
    (hC : Convex ℝ C) (hCint : (interior C).Nonempty) :
    interior (closure C) = interior C := by
  simpa using hC.interior_closure_eq_interior_of_nonempty_interior hCint

/-- Proposition 3.45 (4): if a convex set has nonempty interior, then the closure of its interior
is the closure of the set. -/
theorem closure_interior_eq_closure_of_convex_nonempty_interior {C : Set E}
    (hC : Convex ℝ C) (hCint : (interior C).Nonempty) :
    closure (interior C) = closure C := by
  simpa using hC.closure_interior_eq_closure_of_nonempty_interior hCint

end ContinuousSMul
