/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace IsPathConnectedCoveringMap

variable {p : E → B}

/-- Theorem 3.2.1: a path in the base of a covering map and a chosen point of the fiber over its
initial value determine a unique lifted path. -/
-- Proof sketch: convert `hp` to a mathlib covering map using
-- `IsPathConnectedCoveringMap.isCoveringMap`. Use `IsCoveringMap.exists_path_lifts` for existence,
-- and compare any other lift with the canonical one via `IsCoveringMap.eq_liftPath_iff'`.
theorem existsUnique_pathLift (hp : IsPathConnectedCoveringMap p) (gamma : C(I, B)) (e : E)
    (h0 : gamma 0 = p e) :
    ∃! Gamma : C(I, E), p ∘ Gamma = gamma ∧ Gamma 0 = e := by
  refine ⟨hp.isCoveringMap.liftPath gamma e h0, ?_, ?_⟩
  · exact ⟨hp.isCoveringMap.liftPath_lifts gamma e h0, hp.isCoveringMap.liftPath_zero gamma e h0⟩
  · intro Gamma hGamma
    exact (hp.isCoveringMap.eq_liftPath_iff' h0).2 hGamma

end IsPathConnectedCoveringMap
