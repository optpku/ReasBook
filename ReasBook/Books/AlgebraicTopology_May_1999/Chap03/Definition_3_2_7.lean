/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]

/-- Definition 3.2.7: a covering map in the sense of Definition 3.1.5 is universal when its total
space `E` is simply connected. -/
def IsUniversalCoveringMap (p : E → X) : Prop :=
  IsPathConnectedCoveringMap p ∧ SimplyConnectedSpace E

namespace IsUniversalCoveringMap

variable {p : E → X}

/-- A universal covering map is, in particular, a covering map in the sense of Definition 3.1.5. -/
theorem isPathConnectedCoveringMap (hp : IsUniversalCoveringMap p) :
    IsPathConnectedCoveringMap p := hp.1

/-- A universal covering map is surjective. -/
theorem surjective (hp : IsUniversalCoveringMap p) : Function.Surjective p :=
  hp.1.surjective

/-- A universal covering map is, in particular, a covering map. -/
theorem isCoveringMap (hp : IsUniversalCoveringMap p) : IsCoveringMap p :=
  hp.1.isCoveringMap

/-- The total space of a universal covering map is simply connected. -/
theorem simplyConnectedSpace (hp : IsUniversalCoveringMap p) : SimplyConnectedSpace E := hp.2


end IsUniversalCoveringMap
