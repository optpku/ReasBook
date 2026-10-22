/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- Definition 3.2.6: a covering map `p : E → B` is regular, relative to a chosen basepoint
`e : E`, if `p` is a covering in the sense of Definition 3.1.5 and the image subgroup
`p_*(π₁(E,e)) ≤ π₁(B, p e)` is normal. -/
structure IsRegularCoveringMap (p : E → B) (e : E) : Prop
    extends toIsPathConnectedCoveringMap : IsPathConnectedCoveringMap p where
  /-- The image subgroup of the induced homomorphism on fundamental groups at `e` is normal in
  the fundamental group of the base at `p e`. -/
  normal_fundamentalGroup_map_range :
    ((FundamentalGroup.map
        ⟨p, (IsPathConnectedCoveringMap.isCoveringMap toIsPathConnectedCoveringMap).continuous⟩
        e).range).Normal

namespace IsRegularCoveringMap

variable {p : E → B} {e : E}

/-- A regular covering map is, in particular, a path-connected covering map. -/
theorem isPathConnectedCoveringMap (hp : IsRegularCoveringMap p e) :
    IsPathConnectedCoveringMap p :=
  hp.toIsPathConnectedCoveringMap

/-- A regular covering map is, in particular, a covering map. -/
theorem isCoveringMap (hp : IsRegularCoveringMap p e) : IsCoveringMap p :=
  hp.isPathConnectedCoveringMap.isCoveringMap

/-- A regular covering map is surjective. -/
theorem surjective (hp : IsRegularCoveringMap p e) : Function.Surjective p :=
  hp.isPathConnectedCoveringMap.surjective

/-- A regular covering map is, in particular, a path-connected covering map. -/
instance (hp : IsRegularCoveringMap p e) : IsPathConnectedCoveringMap p :=
  hp.isPathConnectedCoveringMap

end IsRegularCoveringMap
