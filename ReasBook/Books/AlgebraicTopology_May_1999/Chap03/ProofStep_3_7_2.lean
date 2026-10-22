/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Proposition_3_3_4
import AlgebraicTopology_May_1999.Chap03.Theorem_3_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open CategoryTheory FundamentalGroupoid
open CategoryTheory.Functor.IsCovering
open CategoryTheory.Groupoid.CategoryTheory

variable {E : Type u} {B : Type v} {X : Type w}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]

namespace IsPathConnectedCoveringMap

variable {p : E → B} [PathConnectedSpace X]

/-- ProofStep 3.7.2: applying the covering-groupoid lifting criterion to the induced covering
functor `hp.fundamentalGroupoidMap : Π(E) ⥤ Π(B)` reduces the covering-space lifting problem for
`f : X → B` to the
corresponding existence and uniqueness statement for a lift of `Π(f)`. -/
-- Proof sketch: Proposition 3.3.4 shows that `Π(p)` is a covering functor. Then Theorem 3.5.1
-- applies directly to the functor `Π(f) : Π(X) ⥤ Π(B)` and the chosen object `e₀` of the fiber of
-- `Π(p)` over `Π(f)(x)`.
theorem existsUnique_fundamentalGroupoidLift_iff_mapVertexGroup_range_le
    (hp : IsPathConnectedCoveringMap p) (f : C(X, B)) (x : X)
    (e₀ : hp.fundamentalGroupoidMap.Fiber ((FundamentalGroupoid.map f).obj (mk x))) :
    (∃! g : FundamentalGroupoid X ⥤ FundamentalGroupoid E,
      g ⋙ hp.fundamentalGroupoidMap = FundamentalGroupoid.map f ∧
        g.obj (mk x) = e₀.1) ↔
      ((FundamentalGroupoid.map f).mapVertexGroup (mk x)).range ≤
        e₀.2 ▸ (hp.fundamentalGroupoidMap.mapVertexGroup e₀.1).range := by
  letI : CategoryTheory.IsConnected (FundamentalGroupoid X) := by
    refine CategoryTheory.IsConnected.of_any_functor_const_on_obj ?_
    intro α F x y
    ext
    exact CategoryTheory.Discrete.eq_of_hom <|
      F.map (show x ⟶ y from ⟦PathConnectedSpace.somePath x.as y.as⟧)
  simpa using
    existsUnique_lift_iff_mapVertexGroup_range_le hp.fundamentalGroupoidMap_isCovering (mk x) e₀

end IsPathConnectedCoveringMap
