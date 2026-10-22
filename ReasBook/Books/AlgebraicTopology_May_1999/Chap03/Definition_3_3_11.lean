/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]

/-- Definition 3.3.11 (1): a covering functor of groupoids is regular at `e` if the image of the
induced map on the vertex group at `e` is a normal subgroup of the vertex group at `p.obj e`. -/
def IsRegularCovering (p : E ⥤ B) (e : E) : Prop :=
  Functor.IsCovering p ∧ (Functor.mapVertexGroup p e).range.Normal

namespace IsRegularCovering

variable {p : E ⥤ B} {e : E}

/-- A regular covering functor is, in particular, a covering functor. -/
theorem isCovering (hp : IsRegularCovering p e) : Functor.IsCovering p :=
  hp.1

/-- In a regular covering functor, the image of the induced map on vertex groups at `e` is
normal. -/
theorem normal_mapVertexGroup_range (hp : IsRegularCovering p e) :
    (Functor.mapVertexGroup p e).range.Normal :=
  hp.2

instance (hp : IsRegularCovering p e) : Functor.IsCovering p :=
  hp.isCovering

end IsRegularCovering

/-- Definition 3.3.11 (2): a covering functor of groupoids is universal at `e` if the image of
the induced map on the vertex group at `e` is the trivial subgroup of the vertex group at
`p.obj e`. -/
def IsUniversalCovering (p : E ⥤ B) (e : E) : Prop :=
  Functor.IsCovering p ∧ (Functor.mapVertexGroup p e).range = ⊥

namespace IsUniversalCovering

variable {p : E ⥤ B} {e : E}

/-- A universal covering functor is, in particular, a covering functor. -/
theorem isCovering (hp : IsUniversalCovering p e) : Functor.IsCovering p :=
  hp.1

/-- In a universal covering functor, the image of the induced map on vertex groups at `e` is
trivial. -/
theorem mapVertexGroup_range_eq_bot (hp : IsUniversalCovering p e) :
    (Functor.mapVertexGroup p e).range = ⊥ :=
  hp.2

instance (hp : IsUniversalCovering p e) : Functor.IsCovering p :=
  hp.isCovering

/-- A universal covering functor is regular at the chosen base object. -/
-- Proof sketch: the trivial subgroup is normal, so the triviality condition on the image of the
-- induced vertex-group map implies the normality condition required for regularity.
theorem isRegularCovering (hp : IsUniversalCovering p e) : IsRegularCovering p e := by
  refine ⟨hp.isCovering, ?_⟩
  rw [hp.mapVertexGroup_range_eq_bot]
  exact (Subgroup.normal_bot : (⊥ : Subgroup (p.obj e ⟶ p.obj e)).Normal)

instance (hp : IsUniversalCovering p e) : IsRegularCovering p e :=
  hp.isRegularCovering

end IsUniversalCovering

end CategoryTheory.Functor
