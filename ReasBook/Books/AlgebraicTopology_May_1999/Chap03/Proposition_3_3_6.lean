/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Lemma_3_4_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory
open scoped Pointwise

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- Helper for Proposition 3.3.6: the transported image of the vertex group at a fiber point
coincides with the stabilizer of that point under fiber translation. -/
private theorem mapVertexGroup_range_eq_stabilizer (hp : Functor.IsCovering p) {b : B}
    (e : p.Fiber b) :
    by
      let hact : MulAction (b ⟶ b) (p.Fiber b) := by
        simpa using CategoryTheory.Functor.vertexGroupAction (fiberTranslationFunctor hp) b
      letI := hact
      exact e.2 ▸ (Functor.mapVertexGroup p e.1).range =
        MulAction.stabilizer (b ⟶ b) e := by
  rcases e with ⟨e, rfl⟩
  -- Reduce to the distinguished basepoint of the fiber, where Lemma 3.4.11 gives the exact
  -- stabilizer computation.
  simpa [fiberTranslationMulAction] using
    (fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e).symm

/-- Proposition 3.3.6: every conjugate of the subgroup `p(π(E,e))` attached to a chosen fiber
point `e` is the corresponding subgroup for another point of the same fiber. -/
-- Proof sketch: equip the fiber with the canonical owner action
-- `Functor.vertexGroupAction (fiberTranslationFunctor hp) b`. The
-- translated point has
-- stabilizer `MulAut.conj g • MulAction.stabilizer _ e` by
-- `MulAction.stabilizer_smul_eq_stabilizer_map_conj`, and the basepoint isotropy theorem
-- `fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range` identifies these stabilizers
-- with
-- the source-facing transported image subgroups.
theorem exists_fiberPoint_mapVertexGroup_range_eq_conjugate (hp : Functor.IsCovering p) {b : B}
    (e : p.Fiber b) (g : b ⟶ b) :
    ∃ e' : p.Fiber b,
      e'.2 ▸ (Functor.mapVertexGroup p e'.1).range =
        MulAut.conj g • (e.2 ▸ (Functor.mapVertexGroup p e.1).range) := by
  letI : MulAction (b ⟶ b) (p.Fiber b) := fiberTranslationMulAction hp b
  -- Follow the source proof: translate the chosen fiber point by the loop `g`.
  refine ⟨g • e, ?_⟩
  calc
    (g • e).2 ▸ (Functor.mapVertexGroup p (g • e).1).range
        = MulAction.stabilizer (b ⟶ b) (g • e) := by
          -- Rewrite the subgroup attached to the translated point as its stabilizer.
          simpa using mapVertexGroup_range_eq_stabilizer hp (g • e)
    _ = (MulAction.stabilizer (b ⟶ b) e).map (MulAut.conj g).toMonoidHom := by
          -- Translating a point conjugates its stabilizer inside the loop group.
          simpa using MulAction.stabilizer_smul_eq_stabilizer_map_conj g e
    _ = MulAut.conj g • MulAction.stabilizer (b ⟶ b) e := by
          rfl
    _ = MulAut.conj g • (e.2 ▸ (Functor.mapVertexGroup p e.1).range) := by
          -- Rewrite the original subgroup back from the stabilizer description.
          rw [mapVertexGroup_range_eq_stabilizer hp e]

end CategoryTheory.Functor.IsCovering
